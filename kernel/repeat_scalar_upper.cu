#include <cuda_runtime.h>

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <string>
#include <vector>

namespace {

constexpr int kDirections = 8;
constexpr int kDx[kDirections] = {-1, -1, -1, 0, 0, 1, 1, 1};
constexpr int kDy[kDirections] = {-1, 0, 1, -1, 1, -1, 0, 1};
__device__ __constant__ int kDeviceDx[kDirections] = {-1, -1, -1, 0, 0, 1, 1, 1};
__device__ __constant__ int kDeviceDy[kDirections] = {-1, 0, 1, -1, 1, -1, 0, 1};
__device__ __constant__ int kDeviceReverse[kDirections] = {7, 6, 5, 4, 3, 2, 1, 0};

void cuda_check(cudaError_t error, const char* expression, const char* file,
                int line) {
  if (error == cudaSuccess) return;
  std::cerr << file << ':' << line << " CUDA failure in " << expression << ": "
            << cudaGetErrorString(error) << '\n';
  std::exit(2);
}
#define CUDA_CHECK(expression) cuda_check((expression), #expression, __FILE__, __LINE__)

template <class T>
void read_scalar(std::ifstream& input, T& value) {
  input.read(reinterpret_cast<char*>(&value), sizeof(value));
}
template <class T>
void read_vector(std::ifstream& input, std::vector<T>& values) {
  input.read(reinterpret_cast<char*>(values.data()),
             static_cast<std::streamsize>(values.size() * sizeof(T)));
}

struct Graph {
  int q = 0;
  std::uint64_t cells = 0, incidences = 0, types = 0;
  std::vector<std::uint8_t> clean;
  std::vector<std::uint64_t> offsets, component_offsets;
  std::vector<std::int32_t> incidence_type;
  std::vector<std::uint32_t> incidence_site, component_incidences;
};

Graph load_graph(const std::string& path) {
  std::ifstream input(path, std::ios::binary);
  if (!input) throw std::runtime_error("cannot open graph");
  std::uint64_t magic = 0;
  Graph graph;
  read_scalar(input, magic);
  read_scalar(input, graph.q);
  read_scalar(input, graph.cells);
  read_scalar(input, graph.incidences);
  read_scalar(input, graph.types);
  if (magic != 0x4552313231325048ULL) throw std::runtime_error("bad graph magic");
  graph.clean.resize(graph.cells);
  graph.offsets.resize(graph.cells + 1);
  graph.incidence_type.resize(graph.incidences);
  std::vector<std::int16_t> skip_dx(graph.incidences), skip_dy(graph.incidences);
  read_vector(input, graph.clean);
  read_vector(input, graph.offsets);
  read_vector(input, graph.incidence_type);
  read_vector(input, skip_dx);
  read_vector(input, skip_dy);
  if (!input) throw std::runtime_error("truncated graph");
  graph.incidence_site.resize(graph.incidences);
  for (std::uint64_t site = 0; site < graph.cells; ++site)
    for (auto k = graph.offsets[site]; k < graph.offsets[site + 1]; ++k)
      graph.incidence_site[k] = static_cast<std::uint32_t>(site);
  graph.component_offsets.assign(graph.types + 1, 0);
  for (int type : graph.incidence_type)
    ++graph.component_offsets[static_cast<std::size_t>(type) + 1];
  for (std::uint64_t type = 0; type < graph.types; ++type)
    graph.component_offsets[type + 1] += graph.component_offsets[type];
  auto cursor = graph.component_offsets;
  graph.component_incidences.resize(graph.incidences);
  for (std::uint32_t k = 0; k < graph.incidences; ++k)
    graph.component_incidences[cursor[graph.incidence_type[k]]++] = k;
  return graph;
}

template <class T>
T* device_copy(const std::vector<T>& host) {
  T* device = nullptr;
  CUDA_CHECK(cudaMalloc(&device, host.size() * sizeof(T)));
  CUDA_CHECK(cudaMemcpy(device, host.data(), host.size() * sizeof(T),
                        cudaMemcpyHostToDevice));
  return device;
}

struct DeviceGraph {
  std::uint8_t* clean;
  std::uint64_t* offsets;
  std::int32_t* incidence_type;
  std::uint32_t* incidence_site;
  std::uint64_t* component_offsets;
  std::uint32_t* component_incidences;
};

__global__ void site_sums_float_up(
    int q, std::uint64_t cells, const std::uint8_t* clean,
    const std::uint64_t* offsets, const float* a, const float* t,
    double* sum_a, double* incoming_t) {
  const auto site = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x + threadIdx.x;
  if (site >= cells) return;
  double sa = 0.0;
  for (auto k = offsets[site]; k < offsets[site + 1]; ++k)
    sa = __dadd_ru(sa, static_cast<double>(a[k]));
  double st = 0.0;
  if (clean[site]) {
    const int x = static_cast<int>(site / q), y = static_cast<int>(site % q);
    for (int d = 0; d < kDirections; ++d) {
      const int ux = (x + kDeviceDx[d] + q) % q;
      const int uy = (y + kDeviceDy[d] + q) % q;
      const auto u = static_cast<std::uint64_t>(ux) * q + uy;
      if (clean[u])
        st = __dadd_ru(st, static_cast<double>(t[u * kDirections + kDeviceReverse[d]]));
    }
  }
  sum_a[site] = sa;
  incoming_t[site] = st;
}

__global__ void component_sums_float_up(
    std::uint64_t types, const std::uint64_t* component_offsets,
    const std::uint32_t* component_incidences, const float* b, double* sum_b) {
  const auto type = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x + threadIdx.x;
  if (type >= types) return;
  double value = 0.0;
  for (auto j = component_offsets[type]; j < component_offsets[type + 1]; ++j)
    value = __dadd_ru(value, static_cast<double>(b[component_incidences[j]]));
  sum_b[type] = value;
}

__global__ void inner_B_up(
    int q, std::uint64_t incidences, std::uint64_t cells,
    const std::uint8_t* clean, const std::int32_t* incidence_type,
    const std::uint32_t* incidence_site, const float* a, const float* b,
    const float* t, const double* sum_a, const double* incoming_t,
    const double* sum_b, float* out_a, float* out_b, float* out_t) {
  const auto k = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x + threadIdx.x;
  if (k < incidences) {
    out_a[k] = __double2float_ru(
        __dsub_ru(sum_b[incidence_type[k]], static_cast<double>(b[k])));
    out_b[k] = 0.0F;
  }
  if (k < cells * kDirections) {
    const auto site = k / kDirections;
    const int d = static_cast<int>(k % kDirections);
    const int x = static_cast<int>(site / q), y = static_cast<int>(site % q);
    const int ux = (x + kDeviceDx[d] + q) % q;
    const int uy = (y + kDeviceDy[d] + q) % q;
    const auto u = static_cast<std::uint64_t>(ux) * q + uy;
    if (!clean[site] || !clean[u]) {
      out_t[k] = 0.0F;
    } else {
      double value = __dadd_ru(sum_a[site], incoming_t[site]);
      value = __dsub_ru(value,
          static_cast<double>(t[u * kDirections + kDeviceReverse[d]]));
      out_t[k] = __double2float_ru(value);
    }
  }
}

__global__ void H_up(
    int q, double q_up, std::uint64_t incidences, std::uint64_t cells,
    const std::uint8_t* clean, const std::int32_t* incidence_type,
    const std::uint32_t* incidence_site, const float* a, const float* b,
    const float* t, const double* sum_a, const double* incoming_t,
    const double* sum_b, float* out_a, float* out_b, float* out_t) {
  const auto k = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x + threadIdx.x;
  if (k < incidences) {
    double to_b = __dadd_ru(sum_a[incidence_site[k]], incoming_t[incidence_site[k]]);
    to_b = __dsub_ru(to_b, static_cast<double>(a[k]));
    out_b[k] = __double2float_ru(to_b);
    double to_a = __dsub_ru(sum_b[incidence_type[k]], static_cast<double>(b[k]));
    out_a[k] = __double2float_ru(__dmul_ru(q_up, to_a));
  }
  if (k < cells * kDirections) {
    const auto site = k / kDirections;
    const int d = static_cast<int>(k % kDirections);
    const int x = static_cast<int>(site / q), y = static_cast<int>(site % q);
    const int ux = (x + kDeviceDx[d] + q) % q;
    const int uy = (y + kDeviceDy[d] + q) % q;
    const auto u = static_cast<std::uint64_t>(ux) * q + uy;
    if (!clean[site] || !clean[u]) {
      out_t[k] = 0.0F;
    } else {
      double value = __dadd_ru(sum_a[site], incoming_t[site]);
      value = __dsub_ru(value,
          static_cast<double>(t[u * kDirections + kDeviceReverse[d]]));
      out_t[k] = __double2float_ru(__dmul_ru(q_up, value));
    }
  }
}

__global__ void accumulate_up(std::uint64_t count, double coefficient,
                              const float* source, double* target) {
  const auto k = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x + threadIdx.x;
  if (k < count)
    target[k] = __dadd_ru(target[k], __dmul_ru(coefficient,
                                               static_cast<double>(source[k])));
}

__global__ void site_sums_double_up(
    int q, std::uint64_t cells, const std::uint8_t* clean,
    const std::uint64_t* offsets, const double* a, const double* t,
    double* sum_a, double* incoming_t) {
  const auto site = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x + threadIdx.x;
  if (site >= cells) return;
  double sa = 0.0, st = 0.0;
  for (auto k = offsets[site]; k < offsets[site + 1]; ++k)
    sa = __dadd_ru(sa, a[k]);
  if (clean[site]) {
    const int x = static_cast<int>(site / q), y = static_cast<int>(site % q);
    for (int d = 0; d < kDirections; ++d) {
      const int ux = (x + kDeviceDx[d] + q) % q;
      const int uy = (y + kDeviceDy[d] + q) % q;
      const auto u = static_cast<std::uint64_t>(ux) * q + uy;
      if (clean[u]) st = __dadd_ru(st, t[u * kDirections + kDeviceReverse[d]]);
    }
  }
  sum_a[site] = sa;
  incoming_t[site] = st;
}

__global__ void component_sums_double_up(
    std::uint64_t types, const std::uint64_t* component_offsets,
    const std::uint32_t* component_incidences, const double* b, double* sum_b) {
  const auto type = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x + threadIdx.x;
  if (type >= types) return;
  double value = 0.0;
  for (auto j = component_offsets[type]; j < component_offsets[type + 1]; ++j)
    value = __dadd_ru(value, b[component_incidences[j]]);
  sum_b[type] = value;
}

__global__ void outer_B_up(
    int q, std::uint64_t incidences, std::uint64_t cells,
    const std::uint8_t* clean, const std::int32_t* incidence_type,
    const double* b, const double* t, const double* sum_a,
    const double* incoming_t, const double* sum_b, double* out_a,
    double* out_t) {
  const auto k = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x + threadIdx.x;
  if (k < incidences)
    out_a[k] = __dsub_ru(sum_b[incidence_type[k]], b[k]);
  if (k < cells * kDirections) {
    const auto site = k / kDirections;
    const int d = static_cast<int>(k % kDirections);
    const int x = static_cast<int>(site / q), y = static_cast<int>(site % q);
    const int ux = (x + kDeviceDx[d] + q) % q;
    const int uy = (y + kDeviceDy[d] + q) % q;
    const auto u = static_cast<std::uint64_t>(ux) * q + uy;
    if (!clean[site] || !clean[u]) out_t[k] = 0.0;
    else {
      double value = __dadd_ru(sum_a[site], incoming_t[site]);
      out_t[k] = __dsub_ru(value, t[u * kDirections + kDeviceReverse[d]]);
    }
  }
}

void sync() {
  CUDA_CHECK(cudaGetLastError());
  CUDA_CHECK(cudaDeviceSynchronize());
}

}  // namespace

int main(int argc, char** argv) {
  if (argc != 3) {
    std::cerr << "usage: repeat_scalar_upper GRAPH WITNESS\n";
    return 1;
  }
  Graph graph = load_graph(argv[1]);
  const std::uint64_t tail_states = graph.cells * kDirections;
  std::ifstream witness(argv[2], std::ios::binary);
  std::uint64_t magic = 0, wi = 0, wt = 0;
  read_scalar(witness, magic); read_scalar(witness, wi); read_scalar(witness, wt);
  if (magic != 0x455231325749544EULL || wi != graph.incidences || wt != tail_states)
    throw std::runtime_error("bad witness header");
  std::vector<float> ha(graph.incidences), hb(graph.incidences), ht(tail_states);
  read_vector(witness, ha); read_vector(witness, hb); read_vector(witness, ht);
  if (!witness) throw std::runtime_error("truncated witness");

  DeviceGraph d{device_copy(graph.clean), device_copy(graph.offsets),
                device_copy(graph.incidence_type), device_copy(graph.incidence_site),
                device_copy(graph.component_offsets), device_copy(graph.component_incidences)};
  float *a = device_copy(ha), *b = device_copy(hb), *t = device_copy(ht);
  float *next_a = nullptr, *next_b = nullptr, *next_t = nullptr;
  double *sum_a = nullptr, *incoming_t = nullptr, *sum_b = nullptr;
  CUDA_CHECK(cudaMalloc(&next_a, graph.incidences * sizeof(float)));
  CUDA_CHECK(cudaMalloc(&next_b, graph.incidences * sizeof(float)));
  CUDA_CHECK(cudaMalloc(&next_t, tail_states * sizeof(float)));
  CUDA_CHECK(cudaMalloc(&sum_a, graph.cells * sizeof(double)));
  CUDA_CHECK(cudaMalloc(&incoming_t, graph.cells * sizeof(double)));
  CUDA_CHECK(cudaMalloc(&sum_b, graph.types * sizeof(double)));
  const int threads = 128;
  auto blocks = [&](std::uint64_t n) { return static_cast<unsigned>((n + threads - 1) / threads); };

  site_sums_float_up<<<blocks(graph.cells), threads>>>(
      graph.q, graph.cells, d.clean, d.offsets, a, t, sum_a, incoming_t);
  component_sums_float_up<<<blocks(graph.types), threads>>>(
      graph.types, d.component_offsets, d.component_incidences, b, sum_b);
  inner_B_up<<<blocks(std::max(graph.incidences, tail_states)), threads>>>(
      graph.q, graph.incidences, graph.cells, d.clean, d.incidence_type,
      d.incidence_site, a, b, t, sum_a, incoming_t, sum_b,
      next_a, next_b, next_t);
  std::swap(a, next_a); std::swap(b, next_b); std::swap(t, next_t);
  sync();

  constexpr int outputs = 4;
  double *acc_a[outputs], *acc_b[outputs], *acc_t[outputs];
  for (int j = 0; j < outputs; ++j) {
    CUDA_CHECK(cudaMalloc(&acc_a[j], graph.incidences * sizeof(double)));
    CUDA_CHECK(cudaMalloc(&acc_b[j], graph.incidences * sizeof(double)));
    CUDA_CHECK(cudaMalloc(&acc_t[j], tail_states * sizeof(double)));
    CUDA_CHECK(cudaMemset(acc_a[j], 0, graph.incidences * sizeof(double)));
    CUDA_CHECK(cudaMemset(acc_b[j], 0, graph.incidences * sizeof(double)));
    CUDA_CHECK(cudaMemset(acc_t[j], 0, tail_states * sizeof(double)));
  }
  static constexpr double fresh_table[21] = {
      1.0, 1.0, .854, .652, .442, .269, .147, .073, .033, .0137,
      .0053, .0019, .00061, .00019, .000053, .000014, .0000036,
      .00000084, .00000019, .00000004, .000000008};
  const double q_up = std::nextafter(22751.0 / 1000000.0,
                                     std::numeric_limits<double>::infinity());
  for (int power = 0; power <= 400; ++power) {
    const int fresh_count = std::min(20, power / 2);
    const double coefficient = power <= 20 ? 1.0 :
        std::nextafter(fresh_table[fresh_count], std::numeric_limits<double>::infinity());
    bool active[outputs] = {power <= 40, power <= 24,
                            power >= 25, power >= 41};
    double coeff[outputs] = {coefficient, coefficient, coefficient, 1.0};
    for (int j = 0; j < outputs; ++j) if (active[j]) {
      accumulate_up<<<blocks(graph.incidences), threads>>>(graph.incidences, coeff[j], a, acc_a[j]);
      accumulate_up<<<blocks(graph.incidences), threads>>>(graph.incidences, coeff[j], b, acc_b[j]);
      accumulate_up<<<blocks(tail_states), threads>>>(tail_states, coeff[j], t, acc_t[j]);
    }
    if (power == 400) break;
    site_sums_float_up<<<blocks(graph.cells), threads>>>(
        graph.q, graph.cells, d.clean, d.offsets, a, t, sum_a, incoming_t);
    component_sums_float_up<<<blocks(graph.types), threads>>>(
        graph.types, d.component_offsets, d.component_incidences, b, sum_b);
    H_up<<<blocks(std::max(graph.incidences, tail_states)), threads>>>(
        graph.q, q_up, graph.incidences, graph.cells, d.clean,
        d.incidence_type, d.incidence_site, a, b, t, sum_a, incoming_t,
        sum_b, next_a, next_b, next_t);
    std::swap(a, next_a); std::swap(b, next_b); std::swap(t, next_t);
    if ((power + 1) % 25 == 0) {
      sync();
      std::cerr << "upper_power=" << power + 1 << '\n';
    }
  }
  sync();

  const char* names[outputs] = {
      "tmp/repeat_scalar_upper_s0_0_40_u.bin",
      "tmp/repeat_scalar_upper_s1_0_24_u.bin",
      "tmp/repeat_scalar_upper_fresh_25_400_u.bin",
      "tmp/repeat_scalar_upper_unit_41_400_u.bin"};
  std::vector<double> host_a(graph.incidences), host_t(tail_states);
  std::vector<double> zero_b(graph.incidences, 0.0);
  double *out_a = nullptr, *out_t = nullptr;
  CUDA_CHECK(cudaMalloc(&out_a, graph.incidences * sizeof(double)));
  CUDA_CHECK(cudaMalloc(&out_t, tail_states * sizeof(double)));
  for (int j = 0; j < outputs; ++j) {
    site_sums_double_up<<<blocks(graph.cells), threads>>>(
        graph.q, graph.cells, d.clean, d.offsets, acc_a[j], acc_t[j],
        sum_a, incoming_t);
    component_sums_double_up<<<blocks(graph.types), threads>>>(
        graph.types, d.component_offsets, d.component_incidences,
        acc_b[j], sum_b);
    outer_B_up<<<blocks(std::max(graph.incidences, tail_states)), threads>>>(
        graph.q, graph.incidences, graph.cells, d.clean, d.incidence_type,
        acc_b[j], acc_t[j], sum_a, incoming_t, sum_b, out_a, out_t);
    sync();
    CUDA_CHECK(cudaMemcpy(host_a.data(), out_a, graph.incidences * sizeof(double), cudaMemcpyDeviceToHost));
    CUDA_CHECK(cudaMemcpy(host_t.data(), out_t, tail_states * sizeof(double), cudaMemcpyDeviceToHost));
    std::ofstream output(names[j], std::ios::binary | std::ios::trunc);
    const std::uint64_t out_magic = 0x455231325749544EULL;
    output.write(reinterpret_cast<const char*>(&out_magic), sizeof(out_magic));
    output.write(reinterpret_cast<const char*>(&graph.incidences), sizeof(graph.incidences));
    output.write(reinterpret_cast<const char*>(&tail_states), sizeof(tail_states));
    output.write(reinterpret_cast<const char*>(host_a.data()),
                 static_cast<std::streamsize>(host_a.size() * sizeof(double)));
    output.write(reinterpret_cast<const char*>(zero_b.data()),
                 static_cast<std::streamsize>(zero_b.size() * sizeof(double)));
    output.write(reinterpret_cast<const char*>(host_t.data()),
                 static_cast<std::streamsize>(host_t.size() * sizeof(double)));
    if (!output) throw std::runtime_error("output write failed");
    std::cout << "saved_upper_image=" << names[j] << '\n';
  }
  return 0;
}
