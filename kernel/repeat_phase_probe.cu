#include <cuda_runtime.h>

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <numeric>
#include <string>
#include <utility>
#include <vector>

namespace {

#ifndef REPEAT_TAIL_Q
#define REPEAT_TAIL_Q 0.022751F
#endif
constexpr float kTailQ = REPEAT_TAIL_Q;
constexpr double kTailQExact = 22751.0 / 1000000.0;
constexpr double kPi = 3.141592653589793238462643383279502884;
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

#define CUDA_CHECK(expression) \
  cuda_check((expression), #expression, __FILE__, __LINE__)

struct Graph {
  int q = 0;
  std::uint64_t cells = 0;
  std::uint64_t incidences = 0;
  std::uint64_t types = 0;
  std::vector<std::uint8_t> clean;
  std::vector<std::uint64_t> offsets;
  std::vector<std::int32_t> incidence_type;
  std::vector<std::int16_t> anchor_dx;
  std::vector<std::int16_t> anchor_dy;
  std::vector<std::uint32_t> incidence_site;
  std::vector<std::uint64_t> component_offsets;
  std::vector<std::uint32_t> component_incidences;
};

template <class T>
void read_scalar(std::ifstream& input, T& value) {
  input.read(reinterpret_cast<char*>(&value), sizeof(value));
}

template <class T>
void read_vector(std::ifstream& input, std::vector<T>& values) {
  input.read(reinterpret_cast<char*>(values.data()),
             static_cast<std::streamsize>(values.size() * sizeof(T)));
}

Graph load_graph(const std::string& path) {
  std::ifstream input(path, std::ios::binary);
  if (!input) throw std::runtime_error("cannot open graph dump");
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
  graph.anchor_dx.resize(graph.incidences);
  graph.anchor_dy.resize(graph.incidences);
  read_vector(input, graph.clean);
  read_vector(input, graph.offsets);
  read_vector(input, graph.incidence_type);
  read_vector(input, graph.anchor_dx);
  read_vector(input, graph.anchor_dy);
  if (!input) throw std::runtime_error("truncated graph dump");

  graph.incidence_site.resize(graph.incidences);
  for (std::uint64_t site = 0; site < graph.cells; ++site)
    for (auto k = graph.offsets[site]; k < graph.offsets[site + 1]; ++k)
      graph.incidence_site[k] = static_cast<std::uint32_t>(site);

  graph.component_offsets.assign(graph.types + 1, 0);
  for (const auto type : graph.incidence_type)
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

__device__ float2 add(float2 a, float2 b) {
  return make_float2(a.x + b.x, a.y + b.y);
}

__device__ float2 sub(float2 a, float2 b) {
  return make_float2(a.x - b.x, a.y - b.y);
}

__device__ float2 scale(float2 a, float value) {
  return make_float2(a.x * value, a.y * value);
}

__device__ float2 multiply(float2 a, float2 b) {
  return make_float2(a.x * b.x - a.y * b.y,
                     a.x * b.y + a.y * b.x);
}

__global__ void real_site_sums(
    int q, std::uint64_t cells, const std::uint8_t* clean,
    const std::uint64_t* offsets, const float* a, const float* t,
    float* sum_a, float* incoming_t) {
  const auto site = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x +
                    threadIdx.x;
  if (site >= cells) return;
  float a_sum = 0.0F;
  for (auto k = offsets[site]; k < offsets[site + 1]; ++k) a_sum += a[k];
  sum_a[site] = a_sum;
  if (!clean[site]) {
    incoming_t[site] = 0.0F;
    return;
  }
  const int x = static_cast<int>(site / q);
  const int y = static_cast<int>(site % q);
  float incoming = 0.0F;
  for (int d = 0; d < kDirections; ++d) {
    const int ux = (x + kDeviceDx[d] + q) % q;
    const int uy = (y + kDeviceDy[d] + q) % q;
    const auto u = static_cast<std::uint64_t>(ux) * q + uy;
    if (clean[u]) incoming += t[u * kDirections + kDeviceReverse[d]];
  }
  incoming_t[site] = incoming;
}

__global__ void real_component_sums(
    std::uint64_t types, const std::uint64_t* component_offsets,
    const std::uint32_t* component_incidences, const float* b,
    float* sum_b) {
  const auto type = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x +
                    threadIdx.x;
  if (type >= types) return;
  float value = 0.0F;
  for (auto j = component_offsets[type]; j < component_offsets[type + 1]; ++j)
    value += b[component_incidences[j]];
  sum_b[type] = value;
}

__global__ void real_incidence_update(
    std::uint64_t incidences, const std::int32_t* incidence_type,
    const std::uint32_t* incidence_site, const float* a, const float* b,
    const float* sum_a, const float* incoming_t, const float* sum_b,
    float* next_a, float* next_b) {
  const auto k = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x +
                 threadIdx.x;
  if (k >= incidences) return;
  const auto site = incidence_site[k];
  next_b[k] = sum_a[site] - a[k] + incoming_t[site];
  next_a[k] = kTailQ * (sum_b[incidence_type[k]] - b[k]);
}

__global__ void real_tail_update(
    int q, std::uint64_t cells, const std::uint8_t* clean,
    const float* sum_a, const float* incoming_t, const float* t,
    float* next_t) {
  const auto edge = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x +
                    threadIdx.x;
  if (edge >= cells * kDirections) return;
  const auto site = edge / kDirections;
  const int d = static_cast<int>(edge % kDirections);
  if (!clean[site]) {
    next_t[edge] = 0.0F;
    return;
  }
  const int x = static_cast<int>(site / q);
  const int y = static_cast<int>(site % q);
  const int ux = (x + kDeviceDx[d] + q) % q;
  const int uy = (y + kDeviceDy[d] + q) % q;
  const auto u = static_cast<std::uint64_t>(ux) * q + uy;
  if (!clean[u]) {
    next_t[edge] = 0.0F;
    return;
  }
  next_t[edge] =
      kTailQ * (sum_a[site] + incoming_t[site] -
                t[u * kDirections + kDeviceReverse[d]]);
}

__global__ void initialize_real(std::uint64_t count, float* values,
                                float value) {
  const auto k = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x +
                 threadIdx.x;
  if (k < count) values[k] = value;
}

__global__ void initialize_real_tail(int q, std::uint64_t cells,
                                     const std::uint8_t* clean, float* t) {
  const auto edge = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x +
                    threadIdx.x;
  if (edge >= cells * kDirections) return;
  const auto site = edge / kDirections;
  const int d = static_cast<int>(edge % kDirections);
  const int x = static_cast<int>(site / q);
  const int y = static_cast<int>(site % q);
  const int ux = (x + kDeviceDx[d] + q) % q;
  const int uy = (y + kDeviceDy[d] + q) % q;
  const auto u = static_cast<std::uint64_t>(ux) * q + uy;
  t[edge] = clean[site] && clean[u] ? 1.0F : 0.0F;
}

__global__ void complex_site_sums(
    int q, int batch, std::uint64_t cells, const std::uint8_t* clean,
    const std::uint64_t* offsets, const double2* a, const double2* t,
    double2* sum_a, double2* incoming_t) {
  const auto site = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x +
                    threadIdx.x;
  if (site >= cells) return;
  for (int lane = 0; lane < batch; ++lane) {
    double2 a_sum = make_double2(0.0, 0.0);
    for (auto k = offsets[site]; k < offsets[site + 1]; ++k) {
      const auto value = a[k * batch + lane];
      a_sum.x += static_cast<double>(value.x);
      a_sum.y += static_cast<double>(value.y);
    }
    sum_a[site * batch + lane] = a_sum;
    double2 incoming = make_double2(0.0, 0.0);
    if (clean[site]) {
      const int x = static_cast<int>(site / q);
      const int y = static_cast<int>(site % q);
      for (int d = 0; d < kDirections; ++d) {
        const int ux = (x + kDeviceDx[d] + q) % q;
        const int uy = (y + kDeviceDy[d] + q) % q;
        const auto u = static_cast<std::uint64_t>(ux) * q + uy;
        if (clean[u]) {
          const auto value =
              t[(u * kDirections + kDeviceReverse[d]) * batch + lane];
          incoming.x += static_cast<double>(value.x);
          incoming.y += static_cast<double>(value.y);
        }
      }
    }
    incoming_t[site * batch + lane] = incoming;
  }
}

__global__ void rhs_site_sums_double(
    int q, std::uint64_t cells, const std::uint8_t* clean,
    const std::uint64_t* offsets, const float* a, const float* t,
    double* sum_a, double* incoming_t) {
  const auto site = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x +
                    threadIdx.x;
  if (site >= cells) return;
  double a_sum = 0.0;
  for (auto k = offsets[site]; k < offsets[site + 1]; ++k)
    a_sum += static_cast<double>(a[k]);
  sum_a[site] = a_sum;
  double incoming = 0.0;
  if (clean[site]) {
    const int x = static_cast<int>(site / q);
    const int y = static_cast<int>(site % q);
    for (int d = 0; d < kDirections; ++d) {
      const int ux = (x + kDeviceDx[d] + q) % q;
      const int uy = (y + kDeviceDy[d] + q) % q;
      const auto u = static_cast<std::uint64_t>(ux) * q + uy;
      if (clean[u])
        incoming += static_cast<double>(
            t[u * kDirections + kDeviceReverse[d]]);
    }
  }
  incoming_t[site] = incoming;
}

__global__ void rhs_component_sums_double(
    std::uint64_t types, const std::uint64_t* component_offsets,
    const std::uint32_t* component_incidences, const float* b,
    double* sum_b) {
  const auto type = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x +
                    threadIdx.x;
  if (type >= types) return;
  double value = 0.0;
  for (auto j = component_offsets[type]; j < component_offsets[type + 1]; ++j)
    value += static_cast<double>(b[component_incidences[j]]);
  sum_b[type] = value;
}

__global__ void complex_component_sums(
    int batch, std::uint64_t types, const std::uint64_t* component_offsets,
    const std::uint32_t* component_incidences, const double2* b,
    double2* sum_b) {
  const auto type = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x +
                    threadIdx.x;
  if (type >= types) return;
  for (int lane = 0; lane < batch; ++lane) {
    double2 value = make_double2(0.0, 0.0);
    for (auto j = component_offsets[type]; j < component_offsets[type + 1]; ++j) {
      const auto term =
          b[static_cast<std::uint64_t>(component_incidences[j]) * batch + lane];
      value.x += static_cast<double>(term.x);
      value.y += static_cast<double>(term.y);
    }
    sum_b[type * batch + lane] = value;
  }
}

__global__ void complex_incidence_update(
    int batch, std::uint64_t incidences, const std::int32_t* incidence_type,
    const std::uint32_t* incidence_site, const float2* incidence_phase,
    const double2* a, const double2* b, const double2* sum_a,
    const double2* incoming_t, const double2* sum_b, double2* next_a,
    double2* next_b) {
  const auto k = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x +
                 threadIdx.x;
  if (k >= incidences) return;
  const auto site = incidence_site[k];
  for (int lane = 0; lane < batch; ++lane) {
    const auto index = k * batch + lane;
    const auto phase = incidence_phase[index];
    const auto conjugate = make_float2(phase.x, -phase.y);
    const auto site_sum = sum_a[static_cast<std::uint64_t>(site) * batch + lane];
    const auto tail_sum = incoming_t[static_cast<std::uint64_t>(site) * batch + lane];
    const double to_component_x = site_sum.x + tail_sum.x - a[index].x;
    const double to_component_y = site_sum.y + tail_sum.y - a[index].y;
    next_b[index] = make_double2(
        static_cast<double>(phase.x) * to_component_x -
            static_cast<double>(phase.y) * to_component_y,
        static_cast<double>(phase.x) * to_component_y +
            static_cast<double>(phase.y) * to_component_x);
    const auto component_sum =
        sum_b[static_cast<std::uint64_t>(incidence_type[k]) * batch + lane];
    const double to_site_x = component_sum.x - b[index].x;
    const double to_site_y = component_sum.y - b[index].y;
    next_a[index] = make_double2(
        kTailQExact * (static_cast<double>(conjugate.x) * to_site_x -
                       static_cast<double>(conjugate.y) * to_site_y),
        kTailQExact * (static_cast<double>(conjugate.x) * to_site_y +
                       static_cast<double>(conjugate.y) * to_site_x));
  }
}

__global__ void complex_tail_update(
    int q, int batch, std::uint64_t cells, const std::uint8_t* clean,
    const float2* direction_phase, const double2* sum_a,
    const double2* incoming_t, const double2* t, double2* next_t) {
  const auto edge = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x +
                    threadIdx.x;
  if (edge >= cells * kDirections) return;
  const auto site = edge / kDirections;
  const int d = static_cast<int>(edge % kDirections);
  const int x = static_cast<int>(site / q);
  const int y = static_cast<int>(site % q);
  const int ux = (x + kDeviceDx[d] + q) % q;
  const int uy = (y + kDeviceDy[d] + q) % q;
  const auto u = static_cast<std::uint64_t>(ux) * q + uy;
  for (int lane = 0; lane < batch; ++lane) {
    const auto index = edge * batch + lane;
    if (!clean[site] || !clean[u]) {
      next_t[index] = make_double2(0.0, 0.0);
      continue;
    }
    const auto site_sum = sum_a[site * batch + lane];
    const auto tail_sum = incoming_t[site * batch + lane];
    const auto reverse_value =
        t[(u * kDirections + kDeviceReverse[d]) * batch + lane];
    const double source_x = site_sum.x + tail_sum.x - reverse_value.x;
    const double source_y = site_sum.y + tail_sum.y - reverse_value.y;
    const auto phase = direction_phase[d * batch + lane];
    next_t[index] = make_double2(
        kTailQExact * (static_cast<double>(phase.x) * source_x -
                       static_cast<double>(phase.y) * source_y),
        kTailQExact * (static_cast<double>(phase.x) * source_y +
                       static_cast<double>(phase.y) * source_x));
  }
}

__global__ void prepare_phases(
    int batch, std::uint64_t incidences, const std::int16_t* anchor_dx,
    const std::int16_t* anchor_dy, int prime, const int* frequency_x,
    const int* frequency_y, const float2* roots, float2* incidence_phase) {
  const auto k = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x +
                 threadIdx.x;
  if (k >= incidences) return;
  for (int lane = 0; lane < batch; ++lane) {
    int exponent = (frequency_x[lane] * static_cast<int>(anchor_dx[k]) +
                    frequency_y[lane] * static_cast<int>(anchor_dy[k])) %
                   prime;
    if (exponent < 0) exponent += prime;
    incidence_phase[k * batch + lane] = roots[exponent];
  }
}

__global__ void initialize_rhs_incidence(
    int batch, std::uint64_t incidences, const std::int32_t* incidence_type,
    const float* witness_b, const double* sum_b, double2* a, double2* b,
    double2* accumulator_a, double2* accumulator_b) {
  const auto k = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x +
                 threadIdx.x;
  if (k >= incidences) return;
  const double value =
      sum_b[incidence_type[k]] - static_cast<double>(witness_b[k]);
  for (int lane = 0; lane < batch; ++lane) {
    const auto index = k * batch + lane;
    a[index] = make_double2(value, 0.0);
    b[index] = make_double2(0.0, 0.0);
    accumulator_a[index] = a[index];
    accumulator_b[index] = b[index];
  }
}

__global__ void initialize_rhs_tail(
    int q, int batch, std::uint64_t cells, const std::uint8_t* clean,
    const double* sum_a, const double* incoming_t, const float* witness_t,
    double2* t, double2* accumulator_t) {
  const auto edge = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x +
                    threadIdx.x;
  if (edge >= cells * kDirections) return;
  const auto site = edge / kDirections;
  const int d = static_cast<int>(edge % kDirections);
  const int x = static_cast<int>(site / q);
  const int y = static_cast<int>(site % q);
  const int ux = (x + kDeviceDx[d] + q) % q;
  const int uy = (y + kDeviceDy[d] + q) % q;
  const auto u = static_cast<std::uint64_t>(ux) * q + uy;
  double exact_value = 0.0;
  if (clean[site] && clean[u])
    exact_value = sum_a[site] + incoming_t[site] -
                  static_cast<double>(
                      witness_t[u * kDirections + kDeviceReverse[d]]);
  const double value = exact_value;
  for (int lane = 0; lane < batch; ++lane) {
    const auto index = edge * batch + lane;
    t[index] = make_double2(value, 0.0);
    accumulator_t[index] = t[index];
  }
}

__global__ void add_complex(std::uint64_t count, const float2* source,
                            float2* target) {
  const auto k = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x +
                 threadIdx.x;
  if (k < count) target[k] = add(target[k], source[k]);
}

__global__ void add_complex_scaled(std::uint64_t count, double factor,
                                   const double2* source, double2* target) {
  const auto k = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x +
                 threadIdx.x;
  if (k < count) {
    target[k] = make_double2(target[k].x + factor * source[k].x,
                             target[k].y + factor * source[k].y);
  }
}

__global__ void accumulate_projected_incidence(
    int batch, double factor, std::uint64_t incidences,
    const std::int32_t* incidence_type, const float2* incidence_phase,
    const float* phase_multiplicity, const double2* b, const double2* sum_b,
    double* projected_a) {
  const auto k = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x +
                 threadIdx.x;
  if (k >= incidences) return;
  double real_sum = 0.0;
  for (int lane = 0; lane < batch; ++lane) {
    const auto index = k * batch + lane;
    const auto conjugate = make_float2(incidence_phase[index].x,
                                       -incidence_phase[index].y);
    const auto component_sum =
        sum_b[static_cast<std::uint64_t>(incidence_type[k]) * batch + lane];
    const double value_x = component_sum.x - b[index].x;
    const double value_y = component_sum.y - b[index].y;
    real_sum += static_cast<double>(phase_multiplicity[lane]) *
                (static_cast<double>(conjugate.x) * value_x -
                 static_cast<double>(conjugate.y) * value_y);
  }
  projected_a[k] += factor * real_sum;
}

__global__ void accumulate_projected_tail(
    int q, int batch, double factor, std::uint64_t cells,
    const std::uint8_t* clean, const float* phase_multiplicity,
    const float2* direction_phase,
    const double2* sum_a, const double2* incoming_t, const double2* t,
    double* projected_t) {
  const auto edge = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x +
                    threadIdx.x;
  if (edge >= cells * kDirections) return;
  const auto site = edge / kDirections;
  const int d = static_cast<int>(edge % kDirections);
  const int x = static_cast<int>(site / q);
  const int y = static_cast<int>(site % q);
  const int ux = (x + kDeviceDx[d] + q) % q;
  const int uy = (y + kDeviceDy[d] + q) % q;
  const auto u = static_cast<std::uint64_t>(ux) * q + uy;
  if (!clean[site] || !clean[u]) return;
  double real_sum = 0.0;
  for (int lane = 0; lane < batch; ++lane) {
    const auto site_sum = sum_a[site * batch + lane];
    const auto tail_sum = incoming_t[site * batch + lane];
    const auto reverse_value =
        t[(u * kDirections + kDeviceReverse[d]) * batch + lane];
    const double source_x = site_sum.x + tail_sum.x - reverse_value.x;
    const double source_y = site_sum.y + tail_sum.y - reverse_value.y;
    const auto phase = direction_phase[d * batch + lane];
    real_sum += static_cast<double>(phase_multiplicity[lane]) *
                (static_cast<double>(phase.x) * source_x -
                 static_cast<double>(phase.y) * source_y);
  }
  projected_t[edge] += factor * real_sum;
}

struct DeviceGraph {
  std::uint8_t* clean = nullptr;
  std::uint64_t* offsets = nullptr;
  std::int32_t* incidence_type = nullptr;
  std::int16_t* anchor_dx = nullptr;
  std::int16_t* anchor_dy = nullptr;
  std::uint32_t* incidence_site = nullptr;
  std::uint64_t* component_offsets = nullptr;
  std::uint32_t* component_incidences = nullptr;
};

void synchronize() {
  CUDA_CHECK(cudaGetLastError());
  CUDA_CHECK(cudaDeviceSynchronize());
}

}  // namespace

int main(int argc, char** argv) {
  if (argc < 2 || argc > 12) {
    std::cerr <<
        "usage: repeat_phase_probe GRAPH [iterations] [batch] [max-prime] "
        "[outer-iterations] [input-witness] [minimum-green-power] "
        "[fresh-after-20] [minimum-prime] [regularizer-witness] "
        "[regularizer-scale]\n";
    return 1;
  }
  const int iterations = argc >= 3 ? std::stoi(argv[2]) : 60;
  const int batch_capacity = argc >= 4 ? std::stoi(argv[3]) : 8;
  const int maximum_prime = argc >= 5 ? std::stoi(argv[4]) : 29;
  const int outer_iterations = argc >= 6 ? std::stoi(argv[5]) : 1;
  const std::string input_witness = argc >= 7 ? argv[6] : "";
  const int minimum_green_power = argc >= 8 ? std::stoi(argv[7]) : 0;
  const bool fresh_after_twenty = argc >= 9 && std::stoi(argv[8]) != 0;
  const int minimum_prime = argc >= 10 ? std::stoi(argv[9]) : 13;
  const std::string regularizer_witness = argc >= 11 ? argv[10] : "";
  const float regularizer_scale = argc >= 12 ? std::stof(argv[11]) : 0.0F;
  if (batch_capacity <= 0 || batch_capacity > 16) return 1;
  Graph graph = load_graph(argv[1]);
  std::cout << "q=" << graph.q << " cells=" << graph.cells
            << " incidences=" << graph.incidences << " types=" << graph.types
            << " iterations=" << iterations << " batch=" << batch_capacity
            << '\n';

  DeviceGraph device;
  device.clean = device_copy(graph.clean);
  device.offsets = device_copy(graph.offsets);
  device.incidence_type = device_copy(graph.incidence_type);
  device.anchor_dx = device_copy(graph.anchor_dx);
  device.anchor_dy = device_copy(graph.anchor_dy);
  device.incidence_site = device_copy(graph.incidence_site);
  device.component_offsets = device_copy(graph.component_offsets);
  device.component_incidences = device_copy(graph.component_incidences);

  const auto tail_states = graph.cells * kDirections;
  const int threads = 128;
  auto blocks = [&](std::uint64_t count) {
    return static_cast<unsigned>((count + threads - 1) / threads);
  };

  float *a = nullptr, *b = nullptr, *t = nullptr;
  float *next_a = nullptr, *next_b = nullptr, *next_t = nullptr;
  float *sum_a = nullptr, *incoming_t = nullptr, *sum_b = nullptr;
  CUDA_CHECK(cudaMalloc(&a, graph.incidences * sizeof(float)));
  CUDA_CHECK(cudaMalloc(&b, graph.incidences * sizeof(float)));
  CUDA_CHECK(cudaMalloc(&t, tail_states * sizeof(float)));
  CUDA_CHECK(cudaMalloc(&next_a, graph.incidences * sizeof(float)));
  CUDA_CHECK(cudaMalloc(&next_b, graph.incidences * sizeof(float)));
  CUDA_CHECK(cudaMalloc(&next_t, tail_states * sizeof(float)));
  CUDA_CHECK(cudaMalloc(&sum_a, graph.cells * sizeof(float)));
  CUDA_CHECK(cudaMalloc(&incoming_t, graph.cells * sizeof(float)));
  CUDA_CHECK(cudaMalloc(&sum_b, graph.types * sizeof(float)));
  initialize_real<<<blocks(graph.incidences), threads>>>(graph.incidences, a,
                                                         1.0F);
  initialize_real<<<blocks(graph.incidences), threads>>>(graph.incidences, b,
                                                         1.0F);
  initialize_real_tail<<<blocks(tail_states), threads>>>(graph.q, graph.cells,
                                                          device.clean, t);
  synchronize();

  for (int iteration = 0; iteration < 300; ++iteration) {
    real_site_sums<<<blocks(graph.cells), threads>>>(
        graph.q, graph.cells, device.clean, device.offsets, a, t, sum_a,
        incoming_t);
    real_component_sums<<<blocks(graph.types), threads>>>(
        graph.types, device.component_offsets, device.component_incidences, b,
        sum_b);
    real_incidence_update<<<blocks(graph.incidences), threads>>>(
        graph.incidences, device.incidence_type, device.incidence_site, a, b,
        sum_a, incoming_t, sum_b, next_a, next_b);
    real_tail_update<<<blocks(tail_states), threads>>>(
        graph.q, graph.cells, device.clean, sum_a, incoming_t, t, next_t);
    std::swap(a, next_a);
    std::swap(b, next_b);
    std::swap(t, next_t);
  }
  synchronize();

  if (!input_witness.empty()) {
    std::ifstream witness(input_witness, std::ios::binary);
    std::uint64_t magic = 0;
    std::uint64_t witness_incidences = 0;
    std::uint64_t witness_tail_states = 0;
    read_scalar(witness, magic);
    read_scalar(witness, witness_incidences);
    read_scalar(witness, witness_tail_states);
    if (magic != 0x455231325749544EULL ||
        witness_incidences != graph.incidences ||
        witness_tail_states != tail_states)
      throw std::runtime_error("bad witness header");
    std::vector<float> witness_a(graph.incidences);
    std::vector<float> witness_b(graph.incidences);
    std::vector<float> witness_t(tail_states);
    read_vector(witness, witness_a);
    read_vector(witness, witness_b);
    read_vector(witness, witness_t);
    if (!witness) throw std::runtime_error("truncated witness");
    if (!regularizer_witness.empty()) {
      std::ifstream regularizer(regularizer_witness, std::ios::binary);
      std::uint64_t regularizer_magic = 0;
      std::uint64_t regularizer_incidences = 0;
      std::uint64_t regularizer_tail_states = 0;
      read_scalar(regularizer, regularizer_magic);
      read_scalar(regularizer, regularizer_incidences);
      read_scalar(regularizer, regularizer_tail_states);
      if (regularizer_magic != 0x455231325749544EULL ||
          regularizer_incidences != graph.incidences ||
          regularizer_tail_states != tail_states)
        throw std::runtime_error("bad regularizer header");
      std::vector<float> regularizer_a(graph.incidences);
      std::vector<float> regularizer_b(graph.incidences);
      std::vector<float> regularizer_t(tail_states);
      read_vector(regularizer, regularizer_a);
      read_vector(regularizer, regularizer_b);
      read_vector(regularizer, regularizer_t);
      if (!regularizer) throw std::runtime_error("truncated regularizer");
      const float witness_maximum = std::max(
          {*std::max_element(witness_a.begin(), witness_a.end()),
           *std::max_element(witness_b.begin(), witness_b.end()),
           *std::max_element(witness_t.begin(), witness_t.end())});
      const float regularizer_maximum = std::max(
          {*std::max_element(regularizer_a.begin(), regularizer_a.end()),
           *std::max_element(regularizer_b.begin(), regularizer_b.end()),
           *std::max_element(regularizer_t.begin(), regularizer_t.end())});
      if (!(witness_maximum > 0.0F) || !(regularizer_maximum > 0.0F))
        throw std::runtime_error("nonpositive witness maximum");
      for (std::size_t k = 0; k < graph.incidences; ++k) {
        witness_a[k] = witness_a[k] / witness_maximum +
                       regularizer_scale * regularizer_a[k] /
                           regularizer_maximum;
        witness_b[k] = witness_b[k] / witness_maximum +
                       regularizer_scale * regularizer_b[k] /
                           regularizer_maximum;
      }
      for (std::size_t k = 0; k < tail_states; ++k)
        witness_t[k] = witness_t[k] / witness_maximum +
                       regularizer_scale * regularizer_t[k] /
                           regularizer_maximum;
      std::cout << "regularized_with=" << regularizer_witness
                << " regularizer_scale=" << regularizer_scale << '\n';
    }
    CUDA_CHECK(cudaMemcpy(a, witness_a.data(),
                          graph.incidences * sizeof(float),
                          cudaMemcpyHostToDevice));
    CUDA_CHECK(cudaMemcpy(b, witness_b.data(),
                          graph.incidences * sizeof(float),
                          cudaMemcpyHostToDevice));
    CUDA_CHECK(cudaMemcpy(t, witness_t.data(), tail_states * sizeof(float),
                          cudaMemcpyHostToDevice));
    std::cout << "loaded_witness=" << input_witness << '\n';
  }

  real_site_sums<<<blocks(graph.cells), threads>>>(
      graph.q, graph.cells, device.clean, device.offsets, a, t, sum_a,
      incoming_t);
  real_component_sums<<<blocks(graph.types), threads>>>(
      graph.types, device.component_offsets, device.component_incidences, b,
      sum_b);
  synchronize();

  double *rhs_sum_a = nullptr, *rhs_incoming_t = nullptr,
         *rhs_sum_b = nullptr;
  CUDA_CHECK(cudaMalloc(&rhs_sum_a, graph.cells * sizeof(double)));
  CUDA_CHECK(cudaMalloc(&rhs_incoming_t, graph.cells * sizeof(double)));
  CUDA_CHECK(cudaMalloc(&rhs_sum_b, graph.types * sizeof(double)));
  rhs_site_sums_double<<<blocks(graph.cells), threads>>>(
      graph.q, graph.cells, device.clean, device.offsets, a, t, rhs_sum_a,
      rhs_incoming_t);
  rhs_component_sums_double<<<blocks(graph.types), threads>>>(
      graph.types, device.component_offsets, device.component_incidences, b,
      rhs_sum_b);
  synchronize();

  double *projected_a = nullptr, *projected_t = nullptr;
  CUDA_CHECK(cudaMalloc(&projected_a, graph.incidences * sizeof(double)));
  CUDA_CHECK(cudaMalloc(&projected_t, tail_states * sizeof(double)));
  CUDA_CHECK(cudaMemset(projected_a, 0, graph.incidences * sizeof(double)));
  CUDA_CHECK(cudaMemset(projected_t, 0, tail_states * sizeof(double)));

  const std::uint64_t complex_incidences =
      graph.incidences * static_cast<std::uint64_t>(batch_capacity);
  const std::uint64_t complex_tail =
      tail_states * static_cast<std::uint64_t>(batch_capacity);
  const std::uint64_t complex_cells =
      graph.cells * static_cast<std::uint64_t>(batch_capacity);
  const std::uint64_t complex_types =
      graph.types * static_cast<std::uint64_t>(batch_capacity);
  double2 *ca = nullptr, *cb = nullptr, *ct = nullptr;
  double2 *cnext_a = nullptr, *cnext_b = nullptr, *cnext_t = nullptr;
  double2 *acc_a = nullptr, *acc_b = nullptr, *acc_t = nullptr;
  double2 *csum_a = nullptr, *cincoming_t = nullptr, *csum_b = nullptr;
  float2 *incidence_phase = nullptr, *direction_phase = nullptr,
         *root_phase = nullptr;
  int *frequency_x = nullptr, *frequency_y = nullptr;
  float *phase_multiplicity = nullptr;
  CUDA_CHECK(cudaMalloc(&ca, complex_incidences * sizeof(double2)));
  CUDA_CHECK(cudaMalloc(&cb, complex_incidences * sizeof(double2)));
  CUDA_CHECK(cudaMalloc(&ct, complex_tail * sizeof(double2)));
  CUDA_CHECK(cudaMalloc(&cnext_a, complex_incidences * sizeof(double2)));
  CUDA_CHECK(cudaMalloc(&cnext_b, complex_incidences * sizeof(double2)));
  CUDA_CHECK(cudaMalloc(&cnext_t, complex_tail * sizeof(double2)));
  CUDA_CHECK(cudaMalloc(&acc_a, complex_incidences * sizeof(double2)));
  CUDA_CHECK(cudaMalloc(&acc_b, complex_incidences * sizeof(double2)));
  CUDA_CHECK(cudaMalloc(&acc_t, complex_tail * sizeof(double2)));
  CUDA_CHECK(cudaMalloc(&csum_a, complex_cells * sizeof(double2)));
  CUDA_CHECK(cudaMalloc(&cincoming_t, complex_cells * sizeof(double2)));
  CUDA_CHECK(cudaMalloc(&csum_b, complex_types * sizeof(double2)));
  CUDA_CHECK(cudaMalloc(&incidence_phase,
                        complex_incidences * sizeof(float2)));
  CUDA_CHECK(cudaMalloc(&direction_phase,
                        kDirections * batch_capacity * sizeof(float2)));
  CUDA_CHECK(cudaMalloc(&frequency_x, batch_capacity * sizeof(int)));
  CUDA_CHECK(cudaMalloc(&frequency_y, batch_capacity * sizeof(int)));
  CUDA_CHECK(cudaMalloc(&root_phase, 59 * sizeof(float2)));
  CUDA_CHECK(cudaMalloc(&phase_multiplicity,
                        batch_capacity * sizeof(float)));

  const std::vector<int> primes = maximum_prime == 1
                                      ? std::vector<int>{1}
                                      : std::vector<int>{13, 17, 19, 23, 29, 31,
                                                         37, 41, 43, 47, 53, 59};
  std::vector<double> host_projected_a(graph.incidences);
  std::vector<double> host_projected_t(tail_states);
  std::vector<float> host_a(graph.incidences);
  std::vector<float> host_b(graph.incidences);
  std::vector<float> host_t(tail_states);
  const std::string roots_path =
      "tmp/repeat_phase_roots_" + std::to_string(minimum_prime) + "_" +
      std::to_string(maximum_prime) + ".bin";
  std::ofstream roots_audit(roots_path, std::ios::binary | std::ios::trunc);
  const std::uint64_t roots_magic = 0x45523132524F4F54ULL;
  roots_audit.write(reinterpret_cast<const char*>(&roots_magic),
                    sizeof(roots_magic));
  for (int outer = 0; outer < outer_iterations; ++outer) {
    CUDA_CHECK(cudaMemset(projected_a, 0, graph.incidences * sizeof(double)));
    CUDA_CHECK(cudaMemset(projected_t, 0, tail_states * sizeof(double)));
    real_site_sums<<<blocks(graph.cells), threads>>>(
        graph.q, graph.cells, device.clean, device.offsets, a, t, sum_a,
        incoming_t);
    real_component_sums<<<blocks(graph.types), threads>>>(
        graph.types, device.component_offsets, device.component_incidences, b,
        sum_b);
    synchronize();
  for (const int prime : primes) {
    if (prime > maximum_prime || prime < minimum_prime) continue;
    std::vector<float2> host_roots(prime);
    for (int exponent = 0; exponent < prime; ++exponent) {
      const double angle = 2.0 * kPi * static_cast<double>(exponent) /
                           static_cast<double>(prime);
      host_roots[exponent] = make_float2(
          static_cast<float>(std::cos(angle)),
          static_cast<float>(std::sin(angle)));
    }
    roots_audit.write(reinterpret_cast<const char*>(&prime), sizeof(prime));
    roots_audit.write(reinterpret_cast<const char*>(host_roots.data()),
                      static_cast<std::streamsize>(host_roots.size() *
                                                   sizeof(float2)));
    CUDA_CHECK(cudaMemcpy(root_phase, host_roots.data(),
                          host_roots.size() * sizeof(float2),
                          cudaMemcpyHostToDevice));
    std::vector<std::pair<int, int>> frequencies;
    std::vector<float> multiplicities;
    frequencies.reserve((prime * prime + 1) / 2);
    multiplicities.reserve((prime * prime + 1) / 2);
    for (int kx = 0; kx < prime; ++kx) {
      for (int ky = 0; ky < prime; ++ky) {
        const int negative_kx = (prime - kx) % prime;
        const int negative_ky = (prime - ky) % prime;
        const int index = kx * prime + ky;
        const int negative_index = negative_kx * prime + negative_ky;
        if (index > negative_index) continue;
        frequencies.push_back({kx, ky});
        multiplicities.push_back(index == negative_index ? 1.0F : 2.0F);
      }
    }
    for (std::size_t start = 0; start < frequencies.size();
         start += batch_capacity) {
      const int batch = static_cast<int>(
          std::min<std::size_t>(batch_capacity, frequencies.size() - start));
      std::vector<int> host_frequency_x(batch_capacity, 0);
      std::vector<int> host_frequency_y(batch_capacity, 0);
      std::vector<float> host_phase_multiplicity(batch_capacity, 0.0F);
      std::vector<float2> host_direction_phase(kDirections * batch_capacity,
                                                make_float2(1.0F, 0.0F));
      for (int lane = 0; lane < batch; ++lane) {
        host_phase_multiplicity[lane] = multiplicities[start + lane];
        host_frequency_x[lane] = frequencies[start + lane].first;
        host_frequency_y[lane] = frequencies[start + lane].second;
        for (int d = 0; d < kDirections; ++d) {
          int exponent = (host_frequency_x[lane] * kDx[d] +
                          host_frequency_y[lane] * kDy[d]) % prime;
          if (exponent < 0) exponent += prime;
          host_direction_phase[d * batch + lane] = host_roots[exponent];
        }
      }
      CUDA_CHECK(cudaMemcpy(frequency_x, host_frequency_x.data(),
                            batch_capacity * sizeof(int),
                            cudaMemcpyHostToDevice));
      CUDA_CHECK(cudaMemcpy(frequency_y, host_frequency_y.data(),
                            batch_capacity * sizeof(int),
                            cudaMemcpyHostToDevice));
      CUDA_CHECK(cudaMemcpy(phase_multiplicity,
                            host_phase_multiplicity.data(),
                            batch_capacity * sizeof(float),
                            cudaMemcpyHostToDevice));
      CUDA_CHECK(cudaMemcpy(direction_phase, host_direction_phase.data(),
                            kDirections * batch_capacity * sizeof(float2),
                            cudaMemcpyHostToDevice));
      prepare_phases<<<blocks(graph.incidences), threads>>>(
          batch, graph.incidences, device.anchor_dx, device.anchor_dy, prime,
          frequency_x, frequency_y, root_phase, incidence_phase);
      initialize_rhs_incidence<<<blocks(graph.incidences), threads>>>(
          batch, graph.incidences, device.incidence_type, b, rhs_sum_b, ca, cb,
          acc_a, acc_b);
      initialize_rhs_tail<<<blocks(tail_states), threads>>>(
          graph.q, batch, graph.cells, device.clean, rhs_sum_a,
          rhs_incoming_t, t, ct, acc_t);
      if (minimum_green_power > 0) {
        CUDA_CHECK(cudaMemset(acc_a, 0,
                              graph.incidences * batch * sizeof(double2)));
        CUDA_CHECK(cudaMemset(acc_b, 0,
                              graph.incidences * batch * sizeof(double2)));
        CUDA_CHECK(
            cudaMemset(acc_t, 0, tail_states * batch * sizeof(double2)));
      }
      synchronize();

      for (int iteration = 0; iteration < iterations; ++iteration) {
        complex_site_sums<<<blocks(graph.cells), threads>>>(
            graph.q, batch, graph.cells, device.clean, device.offsets, ca, ct,
            csum_a, cincoming_t);
        complex_component_sums<<<blocks(graph.types), threads>>>(
            batch, graph.types, device.component_offsets,
            device.component_incidences, cb, csum_b);
        complex_incidence_update<<<blocks(graph.incidences), threads>>>(
            batch, graph.incidences, device.incidence_type,
            device.incidence_site, incidence_phase, ca, cb, csum_a,
            cincoming_t, csum_b, cnext_a, cnext_b);
        complex_tail_update<<<blocks(tail_states), threads>>>(
            graph.q, batch, graph.cells, device.clean, direction_phase, csum_a,
            cincoming_t, ct, cnext_t);
        if (iteration + 1 >= minimum_green_power) {
          static constexpr double fresh_ratio_upper[21] = {
              1.0F,       1.0F,       0.854F,      0.652F,
              0.442F,     0.269F,     0.147F,      0.073F,
              0.033F,     0.0137F,    0.0053F,     0.0019F,
              0.00061F,   0.00019F,   0.000053F,   0.000014F,
              0.0000036F, 0.00000084F, 0.00000019F, 0.00000004F,
              0.000000008F};
          const int power = iteration + 1;
          const int fresh_count = std::min(20, power / 2);
          const double factor = fresh_after_twenty && power > 20
                                    ? std::nextafter(
                                          fresh_ratio_upper[fresh_count],
                                          std::numeric_limits<double>::infinity())
                                    : 1.0;
          add_complex_scaled<<<blocks(graph.incidences * batch), threads>>>(
              graph.incidences * batch, factor, cnext_a, acc_a);
          add_complex_scaled<<<blocks(graph.incidences * batch), threads>>>(
              graph.incidences * batch, factor, cnext_b, acc_b);
          add_complex_scaled<<<blocks(tail_states * batch), threads>>>(
              tail_states * batch, factor, cnext_t, acc_t);
        }
        std::swap(ca, cnext_a);
        std::swap(cb, cnext_b);
        std::swap(ct, cnext_t);
      }
      synchronize();

      complex_site_sums<<<blocks(graph.cells), threads>>>(
          graph.q, batch, graph.cells, device.clean, device.offsets, acc_a,
          acc_t, csum_a, cincoming_t);
      complex_component_sums<<<blocks(graph.types), threads>>>(
          batch, graph.types, device.component_offsets,
          device.component_incidences, acc_b, csum_b);
      const double factor =
          1.0 / static_cast<double>(prime * prime * prime * prime);
      accumulate_projected_incidence<<<blocks(graph.incidences), threads>>>(
          batch, factor, graph.incidences, device.incidence_type,
          incidence_phase, phase_multiplicity, acc_b, csum_b, projected_a);
      accumulate_projected_tail<<<blocks(tail_states), threads>>>(
          graph.q, batch, factor, graph.cells, device.clean,
          phase_multiplicity, direction_phase, csum_a, cincoming_t, acc_t,
          projected_t);
      synchronize();
      std::cerr << "prime=" << prime << " conjugacy_representatives="
                << std::min<std::size_t>(start + batch, frequencies.size())
                << '/' << frequencies.size() << " full_phases="
                << prime * prime << '\n';
    }
  }
  roots_audit.close();
  if (!roots_audit) throw std::runtime_error("root audit write failed");
  std::cout << "saved_root_table=" << roots_path << '\n';

  CUDA_CHECK(cudaMemcpy(host_projected_a.data(), projected_a,
                        graph.incidences * sizeof(double),
                        cudaMemcpyDeviceToHost));
  CUDA_CHECK(cudaMemcpy(host_projected_t.data(), projected_t,
                        tail_states * sizeof(double), cudaMemcpyDeviceToHost));
  CUDA_CHECK(cudaMemcpy(host_a.data(), a, graph.incidences * sizeof(float),
                        cudaMemcpyDeviceToHost));
  CUDA_CHECK(cudaMemcpy(host_b.data(), b, graph.incidences * sizeof(float),
                        cudaMemcpyDeviceToHost));
  CUDA_CHECK(cudaMemcpy(host_t.data(), t, tail_states * sizeof(float),
                        cudaMemcpyDeviceToHost));
  double maximum_ratio = 0.0;
  long double input_mass = 0.0L;
  long double output_mass = 0.0L;
  double output_maximum = 0.0;
  double minimum_projected = std::numeric_limits<double>::infinity();
  std::uint64_t negative_outputs = 0;
  for (std::uint64_t k = 0; k < graph.incidences; ++k) {
    input_mass += host_a[k] + host_b[k];
    output_mass += host_projected_a[k];
    output_maximum = std::max(output_maximum, host_projected_a[k]);
    minimum_projected = std::min(minimum_projected,
                                 static_cast<double>(host_projected_a[k]));
    negative_outputs += host_projected_a[k] < -1.0e-10;
    if (host_a[k] > 0.0F)
      maximum_ratio =
          std::max(maximum_ratio,
                   static_cast<double>(host_projected_a[k] / host_a[k]));
  }
  for (std::uint64_t edge = 0; edge < tail_states; ++edge) {
    input_mass += host_t[edge];
    output_mass += host_projected_t[edge];
    output_maximum = std::max(output_maximum, host_projected_t[edge]);
    minimum_projected = std::min(minimum_projected,
                                 static_cast<double>(host_projected_t[edge]));
    negative_outputs += host_projected_t[edge] < -1.0e-10;
    if (host_t[edge] > 0.0F)
      maximum_ratio =
          std::max(maximum_ratio,
                   static_cast<double>(host_projected_t[edge] / host_t[edge]));
  }
  std::cout << "outer_iteration=" << outer + 1
            << " phase_primes_through=" << maximum_prime
            << " truncated_green_iterations=" << iterations
            << " minimum_green_power=" << minimum_green_power
            << " fresh_after_twenty=" << fresh_after_twenty
            << " projected_ratio_max=" << maximum_ratio
            << " mass_ratio=" << static_cast<double>(output_mass / input_mass)
            << " projected_min=" << minimum_projected
            << " negative_outputs=" << negative_outputs << '\n';
    if (outer + 1 == outer_iterations) {
      const std::string witness_path = "tmp/repeat_phase_witness.bin";
      const std::string image_path = "tmp/repeat_phase_image.bin";
      std::ofstream witness(witness_path, std::ios::binary | std::ios::trunc);
      const std::uint64_t magic = 0x455231325749544EULL;
      witness.write(reinterpret_cast<const char*>(&magic), sizeof(magic));
      witness.write(reinterpret_cast<const char*>(&graph.incidences),
                    sizeof(graph.incidences));
      witness.write(reinterpret_cast<const char*>(&tail_states),
                    sizeof(tail_states));
      witness.write(reinterpret_cast<const char*>(host_a.data()),
                    static_cast<std::streamsize>(host_a.size() * sizeof(float)));
      witness.write(reinterpret_cast<const char*>(host_b.data()),
                    static_cast<std::streamsize>(host_b.size() * sizeof(float)));
      witness.write(reinterpret_cast<const char*>(host_t.data()),
                    static_cast<std::streamsize>(host_t.size() * sizeof(float)));
      witness.close();
      if (!witness) throw std::runtime_error("witness write failed");
      std::cout << "saved_input_witness=" << witness_path << '\n';
      std::ofstream image(image_path, std::ios::binary | std::ios::trunc);
      image.write(reinterpret_cast<const char*>(&magic), sizeof(magic));
      image.write(reinterpret_cast<const char*>(&graph.incidences),
                  sizeof(graph.incidences));
      image.write(reinterpret_cast<const char*>(&tail_states),
                  sizeof(tail_states));
      image.write(reinterpret_cast<const char*>(host_projected_a.data()),
                   static_cast<std::streamsize>(host_projected_a.size() *
                                                sizeof(double)));
      std::vector<double> zero_b(graph.incidences, 0.0);
      image.write(reinterpret_cast<const char*>(zero_b.data()),
                   static_cast<std::streamsize>(zero_b.size() * sizeof(double)));
      image.write(reinterpret_cast<const char*>(host_projected_t.data()),
                   static_cast<std::streamsize>(host_projected_t.size() *
                                                sizeof(double)));
      image.close();
      if (!image) throw std::runtime_error("image write failed");
      std::cout << "saved_output_image=" << image_path << '\n';
    }
    if (outer + 1 < outer_iterations) {
      if (!(output_maximum > 0.0F)) return 3;
      const double inverse_scale = 1.0 / output_maximum;
      std::vector<float> scaled_a(graph.incidences);
      std::vector<float> scaled_t(tail_states);
      for (std::size_t k = 0; k < graph.incidences; ++k)
        scaled_a[k] = static_cast<float>(host_projected_a[k] * inverse_scale);
      for (std::size_t k = 0; k < tail_states; ++k)
        scaled_t[k] = static_cast<float>(host_projected_t[k] * inverse_scale);
      CUDA_CHECK(cudaMemcpy(a, scaled_a.data(),
                            graph.incidences * sizeof(float),
                            cudaMemcpyHostToDevice));
      CUDA_CHECK(cudaMemset(b, 0, graph.incidences * sizeof(float)));
      CUDA_CHECK(cudaMemcpy(t, scaled_t.data(),
                            tail_states * sizeof(float),
                            cudaMemcpyHostToDevice));
    }
  }
  return 0;
}
