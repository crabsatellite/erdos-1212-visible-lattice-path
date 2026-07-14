#include <cuda_runtime.h>

#include <cstdint>
#include <cmath>
#include <cstring>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

namespace {

void cuda_check(cudaError_t error, const char* expression, const char* file,
                int line) {
  if (error == cudaSuccess) return;
  std::cerr << file << ':' << line << " CUDA failure in " << expression << ": "
            << cudaGetErrorString(error) << '\n';
  std::exit(2);
}
#define CUDA_CHECK(expression) cuda_check((expression), #expression, __FILE__, __LINE__)

struct Header {
  std::uint64_t magic, incidences, tail_states;
};

template <class T>
T* load_image(const std::string& path, const Header& expected) {
  std::ifstream input(path, std::ios::binary);
  Header header{};
  input.read(reinterpret_cast<char*>(&header), sizeof(header));
  if (!input || std::memcmp(&header, &expected, sizeof(header)) != 0)
    throw std::runtime_error("bad image header: " + path);
  const std::uint64_t count = 2 * header.incidences + header.tail_states;
  std::vector<T> host(count);
  input.read(reinterpret_cast<char*>(host.data()),
             static_cast<std::streamsize>(host.size() * sizeof(T)));
  if (!input || input.peek() != std::ifstream::traits_type::eof())
    throw std::runtime_error("bad image length: " + path);
  T* device = nullptr;
  CUDA_CHECK(cudaMalloc(&device, host.size() * sizeof(T)));
  CUDA_CHECK(cudaMemcpy(device, host.data(), host.size() * sizeof(T),
                        cudaMemcpyHostToDevice));
  return device;
}

__global__ void check_interval(
    std::uint64_t count, const float* u, const double* center_s0,
    const double* center_s1, const double* abs_s0, const double* abs_s1,
    const double* tail_s1, const double* tail_s0, unsigned long long* max_bits,
    unsigned long long* failures, unsigned long long* zero_failures,
    unsigned long long* negative_uppers, unsigned long long* nonfinite) {
  const auto k = static_cast<std::uint64_t>(blockIdx.x) * blockDim.x + threadIdx.x;
  if (k >= count) return;
  constexpr double s0_up = 0x1.f2f43ef479abep-7;
  constexpr double s1_up = 0x1.065297d9f371ep-8;
  constexpr double eta20_up = 0x1.12e0be826d695p-27;
  constexpr double post400_up = 0x1.3204341733ce4p-20;
  constexpr double threshold_down = 0x1.ddb22d0e56041p-1;
  constexpr double radius_factor = 500.0 * 0x1p-24;

  double phase_absolute = __dadd_ru(__dmul_ru(s0_up, abs_s0[k]),
                                    __dmul_ru(s1_up, abs_s1[k]));
  double upper = __dadd_ru(center_s0[k], center_s1[k]);
  upper = __dadd_ru(upper, __dmul_ru(radius_factor, phase_absolute));
  upper = __dadd_ru(upper, __dmul_ru(s1_up, tail_s1[k]));
  upper = __dadd_ru(upper,
                    __dmul_ru(__dmul_ru(eta20_up, s0_up), tail_s0[k]));
  upper = __dadd_ru(upper,
                    __dmul_ru(post400_up, static_cast<double>(u[k])));
  if (!isfinite(upper)) {
    atomicAdd(nonfinite, 1ULL);
    return;
  }
  if (upper < 0.0) atomicAdd(negative_uppers, 1ULL);
  if (u[k] == 0.0F) {
    if (upper > 0.0) atomicAdd(zero_failures, 1ULL);
    return;
  }
  const double ratio = __ddiv_ru(upper, static_cast<double>(u[k]));
  if (!(ratio < threshold_down)) atomicAdd(failures, 1ULL);
  if (ratio > 0.0)
    atomicMax(max_bits, static_cast<unsigned long long>(__double_as_longlong(ratio)));
}

}  // namespace

int main(int argc, char** argv) {
  if (argc != 8) {
    std::cerr << "usage: repeat_interval_check U CENTER_S0 CENTER_S1 "
                 "ABS_S0 ABS_S1 TAIL_S1 TAIL_S0\n";
    return 1;
  }
  std::ifstream u_input(argv[1], std::ios::binary);
  Header header{};
  u_input.read(reinterpret_cast<char*>(&header), sizeof(header));
  if (!u_input || header.magic != 0x455231325749544EULL)
    throw std::runtime_error("bad witness header");
  u_input.close();
  float* u = load_image<float>(argv[1], header);
  double* center_s0 = load_image<double>(argv[2], header);
  double* center_s1 = load_image<double>(argv[3], header);
  double* abs_s0 = load_image<double>(argv[4], header);
  double* abs_s1 = load_image<double>(argv[5], header);
  double* tail_s1 = load_image<double>(argv[6], header);
  double* tail_s0 = load_image<double>(argv[7], header);
  unsigned long long *max_bits = nullptr, *failures = nullptr,
                     *zero_failures = nullptr, *negative_uppers = nullptr,
                     *nonfinite = nullptr;
  CUDA_CHECK(cudaMalloc(&max_bits, sizeof(unsigned long long)));
  CUDA_CHECK(cudaMalloc(&failures, sizeof(unsigned long long)));
  CUDA_CHECK(cudaMalloc(&zero_failures, sizeof(unsigned long long)));
  CUDA_CHECK(cudaMalloc(&negative_uppers, sizeof(unsigned long long)));
  CUDA_CHECK(cudaMalloc(&nonfinite, sizeof(unsigned long long)));
  CUDA_CHECK(cudaMemset(max_bits, 0, sizeof(unsigned long long)));
  CUDA_CHECK(cudaMemset(failures, 0, sizeof(unsigned long long)));
  CUDA_CHECK(cudaMemset(zero_failures, 0, sizeof(unsigned long long)));
  CUDA_CHECK(cudaMemset(negative_uppers, 0, sizeof(unsigned long long)));
  CUDA_CHECK(cudaMemset(nonfinite, 0, sizeof(unsigned long long)));
  const std::uint64_t count = 2 * header.incidences + header.tail_states;
  constexpr int threads = 128;
  const auto blocks = static_cast<unsigned>((count + threads - 1) / threads);
  check_interval<<<blocks, threads>>>(count, u, center_s0, center_s1, abs_s0,
                                     abs_s1, tail_s1, tail_s0, max_bits,
                                     failures, zero_failures, negative_uppers,
                                     nonfinite);
  CUDA_CHECK(cudaGetLastError());
  CUDA_CHECK(cudaDeviceSynchronize());
  unsigned long long host_bits = 0, host_failures = 0, host_zero = 0,
                     host_negative = 0, host_nonfinite = 0;
  CUDA_CHECK(cudaMemcpy(&host_bits, max_bits, sizeof(host_bits), cudaMemcpyDeviceToHost));
  CUDA_CHECK(cudaMemcpy(&host_failures, failures, sizeof(host_failures), cudaMemcpyDeviceToHost));
  CUDA_CHECK(cudaMemcpy(&host_zero, zero_failures, sizeof(host_zero), cudaMemcpyDeviceToHost));
  CUDA_CHECK(cudaMemcpy(&host_negative, negative_uppers, sizeof(host_negative), cudaMemcpyDeviceToHost));
  CUDA_CHECK(cudaMemcpy(&host_nonfinite, nonfinite, sizeof(host_nonfinite), cudaMemcpyDeviceToHost));
  double maximum = 0.0;
  std::memcpy(&maximum, &host_bits, sizeof(maximum));
  std::cout.precision(17);
  std::cout << "states=" << count << '\n';
  std::cout << "interval_ratio_max_ru=" << maximum << '\n';
  std::cout << "threshold_down=0x1.ddb22d0e56041p-1\n";
  std::cout << "failures=" << host_failures << '\n';
  std::cout << "positive_over_zero=" << host_zero << '\n';
  std::cout << "negative_uppers=" << host_negative << '\n';
  std::cout << "nonfinite=" << host_nonfinite << '\n';
  std::cout << "common_cone_interval="
            << ((host_failures == 0 && host_zero == 0 && host_negative == 0 &&
                 host_nonfinite == 0)
                    ? "PASS" : "FAIL") << '\n';
  return host_failures == 0 && host_zero == 0 && host_negative == 0 &&
                 host_nonfinite == 0 ? 0 : 3;
}
