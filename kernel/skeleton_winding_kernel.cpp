#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <deque>
#include <fstream>
#include <iostream>
#include <limits>
#include <numeric>
#include <string>
#include <type_traits>
#include <unordered_map>
#include <utility>
#include <vector>

static bool hidden(int x, int y, int q) {
  x %= q;
  y %= q;
  if (x < 0) x += q;
  if (y < 0) y += q;
  return std::gcd(std::gcd(x, y), q) > 1;
}

static std::uint64_t pair_key(int x, int y) {
  return (static_cast<std::uint64_t>(static_cast<std::uint32_t>(x)) << 32) |
         static_cast<std::uint32_t>(y);
}

int main(int argc, char** argv) {
  if (argc < 3 || argc > 7) return 2;
  const int q = std::stoi(argv[1]);
  const int halo = std::stoi(argv[2]);
  const long double tail_q = argc >= 4 ? std::stold(argv[3]) : 0.0L;
  const long double tilt_x = argc >= 6 ? std::stold(argv[5]) : 0.0L;
  const long double tilt_y = argc >= 7 ? std::stold(argv[6]) : 0.0L;
  const int side = q + 2 * halo;
  const std::size_t cells = static_cast<std::size_t>(side) * side;
  auto grid_id = [side, halo](int x, int y) {
    return static_cast<std::size_t>(x + halo) * side + (y + halo);
  };

  std::vector<std::int32_t> label(cells, -1);
  std::vector<int> canonical_x;
  std::vector<int> canonical_y;
  std::vector<int> component_span_x;
  std::vector<int> component_span_y;
  std::vector<std::uint32_t> component_size;
  std::vector<std::uint8_t> touches_edge;
  std::deque<std::pair<int, int>> bfs;

  for (int x = -halo; x < q + halo; ++x) {
    for (int y = -halo; y < q + halo; ++y) {
      const auto root = grid_id(x, y);
      if (label[root] != -1 || !hidden(x, y, q)) continue;
      const int cid = static_cast<int>(canonical_x.size());
      int min_x = x;
      int min_y = y;
      int max_x = x;
      int max_y = y;
      std::uint32_t size = 0;
      bool edge = false;
      label[root] = cid;
      bfs.push_back({x, y});
      while (!bfs.empty()) {
        const auto [a, b] = bfs.front();
        bfs.pop_front();
        ++size;
        if (a < min_x || (a == min_x && b < min_y)) {
          min_x = a;
          min_y = b;
        }
        max_x = std::max(max_x, a);
        max_y = std::max(max_y, b);
        edge = edge || a == -halo || b == -halo || a == q + halo - 1 ||
               b == q + halo - 1;
        for (int dx = -1; dx <= 1; ++dx) {
          for (int dy = -1; dy <= 1; ++dy) {
            if (dx == 0 && dy == 0) continue;
            const int u = a + dx;
            const int v = b + dy;
            if (u < -halo || v < -halo || u >= q + halo ||
                v >= q + halo || !hidden(u, v, q))
              continue;
            const auto z = grid_id(u, v);
            if (label[z] == -1) {
              label[z] = cid;
              bfs.push_back({u, v});
            }
          }
        }
      }
      canonical_x.push_back(min_x);
      canonical_y.push_back(min_y);
      component_span_x.push_back(max_x - min_x);
      component_span_y.push_back(max_y - min_y);
      component_size.push_back(size);
      touches_edge.push_back(edge);
    }
  }

  auto residue = [q](int x) {
    x %= q;
    if (x < 0) x += q;
    return x;
  };
  std::unordered_map<std::uint64_t, int> type_of_canonical;
  std::vector<int> component_type(canonical_x.size(), -1);
  int type_count = 0;
  for (std::size_t cid = 0; cid < canonical_x.size(); ++cid) {
    if (touches_edge[cid]) continue;
    const int x = canonical_x[cid];
    const int y = canonical_y[cid];
    const auto key = pair_key(residue(x), residue(y));
    auto [it, inserted] = type_of_canonical.emplace(key, type_count);
    if (inserted) ++type_count;
    component_type[cid] = it->second;
  }

  // The halo contains translated copies of every component type.  Complete
  // the type map for copies whose canonical representative is outside the
  // central period.
  for (std::size_t cid = 0; cid < canonical_x.size(); ++cid) {
    if (touches_edge[cid]) continue;
    const auto key =
        pair_key(residue(canonical_x[cid]), residue(canonical_y[cid]));
    const auto it = type_of_canonical.find(key);
    if (it == type_of_canonical.end()) {
      std::cerr << "missing component type\n";
      return 3;
    }
    component_type[cid] = it->second;
  }

  std::vector<std::uint64_t> offsets;
  std::vector<std::int32_t> incident_types;
  std::vector<std::int16_t> incident_anchor_dx;
  std::vector<std::int16_t> incident_anchor_dy;
  std::vector<std::uint8_t> clean_mask(static_cast<std::size_t>(q) * q, 0);
  offsets.reserve(static_cast<std::size_t>(q) * q + 1);
  incident_types.reserve(static_cast<std::size_t>(q) * q * 2);
  offsets.push_back(0);
  std::uint64_t clean_sites = 0;
  std::uint64_t active_sites = 0;
  std::uint64_t directed_pairs = 0;
  int max_degree = 0;

  for (int x = 0; x < q; ++x) {
    for (int y = 0; y < q; ++y) {
      const auto central_site = static_cast<std::size_t>(x) * q + y;
      if (hidden(x, y, q)) {
        offsets.push_back(incident_types.size());
        continue;
      }
      clean_mask[central_site] = 1;
      ++clean_sites;
      int actual_ids[8];
      int degree = 0;
      for (int dx = -1; dx <= 1; ++dx) {
        for (int dy = -1; dy <= 1; ++dy) {
          if (dx == 0 && dy == 0) continue;
          const int cid = label[grid_id(x + dx, y + dy)];
          if (cid < 0) continue;
          bool duplicate = false;
          for (int j = 0; j < degree; ++j) duplicate |= actual_ids[j] == cid;
          if (!duplicate) actual_ids[degree++] = cid;
        }
      }
      if (degree >= 2) ++active_sites;
      max_degree = std::max(max_degree, degree);
      directed_pairs += static_cast<std::uint64_t>(degree) * (degree - 1);
      for (int j = 0; j < degree; ++j) {
        const int cid = actual_ids[j];
        const int type = component_type[cid];
        if (type < 0) {
          std::cerr << "halo too small\n";
          return 4;
        }
        incident_types.push_back(type);
        incident_anchor_dx.push_back(
            static_cast<std::int16_t>(canonical_x[cid] - x));
        incident_anchor_dy.push_back(
            static_cast<std::int16_t>(canonical_y[cid] - y));
      }
      offsets.push_back(incident_types.size());
    }
  }

  if (static_cast<std::size_t>(type_count) != type_of_canonical.size()) return 5;
  int largest_span_x = 0;
  int largest_span_y = 0;
  std::uint32_t largest_component = 0;
  for (std::size_t cid = 0; cid < component_type.size(); ++cid) {
    if (touches_edge[cid]) continue;
    largest_span_x = std::max(largest_span_x, component_span_x[cid]);
    largest_span_y = std::max(largest_span_y, component_span_y[cid]);
    largest_component = std::max(largest_component, component_size[cid]);
  }
  std::vector<long double> x(type_count, 1.0L);
  std::vector<long double> y(type_count, 0.0L);
  long double norm = std::sqrt(static_cast<long double>(type_count));
  for (auto& value : x) value /= norm;
  long double rayleigh = 0;
  for (int iteration = 0; iteration < 100; ++iteration) {
    std::fill(y.begin(), y.end(), 0.0L);
    std::size_t site = 0;
    for (int gx = 0; gx < q; ++gx) {
      for (int gy = 0; gy < q; ++gy, ++site) {
        const auto begin = offsets[site];
        const auto end = offsets[site + 1];
        if (end - begin < 2) continue;
        long double sum = 0;
        for (auto k = begin; k < end; ++k) sum += x[incident_types[k]];
        for (auto k = begin; k < end; ++k)
          y[incident_types[k]] += sum - x[incident_types[k]];
      }
    }
    rayleigh = 0;
    long double y_norm = 0;
    for (int i = 0; i < type_count; ++i) {
      rayleigh += x[i] * y[i];
      y_norm += y[i] * y[i];
    }
    y_norm = std::sqrt(y_norm);
    for (int i = 0; i < type_count; ++i) x[i] = y[i] / y_norm;
    if (iteration % 10 == 9)
      std::cerr << "iteration=" << iteration + 1
                << " rayleigh=" << static_cast<double>(rayleigh) << "\n";
  }

  long double min_ratio = std::numeric_limits<long double>::infinity();
  long double max_ratio = 0;
  std::fill(y.begin(), y.end(), 0.0L);
  std::size_t site = 0;
  for (int gx = 0; gx < q; ++gx) {
    for (int gy = 0; gy < q; ++gy, ++site) {
      const auto begin = offsets[site];
      const auto end = offsets[site + 1];
      if (end - begin < 2) continue;
      long double sum = 0;
      for (auto k = begin; k < end; ++k) sum += x[incident_types[k]];
      for (auto k = begin; k < end; ++k)
        y[incident_types[k]] += sum - x[incident_types[k]];
    }
  }
  for (int i = 0; i < type_count; ++i) {
    if (x[i] == 0) continue;
    min_ratio = std::min(min_ratio, y[i] / x[i]);
    max_ratio = std::max(max_ratio, y[i] / x[i]);
  }

  std::cout << "Q=" << q << " halo=" << halo << " types=" << type_count
            << " clean_sites=" << clean_sites << " bridge_sites=" << active_sites
            << " max_degree=" << max_degree
            << " max_component_size=" << largest_component
            << " max_component_span=" << largest_span_x << ',' << largest_span_y
            << " directed_pairs=" << directed_pairs
            << " adjacency_rho=" << static_cast<double>(rayleigh)
            << " collatz_min=" << static_cast<double>(min_ratio)
            << " collatz_max=" << static_cast<double>(max_ratio) << "\n";

  if (tail_q > 0 && argc == 4) {
    // K is the component-to-component fresh-tail operator.  Its length-zero
    // term crosses one clean site and switches components there (the A term
    // above).  Its length-l term, l >= 1, crosses l clean-clean star edges and
    // therefore pays tail_q^(l+1).  Keeping returns to the same component and
    // paths that merely pass an intermediate component makes K an upper
    // operator for loop-erased fresh-tail connections.
    std::vector<long double> kh(type_count, 0.0L);
    for (int i = 0; i < type_count; ++i) kh[i] = tail_q * y[i];

    const std::size_t period_cells = static_cast<std::size_t>(q) * q;
    std::vector<long double> site_x(period_cells, 0.0L);
    std::vector<long double> site_y(period_cells, 0.0L);
    std::vector<long double> last_endpoint(type_count, 0.0L);
    for (std::size_t z = 0; z < period_cells; ++z) {
      for (auto k = offsets[z]; k < offsets[z + 1]; ++k)
        site_x[z] += x[incident_types[k]];
    }

    long double coefficient = tail_q;
    for (int length = 1; length <= 16; ++length) {
      std::fill(site_y.begin(), site_y.end(), 0.0L);
      for (int gx = 0; gx < q; ++gx) {
        for (int gy = 0; gy < q; ++gy) {
          const auto z = static_cast<std::size_t>(gx) * q + gy;
          if (!clean_mask[z]) continue;
          long double value = 0.0L;
          for (int dx = -1; dx <= 1; ++dx) {
            for (int dy = -1; dy <= 1; ++dy) {
              if (dx == 0 && dy == 0) continue;
              const int ux = (gx + dx + q) % q;
              const int uy = (gy + dy + q) % q;
              const auto u = static_cast<std::size_t>(ux) * q + uy;
              if (clean_mask[u]) value += site_x[u];
            }
          }
          site_y[z] = value;
        }
      }
      site_x.swap(site_y);
      coefficient *= tail_q;
      if (length == 16) std::fill(last_endpoint.begin(), last_endpoint.end(), 0.0L);
      for (std::size_t z = 0; z < period_cells; ++z) {
        const long double contribution = coefficient * site_x[z];
        if (contribution == 0.0L && length != 16) continue;
        for (auto k = offsets[z]; k < offsets[z + 1]; ++k) {
          kh[incident_types[k]] += contribution;
          if (length == 16) last_endpoint[incident_types[k]] += site_x[z];
        }
      }

      long double partial_max = 0.0L;
      long double partial_min = std::numeric_limits<long double>::infinity();
      for (int i = 0; i < type_count; ++i) {
        if (x[i] == 0) continue;
        partial_min = std::min(partial_min, kh[i] / x[i]);
        partial_max = std::max(partial_max, kh[i] / x[i]);
      }
      std::cerr << "tail_length=" << length
                << " coefficient=" << static_cast<double>(coefficient)
                << " K_collatz_min=" << static_cast<double>(partial_min)
                << " K_collatz_max=" << static_cast<double>(partial_max)
                << "\n";
    }

    // The omitted l >= 17 contribution is bounded using at most eight clean
    // continuations per star step.  Report the raw endpoint mass at l=16 so a
    // separate interval checker can close this geometrically.
    long double endpoint_max = 0.0L;
    for (int i = 0; i < type_count; ++i) {
      if (x[i] == 0) continue;
      endpoint_max = std::max(endpoint_max, last_endpoint[i] / x[i]);
    }
    std::cout << "fresh_tail_q=" << static_cast<double>(tail_q)
              << " K16_collatz_max=";
    long double final_max = 0.0L;
    for (int i = 0; i < type_count; ++i)
      if (x[i] > 0) final_max = std::max(final_max, kh[i] / x[i]);
    std::cout << static_cast<double>(final_max)
              << " endpoint16_max=" << static_cast<double>(endpoint_max)
              << "\n";

    auto apply_fresh_operator = [&](const std::vector<long double>& input,
                                    std::vector<long double>& output,
                                    int maximum_tail_length) {
      std::fill(output.begin(), output.end(), 0.0L);
      // One active clean site shared by two distinct skeleton components.
      for (std::size_t z = 0; z < period_cells; ++z) {
        const auto begin = offsets[z];
        const auto end = offsets[z + 1];
        if (end - begin < 2) continue;
        long double sum = 0.0L;
        for (auto k = begin; k < end; ++k) sum += input[incident_types[k]];
        for (auto k = begin; k < end; ++k)
          output[incident_types[k]] +=
              tail_q * (sum - input[incident_types[k]]);
      }

      std::fill(site_x.begin(), site_x.end(), 0.0L);
      for (std::size_t z = 0; z < period_cells; ++z)
        for (auto k = offsets[z]; k < offsets[z + 1]; ++k)
          site_x[z] += input[incident_types[k]];

      long double tail_coefficient = tail_q;
      for (int length = 1; length <= maximum_tail_length; ++length) {
        std::fill(site_y.begin(), site_y.end(), 0.0L);
        for (int gx = 0; gx < q; ++gx) {
          for (int gy = 0; gy < q; ++gy) {
            const auto z = static_cast<std::size_t>(gx) * q + gy;
            if (!clean_mask[z]) continue;
            long double value = 0.0L;
            for (int dx = -1; dx <= 1; ++dx) {
              for (int dy = -1; dy <= 1; ++dy) {
                if (dx == 0 && dy == 0) continue;
                const int ux = (gx + dx + q) % q;
                const int uy = (gy + dy + q) % q;
                const auto u = static_cast<std::size_t>(ux) * q + uy;
                if (clean_mask[u]) value += site_x[u];
              }
            }
            site_y[z] = value;
          }
        }
        site_x.swap(site_y);
        tail_coefficient *= tail_q;
        for (std::size_t z = 0; z < period_cells; ++z) {
          const long double value = tail_coefficient * site_x[z];
          if (value == 0.0L) continue;
          for (auto k = offsets[z]; k < offsets[z + 1]; ++k)
            output[incident_types[k]] += value;
        }
      }
    };

    std::vector<long double> iterate = x;
    std::vector<long double> image(type_count, 0.0L);
    long double fresh_rayleigh = 0.0L;
    for (int iteration = 0; iteration < 60; ++iteration) {
      apply_fresh_operator(iterate, image, 8);
      fresh_rayleigh = 0.0L;
      long double image_norm = 0.0L;
      for (int i = 0; i < type_count; ++i) {
        fresh_rayleigh += iterate[i] * image[i];
        image_norm += image[i] * image[i];
      }
      image_norm = std::sqrt(image_norm);
      for (int i = 0; i < type_count; ++i) iterate[i] = image[i] / image_norm;
      if (iteration % 10 == 9)
        std::cerr << "fresh_iteration=" << iteration + 1
                  << " rayleigh=" << static_cast<double>(fresh_rayleigh)
                  << "\n";
    }

    apply_fresh_operator(iterate, image, 16);
    long double fresh_min = std::numeric_limits<long double>::infinity();
    long double fresh_max = 0.0L;
    for (int i = 0; i < type_count; ++i) {
      if (iterate[i] == 0.0L) continue;
      fresh_min = std::min(fresh_min, image[i] / iterate[i]);
      fresh_max = std::max(fresh_max, image[i] / iterate[i]);
    }
    std::cout << "fresh_operator_rho8=" << static_cast<double>(fresh_rayleigh)
              << " fresh_K16_collatz_min=" << static_cast<double>(fresh_min)
              << " fresh_K16_collatz_max=" << static_cast<double>(fresh_max)
              << "\n";
  }

  if (tail_q > 0 && argc >= 5) {
    // Exact weighted Hashimoto operator on the periodic incidence graph.
    // a(C,z): component -> clean site; b(z,C): clean site -> component;
    // t(z,d): clean site -> clean star-neighbour.  A transition entering a
    // clean site pays tail_q, and the reverse directed edge is deleted.
    const std::size_t period_cells = static_cast<std::size_t>(q) * q;
    const std::size_t incidence_count = incident_types.size();
    static const int dx[8] = {-1, -1, -1, 0, 0, 1, 1, 1};
    static const int dy[8] = {-1, 0, 1, -1, 1, -1, 0, 1};
    int reverse[8];
    for (int d = 0; d < 8; ++d) {
      reverse[d] = -1;
      for (int e = 0; e < 8; ++e)
        if (dx[e] == -dx[d] && dy[e] == -dy[d]) reverse[d] = e;
    }

    std::uint64_t valid_tail_edges = 0;
    for (int gx = 0; gx < q; ++gx) {
      for (int gy = 0; gy < q; ++gy) {
        const auto z = static_cast<std::size_t>(gx) * q + gy;
        if (!clean_mask[z]) continue;
        for (int d = 0; d < 8; ++d) {
          const int ux = (gx + dx[d] + q) % q;
          const int uy = (gy + dy[d] + q) % q;
          const auto u = static_cast<std::size_t>(ux) * q + uy;
          valid_tail_edges += clean_mask[u] != 0;
        }
      }
    }

    const long double initial =
        1.0L / std::sqrt(static_cast<long double>(2 * incidence_count +
                                                  valid_tail_edges));
    std::vector<double> a(incidence_count, static_cast<double>(initial));
    std::vector<double> b(incidence_count, static_cast<double>(initial));
    std::vector<double> t(period_cells * 8, 0.0);
    std::vector<double> next_a(incidence_count, 0.0);
    std::vector<double> next_b(incidence_count, 0.0);
    std::vector<double> next_t(period_cells * 8, 0.0);
    std::vector<double> sum_a_site(period_cells, 0.0);
    std::vector<double> incoming_t(period_cells, 0.0);
    std::vector<double> sum_b_component(type_count, 0.0);
    std::vector<std::uint64_t> component_offsets(type_count + 1, 0);
    for (const auto type : incident_types) ++component_offsets[type + 1];
    for (int type = 0; type < type_count; ++type)
      component_offsets[type + 1] += component_offsets[type];
    std::vector<std::uint64_t> component_cursor = component_offsets;
    std::vector<std::uint32_t> component_incidences(incidence_count);
    for (std::uint32_t k = 0; k < incidence_count; ++k)
      component_incidences[component_cursor[incident_types[k]]++] = k;

    if (std::string(argv[4]) == "dump-phase-graph") {
      const std::string output_path = "tmp/phase_graph_q2310.bin";
      std::ofstream output(output_path, std::ios::binary | std::ios::trunc);
      if (!output) {
        std::cerr << "cannot open phase graph output\n";
        return 9;
      }
      const std::uint64_t magic = 0x4552313231325048ULL;
      const std::uint64_t period_cells_u64 = period_cells;
      const std::uint64_t incidence_count_u64 = incidence_count;
      const std::uint64_t type_count_u64 = type_count;
      auto write_scalar = [&](const auto& value) {
        output.write(reinterpret_cast<const char*>(&value), sizeof(value));
      };
      auto write_vector = [&](const auto& values) {
        using Value = typename std::decay_t<decltype(values)>::value_type;
        output.write(reinterpret_cast<const char*>(values.data()),
                     static_cast<std::streamsize>(values.size() * sizeof(Value)));
      };
      write_scalar(magic);
      write_scalar(q);
      write_scalar(period_cells_u64);
      write_scalar(incidence_count_u64);
      write_scalar(type_count_u64);
      write_vector(clean_mask);
      write_vector(offsets);
      write_vector(incident_types);
      write_vector(incident_anchor_dx);
      write_vector(incident_anchor_dy);
      output.close();
      if (!output) {
        std::cerr << "phase graph write failed\n";
        return 10;
      }
      std::cout << "phase_graph=" << output_path
                << " bytes="
                << (sizeof(magic) + sizeof(q) + 3 * sizeof(std::uint64_t) +
                    clean_mask.size() * sizeof(clean_mask[0]) +
                    offsets.size() * sizeof(offsets[0]) +
                    incident_types.size() * sizeof(incident_types[0]) +
                    incident_anchor_dx.size() * sizeof(incident_anchor_dx[0]) +
                    incident_anchor_dy.size() * sizeof(incident_anchor_dy[0]))
                << "\n";
      return 0;
    }

    for (const int repeat_prime : {13, 17, 19, 23, 29, 31}) {
      std::uint64_t directed_repeat_pairs = 0;
      std::uint32_t maximum_repeat_targets = 0;
      for (int type = 0; type < type_count; ++type) {
        const auto begin = component_offsets[type];
        const auto end = component_offsets[type + 1];
        for (auto ii = begin; ii < end; ++ii) {
          const auto i = component_incidences[ii];
          std::uint32_t repeat_targets = 0;
          for (auto jj = begin; jj < end; ++jj) {
            const auto j = component_incidences[jj];
            if (i == j) continue;
            const int ddx = incident_anchor_dx[i] - incident_anchor_dx[j];
            const int ddy = incident_anchor_dy[i] - incident_anchor_dy[j];
            const bool compatible =
                ddx % repeat_prime == 0 && ddy % repeat_prime == 0;
            directed_repeat_pairs += compatible;
            repeat_targets += compatible;
          }
          maximum_repeat_targets =
              std::max(maximum_repeat_targets, repeat_targets);
        }
      }
      std::cout << "repeat_prime=" << repeat_prime
                << " direct_component_repeat_pairs=" << directed_repeat_pairs
                << " max_repeat_targets=" << maximum_repeat_targets
                << "\n";
    }
    if (std::string(argv[4]) == "repeat-pairs") return 0;

    std::vector<double> weight_into_component(incidence_count, 1.0);
    std::vector<double> weight_into_site(incidence_count, 1.0);
    for (std::size_t k = 0; k < incidence_count; ++k) {
      const long double exponent =
          tilt_x * incident_anchor_dx[k] + tilt_y * incident_anchor_dy[k];
      weight_into_component[k] = static_cast<double>(std::exp(exponent));
      weight_into_site[k] = static_cast<double>(std::exp(-exponent));
    }
    double tail_step_weight[8];
    for (int d = 0; d < 8; ++d)
      tail_step_weight[d] =
          static_cast<double>(std::exp(tilt_x * dx[d] + tilt_y * dy[d]));

    for (int gx = 0; gx < q; ++gx) {
      for (int gy = 0; gy < q; ++gy) {
        const auto z = static_cast<std::size_t>(gx) * q + gy;
        if (!clean_mask[z]) continue;
        for (int d = 0; d < 8; ++d) {
          const int ux = (gx + dx[d] + q) % q;
          const int uy = (gy + dy[d] + q) % q;
          const auto u = static_cast<std::size_t>(ux) * q + uy;
          if (clean_mask[u]) t[z * 8 + d] = static_cast<double>(initial);
        }
      }
    }

    auto apply_hashimoto = [&]() {
      std::fill(next_a.begin(), next_a.end(), 0.0F);
      std::fill(next_b.begin(), next_b.end(), 0.0F);
      std::fill(next_t.begin(), next_t.end(), 0.0F);
      std::fill(sum_a_site.begin(), sum_a_site.end(), 0.0F);
      std::fill(incoming_t.begin(), incoming_t.end(), 0.0F);
      std::fill(sum_b_component.begin(), sum_b_component.end(), 0.0F);

#pragma omp parallel for schedule(static)
      for (std::int64_t signed_z = 0;
           signed_z < static_cast<std::int64_t>(period_cells); ++signed_z) {
        const auto z = static_cast<std::size_t>(signed_z);
        double site_sum = 0.0;
        for (auto k = offsets[z]; k < offsets[z + 1]; ++k) site_sum += a[k];
        sum_a_site[z] = site_sum;
      }
#pragma omp parallel for collapse(2) schedule(static)
      for (int gx = 0; gx < q; ++gx) {
        for (int gy = 0; gy < q; ++gy) {
          const auto z = static_cast<std::size_t>(gx) * q + gy;
          if (!clean_mask[z]) continue;
          double incoming = 0.0;
          for (int d = 0; d < 8; ++d) {
            const int ux = (gx + dx[d] + q) % q;
            const int uy = (gy + dy[d] + q) % q;
            const auto u = static_cast<std::size_t>(ux) * q + uy;
            if (clean_mask[u]) incoming += t[u * 8 + reverse[d]];
          }
          incoming_t[z] = incoming;
          for (auto k = offsets[z]; k < offsets[z + 1]; ++k)
            next_b[k] = weight_into_component[k] *
                        (sum_a_site[z] - a[k] + incoming);
        }
      }
#pragma omp parallel for schedule(static)
      for (int type = 0; type < type_count; ++type) {
        double value = 0.0;
        for (auto j = component_offsets[type]; j < component_offsets[type + 1];
             ++j)
          value += b[component_incidences[j]];
        sum_b_component[type] = value;
      }
#pragma omp parallel for schedule(static)
      for (std::int64_t signed_k = 0;
           signed_k < static_cast<std::int64_t>(incidence_count); ++signed_k) {
        const auto k = static_cast<std::size_t>(signed_k);
        next_a[k] = static_cast<double>(tail_q) * weight_into_site[k] *
                    (sum_b_component[incident_types[k]] - b[k]);
      }

#pragma omp parallel for collapse(2) schedule(static)
      for (int gx = 0; gx < q; ++gx) {
        for (int gy = 0; gy < q; ++gy) {
          const auto z = static_cast<std::size_t>(gx) * q + gy;
          if (!clean_mask[z]) continue;
          const double source = sum_a_site[z] + incoming_t[z];
          for (int d = 0; d < 8; ++d) {
            const int ux = (gx + dx[d] + q) % q;
            const int uy = (gy + dy[d] + q) % q;
            const auto u = static_cast<std::size_t>(ux) * q + uy;
            if (!clean_mask[u]) continue;
            next_t[z * 8 + d] = static_cast<double>(tail_q) *
                                 tail_step_weight[d] *
                                 (source - t[u * 8 + reverse[d]]);
          }
        }
      }
    };

    long double norm_ratio = 0.0L;
    const int hashimoto_iterations =
        std::string(argv[4]) == "certify" ? 300 : (q >= 1000 ? 600 : 100);
    for (int iteration = 0; iteration < hashimoto_iterations; ++iteration) {
      apply_hashimoto();
      long double old_norm2 = 0.0L;
      long double new_norm2 = 0.0L;
#pragma omp parallel for reduction(+ : old_norm2, new_norm2) schedule(static)
      for (std::int64_t signed_k = 0;
           signed_k < static_cast<std::int64_t>(incidence_count); ++signed_k) {
        const auto k = static_cast<std::size_t>(signed_k);
        old_norm2 += static_cast<long double>(a[k]) * a[k] +
                     static_cast<long double>(b[k]) * b[k];
        new_norm2 += static_cast<long double>(next_a[k]) * next_a[k] +
                     static_cast<long double>(next_b[k]) * next_b[k];
      }
#pragma omp parallel for reduction(+ : old_norm2, new_norm2) schedule(static)
      for (std::int64_t signed_k = 0;
           signed_k < static_cast<std::int64_t>(t.size()); ++signed_k) {
        const auto k = static_cast<std::size_t>(signed_k);
        old_norm2 += static_cast<long double>(t[k]) * t[k];
        new_norm2 += static_cast<long double>(next_t[k]) * next_t[k];
      }
      norm_ratio = std::sqrt(new_norm2 / old_norm2);
      const long double scale = 1.0L / std::sqrt(new_norm2);
#pragma omp parallel for schedule(static)
      for (std::int64_t signed_k = 0;
           signed_k < static_cast<std::int64_t>(incidence_count); ++signed_k) {
        const auto k = static_cast<std::size_t>(signed_k);
        a[k] = static_cast<double>(next_a[k] * scale);
        b[k] = static_cast<double>(next_b[k] * scale);
      }
#pragma omp parallel for schedule(static)
      for (std::int64_t signed_k = 0;
           signed_k < static_cast<std::int64_t>(t.size()); ++signed_k) {
        const auto k = static_cast<std::size_t>(signed_k);
        t[k] = static_cast<double>(next_t[k] * scale);
      }
      if (iteration % 10 == 9)
        std::cerr << "hashimoto_iteration=" << iteration + 1
                  << " norm_ratio=" << static_cast<double>(norm_ratio) << "\n";
    }

    apply_hashimoto();
    long double ratio_min = std::numeric_limits<long double>::infinity();
    long double ratio_max = 0.0L;
    for (std::size_t k = 0; k < incidence_count; ++k) {
      if (a[k] > 0) {
        ratio_min = std::min(ratio_min,
                             static_cast<long double>(next_a[k]) / a[k]);
        ratio_max = std::max(ratio_max,
                             static_cast<long double>(next_a[k]) / a[k]);
      }
      if (b[k] > 0) {
        ratio_min = std::min(ratio_min,
                             static_cast<long double>(next_b[k]) / b[k]);
        ratio_max = std::max(ratio_max,
                             static_cast<long double>(next_b[k]) / b[k]);
      }
    }
    for (int gx = 0; gx < q; ++gx) {
      for (int gy = 0; gy < q; ++gy) {
        const auto z = static_cast<std::size_t>(gx) * q + gy;
        if (!clean_mask[z]) continue;
        for (int d = 0; d < 8; ++d) {
          const int ux = (gx + dx[d] + q) % q;
          const int uy = (gy + dy[d] + q) % q;
          const auto u = static_cast<std::size_t>(ux) * q + uy;
          if (!clean_mask[u] || t[z * 8 + d] <= 0) continue;
          ratio_min = std::min(
              ratio_min, static_cast<long double>(next_t[z * 8 + d]) /
                             t[z * 8 + d]);
          ratio_max = std::max(
              ratio_max, static_cast<long double>(next_t[z * 8 + d]) /
                             t[z * 8 + d]);
        }
      }
    }
    std::cout << "hashimoto_tail_q=" << static_cast<double>(tail_q)
              << " tilt_x=" << static_cast<double>(tilt_x)
              << " tilt_y=" << static_cast<double>(tilt_y)
              << " directed_incidence_states=" << 2 * incidence_count
              << " directed_tail_states=" << valid_tail_edges
              << " hashimoto_norm_ratio=" << static_cast<double>(norm_ratio)
              << " collatz_min=" << static_cast<double>(ratio_min)
              << " collatz_max=" << static_cast<double>(ratio_max) << "\n";

    if (std::string(argv[4]) == "certify") {
      constexpr long double q_rational = 22751.0L / 1000000.0L;
      constexpr long double error_envelope = 1.0e-10L;
      const bool tilted_certificate =
          std::abs(tilt_x - 0.15L) <= 1.0e-15L && tilt_y == 0.0L;
      const long double beta_rational =
          97.0L / 100.0L;
      static constexpr long double exp_upper[27] = {
          0.142274071586514L, 0.165298888221587L, 0.192049908620755L,
          0.223130160148430L, 0.259240260645892L, 0.301194211912203L,
          0.349937749111156L, 0.406569659740600L, 0.472366552741015L,
          0.548811636094027L, 0.637628151621774L, 0.740818220681718L,
          0.860707976425058L, 1.000000000000000L, 1.161834242728284L,
          1.349858807576004L, 1.568312185490169L, 1.822118800390509L,
          2.117000016612675L, 2.459603111156950L, 2.857651118063164L,
          3.320116922736548L, 3.857425530696975L, 4.481689070338065L,
          5.206979827179849L, 6.049647464412947L, 7.028687580589294L};
      auto certified_tilt_weight = [&](int displacement) {
        if (!tilted_certificate) return 1.0L;
        if (displacement < -13 || displacement > 13) {
          std::cerr << "tilt displacement outside certified table\n";
          std::exit(8);
        }
        return exp_upper[displacement + 13];
      };
      if (std::abs(tail_q - q_rational) > 1.0e-15L ||
          (!tilted_certificate && (tilt_x != 0.0L || tilt_y != 0.0L))) {
        std::cerr << "certify mode requires q=0.022751 and tilt (0,0) or (0.15,0)\n";
        return 6;
      }

      const std::string certificate_witness_path =
          tilted_certificate
              ? "tmp/hashimoto_certificate_witness_tilt_x.bin"
              : "tmp/hashimoto_certificate_witness_untilted.bin";
      {
        std::ofstream witness(certificate_witness_path,
                              std::ios::binary | std::ios::trunc);
        const std::uint64_t magic = 0x4552313248573634ULL;
        const std::uint64_t witness_incidences = incidence_count;
        const std::uint64_t witness_tail_states = t.size();
        witness.write(reinterpret_cast<const char*>(&magic), sizeof(magic));
        witness.write(reinterpret_cast<const char*>(&witness_incidences),
                      sizeof(witness_incidences));
        witness.write(reinterpret_cast<const char*>(&witness_tail_states),
                      sizeof(witness_tail_states));
        witness.write(reinterpret_cast<const char*>(a.data()),
                      static_cast<std::streamsize>(a.size() * sizeof(double)));
        witness.write(reinterpret_cast<const char*>(b.data()),
                      static_cast<std::streamsize>(b.size() * sizeof(double)));
        witness.write(reinterpret_cast<const char*>(t.data()),
                      static_cast<std::streamsize>(t.size() * sizeof(double)));
        witness.close();
        if (!witness) {
          std::cerr << "certificate witness write failed\n";
          return 9;
        }
      }
      std::cout << "certificate_witness=" << certificate_witness_path
                << "\n";

      // Recompute every positive source sum in long double.  A sum contains
      // at most 148 exactly represented binary32 inputs.  The explicit
      // 1e-10 envelope is therefore far larger than the standard gamma_n
      // roundoff bound even on implementations where long double has only
      // binary64 precision.
      next_a.clear();
      next_a.shrink_to_fit();
      next_b.clear();
      next_b.shrink_to_fit();
      next_t.clear();
      next_t.shrink_to_fit();
      sum_a_site.clear();
      sum_a_site.shrink_to_fit();
      incoming_t.clear();
      incoming_t.shrink_to_fit();
      sum_b_component.clear();
      sum_b_component.shrink_to_fit();

      std::vector<long double> certified_sum_a_site(period_cells, 0.0L);
      std::vector<long double> certified_incoming_t(period_cells, 0.0L);
      std::vector<long double> certified_sum_b_component(type_count, 0.0L);
      for (std::size_t z = 0; z < period_cells; ++z)
        for (auto k = offsets[z]; k < offsets[z + 1]; ++k)
          certified_sum_a_site[z] += static_cast<long double>(a[k]);
      for (int gx = 0; gx < q; ++gx) {
        for (int gy = 0; gy < q; ++gy) {
          const auto z = static_cast<std::size_t>(gx) * q + gy;
          if (!clean_mask[z]) continue;
          for (int d = 0; d < 8; ++d) {
            const int ux = (gx + dx[d] + q) % q;
            const int uy = (gy + dy[d] + q) % q;
            const auto u = static_cast<std::size_t>(ux) * q + uy;
            if (clean_mask[u])
              certified_incoming_t[z] +=
                  static_cast<long double>(t[u * 8 + reverse[d]]);
          }
        }
      }
      for (int type = 0; type < type_count; ++type)
        for (auto j = component_offsets[type]; j < component_offsets[type + 1];
             ++j)
          certified_sum_b_component[type] +=
              static_cast<long double>(b[component_incidences[j]]);

      std::uint64_t certified_failures = 0;
      long double certified_ratio_max = 0.0L;
      auto certify_ratio = [&](long double source_upper, long double source_raw,
                               double target) {
        if (target <= 0.0F) {
          certified_failures += source_raw > 0.0L;
          return;
        }
        const long double target_lower =
            beta_rational * static_cast<long double>(target) *
            (1.0L - error_envelope);
        certified_failures += source_upper > target_lower;
        certified_ratio_max = std::max(
            certified_ratio_max,
            source_upper / static_cast<long double>(target));
      };
      for (std::size_t z = 0; z < period_cells; ++z) {
        const long double site_upper =
            (certified_sum_a_site[z] + certified_incoming_t[z]) *
            (1.0L + error_envelope);
        for (auto k = offsets[z]; k < offsets[z + 1]; ++k) {
          const long double site_raw =
              certified_sum_a_site[z] + certified_incoming_t[z] -
              static_cast<long double>(a[k]);
          certify_ratio(certified_tilt_weight(incident_anchor_dx[k]) *
                            (site_upper - static_cast<long double>(a[k])) *
                            (1.0L + error_envelope),
                        certified_tilt_weight(incident_anchor_dx[k]) *
                            site_raw,
                        b[k]);
          const long double component_upper =
              certified_sum_b_component[incident_types[k]] *
              (1.0L + error_envelope) - static_cast<long double>(b[k]);
          const long double component_raw =
              certified_sum_b_component[incident_types[k]] -
              static_cast<long double>(b[k]);
          certify_ratio(q_rational *
                            certified_tilt_weight(-incident_anchor_dx[k]) *
                            component_upper *
                            (1.0L + error_envelope) *
                            (1.0L + error_envelope),
                        q_rational *
                            certified_tilt_weight(-incident_anchor_dx[k]) *
                            component_raw,
                        a[k]);
        }
      }
      for (int gx = 0; gx < q; ++gx) {
        for (int gy = 0; gy < q; ++gy) {
          const auto z = static_cast<std::size_t>(gx) * q + gy;
          if (!clean_mask[z]) continue;
          const long double site_upper =
              (certified_sum_a_site[z] + certified_incoming_t[z]) *
              (1.0L + error_envelope);
          for (int d = 0; d < 8; ++d) {
            const int ux = (gx + dx[d] + q) % q;
            const int uy = (gy + dy[d] + q) % q;
            const auto u = static_cast<std::size_t>(ux) * q + uy;
            if (!clean_mask[u]) continue;
            const long double source_upper =
                site_upper - static_cast<long double>(t[u * 8 + reverse[d]]);
            const long double source_raw =
                certified_sum_a_site[z] + certified_incoming_t[z] -
                static_cast<long double>(t[u * 8 + reverse[d]]);
            certify_ratio(q_rational * certified_tilt_weight(dx[d]) *
                              source_upper *
                              (1.0L + error_envelope) *
                              (1.0L + error_envelope),
                          q_rational * certified_tilt_weight(dx[d]) *
                              source_raw,
                          t[z * 8 + d]);
          }
        }
      }
      std::cout << "interval_collatz_beta="
                << static_cast<double>(beta_rational)
                << " interval_ratio_max="
                << static_cast<double>(certified_ratio_max)
                << " error_envelope=1e-10"
                << " failures=" << certified_failures
                << " certificate="
                << (certified_failures == 0 ? "PASS" : "FAIL") << "\n";
      return certified_failures == 0 ? 0 : 7;
    }

    if (std::string(argv[4]) == "integer-certify") {
      // The certificate uses q = 22751/10^6 and beta = 97/100.  Floating
      // point power iteration is used only to find a positive integer
      // vector.  The acceptance test below is entirely in unsigned 128-bit
      // integer arithmetic.
      constexpr std::uint64_t q_num = 22751;
      constexpr std::uint64_t q_den = 1000000;
      constexpr std::uint64_t beta_num = 97;
      constexpr std::uint64_t beta_den = 100;
      if (std::abs(tail_q - static_cast<long double>(q_num) / q_den) >
          1.0e-15L || tilt_x != 0.0L || tilt_y != 0.0L) {
        std::cerr << "certify mode requires q=0.022751 and zero tilt\n";
        return 6;
      }

      double maximum_value = 0.0;
      double minimum_value = std::numeric_limits<double>::infinity();
      auto inspect_positive = [&](const std::vector<double>& values) {
        for (const double value : values) {
          if (value <= 0.0F) continue;
          maximum_value = std::max(maximum_value, value);
          minimum_value = std::min(minimum_value, value);
        }
      };
      inspect_positive(a);
      inspect_positive(b);
      inspect_positive(t);
      std::cout << "certificate_float_min=" << minimum_value
                << " certificate_float_max=" << maximum_value << "\n";

      // The periodic incidence graph is reducible.  Its connected blocks have
      // no transitions between them, so each block may be rescaled
      // independently before integer quantisation.
      const std::size_t graph_vertices = type_count + period_cells;
      std::vector<std::uint32_t> parent(graph_vertices);
      std::iota(parent.begin(), parent.end(), 0);
      auto find_root = [&](std::uint32_t vertex) {
        std::uint32_t root = vertex;
        while (parent[root] != root) root = parent[root];
        while (parent[vertex] != vertex) {
          const auto next = parent[vertex];
          parent[vertex] = root;
          vertex = next;
        }
        return root;
      };
      auto unite = [&](std::uint32_t first, std::uint32_t second) {
        first = find_root(first);
        second = find_root(second);
        if (first != second) parent[second] = first;
      };
      for (std::size_t z = 0; z < period_cells; ++z)
        for (auto k = offsets[z]; k < offsets[z + 1]; ++k)
          unite(static_cast<std::uint32_t>(incident_types[k]),
                static_cast<std::uint32_t>(type_count + z));
      for (int gx = 0; gx < q; ++gx) {
        for (int gy = 0; gy < q; ++gy) {
          const auto z = static_cast<std::size_t>(gx) * q + gy;
          if (!clean_mask[z]) continue;
          for (int d = 0; d < 8; ++d) {
            if (dx[d] < 0 || (dx[d] == 0 && dy[d] < 0)) continue;
            const int ux = (gx + dx[d] + q) % q;
            const int uy = (gy + dy[d] + q) % q;
            const auto u = static_cast<std::size_t>(ux) * q + uy;
            if (clean_mask[u])
              unite(static_cast<std::uint32_t>(type_count + z),
                    static_cast<std::uint32_t>(type_count + u));
          }
        }
      }
      for (std::size_t vertex = 0; vertex < graph_vertices; ++vertex)
        parent[vertex] = find_root(static_cast<std::uint32_t>(vertex));
      std::vector<double> block_maximum(graph_vertices, 0.0);
      for (std::size_t z = 0; z < period_cells; ++z) {
        const auto root = parent[type_count + z];
        for (auto k = offsets[z]; k < offsets[z + 1]; ++k) {
          block_maximum[root] = std::max(block_maximum[root], a[k]);
          block_maximum[root] = std::max(block_maximum[root], b[k]);
        }
        for (int d = 0; d < 8; ++d)
          block_maximum[root] =
              std::max(block_maximum[root], t[z * 8 + d]);
      }
      std::uint64_t nontrivial_blocks = 0;
      for (std::size_t vertex = 0; vertex < graph_vertices; ++vertex)
        nontrivial_blocks += parent[vertex] == vertex && block_maximum[vertex] > 0;
      std::cout << "certificate_graph_blocks=" << nontrivial_blocks << "\n";

      std::vector<std::uint32_t> incidence_site(incidence_count);
      std::vector<std::uint16_t> graph_degree(graph_vertices, 0);
      for (std::size_t z = 0; z < period_cells; ++z) {
        for (auto k = offsets[z]; k < offsets[z + 1]; ++k) {
          incidence_site[k] = static_cast<std::uint32_t>(z);
          ++graph_degree[incident_types[k]];
          ++graph_degree[type_count + z];
        }
      }
      for (int gx = 0; gx < q; ++gx) {
        for (int gy = 0; gy < q; ++gy) {
          const auto z = static_cast<std::size_t>(gx) * q + gy;
          if (!clean_mask[z]) continue;
          for (int d = 0; d < 8; ++d) {
            if (dx[d] < 0 || (dx[d] == 0 && dy[d] < 0)) continue;
            const int ux = (gx + dx[d] + q) % q;
            const int uy = (gy + dy[d] + q) % q;
            const auto u = static_cast<std::size_t>(ux) * q + uy;
            if (!clean_mask[u]) continue;
            ++graph_degree[type_count + z];
            ++graph_degree[type_count + u];
          }
        }
      }
      std::vector<std::uint8_t> in_two_core(graph_vertices, 1);
      std::deque<std::uint32_t> leaf_queue;
      for (std::uint32_t vertex = 0; vertex < graph_vertices; ++vertex)
        if (graph_degree[vertex] < 2) leaf_queue.push_back(vertex);
      auto remove_neighbour = [&](std::uint32_t neighbour) {
        if (!in_two_core[neighbour] || graph_degree[neighbour] == 0) return;
        --graph_degree[neighbour];
        if (graph_degree[neighbour] == 1) leaf_queue.push_back(neighbour);
      };
      while (!leaf_queue.empty()) {
        const auto vertex = leaf_queue.front();
        leaf_queue.pop_front();
        if (!in_two_core[vertex] || graph_degree[vertex] >= 2) continue;
        in_two_core[vertex] = 0;
        if (vertex < static_cast<std::uint32_t>(type_count)) {
          for (auto j = component_offsets[vertex];
               j < component_offsets[vertex + 1]; ++j) {
            const auto k = component_incidences[j];
            remove_neighbour(type_count + incidence_site[k]);
          }
        } else {
          const auto z = static_cast<std::size_t>(vertex - type_count);
          for (auto k = offsets[z]; k < offsets[z + 1]; ++k)
            remove_neighbour(incident_types[k]);
          const int gx = static_cast<int>(z / q);
          const int gy = static_cast<int>(z % q);
          for (int d = 0; d < 8; ++d) {
            const int ux = (gx + dx[d] + q) % q;
            const int uy = (gy + dy[d] + q) % q;
            const auto u = static_cast<std::size_t>(ux) * q + uy;
            if (clean_mask[u]) remove_neighbour(type_count + u);
          }
        }
      }
      std::uint64_t core_vertices = 0;
      std::uint64_t core_directed_states = 0;
      double core_minimum_value = std::numeric_limits<double>::infinity();
      for (std::size_t vertex = 0; vertex < graph_vertices; ++vertex)
        core_vertices += in_two_core[vertex] != 0;
      for (std::size_t k = 0; k < incidence_count; ++k) {
        if (!in_two_core[incident_types[k]] ||
            !in_two_core[type_count + incidence_site[k]])
          continue;
        core_directed_states += 2;
        core_minimum_value = std::min(core_minimum_value, a[k]);
        core_minimum_value = std::min(core_minimum_value, b[k]);
      }
      for (int gx = 0; gx < q; ++gx) {
        for (int gy = 0; gy < q; ++gy) {
          const auto z = static_cast<std::size_t>(gx) * q + gy;
          if (!in_two_core[type_count + z]) continue;
          for (int d = 0; d < 8; ++d) {
            const int ux = (gx + dx[d] + q) % q;
            const int uy = (gy + dy[d] + q) % q;
            const auto u = static_cast<std::size_t>(ux) * q + uy;
            if (!clean_mask[u] || !in_two_core[type_count + u]) continue;
            ++core_directed_states;
            core_minimum_value =
                std::min(core_minimum_value, t[z * 8 + d]);
          }
        }
      }
      std::cout << "certificate_two_core_vertices=" << core_vertices
                << " certificate_two_core_states=" << core_directed_states
                << " certificate_two_core_float_min=" << core_minimum_value
                << "\n";

      // Release iteration scratch before allocating the integer witness.
      next_a.clear();
      next_a.shrink_to_fit();
      next_b.clear();
      next_b.shrink_to_fit();
      next_t.clear();
      next_t.shrink_to_fit();
      sum_a_site.clear();
      sum_a_site.shrink_to_fit();
      incoming_t.clear();
      incoming_t.shrink_to_fit();
      sum_b_component.clear();
      sum_b_component.shrink_to_fit();

      constexpr long double integer_scale = 4000000000.0L;
      auto quantize = [&](double value, std::uint32_t root) -> std::uint32_t {
        if (value <= 0.0F) return 0;
        const long double scaled =
            static_cast<long double>(value) / block_maximum[root] * integer_scale;
        return static_cast<std::uint32_t>(std::floor(scaled)) + 1;
      };

      std::vector<std::uint32_t> integer_a(incidence_count);
      for (std::size_t z = 0; z < period_cells; ++z) {
        const auto root = parent[type_count + z];
        for (auto k = offsets[z]; k < offsets[z + 1]; ++k) {
          if (in_two_core[incident_types[k]] && in_two_core[type_count + z])
            integer_a[k] = quantize(a[k], root);
        }
      }
      a.clear();
      a.shrink_to_fit();
      std::vector<std::uint32_t> integer_b(incidence_count);
      for (std::size_t z = 0; z < period_cells; ++z) {
        const auto root = parent[type_count + z];
        for (auto k = offsets[z]; k < offsets[z + 1]; ++k) {
          if (in_two_core[incident_types[k]] && in_two_core[type_count + z])
            integer_b[k] = quantize(b[k], root);
        }
      }
      b.clear();
      b.shrink_to_fit();
      std::vector<std::uint32_t> integer_t(t.size());
      for (std::size_t z = 0; z < period_cells; ++z) {
        const auto root = parent[type_count + z];
        if (!in_two_core[type_count + z]) continue;
        const int gx = static_cast<int>(z / q);
        const int gy = static_cast<int>(z % q);
        for (int d = 0; d < 8; ++d) {
          const int ux = (gx + dx[d] + q) % q;
          const int uy = (gy + dy[d] + q) % q;
          const auto u = static_cast<std::size_t>(ux) * q + uy;
          if (clean_mask[u] && in_two_core[type_count + u])
            integer_t[z * 8 + d] = quantize(t[z * 8 + d], root);
        }
      }
      t.clear();
      t.shrink_to_fit();
      parent.clear();
      parent.shrink_to_fit();
      block_maximum.clear();
      block_maximum.shrink_to_fit();

      std::vector<std::uint64_t> integer_sum_a_site(period_cells, 0);
      std::vector<std::uint64_t> integer_incoming_t(period_cells, 0);
      std::vector<std::uint64_t> integer_sum_b_component(type_count, 0);
      for (std::size_t z = 0; z < period_cells; ++z)
        for (auto k = offsets[z]; k < offsets[z + 1]; ++k)
          integer_sum_a_site[z] += integer_a[k];
      for (int gx = 0; gx < q; ++gx) {
        for (int gy = 0; gy < q; ++gy) {
          const auto z = static_cast<std::size_t>(gx) * q + gy;
          if (!clean_mask[z]) continue;
          for (int d = 0; d < 8; ++d) {
            const int ux = (gx + dx[d] + q) % q;
            const int uy = (gy + dy[d] + q) % q;
            const auto u = static_cast<std::size_t>(ux) * q + uy;
            if (clean_mask[u])
              integer_incoming_t[z] += integer_t[u * 8 + reverse[d]];
          }
        }
      }
      for (int type = 0; type < type_count; ++type)
        for (auto j = component_offsets[type]; j < component_offsets[type + 1];
             ++j)
          integer_sum_b_component[type] +=
              integer_b[component_incidences[j]];

      std::uint64_t failures = 0;
      long double exact_ratio_max = 0.0L;
      auto check_unweighted = [&](std::uint64_t source_sum,
                                  std::uint32_t target) {
        if (target == 0) return;
        using U128 = unsigned __int128;
        const U128 left = static_cast<U128>(beta_den) * source_sum;
        const U128 right = static_cast<U128>(beta_num) * target;
        failures += left > right;
        exact_ratio_max = std::max(
            exact_ratio_max,
            static_cast<long double>(source_sum) / target);
      };
      auto check_q_weighted = [&](std::uint64_t source_sum,
                                  std::uint32_t target) {
        if (target == 0) return;
        using U128 = unsigned __int128;
        const U128 left = static_cast<U128>(q_num) * beta_den * source_sum;
        const U128 right =
            static_cast<U128>(q_den) * beta_num * target;
        failures += left > right;
        exact_ratio_max = std::max(
            exact_ratio_max,
            static_cast<long double>(q_num) / q_den * source_sum / target);
      };

      for (std::size_t z = 0; z < period_cells; ++z) {
        for (auto k = offsets[z]; k < offsets[z + 1]; ++k) {
          check_unweighted(integer_sum_a_site[z] - integer_a[k] +
                               integer_incoming_t[z],
                           integer_b[k]);
          check_q_weighted(
              integer_sum_b_component[incident_types[k]] - integer_b[k],
              integer_a[k]);
        }
      }
      for (int gx = 0; gx < q; ++gx) {
        for (int gy = 0; gy < q; ++gy) {
          const auto z = static_cast<std::size_t>(gx) * q + gy;
          if (!clean_mask[z]) continue;
          const auto source = integer_sum_a_site[z] + integer_incoming_t[z];
          for (int d = 0; d < 8; ++d) {
            const int ux = (gx + dx[d] + q) % q;
            const int uy = (gy + dy[d] + q) % q;
            const auto u = static_cast<std::size_t>(ux) * q + uy;
            if (!clean_mask[u]) continue;
            check_q_weighted(source - integer_t[u * 8 + reverse[d]],
                             integer_t[z * 8 + d]);
          }
        }
      }
      std::cout << "exact_integer_collatz_beta=0.97"
                << " exact_ratio_max=" << static_cast<double>(exact_ratio_max)
                << " failures=" << failures
                << " certificate=" << (failures == 0 ? "PASS" : "FAIL")
                << "\n";
      return failures == 0 ? 0 : 7;
    }
  }
}
