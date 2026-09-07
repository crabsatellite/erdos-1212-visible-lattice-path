import Erdos1212Kernel.TaoZetaEulerLimit

namespace Erdos1212Kernel

noncomputable section

open Filter Topology
open scoped BigOperators

set_option maxHeartbeats 1900000

theorem taoZetaEuler_partial_eq_range {s : Complex} (hs : 1 < s.re) {N : Nat} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ico 1 N, (n : Complex) ^ (-s)) =
      ∑ n ∈ Finset.range N, 1 / (n : Complex) ^ s := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; norm_num at hs
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (by omega : 0 ≤ 1) hN]
  simp [Complex.zero_cpow hs0]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Complex.cpow_neg]

theorem taoZetaEuler_partial_tendsto {s : Complex} (hs : 1 < s.re) :
    Tendsto (fun N : Nat => ∑ n ∈ Finset.Ico 1 N, (n : Complex) ^ (-s))
      atTop (𝓝 (riemannZeta s)) := by
  have hsum : Summable (fun n : Nat => 1 / (n : Complex) ^ s) :=
    Complex.summable_one_div_nat_cpow.mpr hs
  have hz := hsum.hasSum
  rw [← zeta_eq_tsum_one_div_nat_cpow hs] at hz
  have hrange := hz.tendsto_sum_nat
  apply Filter.Tendsto.congr' _ hrange
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (taoZetaEuler_partial_eq_range hs hN).symm

theorem taoZetaEuler_correction_tendsto {s : Complex} (hs : 1 < s.re) (hs1 : s ≠ 1) :
    Tendsto (fun N : Nat => (N : Complex) ^ (1 - s) / (s - 1)) atTop (𝓝 0) := by
  have hexp : 0 < s.re - 1 := by linarith
  have hreal : Tendsto (fun N : Nat => (N : Real) ^ (1 - s.re)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop hexp).comp tendsto_natCast_atTop_atTop
    simpa only [neg_sub] using h
  have hnorm : Tendsto (fun N : Nat => ‖(N : Complex) ^ (1 - s) / (s - 1)‖)
      atTop (𝓝 0) := by
    have hdiv : Tendsto (fun N : Nat => (N : Real) ^ (1 - s.re) / ‖s - 1‖)
        atTop (𝓝 0) := by simpa only [zero_div] using hreal.div_const ‖s - 1‖
    apply Filter.Tendsto.congr' _ hdiv
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
    rw [Complex.norm_div]
    change (N : Real) ^ (1 - s.re) / ‖s - 1‖ =
      ‖(((N : Real) : Complex) ^ (1 - s))‖ / ‖s - 1‖
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    congr 2
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

theorem taoZetaEulerApprox_tendsto_riemannZeta {s : Complex} (hs : 1 < s.re) (hs1 : s ≠ 1) :
    Tendsto (taoZetaEulerApprox s) atTop (𝓝 (riemannZeta s)) := by
  unfold taoZetaEulerApprox
  simpa only [add_zero] using (taoZetaEuler_partial_tendsto hs).add
    (taoZetaEuler_correction_tendsto hs hs1)

theorem taoZetaEulerLimit_eq_riemannZeta {s : Complex} (hs : 1 < s.re) (hs1 : s ≠ 1) :
    taoZetaEulerLimit s = riemannZeta s := by
  exact tendsto_nhds_unique (taoZetaEulerApprox_tendsto (by linarith) hs1)
    (taoZetaEulerApprox_tendsto_riemannZeta hs hs1)

end

end Erdos1212Kernel
