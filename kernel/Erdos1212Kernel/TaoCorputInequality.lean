import Erdos1212Kernel.TaoCorputEnergy
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Field

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1400000

theorem taoCorput_vdc_normalized_square (z : Int → Complex) (a : Int) (N H : Nat) (hH : 0 < H) (hHN : H ≤ N)
    (hz : ∀ n, n ∉ taoCorputInterval a N → z n = 0)
    (hunit : ∀ n ∈ taoCorputInterval a N, ‖z n‖ ≤ 1) :
    (‖taoCorputSum z a N‖ / (N : Real)) ^ 2 ≤ 2 / (H : Real) +
      4 / ((H : Real) * N) * ∑ h ∈ Finset.Icc 1 H, ‖taoCorputCorrelation z a N h‖ := by
  have hHr : (0 : Real) < H := by exact_mod_cast hH
  have hNr : (0 : Real) < N := by exact_mod_cast (lt_of_lt_of_le hH hHN)
  have h := taoCorput_vdc_unit_scaled z a N H hH hHN hz hunit
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hNr)).mpr
  apply le_of_mul_le_mul_left (a := (H : Real)) _ hHr
  convert h using 1 <;> field_simp [hHr.ne', hNr.ne'] <;> ring

theorem taoCorput_vdc_normalized (z : Int → Complex) (a : Int) (N H : Nat) (hH : 0 < H) (hHN : H ≤ N)
    (hz : ∀ n, n ∉ taoCorputInterval a N → z n = 0)
    (hunit : ∀ n ∈ taoCorputInterval a N, ‖z n‖ ≤ 1) :
    ‖taoCorputSum z a N‖ / (N : Real) ≤ Real.sqrt (2 / (H : Real)) +
      2 * Real.sqrt ((∑ h ∈ Finset.Icc 1 H, ‖taoCorputCorrelation z a N h‖) / ((H : Real) * N)) := by
  have hHr : (0 : Real) < H := by exact_mod_cast hH
  have hNr : (0 : Real) < N := by exact_mod_cast (lt_of_lt_of_le hH hHN)
  let C := ∑ h ∈ Finset.Icc 1 H, ‖taoCorputCorrelation z a N h‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun h _ => norm_nonneg _)
  have h1 := Real.sq_sqrt (show 0 ≤ 2 / (H : Real) by positivity)
  have h2 := Real.sq_sqrt (show 0 ≤ C / ((H : Real) * N) by positivity)
  have hq := taoCorput_vdc_normalized_square z a N H hH hHN hz hunit
  change (‖taoCorputSum z a N‖ / (N : Real)) ^ 2 ≤ 2 / (H : Real) + 4 / ((H : Real) * N) * C at hq
  rw [show 4 / ((H : Real) * N) * C = 4 * (C / ((H : Real) * N)) by ring] at hq
  have hq0 : 0 ≤ ‖taoCorputSum z a N‖ / (N : Real) := div_nonneg (norm_nonneg _) hNr.le
  have hc := mul_nonneg (Real.sqrt_nonneg (2 / (H : Real))) (Real.sqrt_nonneg (C / ((H : Real) * N)))
  change ‖taoCorputSum z a N‖ / (N : Real) ≤ Real.sqrt (2 / (H : Real)) + 2 * Real.sqrt (C / ((H : Real) * N))
  nlinarith [Real.sqrt_nonneg (2 / (H : Real)), Real.sqrt_nonneg (C / ((H : Real) * N))]

theorem taoCorput_normalized_correlation_average (z : Int → Complex) (a : Int) (N H : Nat) :
    (∑ h ∈ Finset.Icc 1 H, ‖taoCorputCorrelation z a N h‖) / ((H : Real) * N) =
      (1 / (H : Real)) * ∑ h ∈ Finset.Icc 1 H, ‖taoCorputCorrelation z a N h‖ / (N : Real) := by
  rw [← Finset.sum_div]
  ring

/-- The source normalization of Proposition 7 with a concrete absolute
constant 2, still for the actual zero-extended sequence. -/
theorem taoCorput_vdc_source_bound (z : Int → Complex) (a : Int) (N H : Nat) (hH : 0 < H) (hHN : H ≤ N)
    (hz : ∀ n, n ∉ taoCorputInterval a N → z n = 0)
    (hunit : ∀ n ∈ taoCorputInterval a N, ‖z n‖ ≤ 1) :
    ‖taoCorputSum z a N‖ / (N : Real) ≤ 2 * (1 / Real.sqrt (H : Real) +
      Real.sqrt ((1 / (H : Real)) * ∑ h ∈ Finset.Icc 1 H, ‖taoCorputCorrelation z a N h‖ / (N : Real))) := by
  have hHr : (0 : Real) < H := by exact_mod_cast hH
  have hs := Real.sqrt_pos.mpr hHr
  have hfirst : Real.sqrt (2 / (H : Real)) ≤ 2 / Real.sqrt (H : Real) := by
    rw [Real.sqrt_div (by norm_num : (0 : Real) ≤ 2)]
    apply div_le_div_of_nonneg_right _ hs.le
    nlinarith [Real.sq_sqrt (show (0 : Real) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : Real)]
  have h := taoCorput_vdc_normalized z a N H hH hHN hz hunit
  rw [taoCorput_normalized_correlation_average] at h
  calc
    _ ≤ Real.sqrt (2 / (H : Real)) + 2 * Real.sqrt ((1 / (H : Real)) *
        ∑ h ∈ Finset.Icc 1 H, ‖taoCorputCorrelation z a N h‖ / (N : Real)) := h
    _ ≤ 2 / Real.sqrt (H : Real) + 2 * Real.sqrt ((1 / (H : Real)) *
        ∑ h ∈ Finset.Icc 1 H, ‖taoCorputCorrelation z a N h‖ / (N : Real)) := add_le_add hfirst le_rfl
    _ = _ := by ring

end

end Erdos1212Kernel
