import Erdos1212Kernel.TaoRieszRootLogError

namespace Erdos1212Kernel

noncomputable section

open Set Complex
open scoped BigOperators

set_option maxHeartbeats 600000

def taoVonMangoldtRampSum (N : Nat) (x : Real) : Real :=
  ∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n * max 0 (x - n)

theorem taoRiesz_scaled_real_term {x : Real} (hx : 0 < x) (n : Nat) :
    x * ((ArithmeticFunction.vonMangoldt n : Complex) * taoRieszCutoff (n / x)).re =
      ArithmeticFunction.vonMangoldt n * max 0 (x - n) := by
  by_cases hn0 : n = 0
  · subst n
    simp
  · have hn : 0 < (n : Real) := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hnx0 : 0 < (n : Real) / x := div_pos hn hx
    by_cases hnx : (n : Real) ≤ x
    · have hnx1 : (n : Real) / x ≤ 1 := (div_le_one hx).2 hnx
      rw [taoRieszCutoff, Set.indicator_of_mem (show (n : Real) / x ∈ Ioc 0 1 from ⟨hnx0, hnx1⟩)]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [max_eq_right (sub_nonneg.mpr hnx)]
      field_simp
      <;> ring
    · have hxn : x < (n : Real) := lt_of_not_ge hnx
      have hnx1 : 1 ≤ (n : Real) / x := (le_div_iff₀ hx).2 (by linarith)
      rw [taoRieszCutoff_eq_zero_of_one_le hnx1, mul_zero, Complex.zero_re, mul_zero,
        max_eq_left (sub_nonpos.mpr hxn.le), mul_zero]

theorem taoVonMangoldtRampSum_eq_scaled_Riesz
    {x : Real} (hx : 0 < x) {N : Nat} (hN : Nat.ceil x + 1 ≤ N) :
    taoVonMangoldtRampSum N x = x * (taoVonMangoldtRieszSum x).re := by
  have hcanonical : x * (taoVonMangoldtRieszSum x).re =
      taoVonMangoldtRampSum (Nat.ceil x + 1) x := by
    unfold taoVonMangoldtRieszSum taoVonMangoldtRampSum
    rw [Complex.re_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    exact taoRiesz_scaled_real_term hx n
  rw [hcanonical]
  unfold taoVonMangoldtRampSum
  symm
  apply Finset.sum_subset (Finset.range_mono hN)
  intro n _hn hnot
  have hceiln : Nat.ceil x + 1 ≤ n := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hnot)
  have hxn : x ≤ (n : Real) := (Nat.le_ceil x).trans (by exact_mod_cast (show Nat.ceil x ≤ n by omega))
  rw [max_eq_left (sub_nonpos.mpr hxn), mul_zero]

theorem taoPsi_eq_finite_step_sum {x : Real} (hx : 0 ≤ x)
    {N : Nat} (hN : Nat.ceil x + 1 ≤ N) :
    Chebyshev.psi x = ∑ n ∈ Finset.range N,
      if (n : Real) ≤ x then ArithmeticFunction.vonMangoldt n else 0 := by
  classical
  rw [Chebyshev.psi_eq_sum_Icc, ← Finset.sum_filter]
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_Icc, Nat.zero_le, true_and, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hn
      have hnx : (n : Real) ≤ x := (Nat.le_floor_iff hx).1 hn
      have hnceil : n ≤ Nat.ceil x := by exact_mod_cast hnx.trans (Nat.le_ceil x)
      exact ⟨by omega, hnx⟩
    · intro hn
      exact (Nat.le_floor_iff hx).2 hn.2
  · intro n _hn
    rfl

theorem taoRamp_secant_sandwich (n : Real) {x y : Real} (hxy : x ≤ y) :
    (y - x) * (if n ≤ x then 1 else 0) ≤ max 0 (y - n) - max 0 (x - n) ∧
      max 0 (y - n) - max 0 (x - n) ≤ (y - x) * (if n ≤ y then 1 else 0) := by
  by_cases hnx : n ≤ x
  · rw [if_pos hnx, if_pos (hnx.trans hxy), max_eq_right (by linarith), max_eq_right (by linarith)]
    constructor <;> linarith
  · rw [if_neg hnx, max_eq_left (show x - n ≤ 0 by linarith), sub_zero, mul_zero]
    by_cases hny : n ≤ y
    · rw [if_pos hny, max_eq_right (by linarith)]
      constructor <;> linarith
    · rw [if_neg hny, max_eq_left (show y - n ≤ 0 by linarith), mul_zero]
      exact ⟨le_rfl, le_rfl⟩

theorem taoVonMangoldtRampSum_secant_sandwich
    {x y : Real} (hx : 0 ≤ x) (hxy : x ≤ y)
    {N : Nat} (hNx : Nat.ceil x + 1 ≤ N) (hNy : Nat.ceil y + 1 ≤ N) :
    (y - x) * Chebyshev.psi x ≤ taoVonMangoldtRampSum N y - taoVonMangoldtRampSum N x ∧
      taoVonMangoldtRampSum N y - taoVonMangoldtRampSum N x ≤ (y - x) * Chebyshev.psi y := by
  classical
  rw [taoPsi_eq_finite_step_sum hx hNx, taoPsi_eq_finite_step_sum (hx.trans hxy) hNy]
  unfold taoVonMangoldtRampSum
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  constructor
  · apply Finset.sum_le_sum
    intro n _hn
    have h := mul_le_mul_of_nonneg_left (taoRamp_secant_sandwich (n : Real) hxy).1
      (ArithmeticFunction.vonMangoldt_nonneg (n := n))
    by_cases hn : (n : Real) ≤ x <;> simpa only [hn, if_true, if_false, mul_zero, mul_one,
      mul_sub, sub_mul, zero_mul, mul_comm, mul_left_comm, mul_assoc] using h
  · apply Finset.sum_le_sum
    intro n _hn
    have h := mul_le_mul_of_nonneg_left (taoRamp_secant_sandwich (n : Real) hxy).2
      (ArithmeticFunction.vonMangoldt_nonneg (n := n))
    by_cases hn : (n : Real) ≤ y <;> simpa only [hn, if_true, if_false, mul_zero, mul_one,
      mul_sub, sub_mul, zero_mul, mul_comm, mul_left_comm, mul_assoc] using h

end

end Erdos1212Kernel
