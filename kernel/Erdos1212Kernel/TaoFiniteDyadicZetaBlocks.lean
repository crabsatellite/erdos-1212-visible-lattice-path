import Erdos1212Kernel.TaoFiniteDyadicAggregation

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1800000

def taoZetaTerm (σ t : Real) (n : Nat) : Complex :=
  (n : Complex) ^ (-((σ : Complex) + (t : Complex) * Complex.I))

theorem taoDyadicBlock_zeta_eq (σ t : Real) (r : Nat) :
    taoDyadicBlock (taoZetaTerm σ t) r =
      ∑ m ∈ Finset.range (2 ^ r),
        (((2 ^ r + m : Nat) : Complex) ^ (-((σ : Complex) + (t : Complex) * Complex.I))) := rfl

/-- Finite dyadic aggregation of every scale satisfying the explicit
Littlewood width condition. The exceptional N=1 block is handled by
the literal one-term estimate. -/
theorem taoFiniteDyadic_zeta_good_scales (t σ : Real) (J : Nat)
    (ht : t ≠ 0) (hσ : 0 ≤ σ)
    (hfrequency : ∀ r, 1 ≤ r → r < J → ((2 ^ r : Nat) : Real) ≤ taoLogFrequency t)
    (hwidth : ∀ r, 1 ≤ r → r < J →
      1 - σ ≤ taoExplicitDecayExponent (taoLogFrequency t) ((2 ^ r : Nat) : Real)) :
    ‖∑ n ∈ Finset.Ico 1 (2 ^ J), taoZetaTerm σ t n‖ ≤
      (J : Real) * ((2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t)) := by
  let L : Real := (2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t)
  have hT := taoLogFrequency_pos ht
  have hL : 0 ≤ L := by
    unfold L
    have hlog := Real.log_nonneg (by linarith : 1 ≤ 2 + taoLogFrequency t)
    positivity
  have hLone : 1 ≤ L := by
    unfold L
    have hlog := taoSecondDerivative_log_lower hT.le
    have hp : (2 : Real) ≤ 2 ^ 42 := by norm_num
    nlinarith [mul_le_mul hp hlog (by norm_num : (0 : Real) ≤ 1 / 2)
      (by positivity : (0 : Real) ≤ 2 ^ 42)]
  apply taoFiniteDyadic_partial_sum_bound (taoZetaTerm σ t) J hL
  intro r hr
  by_cases hr0 : r = 0
  · subst r
    have htriv := taoDyadicComplexPower_trivial_bound t σ 1 1 (by norm_num) le_rfl hσ
    rw [taoDyadicBlock_zeta_eq]
    exact htriv.trans (by simpa only [Nat.cast_one] using hLone)
  · have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
    have hNr : 2 ≤ 2 ^ r := by
      exact (pow_le_pow_right₀ (by norm_num) hr1 : 2 ^ 1 ≤ 2 ^ r)
    have hgood := taoDyadicComplexPower_log_bound_of_width t σ (2 ^ r) (2 ^ r)
      hNr le_rfl ht hσ (hfrequency r hr1 hr) (hwidth r hr1 hr)
    rw [taoDyadicBlock_zeta_eq]
    exact hgood

end

end Erdos1212Kernel
