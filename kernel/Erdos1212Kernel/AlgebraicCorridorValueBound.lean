import Erdos1212Kernel.AlgebraicCorridorInterpolation
import Erdos1212Kernel.AlgebraicCorridorNegation

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

theorem corridor_coeff_natAbs_le_height (H : MvPolynomial (Fin 2) ℤ) (e : Fin 2 →₀ ℕ) :
    (MvPolynomial.coeff e H).natAbs ≤ corridorPolynomialHeight H := by
  by_cases hz : MvPolynomial.coeff e H = 0
  · simp only [hz, Int.natAbs_zero]
    exact Nat.zero_le _
  · exact Finset.le_sup (f := fun e => (MvPolynomial.coeff e H).natAbs)
      (MvPolynomial.mem_support_iff.mpr hz)

theorem corridor_coeff_abs_le_height (H : MvPolynomial (Fin 2) ℤ) (e : Fin 2 →₀ ℕ) :
    |((MvPolynomial.coeff e H : ℤ) : ℝ)| ≤ (corridorPolynomialHeight H : ℝ) := by
  have hc : ((MvPolynomial.coeff e H).natAbs : ℝ) ≤ (corridorPolynomialHeight H : ℝ) := by
    exact_mod_cast corridor_coeff_natAbs_le_height H e
  simpa only [Nat.cast_natAbs, Int.cast_abs] using hc

/-- The exact coefficient-count evaluation bound used in Proposition 5.2. -/
theorem corridor_polynomial_eval_abs_le (H : MvPolynomial (Fin 2) ℤ)
    {d : ℕ} {X : ℝ} (hdegree : H.totalDegree ≤ d) (hX : 1 ≤ X)
    (x : Fin 2 → ℤ) (hx : ∀ k, |(x k : ℝ)| ≤ X) :
    |(MvPolynomial.eval x H : ℝ)| ≤
      ((d + 2).choose 2 : ℝ) * (corridorPolynomialHeight H : ℝ) * X ^ d := by
  classical
  have hsupport : H.support ⊆ corridorMonomialExponents d := by
    intro e he
    exact mem_corridorMonomialExponents.mpr ((MvPolynomial.le_totalDegree he).trans hdegree)
  have hsum : MvPolynomial.eval x H =
      ∑ e ∈ H.support, MvPolynomial.coeff e H *
        MvPolynomial.eval x (MvPolynomial.monomial e 1) := by
    rw [MvPolynomial.eval_eq]
    apply Finset.sum_congr rfl
    intro e _
    simp only [MvPolynomial.eval_monomial, one_mul, Finsupp.prod]
  have hsumR : (MvPolynomial.eval x H : ℝ) =
      ∑ e ∈ H.support, ((MvPolynomial.coeff e H : ℤ) : ℝ) *
        (MvPolynomial.eval x (MvPolynomial.monomial e 1) : ℝ) := by
    exact_mod_cast hsum
  let B : ℝ := (corridorPolynomialHeight H : ℝ) * X ^ d
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (zero_le_one.trans hX) _)
  calc
    |(MvPolynomial.eval x H : ℝ)| =
        |∑ e ∈ H.support, ((MvPolynomial.coeff e H : ℤ) : ℝ) *
          (MvPolynomial.eval x (MvPolynomial.monomial e 1) : ℝ)| := congrArg abs hsumR
    _ ≤ ∑ e ∈ H.support, |((MvPolynomial.coeff e H : ℤ) : ℝ) *
          (MvPolynomial.eval x (MvPolynomial.monomial e 1) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ H.support, B := by
      apply Finset.sum_le_sum
      intro e he
      rw [abs_mul]
      exact mul_le_mul (corridor_coeff_abs_le_height H e)
        (corridor_eval_monomial_abs_le x e hX hx ((MvPolynomial.le_totalDegree he).trans hdegree))
        (abs_nonneg _) (Nat.cast_nonneg _)
    _ = (H.support.card : ℝ) * B := by simp
    _ ≤ ((corridorMonomialExponents d).card : ℝ) * B :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsupport) hB
    _ = ((d + 2).choose 2 : ℝ) * (corridorPolynomialHeight H : ℝ) * X ^ d := by
      rw [corridorMonomialExponents_card]
      exact (mul_assoc _ _ _).symm

/-- Algebraic part of Proposition 5.2. The geometric witness and the scale
inequality remain explicit inputs; no crossing or asymptotic estimate is assumed proved. -/
theorem corridor_algebraic_zero_of_large_prime_product
    (d : ℕ) (hd : 1 ≤ d) (R X : ℝ) (hR : 1 ≤ R) (hX : 1 ≤ X)
    (root : Fin 2 → ℤ) (point : Fin (corridorInterpolationRowCount d) → Fin 2 → ℤ)
    (q : Fin (corridorInterpolationRowCount d) → ℕ)
    (hpoint : ∀ i k, |(point i k : ℝ)| ≤ R)
    (hroot : ∀ k, |(root k : ℝ)| ≤ X)
    (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q)
    (hdiv : ∀ i k, (q i : ℤ) ∣ root k + point i k)
    (hsize : ((d + 2).choose 2 : ℝ) *
        (((corridorInterpolationRowCount d).factorial : ℝ) *
          R ^ (d * corridorInterpolationRowCount d)) * X ^ d < ((∏ i, q i : ℕ) : ℝ)) :
    ∃ F : MvPolynomial (Fin 2) ℤ,
      F ≠ 0 ∧ F.totalDegree ≤ d ∧ MvPolynomial.eval root F = 0 ∧
      (corridorPolynomialHeight F : ℝ) ≤
        ((corridorInterpolationRowCount d).factorial : ℝ) *
          R ^ (d * corridorInterpolationRowCount d) := by
  obtain ⟨H, hH, hdegree, _hvanish, hheight, hdivisibility⟩ :=
    corridor_integer_interpolation_and_divisibility d hd R hR point hpoint
  have hvalue := corridor_polynomial_eval_abs_le H hdegree hX (fun k => -root k)
    (fun k => by simpa only [Int.cast_neg, abs_neg] using hroot k)
  have hupper := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hheight (Nat.cast_nonneg ((d + 2).choose 2)))
    (pow_nonneg (zero_le_one.trans hX) d)
  have hsmall := (hvalue.trans hupper).trans_lt hsize
  have hnat : (MvPolynomial.eval (fun k => -root k) H).natAbs < ∏ i, q i := by
    have hcast : ((MvPolynomial.eval (fun k => -root k) H).natAbs : ℝ) < ((∏ i, q i : ℕ) : ℝ) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hsmall
    exact_mod_cast hcast
  have hzero : MvPolynomial.eval (fun k => -root k) H = 0 := by
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hdivisibility root q hq hinj hdiv)
    simpa only [Int.natAbs_natCast] using hnat
  refine ⟨corridorNegateVariables H, corridorNegateVariables_ne_zero hH, ?_, ?_, ?_⟩
  · simpa only [corridorNegateVariables_totalDegree] using hdegree
  · simpa only [corridorNegateVariables_eval] using hzero
  · simpa only [corridorNegateVariables_height] using hheight

end

end Erdos1212Kernel
