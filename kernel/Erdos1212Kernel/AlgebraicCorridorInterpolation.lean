import Erdos1212Kernel.AlgebraicCorridorMaximalMinor
import Erdos1212Kernel.AlgebraicCorridorSparsePolynomial
import Erdos1212Kernel.AlgebraicCorridorEvaluation

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

/-!
Lemma 5.1 on the paper's literal two-variable integer polynomial.
The monomial enumeration, rank-deficient matrix construction, zero extension,
degree and coefficient height are all consumed in this producer.
-/

theorem corridor_integer_interpolation (d : ℕ) (_hd : 1 ≤ d) (R : ℝ) (hR : 1 ≤ R)
    (point : Fin (corridorInterpolationRowCount d) → Fin 2 → ℤ)
    (hpoint : ∀ i k, |(point i k : ℝ)| ≤ R) :
    ∃ H : MvPolynomial (Fin 2) ℤ,
      H ≠ 0 ∧ H.totalDegree ≤ d ∧
      (∀ i, MvPolynomial.eval (point i) H = 0) ∧
      (corridorPolynomialHeight H : ℝ) ≤
        ((corridorInterpolationRowCount d).factorial : ℝ) *
          R ^ (d * corridorInterpolationRowCount d) := by
  classical
  let r := corridorInterpolationRowCount d
  have hcard : (corridorMonomialExponents d).card = r + 1 :=
    (corridorMonomialExponents_card d).trans (corridorInterpolationRowCount_succ d).symm
  let enumerate : Fin (r + 1) ≃ ↥(corridorMonomialExponents d) :=
    (Finset.equivFinOfCardEq hcard).symm
  let monomial : Fin (r + 1) → (Fin 2 →₀ ℕ) := fun j => (enumerate j).val
  have hmono : Function.Injective monomial :=
    Subtype.val_injective.comp enumerate.injective
  have hdegree : ∀ j, (monomial j).sum (fun _ n => n) ≤ d :=
    fun j => mem_corridorMonomialExponents.mp (enumerate j).property
  let M : Matrix (Fin r) (Fin (r + 1)) ℤ :=
    fun i j => MvPolynomial.eval (point i) (MvPolynomial.monomial (monomial j) 1)
  have hM : ∀ i j, |(M i j : ℝ)| ≤ R ^ d :=
    fun i j => corridor_eval_monomial_abs_le (point i) (monomial j) hR (hpoint i) (hdegree j)
  obtain ⟨t, _htr, cols, weight, hcols, hweight, hkernel, hheight⟩ :=
    corridor_exists_bounded_minor_kernel M hR hM
  let selected : Fin (t + 1) → (Fin 2 →₀ ℕ) := monomial ∘ cols
  have hselected : Function.Injective selected := hmono.comp hcols
  let H := corridorSparsePolynomial selected weight
  refine ⟨H, corridorSparsePolynomial_ne_zero selected weight hselected hweight,
    corridorSparsePolynomial_totalDegree_le selected weight (fun j => hdegree (cols j)), ?_, ?_⟩
  · intro i
    rw [corridorSparsePolynomial_eval]
    calc
      (∑ j, weight j * MvPolynomial.eval (point i) (MvPolynomial.monomial (selected j) 1)) =
          ∑ j, M i (cols j) * weight j := by
        apply Finset.sum_congr rfl
        intro j _
        exact mul_comm _ _
      _ = 0 := hkernel i
  · have hB : 0 ≤ (r.factorial : ℝ) * R ^ (d * r) :=
      mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (zero_le_one.trans hR) _)
    exact corridorPolynomialHeight_le_of_coeff_bound H hB
      (corridorSparsePolynomial_coeff_bound selected weight hselected hB hheight)

/-- The same interpolation polynomial works for every subsequent root/divisor assignment. -/
theorem corridor_integer_interpolation_and_divisibility
    (d : ℕ) (hd : 1 ≤ d) (R : ℝ) (hR : 1 ≤ R)
    (point : Fin (corridorInterpolationRowCount d) → Fin 2 → ℤ)
    (hpoint : ∀ i k, |(point i k : ℝ)| ≤ R) :
    ∃ H : MvPolynomial (Fin 2) ℤ,
      H ≠ 0 ∧ H.totalDegree ≤ d ∧
      (∀ i, MvPolynomial.eval (point i) H = 0) ∧
      (corridorPolynomialHeight H : ℝ) ≤
        ((corridorInterpolationRowCount d).factorial : ℝ) *
          R ^ (d * corridorInterpolationRowCount d) ∧
      ∀ (root : Fin 2 → ℤ) (q : Fin (corridorInterpolationRowCount d) → ℕ),
        (∀ i, (q i).Prime) → Function.Injective q →
        (∀ i k, (q i : ℤ) ∣ root k + point i k) →
        ((∏ i, q i : ℕ) : ℤ) ∣ MvPolynomial.eval (fun k => -root k) H := by
  obtain ⟨H, hnonzero, hdegree, hvanish, hheight⟩ :=
    corridor_integer_interpolation d hd R hR point hpoint
  refine ⟨H, hnonzero, hdegree, hvanish, hheight, ?_⟩
  intro root q hq hinj hdiv
  exact corridorPolynomial_prime_product_dvd_eval_neg_root H root point q hq hinj hvanish hdiv

end

end Erdos1212Kernel
