import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

/-- Exactly the exponent pairs of all bivariate monomials of total degree at most d. -/
def corridorMonomialExponents (d : ℕ) : Finset (Fin 2 →₀ ℕ) :=
  (Finset.range (d + 1)).biUnion fun n => (Finset.univ : Finset (Fin 2)).finsuppAntidiag n

theorem mem_corridorMonomialExponents {d : ℕ} {e : Fin 2 →₀ ℕ} :
    e ∈ corridorMonomialExponents d ↔ e.sum (fun _ n => n) ≤ d := by
  simp only [corridorMonomialExponents, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_finsuppAntidiag', Finset.subset_univ, and_true]
  constructor
  · rintro ⟨n, hn, he⟩
    omega
  · intro he
    exact ⟨e.sum (fun _ n => n), by omega, rfl⟩

/-- The exact r+1 column count in Lemma 5.1, using the library's stars-and-bars identity. -/
theorem corridorMonomialExponents_card (d : ℕ) :
    (corridorMonomialExponents d).card = (d + 2).choose 2 := by
  have hdisjoint : (Finset.range (d + 1) : Set ℕ).PairwiseDisjoint
      (fun n => (Finset.univ : Finset (Fin 2)).finsuppAntidiag n) := by
    intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro e hea heb
    exact hab ((Finset.mem_finsuppAntidiag.mp hea).1.symm.trans
      (Finset.mem_finsuppAntidiag.mp heb).1)
  calc
    (corridorMonomialExponents d).card =
        ∑ n ∈ Finset.range (d + 1), ((Finset.univ : Finset (Fin 2)).finsuppAntidiag n).card :=
      Finset.card_biUnion hdisjoint
    _ = ∑ n ∈ Finset.range (d + 1), (2 : ℕ).multichoose n := by
      apply Finset.sum_congr rfl
      intro n _
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_finsuppAntidiag_nat_eq_multichoose (s := (Finset.univ : Finset (Fin 2))) n
    _ = (d + 2).choose 2 := Nat.sum_range_multichoose d 2

def corridorInterpolationRowCount (d : ℕ) : ℕ := (d + 2).choose 2 - 1

theorem corridorInterpolationRowCount_succ (d : ℕ) :
    corridorInterpolationRowCount d + 1 = (d + 2).choose 2 := by
  have hpositive : 0 < (d + 2).choose 2 := Nat.choose_pos (by omega)
  unfold corridorInterpolationRowCount
  omega

/-- The real-coordinate entry bound R^d, with no integer rounding of R. -/
theorem corridor_eval_monomial_abs_le {d : ℕ} {R : ℝ}
    (x : Fin 2 → ℤ) (e : Fin 2 →₀ ℕ)
    (hR : 1 ≤ R) (hx : ∀ i, |(x i : ℝ)| ≤ R)
    (he : e.sum (fun _ n => n) ≤ d) :
    |(MvPolynomial.eval x (MvPolynomial.monomial e (1 : ℤ)) : ℝ)| ≤ R ^ d := by
  rw [MvPolynomial.eval_monomial, one_mul]
  simp only [Finsupp.prod, Int.cast_prod, Int.cast_pow, Finset.abs_prod, abs_pow]
  calc
    (∏ i ∈ e.support, |(x i : ℝ)| ^ e i) ≤ ∏ i ∈ e.support, R ^ e i := by
      apply Finset.prod_le_prod
      · intro i _
        exact pow_nonneg (abs_nonneg _) _
      · intro i _
        exact pow_le_pow_left₀ (abs_nonneg _) (hx i) _
    _ = R ^ e.sum (fun _ n => n) := by
      rw [Finset.prod_pow_eq_pow_sum]
      rfl
    _ ≤ R ^ d := pow_le_pow_right₀ hR he

end

end Erdos1212Kernel
