import Erdos1212Kernel.AlgebraicCorridorMonomials

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

/-- The paper's coefficient height; the zero polynomial is assigned height zero. -/
def corridorPolynomialHeight (H : MvPolynomial (Fin 2) ℤ) : ℕ :=
  H.support.sup fun e => (MvPolynomial.coeff e H).natAbs

theorem corridorPolynomialHeight_le_of_coeff_bound
    (H : MvPolynomial (Fin 2) ℤ) {B : ℝ} (hB : 0 ≤ B)
    (hcoeff : ∀ e, |((MvPolynomial.coeff e H : ℤ) : ℝ)| ≤ B) :
    (corridorPolynomialHeight H : ℝ) ≤ B := by
  have hsup (s : Finset (Fin 2 →₀ ℕ)) :
      ((s.sup (fun e => (MvPolynomial.coeff e H).natAbs) : ℕ) : ℝ) ≤ B := by
    induction s using Finset.induction_on with
    | empty => simpa using hB
    | @insert a s ha ih =>
      rw [Finset.sup_insert, Nat.cast_max]
      apply max_le
      · simpa only [Nat.cast_natAbs, Int.cast_abs] using hcoeff a
      · exact ih
  exact hsup H.support

/-- A coefficient vector extended by zero onto distinct selected monomials. -/
def corridorSparsePolynomial {ι : Type*} [Fintype ι]
    (monomial : ι → (Fin 2 →₀ ℕ)) (weight : ι → ℤ) : MvPolynomial (Fin 2) ℤ :=
  ∑ i, MvPolynomial.monomial (monomial i) (weight i)

theorem corridorSparsePolynomial_coeff_at {ι : Type*} [Fintype ι]
    (monomial : ι → (Fin 2 →₀ ℕ)) (weight : ι → ℤ)
    (hinj : Function.Injective monomial) (i : ι) :
    MvPolynomial.coeff (monomial i) (corridorSparsePolynomial monomial weight) = weight i := by
  classical
  simp [corridorSparsePolynomial, MvPolynomial.coeff_sum, hinj.eq_iff]

theorem corridorSparsePolynomial_coeff_off {ι : Type*} [Fintype ι]
    (monomial : ι → (Fin 2 →₀ ℕ)) (weight : ι → ℤ) (e : Fin 2 →₀ ℕ)
    (hoff : e ∉ Set.range monomial) :
    MvPolynomial.coeff e (corridorSparsePolynomial monomial weight) = 0 := by
  classical
  simp only [corridorSparsePolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro i _
  exact if_neg (fun heq => hoff ⟨i, heq⟩)

theorem corridorSparsePolynomial_ne_zero {ι : Type*} [Fintype ι]
    (monomial : ι → (Fin 2 →₀ ℕ)) (weight : ι → ℤ)
    (hinj : Function.Injective monomial) (hweight : weight ≠ 0) :
    corridorSparsePolynomial monomial weight ≠ 0 := by
  intro hzero
  apply hweight
  funext i
  have hi := (corridorSparsePolynomial_coeff_at monomial weight hinj i).symm
  simpa only [hzero, MvPolynomial.coeff_zero] using hi

theorem corridorSparsePolynomial_totalDegree_le {ι : Type*} [Fintype ι]
    (monomial : ι → (Fin 2 →₀ ℕ)) (weight : ι → ℤ) {d : ℕ}
    (hdegree : ∀ i, (monomial i).sum (fun _ n => n) ≤ d) :
    (corridorSparsePolynomial monomial weight).totalDegree ≤ d := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  exact (MvPolynomial.totalDegree_monomial_le (monomial i) (weight i)).trans (hdegree i)

theorem corridorSparsePolynomial_coeff_bound {ι : Type*} [Fintype ι]
    (monomial : ι → (Fin 2 →₀ ℕ)) (weight : ι → ℤ)
    (hinj : Function.Injective monomial) {B : ℝ} (hB : 0 ≤ B)
    (hweight : ∀ i, |(weight i : ℝ)| ≤ B) (e : Fin 2 →₀ ℕ) :
    |((MvPolynomial.coeff e (corridorSparsePolynomial monomial weight) : ℤ) : ℝ)| ≤ B := by
  by_cases he : e ∈ Set.range monomial
  · obtain ⟨i, rfl⟩ := he
    rw [corridorSparsePolynomial_coeff_at monomial weight hinj]
    exact hweight i
  · rw [corridorSparsePolynomial_coeff_off monomial weight e he]
    simpa using hB

theorem corridorSparsePolynomial_eval {ι : Type*} [Fintype ι]
    (monomial : ι → (Fin 2 →₀ ℕ)) (weight : ι → ℤ) (x : Fin 2 → ℤ) :
    MvPolynomial.eval x (corridorSparsePolynomial monomial weight) =
      ∑ i, weight i * MvPolynomial.eval x (MvPolynomial.monomial (monomial i) 1) := by
  simp only [corridorSparsePolynomial, map_sum, MvPolynomial.eval_monomial, one_mul]

end

end Erdos1212Kernel
