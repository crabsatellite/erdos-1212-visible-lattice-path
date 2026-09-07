import Erdos1212Kernel.AlgebraicCorridorSparsePolynomial

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

/-- The paper's literal substitution F(X,Y) = H(-X,-Y). -/
def corridorNegateVariables : MvPolynomial (Fin 2) ℤ →+* MvPolynomial (Fin 2) ℤ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => -MvPolynomial.X i)

@[simp] theorem corridorNegateVariables_C (a : ℤ) :
    corridorNegateVariables (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [corridorNegateVariables]

@[simp] theorem corridorNegateVariables_X (i : Fin 2) :
    corridorNegateVariables (MvPolynomial.X i) = -MvPolynomial.X i := by
  simp [corridorNegateVariables]

theorem corridorNegateVariables_eval (H : MvPolynomial (Fin 2) ℤ) (x : Fin 2 → ℤ) :
    MvPolynomial.eval x (corridorNegateVariables H) =
      MvPolynomial.eval (fun i => -x i) H := by
  refine MvPolynomial.induction_on
    (motive := fun P => MvPolynomial.eval x (corridorNegateVariables P) =
      MvPolynomial.eval (fun i => -x i) P) H ?_ ?_ ?_
  · intro a
    simp
  · intro P Q hP hQ
    simpa only [map_add] using congrArg₂ (fun a b : ℤ => a + b) hP hQ
  · intro P i hP
    simp only [map_mul, corridorNegateVariables_X, map_neg, MvPolynomial.eval_X, hP]

theorem corridorNegateVariables_monomial (e : Fin 2 →₀ ℕ) (a : ℤ) :
    corridorNegateVariables (MvPolynomial.monomial e a) =
      MvPolynomial.monomial e ((-1 : ℤ) ^ e.sum (fun _ n => n) * a) := by
  classical
  rw [corridorNegateVariables, MvPolynomial.eval₂Hom_monomial, Finsupp.prod]
  have hpow (i : Fin 2) :
      (-MvPolynomial.X i : MvPolynomial (Fin 2) ℤ) ^ e i =
        MvPolynomial.C ((-1 : ℤ) ^ e i) * MvPolynomial.X i ^ e i := by
    rw [neg_pow]
    simp only [map_pow, map_neg, map_one]
  simp_rw [hpow]
  rw [Finset.prod_mul_distrib]
  have hC : (∏ i ∈ e.support, MvPolynomial.C ((-1 : ℤ) ^ e i)) =
      (MvPolynomial.C ((-1 : ℤ) ^ e.sum (fun _ n => n)) : MvPolynomial (Fin 2) ℤ) := by
    rw [← map_prod, Finset.prod_pow_eq_pow_sum]
    rfl
  have hX : (∏ i ∈ e.support, (MvPolynomial.X i : MvPolynomial (Fin 2) ℤ) ^ e i) =
      MvPolynomial.monomial e 1 := by
    simpa only [Finsupp.prod] using (MvPolynomial.monic_monomial_eq (R := ℤ) e).symm
  rw [hC, hX, ← mul_assoc, ← map_mul, MvPolynomial.C_mul_monomial]
  simp only [mul_one, one_mul, mul_comm]

/-- Every coefficient changes only by its total-degree sign. -/
theorem corridorNegateVariables_coeff (H : MvPolynomial (Fin 2) ℤ) (e : Fin 2 →₀ ℕ) :
    MvPolynomial.coeff e (corridorNegateVariables H) =
      (-1 : ℤ) ^ e.sum (fun _ n => n) * MvPolynomial.coeff e H := by
  classical
  refine MvPolynomial.induction_on'
    (P := fun P => MvPolynomial.coeff e (corridorNegateVariables P) =
      (-1 : ℤ) ^ e.sum (fun _ n => n) * MvPolynomial.coeff e P) H ?_ ?_
  · intro u a
    rw [corridorNegateVariables_monomial]
    by_cases hue : u = e
    · subst u
      simp
    · simp [MvPolynomial.coeff_monomial, hue]
  · intro P Q hP hQ
    simp only [map_add, MvPolynomial.coeff_add, hP, hQ, mul_add]

theorem corridorNegateVariables_support (H : MvPolynomial (Fin 2) ℤ) :
    (corridorNegateVariables H).support = H.support := by
  ext e
  have hsign : (-1 : ℤ) ^ e.sum (fun _ n => n) ≠ 0 := pow_ne_zero _ (by decide)
  simp only [MvPolynomial.mem_support_iff, corridorNegateVariables_coeff, mul_ne_zero_iff]
  exact ⟨And.right, fun h => ⟨hsign, h⟩⟩

theorem corridorNegateVariables_ne_zero {H : MvPolynomial (Fin 2) ℤ} (hH : H ≠ 0) :
    corridorNegateVariables H ≠ 0 := by
  intro hz
  apply hH
  apply MvPolynomial.ext
  intro e
  have hsign : (-1 : ℤ) ^ e.sum (fun _ n => n) ≠ 0 := pow_ne_zero _ (by decide)
  have hcoeff := corridorNegateVariables_coeff H e
  rw [hz, MvPolynomial.coeff_zero] at hcoeff
  exact (mul_eq_zero.mp hcoeff.symm).resolve_left hsign

theorem corridorNegateVariables_totalDegree (H : MvPolynomial (Fin 2) ℤ) :
    (corridorNegateVariables H).totalDegree = H.totalDegree := by
  simp only [MvPolynomial.totalDegree, corridorNegateVariables_support]

theorem corridorNegateVariables_height (H : MvPolynomial (Fin 2) ℤ) :
    corridorPolynomialHeight (corridorNegateVariables H) = corridorPolynomialHeight H := by
  simp [corridorPolynomialHeight, corridorNegateVariables_support,
    corridorNegateVariables_coeff, Int.natAbs_mul, Int.natAbs_pow]

end

end Erdos1212Kernel
