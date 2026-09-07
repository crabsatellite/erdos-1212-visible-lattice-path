import Erdos1212Kernel.AlgebraicCorridorExceptionalSummable
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

def corridorBinaryExponent (m a : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 (m - a)

theorem corridorBinaryExponent_apply_zero (m a : ℕ) :
    corridorBinaryExponent m a 0 = a := by
  simp [corridorBinaryExponent]

theorem corridorBinaryExponent_apply_one (m a : ℕ) :
    corridorBinaryExponent m a 1 = m - a := by
  simp [corridorBinaryExponent]

theorem corridorBinaryExponent_degree {m a : ℕ} (ha : a ≤ m) :
    (corridorBinaryExponent m a).degree = m := by
  rw [Finsupp.degree_eq_sum]
  rw [Fin.sum_univ_two]
  simp [corridorBinaryExponent, ha]

def corridorTopPolynomial (F : MvPolynomial (Fin 2) ℤ) : Polynomial ℤ :=
  ∑ a ∈ Finset.range (F.totalDegree + 1),
    Polynomial.monomial a (MvPolynomial.coeff
      (corridorBinaryExponent F.totalDegree a) F)

theorem corridorTopPolynomial_coeff (F : MvPolynomial (Fin 2) ℤ) (a : ℕ) :
    (corridorTopPolynomial F).coeff a =
      if a ≤ F.totalDegree then
        MvPolynomial.coeff (corridorBinaryExponent F.totalDegree a) F
      else 0 := by
  classical
  unfold corridorTopPolynomial
  rw [Polynomial.finsetSum_coeff]
  by_cases ha : a ≤ F.totalDegree
  · rw [if_pos ha]
    have haMem : a ∈ Finset.range (F.totalDegree + 1) := by simp; omega
    rw [Finset.sum_eq_single a]
    · simp
    · intro b hb hba
      simp [Polynomial.coeff_monomial, hba]
    · intro hnot
      exact (hnot haMem).elim
  · rw [if_neg ha]
    apply Finset.sum_eq_zero
    intro b hb
    have hba : b ≠ a := by
      intro h
      subst b
      simp at hb
      omega
    simp [Polynomial.coeff_monomial, hba]

theorem corridorTopPolynomial_natDegree_le (F : MvPolynomial (Fin 2) ℤ) :
    (corridorTopPolynomial F).natDegree ≤ F.totalDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [corridorTopPolynomial_coeff, if_neg (by omega)]

theorem exists_topDegree_support
    (F : MvPolynomial (Fin 2) ℤ) (hF : F ≠ 0) :
    ∃ e ∈ F.support, e.degree = F.totalDegree := by
  have hsupp : F.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    apply hF
    exact MvPolynomial.support_eq_empty.mp hempty
  obtain ⟨e, he, hsup⟩ := Finset.exists_mem_eq_sup F.support hsupp
    (fun e => e.degree)
  refine ⟨e, he, ?_⟩
  unfold MvPolynomial.totalDegree
  convert hsup.symm using 1 <;> simp only [Finsupp.degree_eq_sum]

theorem corridorBinaryExponent_eq_of_degree
    {m : ℕ} {e : Fin 2 →₀ ℕ} (he : e.degree = m) :
    corridorBinaryExponent m (e 0) = e := by
  ext i
  fin_cases i
  · simp [corridorBinaryExponent]
  · have hsum : e 0 + e 1 = m := by
      rw [← he, Finsupp.degree_eq_sum, Fin.sum_univ_two]
    simp [corridorBinaryExponent]
    omega

theorem corridorTopPolynomial_ne_zero
    (F : MvPolynomial (Fin 2) ℤ) (hF : F ≠ 0) :
    corridorTopPolynomial F ≠ 0 := by
  obtain ⟨e, heSupport, heDegree⟩ := exists_topDegree_support F hF
  intro hzero
  have hcoeff := congrArg (fun p : Polynomial ℤ => p.coeff (e 0)) hzero
  change (corridorTopPolynomial F).coeff (e 0) = 0 at hcoeff
  have hea : e 0 ≤ F.totalDegree := by
    rw [← heDegree, Finsupp.degree_eq_sum, Fin.sum_univ_two]
    omega
  rw [corridorTopPolynomial_coeff, if_pos hea] at hcoeff
  rw [corridorBinaryExponent_eq_of_degree heDegree] at hcoeff
  exact (MvPolynomial.mem_support_iff.mp heSupport) hcoeff

theorem corridorTopPolynomial_coeff_abs_le_height
    (F : MvPolynomial (Fin 2) ℤ) (a : ℕ) :
    |(corridorTopPolynomial F).coeff a| ≤ (corridorPolynomialHeight F : ℤ) := by
  rw [corridorTopPolynomial_coeff]
  split_ifs
  · have h := corridor_coeff_abs_le_height F
      (corridorBinaryExponent F.totalDegree a)
    exact_mod_cast h
  · simp

theorem corridorTopPolynomial_mem_family
    {F : MvPolynomial (Fin 2) ℤ} {d H : ℕ}
    (hF : F ≠ 0) (hdegree : F.totalDegree ≤ d)
    (hheight : corridorPolynomialHeight F ≤ H) :
    Polynomial.map (Int.castRingHom ℝ) (corridorTopPolynomial F) ∈
      CorridorScale.nonzeroBoundedIntegerPolynomialFamily d H := by
  apply CorridorScale.nonzeroBoundedIntegerPolynomialFamily_mem_of_int
  · exact corridorTopPolynomial_ne_zero F hF
  · exact (corridorTopPolynomial_natDegree_le F).trans hdegree
  · intro i hi
    exact (corridorTopPolynomial_coeff_abs_le_height F i).trans
      (by exact_mod_cast hheight)

theorem corridorTopPolynomial_homogenize_eq
    (F : MvPolynomial (Fin 2) ℤ) :
    (corridorTopPolynomial F).homogenize F.totalDegree =
      MvPolynomial.homogeneousComponent F.totalDegree F := by
  ext e
  rw [Polynomial.coeff_homogenize,
    MvPolynomial.coeff_homogeneousComponent]
  by_cases he : e 0 + e 1 = F.totalDegree
  · rw [if_pos he]
    have heDegree : e.degree = F.totalDegree := by
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
      exact he
    rw [if_pos heDegree, corridorTopPolynomial_coeff,
      if_pos (by omega : e 0 ≤ F.totalDegree),
      corridorBinaryExponent_eq_of_degree heDegree]
  · rw [if_neg he]
    have heDegree : e.degree ≠ F.totalDegree := by
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
      exact he
    rw [if_neg heDegree]

def corridorLowerPolynomial (F : MvPolynomial (Fin 2) ℤ) :
    MvPolynomial (Fin 2) ℤ :=
  F - MvPolynomial.homogeneousComponent F.totalDegree F

theorem corridorLowerPolynomial_totalDegree_le_pred
    (F : MvPolynomial (Fin 2) ℤ) :
    (corridorLowerPolynomial F).totalDegree ≤ F.totalDegree - 1 := by
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro e he
  rw [MvPolynomial.mem_support_iff] at he
  unfold corridorLowerPolynomial at he
  rw [MvPolynomial.coeff_sub,
    MvPolynomial.coeff_homogeneousComponent] at he
  by_cases heDegree : e.degree = F.totalDegree
  · simp [heDegree] at he
  · have hcoeff : MvPolynomial.coeff e F ≠ 0 := by
      simpa [heDegree] using he
    have hdegree₀ := MvPolynomial.le_totalDegree
      (MvPolynomial.mem_support_iff.mpr hcoeff)
    have htd : F.totalDegree =
        F.support.sup (fun s => s.sum fun _ n => n) := rfl
    have hdegree : e.degree ≤
        F.support.sup (fun s => s.sum fun _ n => n) := by
      simpa only [htd] using hdegree₀
    have heDegree' : e.degree ≠
        F.support.sup (fun s => s.sum fun _ n => n) := by
      simpa only [htd] using heDegree
    change e.degree ≤ F.support.sup (fun s => s.sum fun _ n => n) - 1
    omega

theorem corridorLowerPolynomial_height_le
    (F : MvPolynomial (Fin 2) ℤ) :
    corridorPolynomialHeight (corridorLowerPolynomial F) ≤
      corridorPolynomialHeight F := by
  have hreal := corridorPolynomialHeight_le_of_coeff_bound
    (corridorLowerPolynomial F)
    (show (0 : ℝ) ≤ corridorPolynomialHeight F by positivity) (by
      intro e
      unfold corridorLowerPolynomial
      rw [MvPolynomial.coeff_sub,
        MvPolynomial.coeff_homogeneousComponent]
      by_cases heDegree : e.degree = F.totalDegree
      · simp [heDegree]
      · simp only [heDegree, if_false, sub_zero]
        exact corridor_coeff_abs_le_height F e)
  exact_mod_cast hreal

end

end Erdos1212Kernel
