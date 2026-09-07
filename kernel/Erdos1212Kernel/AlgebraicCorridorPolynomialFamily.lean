import Erdos1212Kernel.AlgebraicCorridorExceptionalSet
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Data.Int.Interval

namespace Erdos1212Kernel.CorridorScale

noncomputable section

open Set MeasureTheory Polynomial

/-! A finite, literal coefficient enumeration for the one-variable
polynomials used in the paper's exceptional-direction argument.  The
coefficients are bounded integers, and `ofFn` keeps the degree truncation
explicit; no countable or analytic surrogate is introduced. -/

abbrev BoundedIntegerCoefficient (H : ℕ) :=
  {a : ℤ // a ∈ Finset.Icc (-H : ℤ) H}

abbrev BoundedIntegerCoefficientVector (d H : ℕ) :=
  Fin (d + 1) → BoundedIntegerCoefficient H

noncomputable def boundedIntegerPolynomial
    (d H : ℕ) (v : BoundedIntegerCoefficientVector d H) : Polynomial ℝ :=
  Polynomial.ofFn (d + 1) (fun i => ((v i).1 : ℝ))

noncomputable def boundedIntegerPolynomialFamily
    (d H : ℕ) : Finset (Polynomial ℝ) :=
  (Finset.univ : Finset (BoundedIntegerCoefficientVector d H)).image
    (boundedIntegerPolynomial d H)

noncomputable def nonzeroBoundedIntegerPolynomialFamily
    (d H : ℕ) : Finset (Polynomial ℝ) :=
  (boundedIntegerPolynomialFamily d H).filter (fun p => p ≠ 0)

theorem boundedIntegerCoefficient_card (H : ℕ) :
    Fintype.card (BoundedIntegerCoefficient H) = 2 * H + 1 := by
  rw [Fintype.card_coe, Int.card_Icc]
  have heq : (H : ℤ) + 1 - -(H : ℤ) = ((2 * H + 1 : ℕ) : ℤ) := by
    norm_num
    omega
  rw [heq]
  rw [Int.toNat_natCast]

theorem boundedIntegerCoefficientVector_card (d H : ℕ) :
    Fintype.card (BoundedIntegerCoefficientVector d H) =
      (2 * H + 1) ^ (d + 1) := by
  rw [Fintype.card_fun, Fintype.card_fin, boundedIntegerCoefficient_card]

theorem boundedIntegerPolynomialFamily_card_le (d H : ℕ) :
    (boundedIntegerPolynomialFamily d H).card ≤ (2 * H + 1) ^ (d + 1) := by
  calc
    (boundedIntegerPolynomialFamily d H).card ≤
        (Finset.univ : Finset (BoundedIntegerCoefficientVector d H)).card :=
      Finset.card_image_le
    _ = Fintype.card (BoundedIntegerCoefficientVector d H) := by simp
    _ = (2 * H + 1) ^ (d + 1) := boundedIntegerCoefficientVector_card d H

theorem nonzeroBoundedIntegerPolynomialFamily_card_le (d H : ℕ) :
    (nonzeroBoundedIntegerPolynomialFamily d H).card ≤ (2 * H + 1) ^ (d + 1) := by
  exact (Finset.card_filter_le _ _).trans (boundedIntegerPolynomialFamily_card_le d H)

theorem boundedIntegerPolynomial_natDegree_le
    {d H : ℕ} {p : Polynomial ℝ}
    (hp : p ∈ boundedIntegerPolynomialFamily d H) :
    p.natDegree ≤ d := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
  have hlt : (boundedIntegerPolynomial d H v).natDegree < d + 1 := by
    exact Polynomial.ofFn_natDegree_lt (n := d + 1) (by omega)
      (fun i => ((v i).1 : ℝ))
  exact Nat.le_of_lt_succ (by simpa [Nat.succ_eq_add_one] using hlt)

theorem nonzeroBoundedIntegerPolynomial_natDegree_le
    {d H : ℕ} {p : Polynomial ℝ}
    (hp : p ∈ nonzeroBoundedIntegerPolynomialFamily d H) :
    p.natDegree ≤ d := by
  exact boundedIntegerPolynomial_natDegree_le
    (Finset.mem_filter.mp hp).1

theorem boundedIntegerPolynomialFamily_mem_of_int
    {d H : ℕ} {p : Polynomial ℤ}
    (hdeg : p.natDegree ≤ d)
    (hcoeff : ∀ i, i ≤ d → |p.coeff i| ≤ (H : ℤ)) :
    Polynomial.map (Int.castRingHom ℝ) p ∈ boundedIntegerPolynomialFamily d H := by
  let v : BoundedIntegerCoefficientVector d H := fun i =>
    ⟨p.coeff i.1, by
      rw [Finset.mem_Icc]
      have hi : i.1 ≤ d := by omega
      have habs := hcoeff i.1 hi
      exact (abs_le.mp habs)⟩
  have hv : v ∈ (Finset.univ : Finset (BoundedIntegerCoefficientVector d H)) :=
    Finset.mem_univ v
  apply Finset.mem_image.mpr
  refine ⟨v, hv, ?_⟩
  apply Polynomial.ext
  intro n
  by_cases hn : n < d + 1
  · simp [boundedIntegerPolynomial, Polynomial.coeff_map, hn, v]
  · have hpn : p.coeff n = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      omega
    simp [boundedIntegerPolynomial, Polynomial.coeff_map,
      Nat.le_of_not_gt hn, hpn]

theorem nonzeroBoundedIntegerPolynomialFamily_mem_of_int
    {d H : ℕ} {p : Polynomial ℤ}
    (hp : p ≠ 0) (hdeg : p.natDegree ≤ d)
    (hcoeff : ∀ i, i ≤ d → |p.coeff i| ≤ (H : ℤ)) :
    Polynomial.map (Int.castRingHom ℝ) p ∈
      nonzeroBoundedIntegerPolynomialFamily d H := by
  apply Finset.mem_filter.mpr
  refine ⟨boundedIntegerPolynomialFamily_mem_of_int hdeg hcoeff, ?_⟩
  intro hmap
  apply hp
  apply Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective
  simpa using hmap

theorem finite_nonzeroBoundedIntegerPolynomialFamily_rootNeighborhood_measure_le
    (d H : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    volume (⋃ p : nonzeroBoundedIntegerPolynomialFamily d H,
      rootNeighborhood p.val.roots.toFinset δ) ≤
      ∑ p : nonzeroBoundedIntegerPolynomialFamily d H,
        (p.val.natDegree : ℕ) • ENNReal.ofReal (2 * δ) := by
  apply finite_polynomial_rootNeighborhood_measure_le
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · exact hδ

end

end Erdos1212Kernel.CorridorScale
