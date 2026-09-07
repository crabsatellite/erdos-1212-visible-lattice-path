import Mathlib.Algebra.Polynomial.Roots
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Erdos1212Kernel.AlgebraicCorridorAngularScales

namespace Erdos1212Kernel.CorridorScale

noncomputable section

open Set MeasureTheory Polynomial Filter

def rootNeighborhood (roots : Finset Real) (δ : Real) : Set Real :=
  ⋃ β : roots, Ioo ((β : Real) - δ) ((β : Real) + δ)

theorem rootNeighborhood_measurable (roots : Finset Real) (δ : Real) :
    MeasurableSet (rootNeighborhood roots δ) := by
  unfold rootNeighborhood
  exact MeasurableSet.iUnion (fun β => measurableSet_Ioo)

theorem rootNeighborhood_measure_le (roots : Finset Real) {δ : Real} (hδ : 0 ≤ δ) :
    volume (rootNeighborhood roots δ) ≤
      ∑ β : roots, ENNReal.ofReal (2 * δ) := by
  unfold rootNeighborhood
  calc
    volume (⋃ β : roots, Ioo ((β : Real) - δ) ((β : Real) + δ)) ≤
        ∑ β : roots, volume (Ioo ((β : Real) - δ) ((β : Real) + δ)) :=
      measure_iUnion_fintype_le volume _
    _ = ∑ β : roots, ENNReal.ofReal (2 * δ) := by
      apply Finset.sum_congr rfl
      intro β _
      rw [Real.volume_Ioo]
      congr 1
      ring

theorem polynomial_rootNeighborhood_measure_le {p : Polynomial Real}
    (hp : p ≠ 0) {δ : Real} (hδ : 0 ≤ δ) :
    volume (rootNeighborhood p.roots.toFinset δ) ≤
      ∑ β : p.roots.toFinset, ENNReal.ofReal (2 * δ) :=
  rootNeighborhood_measure_le _ hδ

theorem polynomial_real_root_count_le (p : Polynomial Real) :
    p.roots.toFinset.card ≤ p.natDegree := by
  exact (Multiset.toFinset_card_le p.roots).trans (Polynomial.card_roots' p)

theorem polynomial_rootNeighborhood_measure_le_degree {p : Polynomial Real}
    (hp : p ≠ 0) {δ : Real} (hδ : 0 ≤ δ) :
    volume (rootNeighborhood p.roots.toFinset δ) ≤
      (p.natDegree : ℕ) • ENNReal.ofReal (2 * δ) := by
  have hsum := polynomial_rootNeighborhood_measure_le hp hδ
  calc
    volume (rootNeighborhood p.roots.toFinset δ) ≤
      ∑ β : p.roots.toFinset, ENNReal.ofReal (2 * δ) := hsum
    _ = p.roots.toFinset.card • ENNReal.ofReal (2 * δ) := by simp
    _ ≤ p.natDegree • ENNReal.ofReal (2 * δ) := by
      exact nsmul_le_nsmul_left (by positivity) (polynomial_real_root_count_le p)

/-- A finite family of nonzero polynomial root neighborhoods has the exact
union bound needed before the direction is fixed. -/
theorem finite_polynomial_rootNeighborhood_measure_le
    (family : Finset (Polynomial Real)) (hfamily : ∀ p ∈ family, p ≠ 0)
    {δ : Real} (hδ : 0 ≤ δ) :
    volume (⋃ p : family, rootNeighborhood p.val.roots.toFinset δ) ≤
      ∑ p : family, (p.val.natDegree : ℕ) • ENNReal.ofReal (2 * δ) := by
  calc
    volume (⋃ p : family, rootNeighborhood p.val.roots.toFinset δ) ≤
        ∑ p : family, volume (rootNeighborhood p.val.roots.toFinset δ) :=
      measure_iUnion_fintype_le volume _
    _ ≤ ∑ p : family, (p.val.natDegree : ℕ) • ENNReal.ofReal (2 * δ) := by
      apply Finset.sum_le_sum
      intro p _
      exact polynomial_rootNeighborhood_measure_le_degree (hfamily p.val p.property) hδ

/-- The paper's radius is `4 rho`, hence each real root contributes an interval
of length `8 rho`. -/
theorem finite_polynomial_rootNeighborhood_measure_le_four_rho
    (family : Finset (Polynomial Real)) (hfamily : ∀ p ∈ family, p ≠ 0)
    {N : Real} (hN : 0 < N) (hδ : 0 ≤ rho N) :
    volume (⋃ p : family, rootNeighborhood p.val.roots.toFinset (4 * rho N)) ≤
      ∑ p : family, (p.val.natDegree : ℕ) • ENNReal.ofReal (8 * rho N) := by
  simpa only [show 2 * (4 * rho N) = 8 * rho N by ring] using
    finite_polynomial_rootNeighborhood_measure_le family hfamily
      (δ := 4 * rho N) (by positivity)

/-- First Borel--Cantelli, in exactly the form used to choose one fixed
direction after the scale-dependent exceptional sets have been counted. -/
theorem ae_eventually_outside_exceptional_sets
    (sets : Nat → Set Real)
    (hsum : (∑' n, volume (sets n)) ≠ (⊤ : ENNReal)) :
    (∀ᵐ α ∂ volume, ∀ᶠ n : Nat in atTop, α ∉ sets n) :=
  MeasureTheory.ae_eventually_notMem hsum

end

end Erdos1212Kernel.CorridorScale
