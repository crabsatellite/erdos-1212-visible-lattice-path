import Erdos1212Kernel.IwaniecStrictPrimeSuffix

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

theorem iwaniecStrictList_head_ge_length
    (p : Nat) (tail : List Nat)
    (horder : (p :: tail).Pairwise (fun a b => b < a))
    (hmin : ∀ q ∈ p :: tail, 2 ≤ q) :
    tail.length + 2 ≤ p := by
  induction tail generalizing p with
  | nil => simpa using hmin p (by simp)
  | cons q rest ih =>
      have hpair := List.pairwise_cons.mp horder
      have hqLower := ih q hpair.2 (fun a ha => hmin a (by simp [ha]))
      have hqp : q < p := hpair.1 q (by simp)
      simp only [List.length_cons]
      omega

/-- Distinct decreasing integers at least 2 have product at least `(k+1)!`.
This is the finite arithmetic input in the large-rank branch of Theorem 5. -/
theorem iwaniecStrictList_factorial_le_prod
    (ordered : List Nat) (horder : ordered.Pairwise (fun a b => b < a))
    (hmin : ∀ p ∈ ordered, 2 ≤ p) :
    (ordered.length + 1).factorial ≤ ordered.prod := by
  induction ordered with
  | nil => simp
  | cons p tail ih =>
      have hpair := List.pairwise_cons.mp horder
      have htail := ih hpair.2 (fun q hq => hmin q (by simp [hq]))
      have hhead := iwaniecStrictList_head_ge_length p tail horder hmin
      simp only [List.length_cons, List.prod_cons, Nat.factorial_succ]
      exact Nat.mul_le_mul hhead htail

theorem iwaniecCubicRealProductCount_eq_zero_of_factorial
    (offset : Nat) (level : Real) (factors : List Nat) (k : Nat)
    (horder : factors.Pairwise (fun a b => b < a))
    (hmin : ∀ p ∈ factors, 2 ≤ p)
    (hfactorial : level ≤ ((k + 1).factorial : Real)) :
    iwaniecCubicRealProductCount offset level factors k = 0 := by
  classical
  unfold iwaniecCubicRealProductCount
  have hempty : ((factors.sublistsLen k).filter fun extension =>
      decide (iwaniecCubicRealAdmissible offset level extension ∧
        (extension.prod : Real) < level)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro extension hext htrue
    have hprodLt := (of_decide_eq_true htrue).2
    obtain ⟨hsub, hlength⟩ := List.mem_sublistsLen.mp hext
    have hprodLower := iwaniecStrictList_factorial_le_prod extension
      (horder.sublist hsub) (fun p hp => hmin p (hsub.subset hp))
    rw [hlength] at hprodLower
    have hprodReal : ((k + 1).factorial : Real) ≤ extension.prod := by
      exact_mod_cast hprodLower
    linarith
  rw [hempty]
  rfl

theorem iwaniecPaperSupportCount_saturated
    {small large : Nat} (hrank : small ≤ large)
    (hparity : Even large ↔ Even small) (level z : Real)
    (hfactorial : level ≤ ((small + 2).factorial : Real)) :
    iwaniecPaperSupportCount large level z =
      iwaniecPaperSupportCount small level z := by
  classical
  unfold iwaniecPaperSupportCount
  simp only [hparity]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k hkLarge hkSmall
  have hge : small + 1 ≤ k := by
    simp only [Finset.mem_range] at hkSmall
    omega
  have hfac : ((small + 2).factorial : Real) ≤ ((k + 1).factorial : Real) := by
    exact_mod_cast Nat.factorial_le (show small + 2 ≤ k + 1 by omega)
  apply iwaniecCubicRealProductCount_eq_zero_of_factorial
    _ _ _ k (iwaniecDescendingFactors_strict _) _ (hfactorial.trans hfac)
  intro p hp
  have hpool : p ∈ iwaniecStrictPrimePool z := by
    simpa [iwaniecDescendingFactors] using hp
  exact (mem_iwaniecStrictPrimePool.mp hpool).1.two_le

/-- Increasing the rank by two adds no tuples once the factorial threshold
has exceeded the level; the cutoff parameter remains unchanged. -/
theorem iwaniecPaperA_rank_add_two_saturated
    (rank : Nat) (level s : Real)
    (hfactorial : level ≤ ((rank + 2).factorial : Real)) :
    iwaniecPaperA (rank + 2) level s = iwaniecPaperA rank level s := by
  apply iwaniecPaperSupportCount_saturated (by omega) _ _ _ hfactorial
  simp only [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
  omega

end

end Erdos1212Kernel
