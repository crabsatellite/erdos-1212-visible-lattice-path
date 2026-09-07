import Erdos1212Kernel.IwaniecCubicRealThresholdLayer
import Erdos1212Kernel.IwaniecThresholdPartialMass

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

/-- Exact layer-by-layer transport from the original natural cubic
predicate to the paper's real quotient. No child level is rounded. -/
theorem iwaniecThresholdLayer_eq_realLevel (y : Nat) (selected factors : List Nat) (k : Nat)
    (hprod : 0 < selected.prod) (hpositive : ∀ p ∈ factors, 0 < p) :
    iwaniecThresholdLayer (iwaniecCubicEvenRestriction y) iwaniecReciprocalFactorWeight selected factors k =
      iwaniecCubicRealThresholdLayer selected.length ((y : Real) / selected.prod) factors k := by
  induction factors generalizing selected k with
  | nil => simp
  | cons p tail ih =>
      cases k with
      | zero => simp
      | succ k =>
          have hp : 0 < p := hpositive p (by simp)
          have ht : ∀ q ∈ tail, 0 < q := fun q hq => hpositive q (by simp [hq])
          have hchildProd : 0 < (selected ++ [p]).prod := by simpa using Nat.mul_pos hprod hp
          have hchoice : (Even selected.length ∨ iwaniecCubicEvenRestriction y selected p) ↔
              (Even selected.length ∨ (p : Real) ^ 3 < (y : Real) / selected.prod) := by
            rw [iwaniecCubicRestriction_iff_realLevel y p selected hprod]
          have hweight : |iwaniecReciprocalFactorWeight p| = (p : Real)⁻¹ := by
            unfold iwaniecReciprocalFactorWeight
            exact abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))
          rw [iwaniecThresholdLayer, iwaniecCubicRealThresholdLayer,
            ih selected (k + 1) hprod ht, hweight]
          by_cases hc : Even selected.length ∨ (p : Real) ^ 3 < (y : Real) / selected.prod
          · rw [if_pos (hchoice.mpr hc), if_pos hc, ih (selected ++ [p]) k hchildProd ht]
            have hscale := iwaniecCubicRealLevel_append_singleton (y : Real) selected p
            rw [List.length_append, List.length_singleton, ← hscale]
          · rw [if_neg (fun hh => hc (hchoice.mp hh)), if_neg hc]

theorem iwaniecThresholdLayer_root_eq_realLevel (y : Nat) (factors : List Nat) (k : Nat)
    (hpositive : ∀ p ∈ factors, 0 < p) :
    iwaniecThresholdLayer (iwaniecCubicEvenRestriction y) iwaniecReciprocalFactorWeight [] factors k =
      iwaniecCubicRealThresholdLayer 0 y factors k := by
  simpa using iwaniecThresholdLayer_eq_realLevel y [] factors k (by simp) hpositive

def iwaniecCubicRealThresholdPartial (offset : Nat) (level : Real) (factors : List Nat) (depth : Nat) : Real :=
  ∑ k ∈ Finset.range (depth + 1), iwaniecCubicRealThresholdLayer offset level factors k

theorem iwaniecThresholdPartialMass_eq_realLevel (y : Nat) (selected factors : List Nat) (depth : Nat)
    (hprod : 0 < selected.prod) (hpositive : ∀ p ∈ factors, 0 < p) :
    iwaniecThresholdPartialMass (iwaniecCubicEvenRestriction y) iwaniecReciprocalFactorWeight selected factors depth =
      iwaniecCubicRealThresholdPartial selected.length ((y : Real) / selected.prod) factors depth := by
  unfold iwaniecThresholdPartialMass iwaniecCubicRealThresholdPartial
  apply Finset.sum_congr rfl
  intro k hk
  exact iwaniecThresholdLayer_eq_realLevel y selected factors k hprod hpositive

theorem iwaniecThresholdPartialMass_root_eq_realLevel (y : Nat) (factors : List Nat) (depth : Nat)
    (hpositive : ∀ p ∈ factors, 0 < p) :
    iwaniecThresholdPartialMass (iwaniecCubicEvenRestriction y) iwaniecReciprocalFactorWeight [] factors depth =
      iwaniecCubicRealThresholdPartial 0 y factors depth := by
  simpa using iwaniecThresholdPartialMass_eq_realLevel y [] factors depth (by simp) hpositive

end

end Erdos1212Kernel
