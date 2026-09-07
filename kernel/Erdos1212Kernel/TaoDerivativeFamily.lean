import Erdos1212Kernel.TaoShiftDifferenceScale

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1500000

/-- The source derivative list: F 0 is the phase, each F (j+1) is
proved to differentiate F j on the original closed interval. No
exponential-sum estimate is part of these hypotheses. -/
def taoDerivativeHypotheses (F : Nat → Real → Real) (k : Nat) (L U A N T : Real) : Prop :=
  (∀ j ≤ k, ∀ x ∈ Set.Icc L U, HasDerivAt (F j) (F (j + 1) x) x) ∧
  ContinuousOn (F (k + 1)) (Set.Icc L U) ∧
  ∀ j ∈ Finset.Icc 1 (k + 1), ∀ x ∈ Set.Icc L U,
    T / (A * N ^ j) ≤ |F j x| ∧ |F j x| ≤ A * T / N ^ j

theorem taoDerivativeHypotheses_continuous {F : Nat → Real → Real} {k j : Nat} {L U A N T : Real}
    (hF : taoDerivativeHypotheses F k L U A N T) (hj : j ≤ k + 1) :
    ContinuousOn (F j) (Set.Icc L U) := by
  by_cases htop : j = k + 1
  · simpa only [htop] using hF.2.1
  · exact fun x hx => (hF.1 j (by omega) x hx).continuousAt.continuousWithinAt

theorem taoDerivativeHypotheses_restrict {F : Nat → Real → Real} {k : Nat} {L U L' U' A N T : Real}
    (hF : taoDerivativeHypotheses F k L U A N T) (hsub : Set.Icc L' U' ⊆ Set.Icc L U) :
    taoDerivativeHypotheses F k L' U' A N T := by
  exact ⟨fun j hj x hx => hF.1 j hj x (hsub hx), hF.2.1.mono hsub,
    fun j hj x hx => hF.2.2 j hj x (hsub hx)⟩

/-- Every derivative in the shifted list is the literal difference of
the original derivative. The parameter changes to h*T/N by the proved
FTC transport, and the domain becomes exactly [L,U-h]. -/
theorem taoDerivativeHypotheses_difference {F : Nat → Real → Real} {k : Nat} {L U h A N T : Real}
    (hF : taoDerivativeHypotheses F (k + 1) L U A N T)
    (hA : 0 < A) (hN : 0 < N) (hT : 0 < T) (hh : 0 ≤ h) :
    taoDerivativeHypotheses (fun j => taoShiftDifference (F j) h) k L (U - h) A N (h * T / N) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj x hx
    exact taoShiftDifference_hasDerivAt (F j) (F (j + 1)) hh
      (hF.1 j (by omega)) hx
  · intro x hx
    exact (taoShiftDifference_hasDerivAt (F (k + 1)) (F ((k + 1) + 1)) hh
      (hF.1 (k + 1) le_rfl) hx).continuousAt.continuousWithinAt
  · intro j hj x hx
    have hj' := Finset.mem_Icc.mp hj
    have hjnext : j + 1 ∈ Finset.Icc 1 ((k + 1) + 1) := Finset.mem_Icc.mpr (by omega)
    exact taoShiftDifference_scaled_bounds (F j) (F (j + 1)) j hA hN hT hh
      (hF.1 j hj'.2) (taoDerivativeHypotheses_continuous hF (by omega))
      (fun t ht => (hF.2.2 (j + 1) hjnext t ht).1)
      (fun t ht => (hF.2.2 (j + 1) hjnext t ht).2) hx

end

end Erdos1212Kernel
