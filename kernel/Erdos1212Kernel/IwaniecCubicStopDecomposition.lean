import Erdos1212Kernel.IwaniecWeightedStoppedMass
import Erdos1212Kernel.IwaniecCubicLowerMoebius

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1000000

/-- A stopped node of the literal cubic lower tree is exactly either the
`2r` terminal cut or an odd-depth prefix whose next even factor violates the
cubic product threshold. -/
theorem iwaniecCubic_not_select_iff
    (r y : Nat) (selected : List Nat) (factor : Nat) :
    ¬(selected.length + 1 < 2 * r ∧
        (Even selected.length ∨
          iwaniecCubicEvenRestriction y selected factor)) ↔
      2 * r ≤ selected.length + 1 ∨
        (Odd selected.length ∧
          y ≤ factor ^ 3 * selected.prod) := by
  constructor
  · intro hstop
    by_cases hdepth : selected.length + 1 < 2 * r
    · right
      have hnotChoice :
          ¬(Even selected.length ∨
            iwaniecCubicEvenRestriction y selected factor) := by
        intro hchoice
        exact hstop ⟨hdepth, hchoice⟩
      have hnotEven : ¬Even selected.length := fun heven =>
        hnotChoice (Or.inl heven)
      have hodd : Odd selected.length :=
        Nat.not_even_iff_odd.mp hnotEven
      have hnotRestriction :
          ¬iwaniecCubicEvenRestriction y selected factor := fun hrule =>
        hnotChoice (Or.inr hrule)
      have hproduct : y ≤ factor ^ 3 * selected.prod := by
        by_contra hnot
        apply hnotRestriction
        simp [iwaniecCubicEvenRestriction]
        omega
      exact ⟨hodd, hproduct⟩
    · left
      omega
  · intro hstop hselect
    rcases hstop with hdepth | ⟨hodd, hproduct⟩
    · omega
    · rcases hselect.2 with heven | hrule
      · exact (Nat.not_even_iff_odd.mpr hodd) heven
      · have hlt : factor ^ 3 * selected.prod < y := by
          simpa [iwaniecCubicEvenRestriction] using hrule
        omega

theorem iwaniecCubic_select_iff
    (r y : Nat) (selected : List Nat) (factor : Nat) :
    selected.length + 1 < 2 * r ∧
        (Even selected.length ∨
          iwaniecCubicEvenRestriction y selected factor) ↔
      selected.length + 1 < 2 * r ∧
        (Even selected.length ∨
          factor ^ 3 * selected.prod < y) := by
  simp [iwaniecCubicEvenRestriction]

end

end Erdos1212Kernel
