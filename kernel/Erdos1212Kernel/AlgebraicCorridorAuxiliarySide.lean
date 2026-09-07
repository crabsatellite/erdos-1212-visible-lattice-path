import Erdos1212Kernel.AlgebraicCorridorRectangleBoundary

namespace Erdos1212Kernel
noncomputable section

/-- The exterior left side attached in the paper's boundary-tracing argument. -/
def CorridorRectangle.AuxiliaryLeft (R : CorridorRectangle) (p : LatticePoint) : Prop :=
  p.x + 1 = R.left ∧ R.bottom ≤ p.y ∧ p.y ≤ R.top

def CorridorRectangle.AugmentedLeft (R : CorridorRectangle) (p : LatticePoint) : Prop :=
  R.AuxiliaryLeft p ∨ R.LeftReachable p

theorem CorridorRectangle.auxiliaryLeft_outside {R : CorridorRectangle} {p : LatticePoint}
    (hp : R.AuxiliaryLeft p) : ¬R.Contains p := by
  intro h
  have hx := hp.1
  have hl := h.1
  omega

theorem CorridorRectangle.augmentedLeft_inside_iff {R : CorridorRectangle} {p : LatticePoint}
    (hp : R.Contains p) : R.AugmentedLeft p ↔ R.LeftReachable p := by
  constructor
  · rintro (ha | hr)
    · exact False.elim (R.auxiliaryLeft_outside ha hp)
    · exact hr
  · exact Or.inr

theorem CorridorRectangle.auxiliary_adjacent_inside_left
    {R : CorridorRectangle} {p q : LatticePoint}
    (hp : R.AuxiliaryLeft p) (hq : R.Contains q) (hadj : Adjacent p q) :
    q.x = R.left := by
  have hx := hp.1
  have hqx := hq.1
  rcases hadj with h | h | h | h <;> omega

/-- An exterior neighbour within the original rectangle is bad even when its
inside neighbour lies on the auxiliary side. -/
theorem CorridorRectangle.augmented_frontier_bad
    {R : CorridorRectangle} {p q : LatticePoint}
    (hp : R.AugmentedLeft p) (hq : R.Contains q)
    (hadj : Adjacent p q) (hnot : ¬R.AugmentedLeft q) : CorridorBad q := by
  intro hs
  apply hnot
  right
  rcases hp with hp | hp
  · exact R.leftReachable_of_left hq hs
      (R.auxiliary_adjacent_inside_left hp hq hadj)
  · exact R.leftReachable_step hp hadj hq hs

theorem CorridorRectangle.augmentedLeft_finite (R : CorridorRectangle) :
    {p : LatticePoint | R.AugmentedLeft p}.Finite := by
  have haux : {p : LatticePoint | R.AuxiliaryLeft p}.Finite := by
    have hs := (Set.toFinite (Set.Icc R.bottom R.top)).image
      (fun y => (⟨R.left - 1, y⟩ : LatticePoint))
    apply hs.subset
    intro p hp
    refine ⟨p.y, ⟨hp.2.1, hp.2.2⟩, ?_⟩
    apply LatticePoint.ext
    · have hx := hp.1
      dsimp
      omega
    · rfl
  exact haux.union R.leftReachable_finite

theorem CorridorRectangle.augmentedLeft_nonempty (R : CorridorRectangle)
    (hl : 0 < R.left) : {p : LatticePoint | R.AugmentedLeft p}.Nonempty := by
  refine ⟨⟨R.left - 1, R.bottom⟩, Or.inl ?_⟩
  exact ⟨by dsimp; omega, le_rfl, R.vertical⟩

theorem CorridorRectangle.augmentedLeft_misses_right
    {R : CorridorRectangle} (hno : ¬R.SafeHorizontalCrossing)
    {p : LatticePoint} (hp : R.AugmentedLeft p) : p.x ≠ R.right := by
  intro hx
  rcases hp with ha | hr
  · have hleft := ha.1
    have hwidth := R.horizontal
    omega
  · exact hno ((R.safeHorizontalCrossing_iff).mpr ⟨p, hx, hr⟩)

theorem CorridorRectangle.auxiliary_vertical_walk (R : CorridorRectangle)
    (hl : 0 < R.left) (k : ℕ) (hk : R.bottom + k ≤ R.top) :
    ∃ w : latticeGraph.Walk
      ⟨R.left - 1, R.bottom⟩ ⟨R.left - 1, R.bottom + k⟩,
      ∀ p ∈ w.support, R.AuxiliaryLeft p := by
  induction k with
  | zero =>
    refine ⟨.nil, ?_⟩
    intro p hp
    have heq : p = ⟨R.left - 1, R.bottom⟩ := by simpa using hp
    subst p
    exact ⟨by dsimp; omega, le_rfl, R.vertical⟩
  | succ k ih =>
    obtain ⟨w, hw⟩ := ih (by omega)
    have hadj : Adjacent
        ⟨R.left - 1, R.bottom + k⟩ ⟨R.left - 1, R.bottom + (k + 1)⟩ := by
      exact Or.inr (Or.inr (Or.inl ⟨by dsimp; omega, rfl⟩))
    refine ⟨w.concat hadj, ?_⟩
    intro p hp
    rw [SimpleGraph.Walk.support_concat, List.mem_append] at hp
    rcases hp with hp | hp
    · exact hw p hp
    · have heq : p = ⟨R.left - 1, R.bottom + (k + 1)⟩ := by simpa using hp
      subst p
      exact ⟨by dsimp; omega, by dsimp; omega, hk⟩

theorem CorridorRectangle.augmented_root_walk (R : CorridorRectangle)
    (hl : 0 < R.left) {p : LatticePoint} (hp : R.AugmentedLeft p) :
    ∃ w : latticeGraph.Walk ⟨R.left - 1, R.bottom⟩ p,
      ∀ v ∈ w.support, R.AugmentedLeft v := by
  classical
  have hauxWalk : ∀ a : LatticePoint, R.AuxiliaryLeft a →
      ∃ w : latticeGraph.Walk ⟨R.left - 1, R.bottom⟩ a,
        ∀ v ∈ w.support, R.AugmentedLeft v := by
    intro a ha
    obtain ⟨w, hw⟩ := R.auxiliary_vertical_walk hl (a.y - R.bottom) (by
      have hb := ha.2.1
      have ht := ha.2.2
      omega)
    have heq : (⟨R.left - 1, R.bottom + (a.y - R.bottom)⟩ : LatticePoint) = a := by
      apply LatticePoint.ext <;> dsimp
      · have hx := ha.1
        omega
      · have hy := ha.2.1
        omega
    refine ⟨w.copy rfl heq, ?_⟩
    intro v hv
    exact Or.inl (hw v (by simpa using hv))
  rcases hp with hp | ⟨a, ha, w, hw⟩
  · exact hauxWalk p hp
  · have haMem := (hw a w.start_mem_support).1
    let b : LatticePoint := ⟨R.left - 1, a.y⟩
    have hb : R.AuxiliaryLeft b :=
      ⟨by dsimp [b]; omega, haMem.2.2.1, haMem.2.2.2⟩
    obtain ⟨u, hu⟩ := hauxWalk b hb
    have hba : Adjacent b a := by
      left
      constructor
      · dsimp [b]
        omega
      · rfl
    refine ⟨(u.concat hba).append w, ?_⟩
    intro v hv
    rw [SimpleGraph.Walk.mem_support_append_iff] at hv
    rcases hv with hv | hv
    · rw [SimpleGraph.Walk.support_concat, List.mem_append] at hv
      rcases hv with hv | hv
      · exact hu v hv
      · have heq : v = a := by simpa using hv
        subst v
        exact Or.inr (R.leftReachable_of_left haMem (hw a w.start_mem_support).2 ha)
    · right
      refine ⟨a, ha, w.takeUntil v hv, ?_⟩
      intro z hz
      exact hw z ((w.isSubwalk_takeUntil hv).support_subset hz)

end
end Erdos1212Kernel
