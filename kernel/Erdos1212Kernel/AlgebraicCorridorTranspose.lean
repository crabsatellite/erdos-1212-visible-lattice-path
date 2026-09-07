import Erdos1212Kernel.AlgebraicCorridorBandRestriction

namespace Erdos1212Kernel
noncomputable section

def corridorTranspose (p : LatticePoint) : LatticePoint := ⟨p.y, p.x⟩

@[simp] theorem corridorTranspose_twice (p : LatticePoint) :
    corridorTranspose (corridorTranspose p) = p := by cases p; rfl

theorem corridorTranspose_safe (p : LatticePoint) :
    SafePoint (corridorTranspose p) ↔ SafePoint p := by
  simp only [SafePoint, Visible, corridorTranspose, Nat.gcd_comm]
  tauto

theorem corridorTranspose_adjacent (p q : LatticePoint) :
    Adjacent (corridorTranspose p) (corridorTranspose q) ↔ Adjacent p q := by
  simp only [Adjacent, corridorTranspose]
  tauto

theorem corridorTranspose_starAdjacent (p q : LatticePoint) :
    StarAdjacent (corridorTranspose p) (corridorTranspose q) ↔ StarAdjacent p q := by
  simp [StarAdjacent, corridorTranspose, LatticePoint.ext_iff]
  tauto

def CorridorRectangle.transpose (R : CorridorRectangle) : CorridorRectangle :=
  ⟨R.bottom, R.top, R.left, R.right, R.vertical, R.horizontal⟩

@[simp] theorem CorridorRectangle.transpose_contains (R : CorridorRectangle) (p : LatticePoint) :
    R.transpose.Contains (corridorTranspose p) ↔ R.Contains p := by
  simp only [Contains, transpose, corridorTranspose]
  tauto

def corridorTransposeGraphHom : latticeGraph →g latticeGraph where
  toFun := corridorTranspose
  map_rel' := fun {p q} h => (corridorTranspose_adjacent p q).mpr h

def corridorTransposeStarGraphHom : starLatticeGraph →g starLatticeGraph where
  toFun := corridorTranspose
  map_rel' := fun {p q} h => (corridorTranspose_starAdjacent p q).mpr h

def CorridorRectangle.SafeVerticalCrossing (R : CorridorRectangle) : Prop :=
  ∃ a b : LatticePoint, a.y = R.bottom ∧ b.y = R.top ∧
    ∃ w : latticeGraph.Walk a b,
      ∀ v ∈ w.support, R.Contains v ∧ SafePoint v

set_option backward.isDefEq.respectTransparency false in
theorem CorridorRectangle.safeVertical_of_transpose_horizontal (R : CorridorRectangle)
    (h : R.transpose.SafeHorizontalCrossing) : R.SafeVerticalCrossing := by
  obtain ⟨a, b, ha, hb, w, hw⟩ := h
  refine ⟨corridorTranspose a, corridorTranspose b, ha, hb,
    w.map corridorTransposeGraphHom, ?_⟩
  intro v hv
  have hsupport : (w.map corridorTransposeGraphHom).support =
      w.support.map corridorTranspose := SimpleGraph.Walk.support_map _ _
  rw [hsupport, List.mem_map] at hv
  obtain ⟨p, hp, rfl⟩ := hv
  have hs := hw p hp
  constructor
  · have h := (R.transpose_contains (corridorTranspose p)).mp
      (by simpa using hs.1)
    exact h
  · exact (corridorTranspose_safe p).mpr hs.2

set_option backward.isDefEq.respectTransparency false in
theorem CorridorRectangle.bad_horizontal_crossing_of_no_safe_vertical
    (R : CorridorRectangle) (hb : 2 < R.bottom) (hl : 1 < R.left)
    (hwidth : R.left < R.right) (hno : ¬R.SafeVerticalCrossing) :
    ∃ a b : LatticePoint, a.x = R.left ∧ b.x = R.right ∧
      ∃ w : starLatticeGraph.Walk a b,
        ∀ p ∈ w.support, R.Contains p ∧ CorridorBad p := by
  have hn : ¬R.transpose.SafeHorizontalCrossing :=
    fun h => hno (R.safeVertical_of_transpose_horizontal h)
  obtain ⟨a, b, ha, hbe, w, hw⟩ :=
    R.transpose.bad_vertical_crossing_of_no_safe_horizontal hb hl hwidth hn
  refine ⟨corridorTranspose a, corridorTranspose b, ha, hbe,
    w.map corridorTransposeStarGraphHom, ?_⟩
  intro v hv
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hv
  obtain ⟨p, hp, rfl⟩ := hv
  have hs := hw p hp
  constructor
  · exact (R.transpose_contains (corridorTranspose p)).mp (by simpa using hs.1)
  · intro hsafe
    exact hs.2 ((corridorTranspose_safe p).mp hsafe)

end
end Erdos1212Kernel
