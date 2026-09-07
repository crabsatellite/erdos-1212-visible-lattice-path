import Erdos1212Kernel.AlgebraicCorridorDirectionAvoidance

namespace Erdos1212Kernel
noncomputable section

structure CorridorRectangle where
  left : ℕ
  right : ℕ
  bottom : ℕ
  top : ℕ
  horizontal : left ≤ right
  vertical : bottom ≤ top

def CorridorRectangle.Contains (R : CorridorRectangle) (p : LatticePoint) : Prop :=
  R.left ≤ p.x ∧ p.x ≤ R.right ∧ R.bottom ≤ p.y ∧ p.y ≤ R.top

def CorridorRectangle.LeftReachable (R : CorridorRectangle) (p : LatticePoint) : Prop :=
  ∃ a : LatticePoint, a.x = R.left ∧
    ∃ w : latticeGraph.Walk a p,
      ∀ v ∈ w.support, R.Contains v ∧ SafePoint v

theorem CorridorRectangle.leftReachable_mem {R : CorridorRectangle} {p : LatticePoint}
    (hp : R.LeftReachable p) : R.Contains p ∧ SafePoint p := by
  obtain ⟨a, ha, w, hw⟩ := hp
  exact hw p (by simpa using w.getVert_mem_support w.length)

theorem CorridorRectangle.leftReachable_of_left {R : CorridorRectangle} {p : LatticePoint}
    (hp : R.Contains p) (hs : SafePoint p) (hl : p.x = R.left) :
    R.LeftReachable p := by
  refine ⟨p, hl, .nil, ?_⟩
  intro v hv
  have heq : v = p := by simpa using hv
  subst v
  exact ⟨hp, hs⟩

theorem CorridorRectangle.leftReachable_step {R : CorridorRectangle} {p q : LatticePoint}
    (hp : R.LeftReachable p) (hpq : Adjacent p q)
    (hq : R.Contains q) (hs : SafePoint q) : R.LeftReachable q := by
  obtain ⟨a, ha, w, hw⟩ := hp
  refine ⟨a, ha, w.concat hpq, ?_⟩
  intro v hv
  rw [SimpleGraph.Walk.support_concat, List.mem_append] at hv
  rcases hv with hv | hv
  · exact hw v hv
  · have heq : v = q := by simpa using hv
    subst v
    exact ⟨hq, hs⟩

/-- Every in-rectangle site immediately outside the left reachable set is bad. -/
theorem CorridorRectangle.frontier_bad {R : CorridorRectangle} {p q : LatticePoint}
    (hp : R.LeftReachable p) (hpq : Adjacent p q)
    (hq : R.Contains q) (hnot : ¬R.LeftReachable q) : CorridorBad q := by
  intro hs
  exact hnot (R.leftReachable_step hp hpq hq hs)

def CorridorRectangle.SafeHorizontalCrossing (R : CorridorRectangle) : Prop :=
  ∃ a b : LatticePoint, a.x = R.left ∧ b.x = R.right ∧
    ∃ w : latticeGraph.Walk a b,
      ∀ v ∈ w.support, R.Contains v ∧ SafePoint v

theorem CorridorRectangle.safeHorizontalCrossing_iff (R : CorridorRectangle) :
    R.SafeHorizontalCrossing ↔ ∃ b : LatticePoint,
      b.x = R.right ∧ R.LeftReachable b := by
  constructor
  · rintro ⟨a, b, ha, hb, w, hw⟩
    exact ⟨b, hb, a, ha, w, hw⟩
  · rintro ⟨b, hb, a, ha, w, hw⟩
    exact ⟨a, b, ha, hb, w, hw⟩

theorem CorridorRectangle.leftReachable_finite (R : CorridorRectangle) :
    {p : LatticePoint | R.LeftReachable p}.Finite := by
  have hfinite : {p : LatticePoint | R.Contains p}.Finite := by
    let f : LatticePoint → ℕ × ℕ := fun p => (p.x, p.y)
    have hinj : Function.Injective f := by
      intro p q h
      exact LatticePoint.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
    apply Set.Finite.of_finite_image (f := f) ?_ hinj.injOn
    apply (Set.toFinite (Set.Icc R.left R.right ×ˢ Set.Icc R.bottom R.top)).subset
    rintro v ⟨p, hp, rfl⟩
    exact ⟨⟨hp.1, hp.2.1⟩, ⟨hp.2.2.1, hp.2.2.2⟩⟩
  exact hfinite.subset (fun p hp => (R.leftReachable_mem hp).1)

end
end Erdos1212Kernel
