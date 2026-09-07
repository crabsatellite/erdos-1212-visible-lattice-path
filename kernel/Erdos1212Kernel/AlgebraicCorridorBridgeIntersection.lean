import Erdos1212Kernel.AlgebraicCorridorCrossingRestriction
import Erdos1212Kernel.AlgebraicCorridorPathSeparation

namespace Erdos1212Kernel
noncomputable section

/-- The paper's common-subrectangle argument, on the original unit-edge walks. -/
theorem CorridorRectangle.bridge_crossing_intersects (Q T : CorridorRectangle)
    (hbottom : 0 < Q.bottom) (hheight : Q.bottom < Q.top)
    (hwidth : T.left < T.right)
    (hleft : Q.left ≤ T.left) (hright : T.right ≤ Q.right)
    (hlow : T.bottom ≤ Q.bottom) (hhigh : Q.top ≤ T.top)
    {a b c d : LatticePoint} (w : latticeGraph.Walk a b)
    (v : latticeGraph.Walk c d)
    (ha : a.x = Q.left) (hb : b.x = Q.right)
    (hc : c.y = T.bottom) (hd : d.y = T.top)
    (hw : ∀ p ∈ w.support, Q.Contains p)
    (hv : ∀ p ∈ v.support, T.Contains p) :
    ∃ p, p ∈ w.support ∧ p ∈ v.support := by
  obtain ⟨a', b', w', ha', hb', hw', hws⟩ :=
    corridor_nn_restrict_x w hwidth (by omega) (by omega)
  obtain ⟨c', d', v', hc', hd', hv', hvs⟩ :=
    corridor_nn_restrict_y v hheight (by omega) (by omega)
  let R : CorridorRectangle :=
    ⟨T.left, T.right, Q.bottom, Q.top, T.horizontal, Q.vertical⟩
  have hwR : ∀ p ∈ w'.support, R.Contains p := by
    intro p hp
    exact ⟨(hw' p hp).1, (hw' p hp).2,
      (hw p (hws hp)).2.2.1, (hw p (hws hp)).2.2.2⟩
  have hvR : ∀ p ∈ v'.support, R.Contains p := by
    intro p hp
    exact ⟨(hv p (hvs hp)).1, (hv p (hvs hp)).2.1,
      (hv' p hp).1, (hv' p hp).2⟩
  obtain ⟨p, hpw, hpv⟩ := R.horizontal_vertical_walks_intersect
    hbottom w' v' ha' hb' hc' hd' hwR hvR
  exact ⟨p, hws hpw, hvs hpv⟩

end
end Erdos1212Kernel
