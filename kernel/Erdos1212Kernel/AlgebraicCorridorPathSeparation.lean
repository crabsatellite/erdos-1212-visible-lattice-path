import Erdos1212Kernel.AlgebraicCorridorCrossingFlux

namespace Erdos1212Kernel

def corridorSeparationIndex {a b : LatticePoint} (w : latticeGraph.Walk a b)
    (p : LatticePoint) : ℤ := corridorWalkFlux p w + (if p.y < b.y then 1 else 0)

theorem corridorSeparationIndex_step {a b p q : LatticePoint}
    (w : latticeGraph.Walk a b) (hadj : Adjacent p q)
    (hp : p ∉ w.support) (hq : q ∉ w.support)
    (hleft : a.x ≤ p.x) (hright : p.x < b.x) :
    corridorSeparationIndex w p = corridorSeparationIndex w q := by
  have h := corridorWalkFlux_move hadj w hp hq
  have hl : ¬p.x < a.x := by omega
  simp only [corridorVertexFlux, if_neg hl, if_pos hright, mul_zero, mul_one] at h
  unfold corridorSeparationIndex
  omega

theorem corridorSeparationIndex_along_walk {a b c d : LatticePoint}
    (w : latticeGraph.Walk a b) (v : latticeGraph.Walk c d)
    (hdisjoint : ∀ p ∈ v.support, p ∉ w.support)
    (hx : ∀ p ∈ v.support, a.x ≤ p.x ∧ p.x < b.x) :
    corridorSeparationIndex w c = corridorSeparationIndex w d := by
  induction v with
  | nil => rfl
  | @cons c e d h v ih =>
    have hstart := hx c (by simp)
    have hstep := corridorSeparationIndex_step w h
      (hdisjoint c (by simp))
      (hdisjoint e (by simp [v.start_mem_support])) hstart.1 hstart.2
    exact hstep.trans (ih (fun p hp => hdisjoint p (by simp [hp]))
      (fun p hp => hx p (by simp [hp])))

theorem corridorWalkFlux_zero_below {a b : LatticePoint} (w : latticeGraph.Walk a b)
    (p : LatticePoint) (hy : ∀ v ∈ w.support, p.y < v.y) : corridorWalkFlux p w = 0 := by
  induction w with
  | nil => rfl
  | @cons a c b h w ih =>
    have ha := hy a (by simp)
    have hc := hy c (by simp [w.start_mem_support])
    simp only [corridorWalkFlux, corridorEdgeFlux, if_pos ha, if_pos hc,
      sub_self, zero_mul, zero_add]
    exact ih (fun v hv => hy v (by simp [hv]))

theorem corridorWalkFlux_zero_above {a b : LatticePoint} (w : latticeGraph.Walk a b)
    (p : LatticePoint) (hy : ∀ v ∈ w.support, v.y ≤ p.y) : corridorWalkFlux p w = 0 := by
  induction w with
  | nil => rfl
  | @cons a c b h w ih =>
    have ha : ¬p.y < a.y := not_lt.mpr (hy a (by simp))
    have hc : ¬p.y < c.y := not_lt.mpr (hy c (by simp [w.start_mem_support]))
    simp only [corridorWalkFlux, corridorEdgeFlux, if_neg ha, if_neg hc,
      sub_self, zero_mul, zero_add]
    exact ih (fun v hv => hy v (by simp [hv]))

/-- The paper's separation argument with the endpoints extended outside the
rectangle: opposite indices force a shared lattice vertex. -/
theorem corridor_extended_paths_intersect {a b c d : LatticePoint}
    (w : latticeGraph.Walk a b) (v : latticeGraph.Walk c d)
    (hx : ∀ p ∈ v.support, a.x ≤ p.x ∧ p.x < b.x)
    (hbottom : ∀ p ∈ w.support, c.y < p.y)
    (htop : ∀ p ∈ w.support, p.y ≤ d.y) :
    ∃ p, p ∈ w.support ∧ p ∈ v.support := by
  by_contra hnot
  have hdisjoint : ∀ p ∈ v.support, p ∉ w.support := by
    intro p hp hw
    exact hnot ⟨p, hw, hp⟩
  have h := corridorSeparationIndex_along_walk w v hdisjoint hx
  have hc := hbottom b w.end_mem_support
  have hd : ¬d.y < b.y := not_lt.mpr (htop b w.end_mem_support)
  rw [corridorSeparationIndex, corridorSeparationIndex,
    corridorWalkFlux_zero_below w c hbottom,
    corridorWalkFlux_zero_above w d htop, if_pos hc, if_neg hd] at h
  norm_num at h

theorem CorridorRectangle.horizontal_vertical_walks_intersect
    (R : CorridorRectangle) (hb : 0 < R.bottom)
    {a b c d : LatticePoint} (w : latticeGraph.Walk a b) (v : latticeGraph.Walk c d)
    (ha : a.x = R.left) (hbe : b.x = R.right)
    (hc : c.y = R.bottom) (hd : d.y = R.top)
    (hw : ∀ p ∈ w.support, R.Contains p)
    (hv : ∀ p ∈ v.support, R.Contains p) :
    ∃ p, p ∈ w.support ∧ p ∈ v.support := by
  let b' : LatticePoint := ⟨b.x + 1, b.y⟩
  let c' : LatticePoint := ⟨c.x, c.y - 1⟩
  have hbb : Adjacent b b' := Or.inl ⟨rfl, rfl⟩
  have hcc : Adjacent c' c := by
    apply Or.inr ∘ Or.inr ∘ Or.inl
    exact ⟨by dsimp [c']; omega, rfl⟩
  let w' := w.concat hbb
  let v' := SimpleGraph.Walk.cons hcc v
  have hwMem : ∀ p ∈ w'.support, p ∈ w.support ∨ p = b' := by
    intro p hp
    simpa [w', SimpleGraph.Walk.support_concat] using hp
  have hvMem : ∀ p ∈ v'.support, p = c' ∨ p ∈ v.support := by
    intro p hp
    simpa [v'] using hp
  have hcx := hv c v.start_mem_support
  have hby := hw b w.end_mem_support
  have hx : ∀ p ∈ v'.support, a.x ≤ p.x ∧ p.x < b'.x := by
    intro p hp
    rcases hvMem p hp with rfl | hp
    · dsimp [c', b']
      rw [ha, hbe]
      exact ⟨hcx.1, by have h := hcx.2.1; omega⟩
    · have h := hv p hp
      dsimp [b']
      rw [ha, hbe]
      exact ⟨h.1, by have hh := h.2.1; omega⟩
  have hlo : ∀ p ∈ w'.support, c'.y < p.y := by
    intro p hp
    rcases hwMem p hp with hp | rfl
    · have h := (hw p hp).2.2.1
      dsimp [c']
      omega
    · dsimp [c', b']
      have h := hby.2.2.1
      omega
  have hhi : ∀ p ∈ w'.support, p.y ≤ d.y := by
    intro p hp
    rw [hd]
    rcases hwMem p hp with hp | rfl
    · exact (hw p hp).2.2.2
    · exact hby.2.2.2
  obtain ⟨p, hpw, hpv⟩ := corridor_extended_paths_intersect w' v' hx hlo hhi
  have hpne : p ≠ c' := by
    intro h
    have hh := hlo p hpw
    rw [h] at hh
    omega
  have hpvOrig : p ∈ v.support := (hvMem p hpv).resolve_left hpne
  have hpneB : p ≠ b' := by
    intro h
    have hh := (hv p hpvOrig).2.1
    rw [h] at hh
    dsimp [b'] at hh
    omega
  exact ⟨p, (hwMem p hpw).resolve_right hpneB, hpvOrig⟩

end Erdos1212Kernel
