import Erdos1212Kernel.AlgebraicCorridorBridgeWalk

namespace Erdos1212Kernel

/-- Signed crossing of the horizontal half-line above the query lattice site. -/
def corridorEdgeFlux (p a b : LatticePoint) : ℤ :=
  ((if p.y < a.y then 1 else 0) - (if p.y < b.y then 1 else 0)) *
    (if p.x < a.x then 1 else 0)

def corridorVertexFlux (p q a : LatticePoint) : ℤ :=
  ((if p.y < a.y then 1 else 0) - (if q.y < a.y then 1 else 0)) *
    (if p.x < a.x then 1 else 0)

theorem corridorEdgeFlux_move
    {p q a b : LatticePoint} (hpq : Adjacent p q) (hab : Adjacent a b)
    (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) :
    corridorEdgeFlux p a b - corridorEdgeFlux q a b =
      corridorVertexFlux p q a - corridorVertexFlux p q b := by
  have hpa' : p.x ≠ a.x ∨ p.y ≠ a.y := by
    by_contra h
    push Not at h
    exact hpa (LatticePoint.ext h.1 h.2)
  have hpb' : p.x ≠ b.x ∨ p.y ≠ b.y := by
    by_contra h
    push Not at h
    exact hpb (LatticePoint.ext h.1 h.2)
  have hqa' : q.x ≠ a.x ∨ q.y ≠ a.y := by
    by_contra h
    push Not at h
    exact hqa (LatticePoint.ext h.1 h.2)
  have hqb' : q.x ≠ b.x ∨ q.y ≠ b.y := by
    by_contra h
    push Not at h
    exact hqb (LatticePoint.ext h.1 h.2)
  rcases hpq with hpq | hpq | hpq | hpq <;>
    rcases hab with hab | hab | hab | hab <;>
    unfold corridorEdgeFlux corridorVertexFlux <;>
    simp only [hpq.1, hpq.2, hab.1, hab.2, sub_self, zero_mul, sub_zero] <;>
    split_ifs <;> omega

def corridorWalkFlux (p : LatticePoint) {a b : LatticePoint} :
    latticeGraph.Walk a b → ℤ
  | .nil => 0
  | @SimpleGraph.Walk.cons _ _ a c b h w =>
      corridorEdgeFlux p a c + corridorWalkFlux p w

theorem corridorWalkFlux_move {p q a b : LatticePoint}
    (hpq : Adjacent p q) (w : latticeGraph.Walk a b)
    (hp : p ∉ w.support) (hq : q ∉ w.support) :
    corridorWalkFlux p w - corridorWalkFlux q w =
      corridorVertexFlux p q a - corridorVertexFlux p q b := by
  induction w with
  | nil => simp [corridorWalkFlux]
  | @cons a c b h w ih =>
    have hpa : p ≠ a := by intro heq; subst p; exact hp (by simp)
    have hqa : q ≠ a := by intro heq; subst q; exact hq (by simp)
    have hpw : p ∉ w.support := fun hh => hp (by simp [hh])
    have hqw : q ∉ w.support := fun hh => hq (by simp [hh])
    have hpc : p ≠ c := by
      intro heq
      subst p
      exact hpw w.start_mem_support
    have hqc : q ≠ c := by
      intro heq
      subst q
      exact hqw w.start_mem_support
    have hedge := corridorEdgeFlux_move hpq h hpa hpc hqa hqc
    have htail := ih hpw hqw
    simp only [corridorWalkFlux]
    omega

end Erdos1212Kernel
