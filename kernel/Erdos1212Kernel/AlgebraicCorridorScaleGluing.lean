import Erdos1212Kernel.FiniteReachability

namespace Erdos1212Kernel

noncomputable section

/-! A path-level consumer for the last section of the paper.  It is deliberately
independent of how the finite crossings were obtained: once consecutive
scale pieces are safe walks with matching endpoints, their finite concatenated
walks give the exact input expected by the existing Kőnig extraction. -/

structure CorridorSafeWalk (start finish : LatticePoint) where
  walk : latticeGraph.Walk start finish
  safe : ∀ p, p ∈ walk.support → SafePoint p

def corridorChainWalk
    (endpoint : ℕ → LatticePoint)
    (segment : ∀ n, CorridorSafeWalk (endpoint n) (endpoint (n + 1))) :
    ∀ n, latticeGraph.Walk (endpoint 0) (endpoint n)
  | 0 => SimpleGraph.Walk.nil
  | n + 1 => (corridorChainWalk endpoint segment n).append (segment n).walk

theorem corridorChainWalk_safe
    (endpoint : ℕ → LatticePoint)
    (segment : ∀ n, CorridorSafeWalk (endpoint n) (endpoint (n + 1)))
    (hroot : SafePoint (endpoint 0)) :
    ∀ n p, p ∈ (corridorChainWalk endpoint segment n).support →
      SafePoint p := by
  intro n
  induction n with
  | zero =>
      intro p hp
      have hp0 : p = endpoint 0 := by
        simpa [corridorChainWalk] using hp
      rw [hp0]
      exact hroot
  | succ n ih =>
      intro p hp
      rw [show corridorChainWalk endpoint segment (n + 1) =
        (corridorChainWalk endpoint segment n).append (segment n).walk by
        rfl, SimpleGraph.Walk.mem_support_append_iff] at hp
      rcases hp with hp | hp
      · exact ih p hp
      · exact (segment n).safe p hp

theorem arbitrarily_far_safe_reachable_of_corridor_chain
    (root : LatticePoint)
    (endpoint : ℕ → LatticePoint)
    (hzero : endpoint 0 = root)
    (segment : ∀ n, CorridorSafeWalk (endpoint n) (endpoint (n + 1)))
    (hroot : SafePoint root)
    (hfar : ∀ bound : ℕ,
      ∃ n, bound ≤ (endpoint n).x ∨ bound ≤ (endpoint n).y) :
    Erdos1212FullClose := by
  subst root
  apply fullClose_of_arbitrarily_far_safe_reachable (endpoint 0)
  intro bound
  obtain ⟨n, hn⟩ := hfar bound
  exact ⟨endpoint n, hn, corridorChainWalk endpoint segment n,
    corridorChainWalk_safe endpoint segment hroot n⟩

end

end Erdos1212Kernel
