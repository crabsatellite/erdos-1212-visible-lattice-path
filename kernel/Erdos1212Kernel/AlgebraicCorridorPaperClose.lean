import Erdos1212Kernel.AlgebraicCorridorConstrainedWalks
import Erdos1212Kernel.AlgebraicCorridorChainLimit

namespace Erdos1212Kernel.CorridorScale
noncomputable section
open Filter MeasureTheory

/-- Actual edge union of the chosen finite paths, not the induced graph on
their vertex union. -/
def CorridorDyadicChain.EdgeUnion {α : ℝ} (chain : CorridorDyadicChain α)
    (p q : LatticePoint) : Prop := ∃ k, (chain.segment k).walk.toSubgraph.Adj p q

theorem CorridorDyadicChain.prefix_support {α : ℝ} (chain : CorridorDyadicChain α) :
    ∀ n p, p ∈ (corridorChainWalk chain.endpoint chain.segment n).support → p ∈ chain.Support := by
  intro n
  induction n with
  | zero =>
      intro p hp
      have he : p = chain.endpoint 0 := by simpa [corridorChainWalk] using hp
      subst p
      exact ⟨0, (chain.segment 0).walk.start_mem_support⟩
  | succ n ih =>
      intro p hp
      rw [show corridorChainWalk chain.endpoint chain.segment (n + 1) =
        (corridorChainWalk chain.endpoint chain.segment n).append (chain.segment n).walk by rfl,
        SimpleGraph.Walk.mem_support_append_iff] at hp
      rcases hp with hp | hp
      · exact ih p hp
      · exact ⟨n, hp⟩

theorem CorridorDyadicChain.prefix_edges {α : ℝ} (chain : CorridorDyadicChain α) :
    ∀ n p q, (corridorChainWalk chain.endpoint chain.segment n).toSubgraph.Adj p q →
      chain.EdgeUnion p q := by
  intro n
  induction n with
  | zero =>
      intro p q hp
      simp [corridorChainWalk, SimpleGraph.Walk.toSubgraph] at hp
  | succ n ih =>
      intro p q hp
      rw [show corridorChainWalk chain.endpoint chain.segment (n + 1) =
        (corridorChainWalk chain.endpoint chain.segment n).append (chain.segment n).walk by rfl,
        SimpleGraph.Walk.toSubgraph_append, SimpleGraph.Subgraph.sup_adj] at hp
      rcases hp with hp | hp
      · exact ih p q hp
      · exact ⟨n, hp⟩

theorem CorridorDyadicChain.exists_ray {α : ℝ} (chain : CorridorDyadicChain α) :
    ∃ P : ℕ → LatticePoint, Function.Injective P ∧
      (∀ t, SafePoint (P t)) ∧ (∀ t, Adjacent (P t) (P (t + 1))) ∧
      (∀ t, P t ∈ chain.Support) ∧ (∀ t, chain.EdgeUnion (P t) (P (t + 1))) := by
  apply corridor_ray_of_arbitrarily_far_constrained_walks
    (chain.endpoint 0) chain.Support chain.EdgeUnion
  intro bound
  obtain ⟨n, hn⟩ := (chain.scale_tendsto.eventually_ge_atTop (bound : ℝ)).exists
  refine ⟨chain.endpoint n, Or.inl ?_, corridorChainWalk chain.endpoint chain.segment n, ?_,
    chain.prefix_edges n⟩
  · exact_mod_cast hn.trans (chain.endpoint_lower n)
  · intro p hp
    have hs := chain.prefix_support n p hp
    exact ⟨chain.safe_of_mem_support hs, hs⟩

theorem CorridorDyadicChain.paper_ray {α : ℝ} (chain : CorridorDyadicChain α) :
    AlgebraicCorridorRayAt α := by
  obtain ⟨P, hi, hs, ha, hm, _⟩ := chain.exists_ray
  exact ⟨P, hi, hs, ha, chain.ratio_tendsto hi hm⟩

/-- The complete displayed paper statement, from the original carriers and
the actual chosen crossing paths, with no external mathematical premise. -/
theorem algebraicCorridor_paper_close : AlgebraicCorridorPaperStatement := by
  filter_upwards [ae_corridorDyadicChain] with α hchain
  exact hchain.some.paper_ray

end
end Erdos1212Kernel.CorridorScale
