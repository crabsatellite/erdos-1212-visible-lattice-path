import Erdos1212Kernel.AlgebraicCorridorOriginalClose

namespace Erdos1212Kernel.CorridorScale
noncomputable section
open Filter

/-- Vertex carrier of the actual chosen finite connecting paths. -/
def CorridorDyadicChain.Support {α : ℝ} (chain : CorridorDyadicChain α) : Set LatticePoint :=
  {p | ∃ k, p ∈ (chain.segment k).walk.support}

/-- The paper's final finite-early-paths argument. An injective sequence in
the actual path union eventually leaves every early finite collection, so
its original coordinate ratio converges to the original alpha. -/
theorem CorridorDyadicChain.ratio_tendsto {α : ℝ} (chain : CorridorDyadicChain α)
    {P : ℕ → LatticePoint} (hP : Function.Injective P)
    (hmem : ∀ n, P n ∈ chain.Support) :
    Tendsto (fun n => (P n).x / ((P n).y : ℝ)) atTop (nhds α) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hr := (rho_tendsto_zero.comp chain.scale_tendsto).eventually
    (Iio_mem_nhds hε)
  obtain ⟨K, hK⟩ := eventually_atTop.mp hr
  let early : Finset LatticePoint := (Finset.range K).biUnion
    (fun k => (chain.segment k).walk.support.toFinset)
  have hfinite : Set.Finite {n : ℕ | P n ∈ early} :=
    Set.Finite.preimage hP.injOn early.finite_toSet
  obtain ⟨B, hB⟩ := hfinite.bddAbove
  refine ⟨B + 1, ?_⟩
  intro n hn
  obtain ⟨k, hk⟩ := hmem n
  have hkK : K ≤ k := by
    by_contra hnot
    have hearly : P n ∈ early := Finset.mem_biUnion.mpr
      ⟨k, Finset.mem_range.mpr (by omega), List.mem_toFinset.mpr hk⟩
    have hb : n ≤ B := hB hearly
    omega
  rw [Real.dist_eq]
  rcases chain.segment_corridor k (P n) hk with hc | hc
  · exact hc.2.2.2.2.trans_lt (hK k hkK)
  · exact hc.2.2.2.2.trans_lt (hK (k + 1) (by omega))

theorem CorridorDyadicChain.safe_of_mem_support {α : ℝ}
    (chain : CorridorDyadicChain α) {p : LatticePoint} (hp : p ∈ chain.Support) :
    SafePoint p := by
  obtain ⟨k, hk⟩ := hp
  exact (chain.segment k).safe p hk

end
end Erdos1212Kernel.CorridorScale
