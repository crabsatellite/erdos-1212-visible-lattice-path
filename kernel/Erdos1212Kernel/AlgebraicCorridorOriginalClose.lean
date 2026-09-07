import Erdos1212Kernel.AlgebraicCorridorDyadicChain

namespace Erdos1212Kernel.CorridorScale
noncomputable section
open Filter MeasureTheory

theorem ae_corridorDyadicChain :
    ∀ᵐ α : ℝ ∂volume.restrict algebraicCorridorSlopeInterval,
      Nonempty (CorridorDyadicChain α) := by
  filter_upwards [ae_eventually_directionAvoidance, ae_restrict_mem (by
    exact measurableSet_Ioo : MeasurableSet algebraicCorridorSlopeInterval)]
    with α havoid hα
  exact exists_corridorDyadicChain hα havoid

theorem CorridorDyadicChain.scale_tendsto {α : ℝ} (chain : CorridorDyadicChain α) :
    Tendsto (fun n => dyadicScale (chain.base + n)) atTop atTop := by
  have hshift : Tendsto (fun n : ℕ => chain.base + n) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact eventually_atTop.mpr ⟨b, fun n hn => by omega⟩
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp hshift

theorem CorridorDyadicChain.original_close {α : ℝ} (chain : CorridorDyadicChain α) :
    Erdos1212FullClose := by
  apply arbitrarily_far_safe_reachable_of_corridor_chain (chain.endpoint 0)
    chain.endpoint rfl chain.segment
  · exact (chain.segment 0).safe _ (chain.segment 0).walk.start_mem_support
  · intro bound
    obtain ⟨n, hn⟩ := (chain.scale_tendsto.eventually_ge_atTop (bound : ℝ)).exists
    refine ⟨n, Or.inl ?_⟩
    exact_mod_cast hn.trans (chain.endpoint_lower n)

/-- The original (weaker) problem now follows without an external producer
premise. This is not substituted for the stronger almost-everywhere simple-ray
and limiting-direction paper statement, which is still being assembled. -/
theorem erdos1212_fullClose_from_algebraic_corridors : Erdos1212FullClose := by
  have hμ : volume.restrict algebraicCorridorSlopeInterval ≠ 0 := by
    intro h
    exact algebraicCorridorSlopeInterval_volume_pos.ne' (Measure.restrict_eq_zero.mp h)
  letI : (ae (volume.restrict algebraicCorridorSlopeInterval)).NeBot := ae_neBot.mpr hμ
  obtain ⟨α, ⟨chain⟩⟩ := ae_corridorDyadicChain.exists
  exact chain.original_close

end
end Erdos1212Kernel.CorridorScale
