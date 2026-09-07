import Erdos1212Kernel.IwaniecPaperD2MassCarrier

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 500000

def iwaniecPaperD2PairMass (level s : Real) : Real :=
  ∑ p ∈ iwaniecPaperD2OuterBand level s,
    ∑ q ∈ iwaniecPaperD2InnerPool level p, 1 / ((p : Real) * q)

theorem iwaniecPaperD2PairMass_nonneg (level s : Real) : 0 ≤ iwaniecPaperD2PairMass level s := by
  apply Finset.sum_nonneg
  intro p hp
  apply Finset.sum_nonneg
  intro q hq
  positivity

theorem iwaniecPaperD2PairMass_eq_iterated (level s : Real) :
    iwaniecPaperD2PairMass level s = ∑ p ∈ iwaniecPaperD2OuterBand level s,
      (p : Real)⁻¹ * ∑ q ∈ iwaniecPaperD2InnerPool level p, (q : Real)⁻¹ := by
  unfold iwaniecPaperD2PairMass
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

/-- Both bounds concern the actual source pools. Their inclusion in
the power interval has been proved before applying the analytic bound. -/
theorem exists_iwaniecPaperD2_reciprocal_mass_bounds :
    ∃ K : Real, 0 < K ∧ ∀ level s : Real, 64 ≤ level → 2 ≤ s →
      (∑ p ∈ iwaniecPaperD2OuterBand level s, (p : Real)⁻¹) ≤ K ∧
      ∀ p ∈ iwaniecPaperD2OuterBand level s,
        (∑ q ∈ iwaniecPaperD2InnerPool level p, (q : Real)⁻¹) ≤ K := by
  obtain ⟨K, hK, hband⟩ := exists_iwaniecPrimePowerBand_mass_bound
  refine ⟨K, hK, ?_⟩
  intro level s hy hs
  have hy1 : 1 < level := by linarith
  have hcontrol := hband (Real.log level) (iwaniec_log_level_sixtyfour hy)
  change (∑ p ∈ iwaniecPaperD2ControlBand level, (p : Real)⁻¹) ≤ K at hcontrol
  constructor
  · have hh := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : Nat => (p : Real)⁻¹)
      (iwaniecPaperD2_outer_subset_control hy1 hs)
      (fun p _ _ => inv_nonneg.mpr (Nat.cast_nonneg p))
    exact hh.trans hcontrol
  · intro p hp
    have hpPool := (Finset.mem_filter.mp hp).1
    have hh := Finset.sum_le_sum_of_subset_of_nonneg (f := fun q : Nat => (q : Real)⁻¹)
      (iwaniecPaperD2_inner_subset_control hy1 hs hpPool)
      (fun q _ _ => inv_nonneg.mpr (Nat.cast_nonneg q))
    exact hh.trans hcontrol

theorem exists_iwaniecPaperD2_pair_mass_bound :
    ∃ K : Real, 0 < K ∧ ∀ level s : Real, 64 ≤ level → 2 ≤ s →
      (∑ p ∈ iwaniecPaperD2OuterBand level s, (p : Real)⁻¹) ≤ K ∧
      iwaniecPaperD2PairMass level s ≤ K ^ 2 := by
  obtain ⟨K, hK, hmass⟩ := exists_iwaniecPaperD2_reciprocal_mass_bounds
  refine ⟨K, hK, ?_⟩
  intro level s hy hs
  obtain ⟨hout, hin⟩ := hmass level s hy hs
  refine ⟨hout, ?_⟩
  rw [iwaniecPaperD2PairMass_eq_iterated]
  calc
    _ ≤ ∑ p ∈ iwaniecPaperD2OuterBand level s, (p : Real)⁻¹ * K := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (hin p hp) (inv_nonneg.mpr (Nat.cast_nonneg p))
    _ = (∑ p ∈ iwaniecPaperD2OuterBand level s, (p : Real)⁻¹) * K := by rw [Finset.sum_mul]
    _ ≤ K * K := mul_le_mul_of_nonneg_right hout hK.le
    _ = _ := by ring

end

end Erdos1212Kernel
