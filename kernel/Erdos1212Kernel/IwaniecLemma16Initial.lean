import Erdos1212Kernel.IwaniecLemma16High

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 550000

def iwaniecLemma16InitialMass : Real :=
  ∑ p ∈ iwaniecStrictPrimePool (Real.exp 4), (p : Real)⁻¹

theorem iwaniecPaperD2_le_pair_mass (level s : Real) :
    iwaniecPaperD2 level s ≤ iwaniecPaperD2PairMass level s := by
  rw [iwaniecPaperD2_eq_mass_carrier]
  unfold iwaniecPaperD2PairMass
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro q hq
  exact div_le_div_of_nonneg_right (iwaniecPaperR_le_one (q : Real))
    (mul_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg q))

/-- The bounded initial level range is handled on one actual finite
prime pool. No asymptotic assertion is extended across small y by fiat. -/
theorem iwaniecPaperD2_initial_bound {level s : Real} (hy : 1 < level)
    (hL : Real.log level ≤ 8) (hs : 2 ≤ s) :
    iwaniecPaperD2 level s ≤ iwaniecLemma16InitialMass ^ 2 := by
  let P := iwaniecStrictPrimePool (Real.exp 4)
  have hcutoff : Real.exp (Real.log level / s) ≤ Real.exp 4 := by
    apply Real.exp_le_exp.mpr
    have hh := div_le_div_of_nonneg_left (Real.log_pos hy).le (by norm_num : (0 : Real) < 2) hs
    linarith
  have houtSub : iwaniecPaperD2OuterBand level s ⊆ P := by
    intro p hp
    obtain ⟨hpPrime, hpLt⟩ := mem_iwaniecStrictPrimePool.mp (Finset.mem_filter.mp hp).1
    exact mem_iwaniecStrictPrimePool.mpr ⟨hpPrime, hpLt.trans_le hcutoff⟩
  have hinSub : ∀ p ∈ iwaniecPaperD2OuterBand level s, iwaniecPaperD2InnerPool level p ⊆ P := by
    intro p hp q hq
    have hpP := (mem_iwaniecStrictPrimePool.mp (houtSub hp)).2
    obtain ⟨hqPrime, hqp⟩ := mem_iwaniecStrictPrimePool.mp (Finset.mem_filter.mp hq).1
    exact mem_iwaniecStrictPrimePool.mpr ⟨hqPrime, hqp.trans hpP⟩
  have hnonneg : 0 ≤ iwaniecLemma16InitialMass :=
    Finset.sum_nonneg (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))
  have hout : (∑ p ∈ iwaniecPaperD2OuterBand level s, (p : Real)⁻¹) ≤ iwaniecLemma16InitialMass := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : Nat => (p : Real)⁻¹) houtSub
      (fun p _ _ => inv_nonneg.mpr (Nat.cast_nonneg p))
  have hin : ∀ p ∈ iwaniecPaperD2OuterBand level s,
      (∑ q ∈ iwaniecPaperD2InnerPool level p, (q : Real)⁻¹) ≤ iwaniecLemma16InitialMass := by
    intro p hp
    exact Finset.sum_le_sum_of_subset_of_nonneg (f := fun q : Nat => (q : Real)⁻¹) (hinSub p hp)
      (fun q _ _ => inv_nonneg.mpr (Nat.cast_nonneg q))
  apply (iwaniecPaperD2_le_pair_mass level s).trans
  rw [iwaniecPaperD2PairMass_eq_iterated]
  calc
    _ ≤ ∑ p ∈ iwaniecPaperD2OuterBand level s, (p : Real)⁻¹ * iwaniecLemma16InitialMass := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (hin p hp) (inv_nonneg.mpr (Nat.cast_nonneg p))
    _ = (∑ p ∈ iwaniecPaperD2OuterBand level s, (p : Real)⁻¹) * iwaniecLemma16InitialMass := by
      rw [Finset.sum_mul]
    _ ≤ iwaniecLemma16InitialMass * iwaniecLemma16InitialMass :=
      mul_le_mul_of_nonneg_right hout hnonneg
    _ = _ := by ring

theorem exists_iwaniecLemma16_initial_constant :
    ∃ C : Real, 0 < C ∧ ∀ level s : Real, 1 < level → Real.log level ≤ 8 → 2 ≤ s →
      Real.exp Real.eulerMascheroniConstant * iwaniecPaperD2 level s ≤
        iwaniecGTwo s / Real.log level + C * Real.exp (-Real.sqrt (Real.log level / 6)) := by
  let M := Real.exp Real.eulerMascheroniConstant * iwaniecLemma16InitialMass ^ 2 + 1
  let E₀ := Real.exp (-Real.sqrt (8 / 6 : Real))
  let C := M / E₀
  have hM : 0 < M := by dsimp [M]; positivity
  have hC : 0 < C := div_pos hM (Real.exp_pos _)
  refine ⟨C, hC, ?_⟩
  intro level s hy hL hs
  have hb := mul_le_mul_of_nonneg_left (iwaniecPaperD2_initial_bound hy hL hs)
    (Real.exp_pos Real.eulerMascheroniConstant).le
  have he : E₀ ≤ Real.exp (-Real.sqrt (Real.log level / 6)) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (Real.sqrt_le_sqrt (by linarith : Real.log level / 6 ≤ 8 / 6))
  have hfloor : M = C * E₀ := by
    have hEne : E₀ ≠ 0 := (Real.exp_pos _).ne'
    dsimp [C]
    rw [div_mul_cancel₀ _ hEne]
  have hm : Real.exp Real.eulerMascheroniConstant * iwaniecPaperD2 level s ≤ M := by
    dsimp [M]
    linarith
  have hc := mul_le_mul_of_nonneg_left he hC.le
  rw [← hfloor] at hc
  have hmain : 0 ≤ iwaniecGTwo s / Real.log level :=
    div_nonneg (iwaniecGTwo_nonneg_of_two_le hs) (Real.log_pos hy).le
  exact (hm.trans hc).trans (by linarith)

end

end Erdos1212Kernel
