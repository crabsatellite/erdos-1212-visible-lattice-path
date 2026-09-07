import Erdos1212Kernel.IwaniecQMiddleBudget

namespace Erdos1212Kernel

noncomputable section

open Filter Topology MeasureTheory

set_option maxHeartbeats 600000

theorem iwaniecGTwo_le_evenSeries {s : Real} (hs : 2 ≤ s) :
    iwaniecGTwo s ≤ iwaniecEvenSieveSeries s := by
  rw [iwaniecEvenSieveSeries_eq_integral_Ioi_add_gTwo hs]
  have hi : 0 ≤ ∫ t in Set.Ioi s, iwaniecOddSieveSeries (t - 1) / (t - 1) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact div_nonneg (iwaniecOddSieveSeries_nonneg (by linarith [ht.out])) (by linarith [ht.out])
  linarith only [hi]

theorem iwaniecPaperQ_one_bound {C level s : Real}
    (hC : 0 < C) (hy : 1 < level) (hs : iwaniecAuxGStart 1 ≤ s) :
    Real.exp Real.eulerMascheroniConstant * iwaniecPaperQ 1 level s < iwaniecPaperQMajorant C 1 level s := by
  rw [iwaniecPaperQ_one hy s, mul_zero]
  exact iwaniecPaperQMajorant_pos hC (by norm_num) hy hs

/-- The source r=2 base, directly from Lemma 16 and (4.3), before
the strong rank induction. No hypothesis at a smaller rank is needed. -/
theorem eventually_iwaniecPaperQ_two_base :
    ∀ᶠ level : Real in atTop, 1 < level ∧ ∀ C s : Real, 2 ≤ C → 2 ≤ s →
      Real.exp Real.eulerMascheroniConstant * iwaniecPaperQ 2 level s < iwaniecPaperQMajorant C 2 level s := by
  obtain ⟨D, hD, hbase⟩ := exists_iwaniecPaperQ_d2_correction_bound
  filter_upwards [eventually_iwaniecQ_d2_error_absorbed hD.le,
    Real.tendsto_log_atTop.eventually_ge_atTop 2] with level herror hlog
  have hy := herror.1
  refine ⟨hy, ?_⟩
  intro C s hC hs
  let L := Real.log level
  let B := iwaniecAuxWeightPower level s * iwaniecAuxG 2 s / L ^ 2
  let q := (L ^ 2)⁻¹
  let F := iwaniecParitySieveProfile 2 s / L
  have hL : 0 < L := Real.log_pos hy
  have hsdom : iwaniecAuxGStart 2 ≤ s := by norm_num [iwaniecAuxGStart]; exact hs
  have hW := iwaniecAuxWeightPower_pos level (by linarith : 1 ≤ s)
  have hG := iwaniecAuxG_pos_exactDomain 2 hsdom
  have hB : 0 < B := by dsimp [B]; positivity
  have hq1 : q ≤ 1 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1)
      (show 1 ≤ L ^ 2 by change 2 ≤ L at hlog; nlinarith only [hlog])
    simpa only [one_div, inv_one] using hh
  have hb := hbase 2 level s hy hs
  have he := herror.2 2 s hsdom
  have hn := iwaniecQ_inv_four_le_weighted 2 hy hsdom
  have he' := he.trans hn
  simp only [even_two, if_true, true_and] at hb he'
  have hf : iwaniecGTwo s / L ≤ F := by
    simpa only [F, iwaniecParitySieveProfile, even_two, if_true] using
      div_le_div_of_nonneg_right (iwaniecGTwo_le_evenSeries hs) hL.le
  have hraw : Real.exp Real.eulerMascheroniConstant * iwaniecPaperQ 2 level s ≤ F + B * q := by
    rw [iwaniecPaperQ_two_eq_d2]
    linarith only [hb, he', hf]
  have hfactor : (1 : Real) < C * (2 / 3) := by linarith only [hC]
  have hsmall := mul_le_mul_of_nonneg_left hq1 hB.le
  have hpaid := mul_lt_mul_of_pos_right hfactor hB
  have hmainId : iwaniecPaperQMajorant C 2 level s = F + C * (2 / 3) * B := by
    norm_num only [iwaniecPaperQMajorant, Nat.cast_ofNat]
    dsimp [F, B, L]
    ring
  rw [hmainId]
  nlinarith only [hraw, hsmall, hpaid]

end

end Erdos1212Kernel
