import Erdos1212Kernel.TaoZetaCanonicalResidualThreshold

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 700000

/-- Keep the full Littlewood width: any fixed multiple of the earlier
conservative radius fits once `log log T` exceeds that multiple. -/
theorem tao_scaled_baseRadius_le_littlewoodWidth {D T : Real}
    (hT : 1 < T) (hL : 1 < Real.log T)
    (hll : 1 ≤ Real.log (Real.log T)) (hD : D ≤ Real.log (Real.log T)) :
    D * taoZeroFreeBaseRadius T ≤ taoLittlewoodWidth T (taoLittlewoodR T) := by
  let L := Real.log T
  let l := Real.log L
  have hLp : 0 < L := by dsimp [L]; linarith
  have hlp : 0 < l := by dsimp [l, L]; linarith
  have hlL : l ≤ L := by
    have ht := Real.log_le_sub_one_of_pos hLp
    dsimp [l]
    linarith
  have hR : (taoLittlewoodR T : Real) < 8 * L / l + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hRl : (taoLittlewoodR T : Real) * l ≤ 9 * L := by
    have ht := (mul_lt_mul_of_pos_right hR hlp).le
    have heq : (8 * L / l + 1) * l = 8 * L + l := by field_simp
    rw [heq] at ht
    linarith
  have hlog2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    linarith
  have hRpos : 0 < (taoLittlewoodR T : Real) := by
    exact_mod_cast taoLittlewoodR_one hT hL
  have hdenp : 0 < (taoLittlewoodR T : Real) * Real.log 2 := mul_pos hRpos hlog2p
  have hdenl : l * ((taoLittlewoodR T : Real) * Real.log 2) ≤ 9 * L := by
    have ht := mul_le_mul_of_nonneg_left hlog2le (mul_nonneg hRpos.le hlp.le)
    nlinarith
  have hdenD : D * ((taoLittlewoodR T : Real) * Real.log 2) ≤ 100 * L := by
    have ht := mul_le_mul_of_nonneg_right hD hdenp.le
    change D * ((taoLittlewoodR T : Real) * Real.log 2) ≤
      l * ((taoLittlewoodR T : Real) * Real.log 2) at ht
    linarith
  unfold taoZeroFreeBaseRadius taoLittlewoodWidth
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (show 0 < 100 * Real.log T by positivity) hdenp).mpr
  have ht := mul_le_mul_of_nonneg_left hdenD hlp.le
  dsimp [l, L] at ht
  nlinarith only [ht]

theorem eventually_taoScaledNearbyFrequencyConditions (D : Real) (hD : 0 ≤ D) :
    ∀ᶠ T : Real in atTop, ∀ U ∈ Set.Icc (T - 1) (T + 1),
      TaoLittlewoodFinalFrequencyConditions U ∧ 4 ≤ U ∧ 1 ≤ Real.log U ∧
      D * taoZeroFreeBaseRadius T / 4 ≤ taoLittlewoodWidth U (taoLittlewoodR U) ∧
      Real.log U ≤ 2 * Real.log T := by
  have hshift : Tendsto (fun T : Real => T - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ (-1) tendsto_id
  have hs := ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp hshift).eventually_ge_atTop
    (max 1 D)
  have hL := Real.tendsto_log_atTop.eventually_ge_atTop (2 * Real.log 2)
  have hll := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop
    (2 * Real.log 2)
  filter_upwards [eventually_taoNearbyFrequencyConditions, hs, hL, hll,
    eventually_ge_atTop 5] with T hnear hs hL hll hT
  intro U hU
  obtain ⟨hfinal, hU4, hUL, _hold, hcompare⟩ := hnear U hU
  have hLshift : 0 < Real.log (T - 1) := Real.log_pos (by linarith)
  have hlogmono := Real.log_le_log (by linarith : 0 < T - 1) hU.1
  have hllmono := Real.log_le_log hLshift hlogmono
  have hllU : 1 ≤ Real.log (Real.log U) := (le_max_left _ _).trans (hs.trans hllmono)
  have hDU : D ≤ Real.log (Real.log U) := (le_max_right _ _).trans (hs.trans hllmono)
  have hULstrict : 1 < Real.log U := by
    have ht := Real.exp_le_exp.mpr hllU
    rw [Real.exp_log (by linarith : 0 < Real.log U)] at ht
    exact (Real.one_lt_exp_iff.mpr one_pos).trans_le ht
  have hbase := taoZeroFreeBaseRadius_quarter_le_of_near
    (by linarith) hU.1 hU.2 hL hll hllU
  have hwidth := tao_scaled_baseRadius_le_littlewoodWidth (by linarith : 1 < U)
    hULstrict hllU hDU
  refine ⟨hfinal, hU4, hUL, ?_, hcompare⟩
  calc
    _ = D * (taoZeroFreeBaseRadius T / 4) := by ring
    _ ≤ D * taoZeroFreeBaseRadius U := mul_le_mul_of_nonneg_left hbase hD
    _ ≤ _ := hwidth

theorem tendsto_taoZeroFreeBaseRadius :
    Tendsto taoZeroFreeBaseRadius atTop (nhds 0) := by
  have ht := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    Real.tendsto_log_atTop).div_const 100
  unfold taoZeroFreeBaseRadius
  simpa [Function.comp_def, div_div, mul_comm] using ht

end

end Erdos1212Kernel
