import Erdos1212Kernel.TaoZetaZeroFreePointwise

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 1900000

/-- A genuine de la Vallee Poussin zero-free region for canonical
`riemannZeta`, obtained from the completed Littlewood/Borel/3-4-1
chain. The constants are absolute existential witnesses. -/
theorem exists_riemannZeta_zero_free_region_log :
    ∃ c T₀ : Real, 0 < c ∧ ∀ (t β : Real),
      T₀ ≤ taoLogFrequency t →
      1 - c / Real.log (taoLogFrequency t) < β →
      riemannZeta ((β : Complex) + (t : Complex) * Complex.I) ≠ 0 := by
  obtain ⟨a, ha, hsmall⟩ := exists_taoZeroFreeParameter
  obtain ⟨δ, hδ, hpole⟩ := exists_norm_taoZetaLogDerivative_real_le_nine_eighth
  obtain ⟨Tnear, hnear⟩ := exists_taoNearbyFrequencyThreshold
  let c : Real := a / 100
  have hc : 0 < c := by unfold c; positivity
  have hevent : ∀ᶠ T : Real in atTop,
      Tnear ≤ T ∧ Tnear ≤ 2 * T ∧ 1 ≤ T ∧
      1 < Real.log T ∧
      max 1 (4000 * a) ≤ Real.log (Real.log T) ∧
      20 * Real.log 2 ≤ Real.log T ∧
      max (2 * a) (a / δ) ≤ Real.log T := by
    filter_upwards [eventually_ge_atTop Tnear,
      eventually_ge_atTop (Tnear / 2), eventually_ge_atTop 1,
      Real.tendsto_log_atTop.eventually_gt_atTop 1,
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop
        (max 1 (4000 * a)),
      Real.tendsto_log_atTop.eventually_ge_atTop (20 * Real.log 2),
      Real.tendsto_log_atTop.eventually_ge_atTop (max (2 * a) (a / δ))]
      with T hnear1 hnear2 hT1 hL hll hratio hshift
    exact ⟨hnear1, by linarith, hT1, hL, hll, hratio, hshift⟩
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨c, T₀, hc, fun t β ht hβ => ?_⟩
  let T : Real := taoLogFrequency t
  let T2 : Real := taoLogFrequency (2 * t)
  let L : Real := Real.log T
  let L2 : Real := Real.log T2
  let l : Real := Real.log L
  obtain ⟨hnearT, hnearT2, hT1, hL, hllMax, hratio, hshift⟩ :=
    hT₀ T (by simpa only [T] using ht)
  have htne : t ≠ 0 := by
    intro ht0
    subst t
    norm_num [T, taoLogFrequency] at hL
  have hTpos : 0 < T := by simpa only [T] using taoLogFrequency_pos htne
  have hT2eq : T2 = 2 * T := by
    unfold T2 T
    exact taoLogFrequency_two_mul t
  have hT2pos : 0 < T2 := by rw [hT2eq]; positivity
  have hLpos : 0 < L := by unfold L; linarith
  have hL2pos : 0 < L2 := by unfold L2; exact Real.log_pos (by
    rw [hT2eq]
    nlinarith)
  have hL2eq : L2 = L + Real.log 2 := by
    unfold L2 L
    rw [hT2eq, Real.log_mul (by norm_num : (2 : Real) ≠ 0) hTpos.ne']
    ring
  have hLleL2 : L ≤ L2 := by
    rw [hL2eq]
    exact le_add_of_nonneg_right (Real.log_nonneg (by norm_num))
  have hLratio : L2 ≤ (21 / 20 : Real) * L := by
    rw [hL2eq]
    linarith
  have hll1 : 1 ≤ Real.log L := by
    dsimp only [l]
    exact (le_max_left _ _).trans hllMax
  have hll2 : 1 ≤ Real.log L2 := by
    exact hll1.trans (Real.log_le_log hLpos hLleL2)
  have hL1strict : 1 < L := by simpa only [L] using hL
  have hL2strict : 1 < L2 := hL1strict.trans_le hLleL2
  have hnear1 : ∀ U ∈ Set.Icc (T - 1) (T + 1),
      TaoLittlewoodFinalFrequencyConditions U ∧
      4 ≤ U ∧ 1 ≤ Real.log U ∧
      taoZeroFreeBaseRadius T / 4 ≤
        taoLittlewoodWidth U (taoLittlewoodR U) ∧
      Real.log U ≤ 2 * Real.log T :=
    fun U hU => hnear T U hnearT hU
  have hnear2 : ∀ U ∈ Set.Icc (T2 - 1) (T2 + 1),
      TaoLittlewoodFinalFrequencyConditions U ∧
      4 ≤ U ∧ 1 ≤ Real.log U ∧
      taoZeroFreeBaseRadius T2 / 4 ≤
        taoLittlewoodWidth U (taoLittlewoodR U) ∧
      Real.log U ≤ 2 * Real.log T2 :=
    fun U hU => hnear T2 U (by rw [hT2eq]; exact hnearT2) hU
  have hqsmall1 := taoZeroFreeBaseRadius_quarter_le_one_div_four_hundred
    (T := T) hL1strict hll1
  have hqsmall2 := taoZeroFreeBaseRadius_quarter_le_one_div_four_hundred
    (T := T2) hL2strict hll2
  have hqhalf1 : taoZeroFreeBaseRadius T / 4 ≤ 1 / 2 :=
    hqsmall1.trans (by norm_num)
  have hqhalf2 : taoZeroFreeBaseRadius T2 / 4 ≤ 1 / 2 :=
    hqsmall2.trans (by norm_num)
  have habs : |t| = (2 * Real.pi) * T := by
    unfold T taoLogFrequency
    field_simp [Real.pi_ne_zero]
  have habs2 : |2 * t| = (2 * Real.pi) * T2 := by
    unfold T2 taoLogFrequency
    field_simp [Real.pi_ne_zero]
  have hqimag1 : taoZeroFreeBaseRadius T / 4 < |t| := by
    rw [habs]
    nlinarith [Real.pi_gt_three]
  have hqimag2 : taoZeroFreeBaseRadius T2 / 4 < |2 * t| := by
    rw [habs2]
    nlinarith [Real.pi_gt_three]
  have hηhalf : a / L2 ≤ 1 / 2 := by
    apply (div_le_iff₀ hL2pos).2
    have ha2 : 2 * a ≤ L := (le_max_left _ _).trans hshift
    nlinarith
  have hηδ : a / L2 < δ := by
    have haδ : a / δ ≤ L := (le_max_right _ _).trans hshift
    have haL : a ≤ δ * L := by
      simpa only [mul_comm] using (div_le_iff₀ hδ).mp haδ
    have hLL2 : L < L2 := by
      rw [hL2eq]
      exact lt_add_of_pos_right _ (Real.log_pos (by norm_num))
    have hmul : δ * L < δ * L2 := mul_lt_mul_of_pos_left hLL2 hδ
    exact (div_lt_iff₀ hL2pos).2 (haL.trans_lt hmul)
  have hlLarge : 4000 * a ≤ l := by
    dsimp only [l]
    exact (le_max_right _ _).trans hllMax
  have hkernelScale :
      4 * (a / L2 + a / (100 * L)) ≤ taoZeroFreeBaseRadius T / 8 := by
    have hηupper : a / L2 ≤ a / L :=
      div_le_div_of_nonneg_left ha.le hLpos hLleL2
    unfold taoZeroFreeBaseRadius
    change 4 * (a / L2 + a / (100 * L)) ≤ l / (100 * L) / 8
    have hleft : 4 * (a / L2 + a / (100 * L)) ≤
        4 * (a / L + a / (100 * L)) := mul_le_mul_of_nonneg_left
      (add_le_add hηupper le_rfl) (by norm_num)
    apply hleft.trans
    rw [div_div]
    apply (le_div_iff₀ (by positivity : 0 < (100 * L) * 8)).2
    field_simp [hLpos.ne']
    nlinarith
  apply riemannZeta_ne_zero_of_pointwise_zeroFree_conditions ha hsmall hδ hpole
    (by simpa only [T] using hnear1) (by simpa only [T2] using hnear2)
    (by simpa only [T, L] using hL1strict) (by simpa only [T, L, l] using hll1)
    (by simpa only [T2, L2] using hL2strict) (by simpa only [T2, L2] using hll2)
    (by simpa only [T, T2, L, L2] using hLratio)
    (by simpa only [T2, L2] using hηhalf) (by simpa only [T2, L2] using hηδ)
    (by simpa only [T] using hqhalf1) (by simpa only [T2] using hqhalf2)
    (by simpa only [T] using hqimag1) (by simpa only [T2] using hqimag2)
    (by simpa only [T, T2, L, L2] using hkernelScale)
    (by simpa only [c, T, L, div_div] using hβ)

end

end Erdos1212Kernel
