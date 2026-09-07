import Erdos1212Kernel.TaoZetaDiskBoundary

namespace Erdos1212Kernel

noncomputable section

open Filter Metric Topology

set_option maxHeartbeats 1900000

theorem abs_taoLogFrequency_sub_le_dist_imaginary_centers
    (z : Complex) (σ t : Real) :
    |taoLogFrequency z.im - taoLogFrequency t| ≤
      dist z ((σ : Complex) + (t : Complex) * Complex.I) := by
  have habs : |(|z.im| - |t|)| ≤ |z.im - t| := abs_abs_sub_abs_le_abs_sub _ _
  have htwoPi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hdiv : |(|z.im| - |t|)| / (2 * Real.pi) ≤ |z.im - t| := by
    calc
      _ ≤ |z.im - t| / (2 * Real.pi) :=
        div_le_div_of_nonneg_right habs (by positivity)
      _ ≤ |z.im - t| := div_le_self (abs_nonneg _) htwoPi
  have him : |z.im - t| ≤
      ‖z - ((σ : Complex) + (t : Complex) * Complex.I)‖ := by
    have h := Complex.abs_im_le_norm
      (z - ((σ : Complex) + (t : Complex) * Complex.I))
    convert h using 1 <;> simp
  unfold taoLogFrequency
  rw [← sub_div]
  rw [abs_div]
  have hdenabs : |2 * Real.pi| = 2 * Real.pi := abs_of_pos (by positivity)
  rw [hdenabs]
  rw [Complex.dist_eq]
  exact hdiv.trans him

theorem taoZeroFreeBaseRadius_quarter_le_of_near
    {T U : Real} (hT4 : 4 ≤ T)
    (hUlow : T - 1 ≤ U) (hUhigh : U ≤ T + 1)
    (hlogT : 2 * Real.log 2 ≤ Real.log T)
    (hloglogT : 2 * Real.log 2 ≤ Real.log (Real.log T))
    (hloglogU : 1 ≤ Real.log (Real.log U)) :
    taoZeroFreeBaseRadius T / 4 ≤ taoZeroFreeBaseRadius U := by
  let L := Real.log T
  let M := Real.log U
  let l := Real.log L
  let m := Real.log M
  have hTpos : 0 < T := by linarith
  have hUpos : 0 < U := by linarith
  have hTtwo : T / 2 ≤ U := by linarith
  have hUtwo : U ≤ 2 * T := by linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLpos : 0 < L := by unfold L; exact Real.log_pos (by linarith)
  have hMpos : 0 < M := by
    unfold M
    exact Real.log_pos (by linarith)
  have hlpos : 0 < l := by unfold l; linarith
  have hmpos : 0 < m := by unfold m; linarith
  have hMlower : L / 2 ≤ M := by
    have hlogDiv : Real.log (T / 2) = L - Real.log 2 := by
      rw [Real.log_div (ne_of_gt hTpos) (by norm_num : (2 : Real) ≠ 0)]
    have hmono := Real.log_le_log (by positivity : 0 < T / 2) hTtwo
    rw [hlogDiv] at hmono
    dsimp only [L, M]
    linarith
  have hMupper : M ≤ 2 * L := by
    have hlogMul : Real.log (2 * T) = Real.log 2 + L := by
      rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0) (ne_of_gt hTpos)]
    have hmono := Real.log_le_log hUpos hUtwo
    rw [hlogMul] at hmono
    dsimp only [L, M]
    linarith
  have hmlower : l / 2 ≤ m := by
    have hlogDiv : Real.log (L / 2) = l - Real.log 2 := by
      rw [Real.log_div (ne_of_gt hLpos) (by norm_num : (2 : Real) ≠ 0)]
    have hmono := Real.log_le_log (by positivity : 0 < L / 2) hMlower
    rw [hlogDiv] at hmono
    dsimp only [l, m]
    linarith
  have hprod : l * M ≤ 4 * m * L := by
    calc
      l * M ≤ l * (2 * L) := mul_le_mul_of_nonneg_left hMupper hlpos.le
      _ ≤ (2 * m) * (2 * L) := by
        have hlm : l ≤ 2 * m := by linarith
        exact mul_le_mul hlm le_rfl (by positivity) (by positivity)
      _ = 4 * m * L := by ring
  unfold taoZeroFreeBaseRadius
  dsimp only [L, M, l, m] at *
  rw [div_div]
  apply (div_le_div_iff₀ (by positivity : 0 < (100 * L) * 4)
    (by positivity : 0 < 100 * M)).2
  nlinarith

theorem eventually_taoNearbyFrequencyConditions :
    ∀ᶠ T : Real in atTop,
      ∀ U ∈ Set.Icc (T - 1) (T + 1),
        TaoLittlewoodFinalFrequencyConditions U ∧
        4 ≤ U ∧
        1 ≤ Real.log U ∧
        taoZeroFreeBaseRadius T / 4 ≤
          taoLittlewoodWidth U (taoLittlewoodR U) ∧
        Real.log U ≤ 2 * Real.log T := by
  obtain ⟨Tf, hTf⟩ := exists_taoLittlewood_final_frequency_threshold
  have hlog : ∀ᶠ T : Real in atTop, 2 * Real.log 2 ≤ Real.log T :=
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * Real.log 2)
  have hloglog : ∀ᶠ T : Real in atTop,
      2 * Real.log 2 ≤ Real.log (Real.log T) :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop
      (2 * Real.log 2)
  have hshift : Tendsto (fun T : Real => T - 1) atTop atTop := by
    refine tendsto_atTop.2 (fun b => ?_)
    filter_upwards [eventually_ge_atTop (b + 1)] with T hT
    linarith
  have hlogShift : ∀ᶠ T : Real in atTop, 1 ≤ Real.log (T - 1) :=
    (Real.tendsto_log_atTop.comp hshift).eventually_ge_atTop 1
  have hloglogShift : ∀ᶠ T : Real in atTop,
      1 ≤ Real.log (Real.log (T - 1)) :=
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hshift)).eventually_ge_atTop 1
  filter_upwards [eventually_ge_atTop (Tf + 1), eventually_ge_atTop 5,
    hlog, hloglog, hlogShift, hloglogShift] with T hTfT hT5 hLT hllT hLs hlls
  intro U hU
  have hUlow := hU.1
  have hUhigh := hU.2
  have hTfU : Tf ≤ U := by linarith
  have hU4 : 4 ≤ U := by linarith
  have hlogU : 1 ≤ Real.log U := by
    exact hLs.trans (Real.log_le_log (by linarith : 0 < T - 1) hUlow)
  have hloglogU : 1 ≤ Real.log (Real.log U) := by
    have hlogMono : Real.log (T - 1) ≤ Real.log U :=
      Real.log_le_log (by linarith : 0 < T - 1) hUlow
    exact hlls.trans (Real.log_le_log (by linarith) hlogMono)
  have hT1 : 1 < T := by linarith
  have hU1 : 1 < U := by linarith
  have hlogUstrict : 1 < Real.log U := by
    have hlogUpos : 0 < Real.log U := by linarith
    have hexp := Real.exp_le_exp.mpr hloglogU
    rw [Real.exp_log hlogUpos] at hexp
    have honeExp : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr one_pos
    linarith
  have hbaseCompare := taoZeroFreeBaseRadius_quarter_le_of_near
    (by linarith : 4 ≤ T) hUlow hUhigh hLT hllT hloglogU
  have hwidthU := taoZeroFreeBaseRadius_le_littlewoodWidth hU1
    hlogUstrict hloglogU
  have hlogCompare : Real.log U ≤ 2 * Real.log T := by
    have hUtwo : U ≤ 2 * T := by linarith
    have hmono := Real.log_le_log (by linarith : 0 < U) hUtwo
    rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0) (by linarith : T ≠ 0)] at hmono
    have hlog2le : Real.log 2 ≤ Real.log T := by linarith
    linarith
  exact ⟨hTf U hTfU, hU4, hlogU, hbaseCompare.trans hwidthU, hlogCompare⟩

theorem exists_taoNearbyFrequencyThreshold :
    ∃ T₀ : Real, ∀ T U, T₀ ≤ T → U ∈ Set.Icc (T - 1) (T + 1) →
      TaoLittlewoodFinalFrequencyConditions U ∧
      4 ≤ U ∧ 1 ≤ Real.log U ∧
      taoZeroFreeBaseRadius T / 4 ≤
        taoLittlewoodWidth U (taoLittlewoodR U) ∧
      Real.log U ≤ 2 * Real.log T := by
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 eventually_taoNearbyFrequencyConditions
  exact ⟨T₀, fun T U hT hU => hT₀ T hT U hU⟩

end

end Erdos1212Kernel
