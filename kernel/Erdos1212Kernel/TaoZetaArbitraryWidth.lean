import Erdos1212Kernel.TaoZetaScaledResidual
import Erdos1212Kernel.TaoZetaZeroFreeRegion

namespace Erdos1212Kernel

noncomputable section

open Filter Metric Topology

set_option maxHeartbeats 800000

theorem taoCanonicalResidualConstant_pos {a : Real} (ha : 0 < a) :
    0 < taoCanonicalResidualConstant a := by
  have hlog2 := Real.log_nonneg (by norm_num : (1 : Real) ≤ 2)
  have hinv : 0 ≤ 1 / a := by positivity
  have hloga := Real.log_nonneg (by linarith : (1 : Real) ≤ 1 + 1 / a)
  unfold taoCanonicalResidualConstant
  positivity

/-- The full Littlewood width yields every fixed zero-free coefficient
at a sufficiently large height, without an unproved zero-free premise. -/
theorem exists_riemannZeta_zero_free_region_any_coefficient (c : Real) (hc : 0 < c) :
    ∃ T₀ : Real, ∀ (t β : Real), T₀ ≤ taoLogFrequency t →
      1 - c / Real.log (taoLogFrequency t) < β →
      riemannZeta ((β : Complex) + (t : Complex) * Complex.I) ≠ 0 := by
  let a : Real := 100 * c
  let Q : Real := taoCanonicalResidualConstant a
  let D : Real := 100 * a * Q + 1
  have ha : 0 < a := by dsimp [a]; positivity
  have hQ : 0 < Q := taoCanonicalResidualConstant_pos ha
  have hD1 : 1 ≤ D := by
    have hm : 0 ≤ 100 * a * Q := by positivity
    dsimp [D]
    linarith only [hm]
  have hD : 0 < D := by linarith
  have hQsmall : Q / D ≤ 1 / (100 * a) := by
    apply (div_le_div_iff₀ hD (by positivity : 0 < 100 * a)).mpr
    dsimp [D]
    nlinarith only
  obtain ⟨δ, hδ, hpole⟩ := exists_norm_taoZetaLogDerivative_real_le_nine_eighth
  have hqt : Tendsto (fun T : Real => D * taoZeroFreeBaseRadius T / 4) atTop (nhds 0) := by
    simpa using (tendsto_taoZeroFreeBaseRadius.const_mul D).div_const 4
  have hqsmall : ∀ᶠ T : Real in atTop, D * taoZeroFreeBaseRadius T / 4 ≤ 1 / 2 :=
    ((tendsto_order.1 hqt).2 (1 / 2) (by norm_num)).mono (fun _ h => h.le)
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.1
    ((eventually_taoScaledNearbyFrequencyConditions D hD.le).and hqsmall)
  have hevent : ∀ᶠ T : Real in atTop, B ≤ T ∧ 1 ≤ T ∧
      1 < Real.log T ∧ max 1 (4000 * a) ≤ Real.log (Real.log T) ∧
      max (2 * a) (a / δ + 1) ≤ Real.log T ∧ Real.log 2 ≤ Real.log T := by
    filter_upwards [eventually_ge_atTop B, eventually_ge_atTop 1,
      Real.tendsto_log_atTop.eventually_gt_atTop 1,
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (max 1 (4000 * a)),
      Real.tendsto_log_atTop.eventually_ge_atTop (max (2 * a) (a / δ + 1)),
      Real.tendsto_log_atTop.eventually_ge_atTop (Real.log 2)] with T hB hT hL hll hshift h2
    exact ⟨hB, hT, hL, hll, hshift, h2⟩
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨T₀, ?_⟩
  intro t β ht hβ
  let T := taoLogFrequency t
  let T2 := taoLogFrequency (2 * t)
  let L := Real.log T
  let L2 := Real.log T2
  let η := a / L
  let σ := 1 + η
  obtain ⟨hBT, hT1, hL, hll, hshift, hlog2⟩ := hT₀ T ht
  have hTpos : 0 < T := by linarith
  have hT2eq : T2 = 2 * T := taoLogFrequency_two_mul t
  have hBT2 : B ≤ T2 := by rw [hT2eq]; linarith
  obtain ⟨hnear1, hqhalf1⟩ := hB T hBT
  obtain ⟨hnear2, hqhalf2⟩ := hB T2 hBT2
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hL2eq : L2 = Real.log 2 + L := by
    dsimp [L2]
    rw [hT2eq, Real.log_mul (by norm_num : (2 : Real) ≠ 0) hTpos.ne']
  have hLL2 : L ≤ L2 := by
    rw [hL2eq]
    have hlog2pos := Real.log_nonneg (by norm_num : (1 : Real) ≤ 2)
    linarith
  have hL2upper : L2 ≤ 2 * L := by rw [hL2eq]; linarith
  have hL2strict : 1 < L2 := hL.trans_le hLL2
  have hL2pos : 0 < L2 := by linarith
  have hll1 : 1 ≤ Real.log L := (le_max_left _ _).trans hll
  have hll2 : 1 ≤ Real.log L2 := hll1.trans (Real.log_le_log hLpos hLL2)
  have hηpos : 0 < η := div_pos ha hLpos
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hηhalf : η ≤ 1 / 2 := by
    apply (div_le_iff₀ hLpos).mpr
    have hh := (le_max_left _ _).trans hshift
    linarith
  have hηδ : η < δ := by
    apply (div_lt_iff₀ hLpos).mpr
    have hh := (le_max_right _ _).trans hshift
    have hd := (div_le_iff₀ hδ).mp (show a / δ ≤ L - 1 by linarith)
    nlinarith only [hd, hδ]
  have hηlower2 : a / L2 ≤ η := div_le_div_of_nonneg_left ha.le hLpos hLL2
  have habs : |t| = 2 * Real.pi * T := by dsimp [T, taoLogFrequency]; field_simp
  have habs2 : |2 * t| = 2 * Real.pi * T2 := by dsimp [T2, taoLogFrequency]; field_simp
  have hqimag1 : D * taoZeroFreeBaseRadius T / 4 < |t| := by
    rw [habs]
    nlinarith only [hqhalf1, hT1, Real.pi_gt_three]
  have hqimag2 : D * taoZeroFreeBaseRadius T2 / 4 < |2 * t| := by
    rw [habs2]
    have hT21 : 1 ≤ T2 := by rw [hT2eq]; linarith only [hT1]
    nlinarith only [hqhalf2, hT21, Real.pi_gt_three]
  obtain ⟨R1, G1, hR1, _hG1, heq1, hE1⟩ := exists_taoScaledAdjustedResidual_common_shift
    D t η a hD ha hL hll1 hqhalf1 hηhalf hqimag1 le_rfl hnear1
  obtain ⟨R2, G2, hR2, _hG2, heq2, hE2⟩ := exists_taoScaledAdjustedResidual_common_shift
    D (2 * t) η a hD ha hL2strict hll2 hqhalf2 hηhalf hqimag2 hηlower2 hnear2
  have hR1pos : 0 < R1 :=
    (div_pos (mul_pos hD (taoZeroFreeBaseRadius_pos hL)) (by norm_num)).trans hR1.1
  have hR2pos : 0 < R2 :=
    (div_pos (mul_pos hD (taoZeroFreeBaseRadius_pos hL2strict)) (by norm_num)).trans hR2.1
  intro hzero
  have hβone : β < 1 := by simpa using taoZetaZero_re_lt_one hzero
  have hβσ : β < σ := hβone.trans hσ
  let g := σ - β
  have hg : 0 < g := sub_pos.mpr hβσ
  have hac : c = a / 100 := by dsimp [a]; ring
  have hgupper : g < 101 * a / (100 * L) := by
    calc
      g < η + c / L := by dsimp [g, σ]; linarith only [hβ]
      _ = 101 * a / (100 * L) := by rw [hac]; dsimp [η]; ring
  have hkernel : 4 * (101 * a / (100 * L)) ≤ D * taoZeroFreeBaseRadius T / 8 := by
    have hlllarge : 4000 * a ≤ Real.log L := (le_max_right _ _).trans hll
    have hbasepos := (taoZeroFreeBaseRadius_pos hL).le
    have hbaseD : taoZeroFreeBaseRadius T ≤ D * taoZeroFreeBaseRadius T := by
      nlinarith only [hD1, hbasepos]
    apply le_trans _ (div_le_div_of_nonneg_right hbaseD (by norm_num : (0 : Real) ≤ 8))
    unfold taoZeroFreeBaseRadius
    change 4 * (101 * a / (100 * L)) ≤ Real.log L / (100 * L) / 8
    rw [div_div]
    apply (le_div_iff₀ (show 0 < (100 * L) * 8 by positivity)).mpr
    have heq : (4 * (101 * a / (100 * L))) * ((100 * L) * 8) = 3232 * a := by
      field_simp [hLpos.ne']
      <;> ring
    rw [heq]
    linarith only [hlllarge, ha]
  have hquarter : 4 * (σ - β) ≤ R1 := by
    change 4 * g ≤ R1
    linarith [hR1.1]
  have hρmem : (β : Complex) + (t : Complex) * Complex.I ∈
      closedBall ((σ : Complex) + (t : Complex) * Complex.I) R1 := by
    rw [mem_closedBall, dist_same_imaginary_part, abs_of_pos (sub_pos.mpr hβσ)]
    linarith
  have hreal := hpole σ hσ (by simpa only [σ, add_sub_cancel_left] using hηδ)
  have hrep := fifteen_div_four_gap_le_sharpRealCenter_and_adjustedResidualNorm hσ hR1pos hR2pos
    (closedBall_avoids_one_of_radius_lt_abs_imaginary (hR1.2.trans hqimag1))
    (closedBall_avoids_one_of_radius_lt_abs_imaginary (hR2.2.trans hqimag2))
    hβσ hzero hρmem hquarter hreal heq1 heq2
  have hE1upper : ‖logDeriv G1 ((σ : Complex) + (t : Complex) * Complex.I)‖ ≤ L / (100 * a) := by
    have hh := hE1.trans (mul_le_mul_of_nonneg_right hQsmall hLpos.le)
    convert hh using 1 <;> ring
  have hE2upper : ‖logDeriv G2 ((σ : Complex) + ((2 * t : Real) : Complex) * Complex.I)‖ ≤
      2 * L / (100 * a) := by
    have hh := hE2.trans (mul_le_mul_of_nonneg_right hQsmall hL2pos.le)
    have hm := mul_le_mul_of_nonneg_left hL2upper (by positivity : 0 ≤ 1 / (100 * a))
    have hz := hh.trans hm
    convert hz using 1 <;> ring
  have hpoleeq : 27 / (8 * (σ - 1)) = (27 / 8 : Real) * (L / a) := by
    dsimp [σ, η]
    field_simp [ha.ne', hLpos.ne']
    <;> ring
  rw [hpoleeq] at hrep
  have hupper : 15 / (4 * g) ≤ ((27 / 8 : Real) + 6 / 100) * (L / a) := by
    have hh := hrep.trans (add_le_add (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hE1upper (by norm_num))) hE2upper)
    convert hh using 1 <;> ring
  have hinv := one_div_lt_one_div_of_lt hg hgupper
  have hlower : (375 / 101 : Real) * (L / a) < 15 / (4 * g) := by
    have hh := mul_lt_mul_of_pos_left hinv (by norm_num : (0 : Real) < 15 / 4)
    convert hh using 1 <;> field_simp [ha.ne', hLpos.ne'] <;> ring
  have hnumeric : ((27 / 8 : Real) + 6 / 100) * (L / a) < (375 / 101 : Real) * (L / a) :=
    mul_lt_mul_of_pos_right (by norm_num) (div_pos hLpos ha)
  linarith

end

end Erdos1212Kernel
