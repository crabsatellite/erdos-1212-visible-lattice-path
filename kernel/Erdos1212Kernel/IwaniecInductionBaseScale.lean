import Erdos1212Kernel.IwaniecInductionExponentialError
import Erdos1212Kernel.IwaniecAuxiliaryLemmaNine
import Erdos1212Kernel.IwaniecAuxiliaryMonotonicity

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 650000

theorem eventually_iwaniecXi_exponent_le_quarter_log {D : Real} (hD : 0 ≤ D) :
    ∀ᶠ y : Real in atTop, 1 < Real.log y ∧ 2 ≤ iwaniecPaperXi y ∧
      iwaniecPaperXi y * Real.log (iwaniecPaperXi y) +
        iwaniecPaperXi y * Real.log (Real.log (iwaniecPaperXi y)) + D * iwaniecPaperXi y ≤ Real.log y / 4 := by
  filter_upwards [eventually_gt_atTop (1 : Real), Real.tendsto_log_atTop.eventually_gt_atTop 1,
    tendsto_iwaniecPaperXi_atTop.eventually_ge_atTop (Real.exp 1),
    tendsto_iwaniecLogLogThree_atTop.eventually_ge_atTop (max 16 (8 * D))]
    with y hy hL hξ hu
  let u := Real.log (Real.log (3 * y))
  let ξ := iwaniecPaperXi y
  have hu16 : 16 ≤ u := (le_max_left _ _).trans hu
  have huD : 8 * D ≤ u := (le_max_right _ _).trans hu
  have hu0 : 0 < u := by linarith
  have hξ2 : 2 ≤ ξ := Real.exp_one_gt_two.le.trans hξ
  have hξ0 : 0 < ξ := by linarith
  have hlogξ1 : 1 ≤ Real.log ξ := by
    have hh := Real.log_le_log (Real.exp_pos 1) hξ
    simpa only [Real.log_exp] using hh
  have hlogξu : Real.log ξ ≤ u := by
    have hh := Real.log_le_log hξ0 (iwaniecPaperXi_le_exp_loglog hy (by linarith))
    simpa only [Real.log_exp] using hh
  have hloglog : Real.log (Real.log ξ) ≤ u := by
    have hh := Real.log_le_sub_one_of_pos (show 0 < Real.log ξ by linarith)
    linarith
  have hpow : u ^ 2 ≤ u ^ (11 / 5 : Real) := by
    have hh := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ u by linarith) (show (2 : Real) ≤ 11 / 5 by norm_num)
    simpa only [Real.rpow_two] using hh
  have hcoef : 2 * u + D ≤ u ^ (11 / 5 : Real) / 4 := by
    have hquad : 0 ≤ u * (u - 16) := mul_nonneg hu0.le (sub_nonneg.mpr hu16)
    nlinarith only [hquad, huD, hu16, hpow]
  have hscale : ξ * u ^ (11 / 5 : Real) = Real.log y := by
    change (Real.log y / u ^ (11 / 5 : Real)) * u ^ (11 / 5 : Real) = Real.log y
    exact div_mul_cancel₀ _ (Real.rpow_pos_of_pos hu0 (11 / 5 : Real)).ne'
  refine ⟨hL, hξ2, ?_⟩
  calc
    _ ≤ ξ * (2 * u + D) := by
      have h1 := mul_le_mul_of_nonneg_left hlogξu hξ0.le
      have h2 := mul_le_mul_of_nonneg_left hloglog hξ0.le
      nlinarith only [h1, h2]
    _ ≤ ξ * (u ^ (11 / 5 : Real) / 4) := mul_le_mul_of_nonneg_left hcoef hξ0.le
    _ = Real.log y / 4 := by rw [← mul_div_assoc, hscale]

/-- The original base-rank scale (4.7), with an arbitrary fixed positive
coefficient in the source exponent. -/
theorem eventually_iwaniec_source_four_seven {D : Real} (hD : 0 ≤ D) :
    ∀ᶠ y : Real in atTop, 1 < y ∧ 2 ≤ iwaniecPaperXi y ∧
      Real.log y ^ 2 / Real.sqrt y <
        Real.exp (-iwaniecPaperXi y * Real.log (iwaniecPaperXi y) -
          iwaniecPaperXi y * Real.log (Real.log (iwaniecPaperXi y)) - D * iwaniecPaperXi y) := by
  have hlim := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  have hsmall := hlim.eventually (Iio_mem_nhds (show (0 : Real) < 1 / 16 by norm_num))
  filter_upwards [eventually_gt_atTop (1 : Real), eventually_iwaniecXi_exponent_le_quarter_log hD, hsmall]
    with y hy hdata hlog
  let L := Real.log y
  have hL : 0 < L := Real.log_pos hy
  have hlogsmall : Real.log L ≤ L / 16 := by
    have hh := (div_lt_iff₀ hL).mp (show Real.log L / L < 1 / 16 from hlog)
    linarith only [hh]
  have hnum : Real.exp (2 * Real.log L) = L ^ 2 := by
    calc
      _ = Real.exp (Real.log L) ^ 2 := by simpa only [Nat.cast_ofNat] using Real.exp_nat_mul (Real.log L) 2
      _ = _ := by rw [Real.exp_log hL]
  have hroot : Real.sqrt y = Real.exp (L / 2) := by rw [Real.exp_half, Real.exp_log (show 0 < y by linarith)]
  refine ⟨hy, hdata.2.1, ?_⟩
  change L ^ 2 / Real.sqrt y < _
  rw [← hnum, hroot, ← Real.exp_sub]
  apply Real.exp_lt_exp.mpr
  have hF := hdata.2.2
  dsimp [L] at hlogsmall hL ⊢
  linarith only [hF, hlogsmall, hL]

theorem eventually_iwaniec_sqrt_le_aux_normalization :
    ∀ᶠ y : Real in atTop, 1 < y ∧ ∀ (rank : Nat) (s : Real),
      iwaniecAuxGStart rank ≤ s → s ≤ iwaniecPaperXi y →
        Real.sqrt y ≤ (y / Real.log y ^ 2) * iwaniecAuxG rank s := by
  obtain ⟨D, hD, hGbound⟩ := iwaniecAuxG_sharp_decay_bounds
  filter_upwards [eventually_iwaniec_source_four_seven hD.le] with y hy
  refine ⟨hy.1, ?_⟩
  intro rank s hs hsξ
  have hξ := (hGbound rank (iwaniecPaperXi y) hy.2.1).1
  have hG : Real.log y ^ 2 / Real.sqrt y ≤ iwaniecAuxG rank s := by
    have hmain : Real.log y ^ 2 / Real.sqrt y ≤ iwaniecAuxG rank (iwaniecPaperXi y) := by
      have hh := hy.2.2.le
      unfold iwaniecAuxSharpExponent at hξ
      exact hh.trans (by convert hξ using 1 <;> congr 1 <;> ring)
    exact hmain.trans (iwaniecAuxG_antitoneOn_exactDomain rank hs (hs.trans hsξ) hsξ)
  have hroot : 0 < Real.sqrt y := Real.sqrt_pos.mpr (by linarith [hy.1])
  have hfirst := (div_le_iff₀ hroot).mp hG
  have hsecond := mul_le_mul_of_nonneg_right hfirst hroot.le
  have hsq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt (by linarith [hy.1])
  rw [mul_assoc, ← pow_two, hsq] at hsecond
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos (Real.log_pos hy.1))).mpr
  nlinarith only [hsecond]

end

end Erdos1212Kernel
