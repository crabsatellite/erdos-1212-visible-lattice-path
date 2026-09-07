import Erdos1212Kernel.TaoZetaZeroFreeParameter

namespace Erdos1212Kernel

noncomputable section

open Metric

set_option maxHeartbeats 1900000

theorem taoLogFrequency_two_mul (t : Real) :
    taoLogFrequency (2 * t) = 2 * taoLogFrequency t := by
  unfold taoLogFrequency
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
  ring

/-- Pointwise high-frequency zero exclusion after all eventual scalar
conditions have been isolated. -/
theorem riemannZeta_ne_zero_of_pointwise_zeroFree_conditions
    {a t β δ : Real} (ha : 0 < a)
    (hsmall : a * taoCanonicalResidualConstant (20 * a / 21) ≤ 1 / 100)
    (hδ : 0 < δ)
    (hpole : ∀ σ : Real, 1 < σ → σ - 1 < δ →
      ‖taoZetaLogDerivative (σ : Complex)‖ ≤ 9 / (8 * (σ - 1)))
    (hnear1 : ∀ U ∈ Set.Icc (taoLogFrequency t - 1)
        (taoLogFrequency t + 1),
      TaoLittlewoodFinalFrequencyConditions U ∧
      4 ≤ U ∧ 1 ≤ Real.log U ∧
      taoZeroFreeBaseRadius (taoLogFrequency t) / 4 ≤
        taoLittlewoodWidth U (taoLittlewoodR U) ∧
      Real.log U ≤ 2 * Real.log (taoLogFrequency t))
    (hnear2 : ∀ U ∈ Set.Icc (taoLogFrequency (2 * t) - 1)
        (taoLogFrequency (2 * t) + 1),
      TaoLittlewoodFinalFrequencyConditions U ∧
      4 ≤ U ∧ 1 ≤ Real.log U ∧
      taoZeroFreeBaseRadius (taoLogFrequency (2 * t)) / 4 ≤
        taoLittlewoodWidth U (taoLittlewoodR U) ∧
      Real.log U ≤ 2 * Real.log (taoLogFrequency (2 * t)))
    (hL1 : 1 < Real.log (taoLogFrequency t))
    (hll1 : 1 ≤ Real.log (Real.log (taoLogFrequency t)))
    (hL2 : 1 < Real.log (taoLogFrequency (2 * t)))
    (hll2 : 1 ≤ Real.log (Real.log (taoLogFrequency (2 * t))))
    (hlogRatio : Real.log (taoLogFrequency (2 * t)) ≤
      (21 / 20 : Real) * Real.log (taoLogFrequency t))
    (hηhalf : a / Real.log (taoLogFrequency (2 * t)) ≤ 1 / 2)
    (hηδ : a / Real.log (taoLogFrequency (2 * t)) < δ)
    (hqhalf1 : taoZeroFreeBaseRadius (taoLogFrequency t) / 4 ≤ 1 / 2)
    (hqhalf2 : taoZeroFreeBaseRadius (taoLogFrequency (2 * t)) / 4 ≤ 1 / 2)
    (hqimag1 : taoZeroFreeBaseRadius (taoLogFrequency t) / 4 < |t|)
    (hqimag2 : taoZeroFreeBaseRadius (taoLogFrequency (2 * t)) / 4 < |2 * t|)
    (hkernelScale :
      4 * (a / Real.log (taoLogFrequency (2 * t)) +
        a / (100 * Real.log (taoLogFrequency t))) ≤
          taoZeroFreeBaseRadius (taoLogFrequency t) / 8)
    (hβ : 1 - a / (100 * Real.log (taoLogFrequency t)) < β) :
    riemannZeta ((β : Complex) + (t : Complex) * Complex.I) ≠ 0 := by
  let T : Real := taoLogFrequency t
  let T2 : Real := taoLogFrequency (2 * t)
  let L : Real := Real.log T
  let L2 : Real := Real.log T2
  let amin : Real := 20 * a / 21
  let η : Real := a / L2
  let σ : Real := 1 + η
  let Q : Real := taoCanonicalResidualConstant amin
  have ht : t ≠ 0 := by
    intro ht
    subst t
    norm_num [taoLogFrequency] at hL1
  have hTpos : 0 < T := by simpa only [T] using taoLogFrequency_pos ht
  have hT2pos : 0 < T2 := by
    dsimp only [T2]
    rw [taoLogFrequency_two_mul]
    positivity
  have hLpos : 0 < L := by unfold L; linarith
  have hL2pos : 0 < L2 := by unfold L2; linarith
  have hamin : 0 < amin := by unfold amin; positivity
  have hη : 0 < η := by unfold η; positivity
  have hσ : 1 < σ := by unfold σ; linarith
  have hLleL2 : L ≤ L2 := by
    have hfreq : T ≤ T2 := by
      dsimp only [T2, T]
      rw [taoLogFrequency_two_mul]
      linarith
    exact Real.log_le_log hTpos hfreq
  have hηlower1 : amin / L ≤ η := by
    unfold amin η
    apply (div_le_div_iff₀ hLpos hL2pos).2
    have h := mul_le_mul_of_nonneg_left hlogRatio ha.le
    dsimp only [L, L2] at h ⊢
    nlinarith
  have hηlower2 : amin / L2 ≤ η := by
    unfold amin η
    apply div_le_div_of_nonneg_right (by linarith) hL2pos.le
  obtain ⟨R1, G1, hR1, hSphere1, hG1nz, hexact1, hE1⟩ :=
    exists_taoCanonicalAdjustedResidual_common_shift t η amin hamin hL1 hll1
      hqhalf1 hηhalf hqimag1 (by simpa only [L, η] using hηlower1) hnear1
  obtain ⟨R2, G2, hR2, hSphere2, hG2nz, hexact2, hE2⟩ :=
    exists_taoCanonicalAdjustedResidual_common_shift (2 * t) η amin hamin hL2 hll2
      hqhalf2 hηhalf hqimag2 (by simpa only [L2, η] using hηlower2) hnear2
  intro hzero
  have hβone := taoZetaZero_re_lt_one hzero
  have hβσ : β < σ := by
    have hre := hβone
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero] at hre
    unfold σ
    linarith
  let d : Real := σ - β
  have hd : 0 < d := by unfold d; linarith
  have hdupper : d < η + a / (100 * L) := by
    unfold d σ
    dsimp only [L] at hβ ⊢
    linarith
  have hquarter : 4 * d ≤ R1 := by
    have hRlower := hR1.1
    dsimp only [d, σ, η, L, L2, T, T2] at hkernelScale hRlower ⊢
    linarith
  have hρU : (β : Complex) + (t : Complex) * Complex.I ∈
      closedBall ((σ : Complex) + (t : Complex) * Complex.I) R1 := by
    rw [mem_closedBall, dist_same_imaginary_part]
    rw [abs_of_pos (by unfold σ; linarith : 0 < σ - β)]
    unfold d at hquarter
    linarith
  have hL0 := hpole σ hσ (by
    simpa only [σ, add_sub_cancel_left, η, L2] using hηδ)
  have hrep := fifteen_div_four_gap_le_sharpRealCenter_and_adjustedResidualNorm
    hσ (show 0 < R1 by
      have hq := taoZeroFreeBaseRadius_pos hL1
      linarith [hR1.1]) (show 0 < R2 by
      have hq := taoZeroFreeBaseRadius_pos hL2
      linarith [hR2.1])
    (closedBall_avoids_one_of_radius_lt_abs_imaginary (hR1.2.trans hqimag1))
    (closedBall_avoids_one_of_radius_lt_abs_imaginary (hR2.2.trans hqimag2))
    hβσ hzero hρU hquarter hL0
    (E1 := logDeriv G1 ((σ : Complex) + (t : Complex) * Complex.I))
    (E2 := logDeriv G2 ((σ : Complex) + ((2 * t : Real) : Complex) * Complex.I))
    (by simpa only [σ, η] using hexact1)
    (by simpa only [σ, η] using hexact2)
  have hQ : 0 ≤ Q := by
    unfold Q taoCanonicalResidualConstant
    have hlog2 := Real.log_nonneg (by norm_num : (1 : Real) ≤ 2)
    have haminv : 0 ≤ 1 / amin := by positivity
    have hloga := Real.log_nonneg (by linarith : (1 : Real) ≤ 1 + 1 / amin)
    positivity
  have hQbound : Q ≤ 1 / (100 * a) := by
    have hs := hsmall
    change a * Q ≤ 1 / 100 at hs
    calc
      Q ≤ (1 / 100) / a := (le_div_iff₀ ha).2 (by simpa only [mul_comm] using hs)
      _ = 1 / (100 * a) := by field_simp [ha.ne']
  have hE1' :
      ‖logDeriv G1 ((σ : Complex) + (t : Complex) * Complex.I)‖ ≤ Q * L := by
    simpa only [Q, amin, L, σ, η] using hE1
  have hE2' :
      ‖logDeriv G2 ((σ : Complex) + ((2 * t : Real) : Complex) * Complex.I)‖ ≤
        Q * L2 := by
    simpa only [Q, amin, L2, σ, η] using hE2
  have hE1upper :
      4 * ‖logDeriv G1 ((σ : Complex) + (t : Complex) * Complex.I)‖ ≤
        4 * (1 / (100 * a)) * L := by
    have hQL : Q * L ≤ (1 / (100 * a)) * L :=
      mul_le_mul_of_nonneg_right hQbound hLpos.le
    nlinarith
  have hE2upper :
      ‖logDeriv G2 ((σ : Complex) + ((2 * t : Real) : Complex) * Complex.I)‖ ≤
        (1 / (100 * a)) * ((21 / 20 : Real) * L) := by
    exact hE2'.trans ((mul_le_mul_of_nonneg_left hlogRatio hQ).trans
      (mul_le_mul_of_nonneg_right hQbound (by positivity : 0 ≤ (21 / 20 : Real) * L)))
  have hpoleEq : 27 / (8 * (σ - 1)) = 27 * L2 / (8 * a) := by
    unfold σ η
    field_simp [ha.ne', hL2pos.ne']
    ring
  rw [hpoleEq] at hrep
  have hrepUpper : 15 / (4 * d) ≤
      (567 / (160 * a) + 101 / (2000 * a)) * L := by
    have hpoleUpper : 27 * L2 / (8 * a) ≤ 567 * L / (160 * a) := by
      apply (div_le_div_iff₀ (by positivity : 0 < 8 * a)
        (by positivity : 0 < 160 * a)).2
      nlinarith
    have := hrep.trans (add_le_add (add_le_add hpoleUpper hE1upper) hE2upper)
    dsimp only [d] at this ⊢
    convert this using 1 <;> ring
  have hηupper : η ≤ a / L := by
    unfold η
    exact div_le_div_of_nonneg_left ha.le hLpos hLleL2
  have hd101 : d < 101 * a / (100 * L) := by
    calc
      d < η + a / (100 * L) := hdupper
      _ ≤ a / L + a / (100 * L) := add_le_add hηupper le_rfl
      _ = 101 * a / (100 * L) := by ring
  have hinv := one_div_lt_one_div_of_lt hd (by
    exact hd101)
  have hlower : (375 / (101 * a)) * L < 15 / (4 * d) := by
    calc
      (375 / (101 * a)) * L =
          (15 / 4) * (1 / (101 * a / (100 * L))) := by
        field_simp [ha.ne', hLpos.ne']
        ring
      _ < (15 / 4) * (1 / d) :=
        mul_lt_mul_of_pos_left hinv (by norm_num : (0 : Real) < 15 / 4)
      _ = 15 / (4 * d) := by ring
  have hnumeric :
      (567 / (160 * a) + 101 / (2000 * a)) * L <
        (375 / (101 * a)) * L := by
    have hLa : 0 < L / a := div_pos hLpos ha
    have hcoeff : (567 / 160 : Real) + 101 / 2000 < 375 / 101 := by norm_num
    calc
      (567 / (160 * a) + 101 / (2000 * a)) * L =
          ((567 / 160 : Real) + 101 / 2000) * (L / a) := by
        field_simp [ha.ne']
      _ < (375 / 101 : Real) * (L / a) :=
        mul_lt_mul_of_pos_right hcoeff hLa
      _ = (375 / (101 * a)) * L := by
        field_simp [ha.ne']
  linarith

end

end Erdos1212Kernel
