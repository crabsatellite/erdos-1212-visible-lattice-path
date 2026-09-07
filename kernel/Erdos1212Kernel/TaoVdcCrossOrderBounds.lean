import Erdos1212Kernel.TaoVdcCrossOrderAlgebra

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1900000

theorem taoVdc_high_threshold_bound {k : Nat} (hk : 2 ≤ k) {N T : Real}
    (hN : 1 ≤ N) (hT : 0 < T)
    (hhigh : N ^ (taoVdcThreshold k) ≤ T) :
    taoVdcBareFirst k N T ≤ taoVdcSecond k N T := by
  have hNp : 0 < N := by linarith
  have hb := taoVdcBeta_pos hk
  let q := T / N ^ k
  have hq : 0 < q := by unfold q; positivity
  have hqlo : N ^ (taoVdcAlpha k - 2) ≤ q := by
    have hdiv := (div_le_div_iff_of_pos_right (pow_pos hNp k)).2 hhigh
    calc
      _ = N ^ (taoVdcThreshold k - (k : Real)) := by
        congr 1
        unfold taoVdcThreshold
        ring
      _ = N ^ (taoVdcThreshold k) / N ^ (k : Real) := Real.rpow_sub hNp _ _
      _ = N ^ (taoVdcThreshold k) / N ^ k := by rw [Real.rpow_natCast]
      _ ≤ T / N ^ k := hdiv
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hNp.le _) hqlo
    (show 0 ≤ 2 * taoVdcBeta k by positivity)
  have hcore : N ^ (-taoVdcAlpha k) ≤ q ^ (2 * taoVdcBeta k) := by
    calc
      _ = N ^ ((taoVdcAlpha k - 2) * (2 * taoVdcBeta k)) := by
        rw [taoVdc_high_exponent_identity hk]
      _ = (N ^ (taoVdcAlpha k - 2)) ^ (2 * taoVdcBeta k) :=
        Real.rpow_mul hNp.le _ _
      _ ≤ _ := hpow
  have hratio : N ^ k / T = q⁻¹ := by unfold q; field_simp
  have hbare : taoVdcBareFirst k N T =
      N ^ (-taoVdcAlpha k) * q ^ (-taoVdcBeta k) := by
    unfold taoVdcBareFirst
    rw [one_div, ← Real.rpow_neg hNp.le, hratio, Real.inv_rpow hq.le,
      ← Real.rpow_neg hq.le]
  have hmul : N ^ (-taoVdcAlpha k) * q ^ (-taoVdcBeta k) ≤
      q ^ (2 * taoVdcBeta k) * q ^ (-taoVdcBeta k) :=
    mul_le_mul_of_nonneg_right hcore (Real.rpow_nonneg hq.le _)
  rw [hbare]
  unfold taoVdcSecond
  change N ^ (-taoVdcAlpha k) * q ^ (-taoVdcBeta k) ≤ q ^ (taoVdcBeta k)
  calc
    _ ≤ q ^ (2 * taoVdcBeta k) * q ^ (-taoVdcBeta k) := hmul
    _ = q ^ (taoVdcBeta k) := by
      rw [← Real.rpow_add hq]
      congr 1
      ring

theorem taoVdc_low_threshold_bound {k : Nat} (hk : 3 ≤ k) {N T : Real}
    (hN : 1 ≤ N) (hT : 0 < T)
    (hlow : T ≤ N ^ (taoVdcThreshold k)) :
    taoVdcSecond (k - 1) N T ≤ taoVdcSecond k N T := by
  have hNp : 0 < N := by linarith
  have hprev : 2 ≤ k - 1 := by omega
  have hbp := taoVdcBeta_pos hprev
  have hb := taoVdcBeta_pos (by omega : 2 ≤ k)
  have hdiff : taoVdcBeta k - taoVdcBeta (k - 1) < 0 := by
    linarith [taoVdc_beta_strict_decrease hk]
  let q := T / N ^ k
  have hq : 0 < q := by unfold q; positivity
  have hqhi : q ≤ N ^ (taoVdcAlpha k - 2) := by
    have hdiv := (div_le_div_iff_of_pos_right (pow_pos hNp k)).2 hlow
    calc
      _ ≤ N ^ (taoVdcThreshold k) / N ^ k := hdiv
      _ = N ^ (taoVdcThreshold k) / N ^ (k : Real) := by rw [Real.rpow_natCast]
      _ = N ^ (taoVdcThreshold k - (k : Real)) := (Real.rpow_sub hNp _ _).symm
      _ = N ^ (taoVdcAlpha k - 2) := by
        congr 1
        unfold taoVdcThreshold
        ring
  have hrev := Real.rpow_le_rpow_of_nonpos hq hqhi hdiff.le
  have hcore : N ^ (taoVdcBeta (k - 1)) ≤
      q ^ (taoVdcBeta k - taoVdcBeta (k - 1)) := by
    calc
      _ = N ^ ((taoVdcAlpha k - 2) *
          (taoVdcBeta k - taoVdcBeta (k - 1))) := by
        rw [taoVdc_low_exponent_identity hk]
      _ = (N ^ (taoVdcAlpha k - 2)) ^
          (taoVdcBeta k - taoVdcBeta (k - 1)) := Real.rpow_mul hNp.le _ _
      _ ≤ _ := hrev
  have hprevRatio : T / N ^ (k - 1) = q * N := by
    unfold q
    have hpow : N ^ k = N ^ (k - 1) * N := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow]
    field_simp
  unfold taoVdcSecond
  rw [hprevRatio, Real.mul_rpow hq.le hNp.le]
  change q ^ (taoVdcBeta (k - 1)) * N ^ (taoVdcBeta (k - 1)) ≤
    q ^ (taoVdcBeta k)
  have hmul : q ^ (taoVdcBeta (k - 1)) * N ^ (taoVdcBeta (k - 1)) ≤
      q ^ (taoVdcBeta (k - 1)) * q ^ (taoVdcBeta k - taoVdcBeta (k - 1)) :=
    mul_le_mul_of_nonneg_left hcore (Real.rpow_nonneg hq.le _)
  calc
    _ ≤ q ^ (taoVdcBeta (k - 1)) *
        q ^ (taoVdcBeta k - taoVdcBeta (k - 1)) := hmul
    _ = q ^ (taoVdcBeta k) := by
      rw [← Real.rpow_add hq]
      congr 1
      ring

end

end Erdos1212Kernel
