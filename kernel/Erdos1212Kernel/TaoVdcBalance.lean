import Erdos1212Kernel.TaoVdcShiftChoice

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1700000

def taoVdcFirst (k : Nat) (N T : Real) : Real :=
  (1 / N ^ (taoVdcAlpha k)) * (N ^ k / T) ^ (taoVdcBeta k) *
    (Real.log (2 + T)) ^ (taoVdcAlpha k)

def taoVdcSecond (k : Nat) (N T : Real) : Real := (T / N ^ k) ^ (taoVdcBeta k)

theorem taoVdcRate_split (k : Nat) (N T : Real) :
    taoVdcRate k N T = taoVdcFirst k N T + taoVdcSecond k N T := rfl

theorem taoVdc_beta_balance {k : Nat} (hk : 2 ≤ k) :
    taoVdcBeta k * (1 - 2 * taoVdcBeta (k + 1)) = 2 * taoVdcBeta (k + 1) := by
  rw [taoVdcBeta_succ hk]
  have hb := taoVdcBeta_pos hk
  field_simp
  <;> ring

theorem taoVdc_ratio_inverse (k : Nat) (p : Real) {N T : Real} (hN : 0 < N) (hT : 0 < T) :
    (T / N ^ k) ^ p = (N ^ k / T) ^ (-p) := by
  have he : T / N ^ k = (N ^ k / T)⁻¹ := by field_simp
  rw [he, ← Real.rpow_neg_eq_inv_rpow]

theorem taoVdc_first_balance {k : Nat} (hk : 2 ≤ k) {N T : Real} (hN : 0 < N) (hT : 0 < T) :
    ((1 / N ^ (taoVdcAlpha k)) * (N ^ (k + 1) / T) ^ (taoVdcBeta k) *
      (Real.log (2 + T)) ^ (taoVdcAlpha k)) * (taoVdcRealShift (k + 1) N T) ^ (-taoVdcBeta k) =
        (taoVdcFirst (k + 1) N T) ^ 2 := by
  have hQ : 0 < N ^ (k + 1) / T := by positivity
  have hL : 0 < Real.log (2 + T) := Real.log_pos (by linarith)
  have ha : taoVdcAlpha k = 2 * taoVdcAlpha (k + 1) := by rw [taoVdcAlpha_succ hk]; ring
  have hNpow : N ^ (taoVdcAlpha k) = (N ^ (taoVdcAlpha (k + 1))) ^ 2 := by
    rw [ha, mul_comm 2, Real.rpow_mul hN.le, Real.rpow_two]
  have hLpow : (Real.log (2 + T)) ^ (taoVdcAlpha k) = ((Real.log (2 + T)) ^ (taoVdcAlpha (k + 1))) ^ 2 := by
    rw [ha, mul_comm 2, Real.rpow_mul hL.le, Real.rpow_two]
  have hQpow : (N ^ (k + 1) / T) ^ (2 * taoVdcBeta (k + 1)) =
      ((N ^ (k + 1) / T) ^ (taoVdcBeta (k + 1))) ^ 2 := by
    rw [mul_comm 2, Real.rpow_mul hQ.le, Real.rpow_two]
  have hcombine : (N ^ (k + 1) / T) ^ (taoVdcBeta k) *
      ((N ^ (k + 1) / T) ^ (2 * taoVdcBeta (k + 1))) ^ (-taoVdcBeta k) =
        (N ^ (k + 1) / T) ^ (2 * taoVdcBeta (k + 1)) := by
    rw [← Real.rpow_mul hQ.le, ← Real.rpow_add hQ]
    congr 1
    nlinarith [taoVdc_beta_balance hk]
  unfold taoVdcRealShift taoVdcFirst
  calc
    _ = (1 / N ^ (taoVdcAlpha k)) * ((N ^ (k + 1) / T) ^ (taoVdcBeta k) *
        ((N ^ (k + 1) / T) ^ (2 * taoVdcBeta (k + 1))) ^ (-taoVdcBeta k)) *
        (Real.log (2 + T)) ^ (taoVdcAlpha k) := by ring
    _ = (1 / N ^ (taoVdcAlpha k)) * (N ^ (k + 1) / T) ^ (2 * taoVdcBeta (k + 1)) *
        (Real.log (2 + T)) ^ (taoVdcAlpha k) := by rw [hcombine]
    _ = _ := by rw [hNpow, hLpow, hQpow]; ring

theorem taoVdc_second_balance {k : Nat} (hk : 2 ≤ k) {N T : Real} (hN : 0 < N) (hT : 0 < T) :
    (T / N ^ (k + 1)) ^ (taoVdcBeta k) * (taoVdcRealShift (k + 1) N T) ^ (taoVdcBeta k) =
      (taoVdcSecond (k + 1) N T) ^ 2 := by
  have hQ : 0 < N ^ (k + 1) / T := by positivity
  unfold taoVdcRealShift taoVdcSecond
  rw [taoVdc_ratio_inverse (k + 1) (taoVdcBeta k) hN hT,
    taoVdc_ratio_inverse (k + 1) (taoVdcBeta (k + 1)) hN hT,
    ← Real.rpow_mul hQ.le, ← Real.rpow_add hQ, ← Real.rpow_two, ← Real.rpow_mul hQ.le]
  congr 1
  nlinarith [taoVdc_beta_balance hk]

theorem taoVdc_amplitude_square {k : Nat} (hk : 2 ≤ k) {A : Real} (hA : 0 ≤ A) :
    A ^ (2 * taoVdcAlpha k) = (A ^ (2 * taoVdcAlpha (k + 1))) ^ 2 := by
  rw [← Real.rpow_two, ← Real.rpow_mul hA, taoVdcAlpha_succ hk]
  congr 1
  ring

theorem taoVdcShift_root_bound {k : Nat} (hk : 3 ≤ k) {N : Nat} {T : Real}
    (hN : 0 < N) (hT : 1 ≤ T) (hupper : T ≤ (N : Real) ^ k) :
    1 / Real.sqrt (taoVdcShift k N T : Real) ≤ 2 * taoVdcSecond k N T := by
  have hNp : 0 < (N : Real) := by exact_mod_cast hN
  have hTp : 0 < T := by linarith
  have hH := taoVdcShift_negative_power hk hN hT hupper (by norm_num : (0 : Real) ≤ 1 / 2) (by norm_num : (1 : Real) / 2 ≤ 1)
  have hleft : (taoVdcShift k N T : Real) ^ (-(1 / 2 : Real)) = 1 / Real.sqrt (taoVdcShift k N T : Real) := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, one_div]
  have hright : (taoVdcRealShift k N T) ^ (-(1 / 2 : Real)) = taoVdcSecond k N T := by
    unfold taoVdcRealShift taoVdcSecond
    rw [← Real.rpow_mul (by positivity), taoVdc_ratio_inverse k (taoVdcBeta k) hNp hTp]
    congr 1
    ring
  simpa only [hleft, hright] using hH

end

end Erdos1212Kernel
