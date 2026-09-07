import Erdos1212Kernel.TaoVdcExponents
import Erdos1212Kernel.TaoSecondDerivativeRate

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1500000

/-- The two terms displayed in Proposition 10, with the literal k,N,T
parameters. Alpha is 1/2^(k-2), beta is 1/(2^k-2). -/
def taoVdcRate (k : Nat) (N T : Real) : Real :=
  (1 / N ^ (taoVdcAlpha k)) * (N ^ k / T) ^ (taoVdcBeta k) *
      (Real.log (2 + T)) ^ (taoVdcAlpha k) + (T / N ^ k) ^ (taoVdcBeta k)

theorem taoVdcRate_pos (k : Nat) {N T : Real} (hN : 0 < N) (hT : 0 < T) :
    0 < taoVdcRate k N T := by
  have hL : 0 < Real.log (2 + T) := Real.log_pos (by linarith)
  unfold taoVdcRate
  positivity

theorem taoVdcRate_two {N T : Real} (hN : 0 < N) (hT : 0 < T) :
    taoVdcRate 2 N T = taoSecondDerivativeRate N T := by
  unfold taoVdcRate taoSecondDerivativeRate
  rw [taoVdcAlpha_two, taoVdcBeta_two]
  simp only [Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [Real.sqrt_div (sq_nonneg N), Real.sqrt_sq hN.le, Real.sqrt_div hT.le, Real.sqrt_sq hN.le]
  field_simp
  <;> ring

theorem taoVdc_amplitude_two (A : Real) : A ^ (2 * taoVdcAlpha 2) = A ^ 2 := by
  norm_num [taoVdcAlpha]

/-- Exact phase-scale change, before the sum in h. Only the source
monotonicity log(2+h*T/N)<=log(2+T) is used for the logarithmic term. -/
theorem taoVdcRate_difference_bound (k : Nat) {N T h : Real} (hN : 0 < N) (hT : 0 < T)
    (hh : 0 < h) (hhN : h ≤ N) :
    taoVdcRate k N (h * T / N) ≤
      ((1 / N ^ (taoVdcAlpha k)) * (N ^ (k + 1) / T) ^ (taoVdcBeta k) *
        (Real.log (2 + T)) ^ (taoVdcAlpha k)) * h ^ (-taoVdcBeta k) +
      (T / N ^ (k + 1)) ^ (taoVdcBeta k) * h ^ (taoVdcBeta k) := by
  have hnew : 0 < h * T / N := by positivity
  have hsmall : h * T / N ≤ T := (div_le_iff₀ hN).2 (by nlinarith [mul_le_mul_of_nonneg_right hhN hT.le])
  have hlog : Real.log (2 + h * T / N) ≤ Real.log (2 + T) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlogpow := Real.rpow_le_rpow (Real.log_nonneg (by linarith : 1 ≤ 2 + h * T / N)) hlog (taoVdcAlpha_pos k).le
  have hfirst : N ^ k / (h * T / N) = (N ^ (k + 1) / T) / h := by rw [pow_succ]; field_simp
    <;> ring
  have hsecond : (h * T / N) / N ^ k = (T / N ^ (k + 1)) * h := by rw [pow_succ]; field_simp
    <;> ring
  unfold taoVdcRate
  rw [hfirst, hsecond, Real.div_rpow (by positivity) hh.le, Real.mul_rpow (by positivity) hh.le,
    Real.rpow_neg hh.le]
  have hcoeff : 0 ≤ (1 / N ^ (taoVdcAlpha k)) * ((N ^ (k + 1) / T) ^ (taoVdcBeta k) / h ^ (taoVdcBeta k)) := by positivity
  calc
    _ ≤ (1 / N ^ (taoVdcAlpha k)) * ((N ^ (k + 1) / T) ^ (taoVdcBeta k) / h ^ (taoVdcBeta k)) *
        (Real.log (2 + T)) ^ (taoVdcAlpha k) + (T / N ^ (k + 1)) ^ (taoVdcBeta k) * h ^ (taoVdcBeta k) :=
      add_le_add (mul_le_mul_of_nonneg_left hlogpow hcoeff) le_rfl
    _ = _ := by ring

end

end Erdos1212Kernel
