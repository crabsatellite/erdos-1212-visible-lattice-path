import Erdos1212Kernel.TaoVdcBandRate

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1800000

theorem taoLogDerivativeHypotheses_short (t : Real) (k N M : Nat) (hN : 0 < N) (hMN : M ≤ N) :
    taoDerivativeHypotheses (taoLogDerivativeFamily t) k (N : Real) ((N : Real) + M)
      (taoLogDerivativeAmplitude k) N (taoLogFrequency t) := by
  have hNp : 0 < (N : Real) := by exact_mod_cast hN
  apply taoDerivativeHypotheses_restrict (taoLogDerivativeHypotheses t k hNp)
  intro x hx
  constructor
  · exact hx.1
  · have hMR : (M : Real) ≤ N := by exact_mod_cast hMN
    nlinarith [hx.2, hMR]

theorem taoLogDirichlet_short_vdc_bound (t : Real) (k N M : Nat)
    (hk : 2 ≤ k) (hN : 0 < N) (hMN : M ≤ N) (ht : t ≠ 0) :
    ‖∑ n ∈ taoCorputInterval (N : Int) M,
        (n : Complex) ^ (-(t : Complex) * Complex.I)‖ / (N : Real) ≤
      256 * (taoLogDerivativeAmplitude k) ^ (2 * taoVdcAlpha k) *
        taoVdcRate k N (taoLogFrequency t) := by
  have hA := taoLogDerivativeAmplitude_one_le k
  have hT := taoLogFrequency_pos ht
  have hF := taoLogDerivativeHypotheses_short t k N M hN hMN
  have h := taoVdc_proposition10 (taoLogDerivativeFamily t) k (N : Int) M N
    hk hA hN hT hMN hF
  have hsum : (∑ n ∈ taoCorputInterval (N : Int) M,
      taoCorputPhase (taoLogDerivativeFamily t 0 (n : Real))) =
      ∑ n ∈ taoCorputInterval (N : Int) M,
        (n : Complex) ^ (-(t : Complex) * Complex.I) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnleft := (Finset.mem_Ico.mp hn).1
    have hnpos : (0 : Real) < (n : Real) := by
      exact_mod_cast (show (0 : Int) < n by omega)
    rw [taoLogDerivativeFamily_zero]
    exact taoCorputLogPhase_cpow t hnpos
  rw [hsum] at h
  simpa only [taoVdcRate] using h

theorem taoLogDirichlet_short_band_bound (t : Real) (k N M : Nat)
    (hk : 2 ≤ k) (hN : 0 < N) (hMN : M ≤ N) (ht : t ≠ 0)
    (hlow : (N : Real) ^ (k - 1) ≤ taoLogFrequency t) :
    ‖∑ n ∈ taoCorputInterval (N : Int) M,
        (n : Complex) ^ (-(t : Complex) * Complex.I)‖ / (N : Real) ≤
      (2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t) *
        (taoLogFrequency t / (N : Real) ^ k) ^ (taoVdcBeta k) := by
  have hNp : 1 ≤ (N : Real) := by
    have : 1 ≤ N := by omega
    exact_mod_cast this
  have hT := taoLogFrequency_pos ht
  have hbase := taoLogDirichlet_short_vdc_bound t k N M hk hN hMN ht
  have hamp := taoLogDerivativeAmplitude_uniform hk
  have hrate := taoVdcRate_band_bound k hk hNp hT hlow
  have hright : 0 ≤ 256 * (2 : Real) ^ 32 := by positivity
  calc
    _ ≤ 256 * taoLogDerivativeAmplitude k ^ (2 * taoVdcAlpha k) *
        taoVdcRate k N (taoLogFrequency t) := hbase
    _ ≤ 256 * (2 : Real) ^ 32 *
        (4 * Real.log (2 + taoLogFrequency t) * taoVdcSecond k N (taoLogFrequency t)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hamp (by norm_num : (0 : Real) ≤ 256)) hrate
        (taoVdcRate_pos k (by linarith) hT).le hright
    _ = (2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t) *
        (taoLogFrequency t / (N : Real) ^ k) ^ (taoVdcBeta k) := by
      unfold taoVdcSecond
      norm_num
      ring

end

end Erdos1212Kernel
