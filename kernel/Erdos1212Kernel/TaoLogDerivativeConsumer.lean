import Erdos1212Kernel.TaoLogDerivativeBounds

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1700000

theorem taoLogDerivativeHypotheses (t : Real) (k : Nat) {N : Real} (hN : 0 < N) :
    taoDerivativeHypotheses (taoLogDerivativeFamily t) k N (2 * N)
      (taoLogDerivativeAmplitude k) N (taoLogFrequency t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j _hj x hx
    exact taoLogDerivativeFamily_hasDerivAt t j (hN.trans_le hx.1)
  · intro x hx
    exact (taoLogDerivativeFamily_hasDerivAt t (k + 1) (hN.trans_le hx.1)).continuousAt.continuousWithinAt
  · intro j hj x hx
    exact taoLogDerivativeFamily_dyadic_bounds t k j hN hj hx

/-- The fully proved arbitrary-order estimate applied to the literal
logarithmic phase on one dyadic integer block. -/
theorem taoLogPhase_vdc_bound (t : Real) (k N : Nat) (hk : 2 ≤ k) (hN : 0 < N) (ht : t ≠ 0) :
    ‖∑ n ∈ taoCorputInterval (N : Int) N,
        taoCorputPhase (taoCorputLogPhase t (n : Real))‖ / (N : Real) ≤
      256 * (taoLogDerivativeAmplitude k) ^ (2 * taoVdcAlpha k) *
        taoVdcRate k N (taoLogFrequency t) := by
  have hNp : 0 < (N : Real) := by exact_mod_cast hN
  have hA := taoLogDerivativeAmplitude_one_le k
  have hT := taoLogFrequency_pos ht
  have hF0 := taoLogDerivativeHypotheses t k hNp
  have hF : taoDerivativeHypotheses (taoLogDerivativeFamily t) k (N : Real)
      ((N : Real) + N) (taoLogDerivativeAmplitude k) N (taoLogFrequency t) := by
    convert hF0 using 1 <;> ring
  have h := taoVdc_proposition10 (taoLogDerivativeFamily t) k (N : Int) N N
    hk hA hN hT le_rfl hF
  simpa only [taoLogDerivativeFamily_zero, taoVdcRate] using h

/-- Actual x^(-it) Dirichlet polynomial consumer. The equality to the
phase sum is proved term by term on positive integers. -/
theorem taoLogDirichlet_vdc_bound (t : Real) (k N : Nat) (hk : 2 ≤ k) (hN : 0 < N) (ht : t ≠ 0) :
    ‖∑ n ∈ taoCorputInterval (N : Int) N,
        (n : Complex) ^ (-(t : Complex) * Complex.I)‖ / (N : Real) ≤
      256 * (taoLogDerivativeAmplitude k) ^ (2 * taoVdcAlpha k) *
        taoVdcRate k N (taoLogFrequency t) := by
  have h := taoLogPhase_vdc_bound t k N hk hN ht
  have hsum : (∑ n ∈ taoCorputInterval (N : Int) N,
      taoCorputPhase (taoCorputLogPhase t (n : Real))) =
      ∑ n ∈ taoCorputInterval (N : Int) N,
        (n : Complex) ^ (-(t : Complex) * Complex.I) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnleft := (Finset.mem_Ico.mp hn).1
    have hnpos : (0 : Real) < (n : Real) := by
      exact_mod_cast (show (0 : Int) < n by omega)
    exact taoCorputLogPhase_cpow t hnpos
  rwa [hsum] at h

theorem taoLogDirichlet_vdc_source_amplitude (t : Real) (k N : Nat)
    (hk : 3 ≤ k) (hN : 0 < N) (ht : t ≠ 0) :
    ‖∑ n ∈ taoCorputInterval (N : Int) N,
        (n : Complex) ^ (-(t : Complex) * Complex.I)‖ / (N : Real) ≤
      256 * (taoLogDerivativeAmplitude k) ^ (1 / (2 : Real) ^ (k - 3)) *
        ((1 / (N : Real) ^ (1 / (2 : Real) ^ (k - 2))) *
            ((N : Real) ^ k / taoLogFrequency t) ^ (1 / ((2 : Real) ^ k - 2)) *
            (Real.log (2 + taoLogFrequency t)) ^ (1 / (2 : Real) ^ (k - 2)) +
          (taoLogFrequency t / (N : Real) ^ k) ^ (1 / ((2 : Real) ^ k - 2))) := by
  have h := taoLogDirichlet_vdc_bound t k N (by omega) hN ht
  rw [taoVdc_source_amplitude_exponent hk] at h
  simpa only [taoVdcRate, taoVdcAlpha, taoVdcBeta] using h

end

end Erdos1212Kernel
