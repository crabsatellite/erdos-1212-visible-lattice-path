import Erdos1212Kernel.TaoCorputPhase

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1500000

theorem taoCorputInterval_mono (a : Int) {M N : Nat} (hMN : M ≤ N) :
    taoCorputInterval a M ⊆ taoCorputInterval a N := by
  intro n hn
  have h := Finset.mem_Ico.mp hn
  apply Finset.mem_Ico.mpr
  constructor <;> omega

theorem taoCorput_support_sum_mono (z : Int → Complex) (a : Int) {M N : Nat} (hMN : M ≤ N)
    (hz : ∀ n, n ∉ taoCorputInterval a M → z n = 0) :
    taoCorputSum z a N = taoCorputSum z a M := by
  unfold taoCorputSum
  symm
  apply Finset.sum_subset (taoCorputInterval_mono a hMN)
  intro n _hn hnnot
  exact hz n hnnot

theorem taoCorput_support_correlation_mono (z : Int → Complex) (a : Int) {M N : Nat} (hMN : M ≤ N)
    (hz : ∀ n, n ∉ taoCorputInterval a M → z n = 0) (h : Nat) :
    taoCorputCorrelation z a N h = taoCorputCorrelation z a M h := by
  unfold taoCorputCorrelation
  symm
  apply Finset.sum_subset (taoCorputInterval_mono a hMN)
  intro n _hn hnnot
  simp only [hz n hnnot, star_zero, mul_zero]

/-- The source scale N need not equal the number M of summands. Both
the outside normalization and the correlation normalizations remain N. -/
theorem taoCorput_short_exponential_sum_bound (f : Int → Real) (a : Int) (M N H : Nat)
    (hMN : M ≤ N) (hH : 0 < H) (hHN : H ≤ N) :
    ‖∑ n ∈ taoCorputInterval a M, taoCorputPhase (f n)‖ / (N : Real) ≤
      2 * (1 / Real.sqrt (H : Real) + Real.sqrt ((1 / (H : Real)) *
        ∑ h ∈ Finset.Icc 1 H, ‖∑ n ∈ taoCorputOverlap a M h, taoCorputPhase (f (n + h) - f n)‖ / (N : Real))) := by
  let z := taoCorputPhaseSequence f a M
  have hz : ∀ n, n ∉ taoCorputInterval a M → z n = 0 := fun n hn => taoCorputPhaseSequence_off f a M hn
  have hzN : ∀ n, n ∉ taoCorputInterval a N → z n = 0 := by
    intro n hn
    apply hz n
    exact fun hm => hn (taoCorputInterval_mono a hMN hm)
  have hu : ∀ n ∈ taoCorputInterval a N, ‖z n‖ ≤ 1 := by
    intro n _hn
    by_cases hm : n ∈ taoCorputInterval a M
    · rw [show z n = taoCorputPhase (f n) from taoCorputPhaseSequence_on f a M hm, taoCorputPhase_norm]
    · rw [hz n hm, norm_zero]
      norm_num
  have h := taoCorput_vdc_source_bound z a N H hH hHN hzN hu
  rw [taoCorput_support_sum_mono z a hMN hz] at h
  simp_rw [taoCorput_support_correlation_mono z a hMN hz] at h
  simpa only [z, taoCorputPhaseSequence_sum, taoCorputPhaseSequence_correlation] using h

end

end Erdos1212Kernel
