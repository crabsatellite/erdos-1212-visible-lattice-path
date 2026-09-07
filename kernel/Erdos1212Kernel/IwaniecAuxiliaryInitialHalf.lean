import Erdos1212Kernel.IwaniecAuxiliaryMProperties

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1200000

theorem iwaniecAuxDelayKernel_le_three_fourths {t : Real} (ht : 3 ≤ t) :
    iwaniecAuxDelayKernel t ≤ 3 / 4 := by
  unfold iwaniecAuxDelayKernel
  rw [div_le_iff₀ (sq_pos_of_pos (show 0 < t - 1 by linarith))]
  nlinarith [sq_nonneg (t - 3)]

/-- Rational lower bound for the short initial branch of source Lemma 8.
This follows from the exact defining integral on `[3,7/2]`, not numerics. -/
theorem iwaniecAuxM_seven_halves_lower : (3 / 8 : Real) ≤ iwaniecAuxM (7 / 2) := by
  have hkernel : ContinuousOn iwaniecAuxDelayKernel (Set.Icc (3 : Real) (7 / 2)) := by
    intro t ht
    exact (iwaniecAuxDelayKernel_continuousAt (by linarith [ht.1])).continuousWithinAt
  have hshift : ContinuousOn (fun t : Real => iwaniecAuxM (t - 1))
      (Set.Icc (3 : Real) (7 / 2)) := by
    apply iwaniecAuxM_continuousOn.comp (continuousOn_id.sub continuousOn_const)
    intro t ht
    change (2 : Real) ≤ t - 1
    linarith [ht.1]
  have hint : IntervalIntegrable (fun t => iwaniecAuxDelayKernel t * iwaniecAuxM (t - 1))
      volume (3 : Real) (7 / 2) := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le (show (3 : Real) ≤ 7 / 2 by norm_num)] using hkernel.mul hshift
  have hpoint : ∀ t ∈ Set.Icc (3 : Real) (7 / 2),
      iwaniecAuxDelayKernel t * iwaniecAuxM (t - 1) ≤ 9 / 4 := by
    intro t ht
    have hk := iwaniecAuxDelayKernel_le_three_fourths ht.1
    have hM := iwaniecAuxM_le_three (s := t - 1) (by linarith [ht.1])
    have hpos := (iwaniecAuxM_pos (s := t - 1) (by linarith [ht.1])).le
    have hmul := mul_le_mul hk hM hpos (by norm_num : (0 : Real) ≤ 3 / 4)
    norm_num at hmul
    exact hmul
  have hInt := intervalIntegral.integral_mono_on
    (show (3 : Real) ≤ 7 / 2 by norm_num) hint
    (g := fun _t : Real => (9 / 4 : Real)) intervalIntegrable_const hpoint
  norm_num only [intervalIntegral.integral_const, smul_eq_mul] at hInt
  have hrep := iwaniecAuxFunction_integral_equation (-1) (s := (7 / 2 : Real)) (by norm_num)
  have hrep' : iwaniecAuxM (7 / 2) = 5 / 2 - Real.log 2 -
      ∫ t in (3 : Real)..(7 / 2), iwaniecAuxDelayKernel t * iwaniecAuxM (t - 1) := by
    norm_num [iwaniecAuxBase, iwaniecAuxInitial] at hrep
    simpa only [iwaniecAuxM, sub_eq_add_neg] using hrep
  have hlog := Real.log_le_sub_one_of_pos (show (0 : Real) < 2 by norm_num)
  linarith

theorem iwaniecAuxM_lag_lt_four_square_low
    {s : Real} (hs : s ∈ Set.Icc (3 : Real) (7 / 2)) :
    iwaniecAuxM (s - 1) < 4 * s ^ 2 * iwaniecAuxM s := by
  have hMprev := iwaniecAuxM_le_three (s := s - 1) (by linarith [hs.1])
  have hMlow : (3 / 8 : Real) ≤ iwaniecAuxM s :=
    iwaniecAuxM_seven_halves_lower.trans
      (iwaniecAuxM_antitoneOn (show (2 : Real) ≤ s by linarith [hs.1]) (by norm_num) hs.2)
  have hsSquare : (9 : Real) ≤ s ^ 2 := by nlinarith [hs.1]
  have hmul := mul_le_mul hsSquare hMlow (by norm_num : (0 : Real) ≤ 3 / 8)
    (sq_nonneg s)
  nlinarith

end

end Erdos1212Kernel
