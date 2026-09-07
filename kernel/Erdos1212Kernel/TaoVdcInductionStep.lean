import Erdos1212Kernel.TaoVdcOverlapInduction
import Erdos1212Kernel.TaoVdcBalancedAverage
import Erdos1212Kernel.TaoVdcRootCombination

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1800000

theorem taoVdcBound_step {k : Nat} (hk : 2 ≤ k) {C : Real}
    (hC0 : 2 ≤ C) (hclose : 4 + 4 * Real.sqrt C ≤ C)
    (hbound : taoVdcBound k C) : taoVdcBound (k + 1) C := by
  intro F a M N A T hA hN hT hMN hF
  have hn : 3 ≤ k + 1 := by omega
  have hNp : 0 < (N : Real) := by exact_mod_cast hN
  have hAp : 0 < A := by linarith
  have htriv := taoSecondDerivative_trivial_sum_bound (F 0) a M N hN hMN
  have hamp : 1 ≤ A ^ (2 * taoVdcAlpha (k + 1)) := taoVdc_amplitude_ge_one (k + 1) hA
  by_cases hsmall : T ≤ 1
  · have hN1Nat : 1 ≤ N := by omega
    have hN1 : 1 ≤ (N : Real) := by exact_mod_cast hN1Nat
    have hrate := taoVdcRate_small_lower hn hN1 hT hsmall
    exact taoVdc_trivial_from_rate htriv hC0 hamp hrate
  by_cases hlarge : (N : Real) ^ (k + 1) ≤ T
  · have hrate := taoVdcRate_large_lower (by omega : 2 ≤ k + 1) hNp hT hlarge
    have hrate' : 1 / 2 ≤ taoVdcRate (k + 1) N T :=
      (show (1 : Real) / 2 ≤ 1 by norm_num).trans hrate
    exact taoVdc_trivial_from_rate htriv hC0 hamp hrate'
  have hTone : 1 ≤ T := (lt_of_not_ge hsmall).le
  have hupper : T ≤ (N : Real) ^ (k + 1) := (lt_of_not_ge hlarge).le
  obtain ⟨hH, hHN, _hhalf, _hfull⟩ := taoVdcShift_admissible hn hN hTone hupper
  have hvdc := taoCorput_short_exponential_sum_bound (fun n : Int => F 0 n) a M N
    (taoVdcShift (k + 1) N T) hMN hH hHN
  have hvdc' : ‖∑ n ∈ taoCorputInterval a M, taoCorputPhase (F 0 (n : Real))‖ / (N : Real) ≤
      2 * (1 / Real.sqrt (taoVdcShift (k + 1) N T : Real) + Real.sqrt
        ((1 / (taoVdcShift (k + 1) N T : Real)) *
          ∑ h ∈ Finset.Icc 1 (taoVdcShift (k + 1) N T),
            ‖∑ n ∈ taoCorputOverlap a M h, taoCorputPhase (F 0 ((n : Real) + h) - F 0 n)‖ / (N : Real))) := by
    simpa only [Int.cast_add, Int.cast_natCast] using hvdc
  have hinner (h : Nat) (hh : h ∈ Finset.Icc 1 (taoVdcShift (k + 1) N T)) :
      ‖∑ n ∈ taoCorputOverlap a M h, taoCorputPhase (F 0 ((n : Real) + h) - F 0 n)‖ / (N : Real) ≤
        C * A ^ (2 * taoVdcAlpha k) * taoVdcRate k N ((h : Real) * T / N) := by
    have hhpos : 0 < h := by have := (Finset.mem_Icc.mp hh).1; omega
    exact taoVdc_induction_overlap hbound F a M N h (by linarith) hA hN hT hMN hhpos hF
  have hsum := Finset.sum_le_sum hinner
  have havg := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 1 / (taoVdcShift (k + 1) N T : Real) by positivity)
  have hbalanced := taoVdc_balanced_average hk hN hTone hupper
  have hampEq : A ^ (2 * taoVdcAlpha k) = (A ^ (2 * taoVdcAlpha (k + 1))) ^ 2 :=
    taoVdc_amplitude_square hk hAp.le
  have havgFactor : (1 / (taoVdcShift (k + 1) N T : Real)) *
      (∑ h ∈ Finset.Icc 1 (taoVdcShift (k + 1) N T),
        C * A ^ (2 * taoVdcAlpha k) * taoVdcRate k N ((h : Real) * T / N)) =
      (C * A ^ (2 * taoVdcAlpha k)) *
        ((1 / (taoVdcShift (k + 1) N T : Real)) *
          ∑ h ∈ Finset.Icc 1 (taoVdcShift (k + 1) N T), taoVdcRate k N ((h : Real) * T / N)) := by
    calc
      _ = (1 / (taoVdcShift (k + 1) N T : Real)) *
          ((C * A ^ (2 * taoVdcAlpha k)) *
            ∑ h ∈ Finset.Icc 1 (taoVdcShift (k + 1) N T), taoVdcRate k N ((h : Real) * T / N)) := by
        congr 1
        rw [Finset.mul_sum]
      _ = _ := by ring
  rw [havgFactor] at havg
  have havg' : (1 / (taoVdcShift (k + 1) N T : Real)) *
      (∑ h ∈ Finset.Icc 1 (taoVdcShift (k + 1) N T),
        ‖∑ n ∈ taoCorputOverlap a M h, taoCorputPhase (F 0 ((n : Real) + h) - F 0 n)‖ / (N : Real)) ≤
      C * (A ^ (2 * taoVdcAlpha (k + 1))) ^ 2 *
        (4 * (taoVdcFirst (k + 1) N T) ^ 2 + (taoVdcSecond (k + 1) N T) ^ 2) := by
    have hfactor : 0 ≤ C * A ^ (2 * taoVdcAlpha k) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg hAp.le _)
    have hh := mul_le_mul_of_nonneg_left hbalanced hfactor
    have htotal := havg.trans hh
    rw [hampEq] at htotal
    simpa only [mul_assoc] using htotal
  have hP : 0 ≤ taoVdcFirst (k + 1) N T := by
    unfold taoVdcFirst
    exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _)
  have hB : 0 ≤ taoVdcSecond (k + 1) N T := by
    unfold taoVdcSecond
    exact Real.rpow_nonneg (by positivity) _
  have hsqrt := Real.sqrt_le_sqrt havg'
  have hroot : Real.sqrt (C * (A ^ (2 * taoVdcAlpha (k + 1))) ^ 2 *
      (4 * (taoVdcFirst (k + 1) N T) ^ 2 + (taoVdcSecond (k + 1) N T) ^ 2)) ≤
      Real.sqrt C * A ^ (2 * taoVdcAlpha (k + 1)) *
        (2 * taoVdcFirst (k + 1) N T + taoVdcSecond (k + 1) N T) :=
    taoVdc_square_root_majorant (show 0 ≤ C by linarith)
      (Real.rpow_nonneg hAp.le _) hP hB
  have hsqrt' : Real.sqrt ((1 / (taoVdcShift (k + 1) N T : Real)) *
      (∑ h ∈ Finset.Icc 1 (taoVdcShift (k + 1) N T),
        ‖∑ n ∈ taoCorputOverlap a M h, taoCorputPhase (F 0 ((n : Real) + h) - F 0 n)‖ / (N : Real))) ≤
      Real.sqrt C * A ^ (2 * taoVdcAlpha (k + 1)) *
        (2 * taoVdcFirst (k + 1) N T + taoVdcSecond (k + 1) N T) := hsqrt.trans hroot
  have hshift := taoVdcShift_root_bound hn hN hTone hupper
  have hclose' : 2 * (2 * taoVdcSecond (k + 1) N T +
      Real.sqrt C * A ^ (2 * taoVdcAlpha (k + 1)) *
        (2 * taoVdcFirst (k + 1) N T + taoVdcSecond (k + 1) N T)) ≤
      C * A ^ (2 * taoVdcAlpha (k + 1)) *
        (taoVdcFirst (k + 1) N T + taoVdcSecond (k + 1) N T) :=
    taoVdc_constant_closes_step (show 0 ≤ C by linarith) hamp hP hB hclose
  apply hvdc'.trans
  have hinside := add_le_add hshift hsqrt'
  have htwo := mul_le_mul_of_nonneg_left hinside (by norm_num : (0 : Real) ≤ 2)
  exact htwo.trans (by simpa only [taoVdcRate_split] using hclose')

end

end Erdos1212Kernel
