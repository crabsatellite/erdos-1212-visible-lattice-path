import Erdos1212Kernel.IwaniecSieveSeriesEquations
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory intervalIntegral

set_option maxHeartbeats 1800000

/-!
# Iwaniec 1971, equation (3.9)

This is the local part of Lemma 5.  It uses only equations (3.6)--(3.7):
on the interval `2 <= s <= 4`, the odd series in the kernel is constant at its
value at `3`.  No value for that constant is assumed here.
-/

theorem iwaniecGEven_succ_sub_eq_intervalIntegral_oddKernel
    (n : Nat) {a b : Real} (ha : 2 ≤ a) (hab : a ≤ b) :
    iwaniecGEven (n + 1) a - iwaniecGEven (n + 1) b =
      ∫ t in a..b, iwaniecOddKernel n t := by
  have hdiff := integral_Ioi_sub_Ioi
    (iwaniecOddKernel_integrableOn_Ioi n ha) hab
  rw [← iwaniecGEven_succ_eq_integral_Ioi n ha,
    ← iwaniecGEven_succ_eq_integral_Ioi n (ha.trans hab)] at hdiff
  exact hdiff

private theorem iwaniecOddKernel_nonneg_on_interval
    (n : Nat) {a b t : Real} (ha : 2 ≤ a) (ht : t ∈ Set.Ioc a b) :
    0 ≤ iwaniecOddKernel n t := by
  have ht' : a < t := ht.1
  have hden : 0 < t - 1 := by linarith
  exact div_nonneg (iwaniecGOdd_nonneg n (by linarith [ht'])) hden.le

/-- The odd kernels may also be summed under any finite interval integral in
their common domain. -/
theorem iwaniec_tsum_intervalIntegral_oddKernel
    {a b : Real} (ha : 2 ≤ a) (hab : a ≤ b) :
    (∑' n : Nat, ∫ t in a..b, iwaniecOddKernel n t) =
      ∫ t in a..b, ∑' n : Nat, iwaniecOddKernel n t := by
  have hb : 2 ≤ b := ha.trans hab
  have hterm : ∀ n : Nat,
      Integrable (iwaniecOddKernel n) (volume.restrict (Set.Ioc a b)) := by
    intro n
    exact (iwaniecOddKernel_integrableOn_Ioi n ha).mono_set
      Set.Ioc_subset_Ioi_self
  have hnorm (n : Nat) :
      (∫ t in Set.Ioc a b, ‖iwaniecOddKernel n t‖) =
        iwaniecGEven (n + 1) a - iwaniecGEven (n + 1) b := by
    calc
      (∫ t in Set.Ioc a b, ‖iwaniecOddKernel n t‖) =
          ∫ t in Set.Ioc a b, iwaniecOddKernel n t := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t ht
        exact Real.norm_of_nonneg
          (iwaniecOddKernel_nonneg_on_interval n ha ht)
      _ = (∫ t in a..b, iwaniecOddKernel n t) := by
        rw [intervalIntegral.integral_of_le hab]
      _ = iwaniecGEven (n + 1) a - iwaniecGEven (n + 1) b :=
        (iwaniecGEven_succ_sub_eq_intervalIntegral_oddKernel n ha hab).symm
  have hsumA : Summable (fun n : Nat => iwaniecGEven (n + 1) a) :=
    (summable_nat_add_iff 1).2 (summable_iwaniecGEven ha)
  have hsumB : Summable (fun n : Nat => iwaniecGEven (n + 1) b) :=
    (summable_nat_add_iff 1).2 (summable_iwaniecGEven hb)
  have hnormSum : Summable (fun n : Nat =>
      ∫ t in Set.Ioc a b, ‖iwaniecOddKernel n t‖) := by
    simpa only [hnorm] using hsumA.sub hsumB
  have hswap := integral_tsum_of_summable_integral_norm hterm hnormSum
  simpa only [intervalIntegral.integral_of_le hab] using hswap

theorem iwaniecEvenSieveSeries_eq_gTwo_add_tail
    {s : Real} (hs : 2 ≤ s) :
    iwaniecEvenSieveSeries s =
      iwaniecGTwo s + ∑' n : Nat, iwaniecGEven (n + 1) s := by
  unfold iwaniecEvenSieveSeries
  calc
    (∑' n : Nat, iwaniecGEven n s) =
        (∑ n ∈ Finset.range 1, iwaniecGEven n s) +
          ∑' n : Nat, iwaniecGEven (n + 1) s :=
      ((summable_iwaniecGEven hs).sum_add_tsum_nat_add 1).symm
    _ = _ := by simp [iwaniecGEven_zero]

theorem intervalIntegral_inv_sub_one
    {s : Real} (hs : 1 < s) :
    (∫ t in s..(4 : Real), (t - 1)⁻¹) =
      Real.log (3 / (s - 1)) := by
  rw [intervalIntegral.integral_comp_sub_right (f := fun x : Real => x⁻¹) 1]
  convert (integral_inv_of_pos (a := s - 1) (b := (3 : Real))
    (by linarith) (by norm_num)) using 1 <;>
    ring

theorem intervalIntegral_oddSeriesKernel_eq_at_three_mul_log
    {s : Real} (hlower : 2 ≤ s) (hupper : s ≤ 4) :
    (∫ t in s..(4 : Real),
        iwaniecOddSieveSeries (t - 1) / (t - 1)) =
      iwaniecOddSieveSeries 3 * Real.log (3 / (s - 1)) := by
  have hpoint :
      (∫ t in s..(4 : Real),
          iwaniecOddSieveSeries (t - 1) / (t - 1)) =
        ∫ t in s..(4 : Real), iwaniecOddSieveSeries 3 / (t - 1) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Set.Icc s (4 : Real) := by
      simpa [Set.uIcc_of_le hupper] using ht
    have htLower : 1 ≤ t - 1 := by linarith [htIcc.1]
    have htUpper : t - 1 ≤ 3 := by linarith [htIcc.2]
    change iwaniecOddSieveSeries (t - 1) / (t - 1) =
      iwaniecOddSieveSeries 3 / (t - 1)
    rw [iwaniecOddSieveSeries_eq_three htLower htUpper]
  rw [hpoint]
  calc
    (∫ t in s..(4 : Real), iwaniecOddSieveSeries 3 / (t - 1)) =
        iwaniecOddSieveSeries 3 *
          (∫ t in s..(4 : Real), (t - 1)⁻¹) := by
      simp only [div_eq_mul_inv, intervalIntegral.integral_const_mul]
    _ = _ := by rw [intervalIntegral_inv_sub_one (by linarith)]

theorem iwaniecEvenSieveTail_sub_at_four
    {s : Real} (hlower : 2 ≤ s) (hupper : s ≤ 4) :
    (∑' n : Nat, iwaniecGEven (n + 1) s) -
        (∑' n : Nat, iwaniecGEven (n + 1) 4) =
      iwaniecOddSieveSeries 3 * Real.log (3 / (s - 1)) := by
  have hsumS : Summable (fun n : Nat => iwaniecGEven (n + 1) s) :=
    (summable_nat_add_iff 1).2 (summable_iwaniecGEven hlower)
  have hsumFour : Summable (fun n : Nat => iwaniecGEven (n + 1) 4) :=
    (summable_nat_add_iff 1).2 (summable_iwaniecGEven (by norm_num))
  calc
    (∑' n : Nat, iwaniecGEven (n + 1) s) -
        (∑' n : Nat, iwaniecGEven (n + 1) 4) =
        ∑' n : Nat,
          (iwaniecGEven (n + 1) s - iwaniecGEven (n + 1) 4) := by
      rw [hsumS.tsum_sub hsumFour]
    _ = ∑' n : Nat, ∫ t in s..(4 : Real), iwaniecOddKernel n t := by
      apply tsum_congr
      intro n
      exact iwaniecGEven_succ_sub_eq_intervalIntegral_oddKernel n hlower hupper
    _ = (∫ t in s..(4 : Real), ∑' n : Nat, iwaniecOddKernel n t) :=
      iwaniec_tsum_intervalIntegral_oddKernel hlower hupper
    _ = (∫ t in s..(4 : Real),
        iwaniecOddSieveSeries (t - 1) / (t - 1)) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      simp only [iwaniecOddKernel, iwaniecOddSieveSeries, tsum_div_const]
    _ = _ := intervalIntegral_oddSeriesKernel_eq_at_three_mul_log hlower hupper

/-- Iwaniec 1971, equation (3.9), before evaluating the global constant
`F(3)`. -/
theorem iwaniecEvenSieveSeries_local_formula
    {s : Real} (hlower : 2 ≤ s) (hupper : s ≤ 4) :
    iwaniecEvenSieveSeries s =
      iwaniecEvenSieveSeries 4 +
        (iwaniecOddSieveSeries 3 + 3) * Real.log (3 / (s - 1)) +
        s - 4 := by
  have hsplitS := iwaniecEvenSieveSeries_eq_gTwo_add_tail hlower
  have hsplitFour := iwaniecEvenSieveSeries_eq_gTwo_add_tail (by norm_num : (2 : Real) ≤ 4)
  have htail := iwaniecEvenSieveTail_sub_at_four hlower hupper
  have hgS := iwaniecGTwo_eq hlower hupper
  have hgFour := iwaniecGTwo_eq_zero_of_four_le (le_refl (4 : Real))
  rw [hgS] at hsplitS
  rw [hgFour, zero_add] at hsplitFour
  linarith

end

end Erdos1212Kernel
