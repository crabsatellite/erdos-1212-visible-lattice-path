import Erdos1212Kernel.IwaniecPrimeWeightedIntegral

namespace Erdos1212Kernel

noncomputable section

open Filter

set_option maxHeartbeats 1200000

def iwaniecLogKernelTwoStepRatio (k : Nat) : Real :=
  iwaniecLogKernel (k : Real) / iwaniecLogKernel (k + 2 : Nat)

theorem iwaniecLogKernelTwoStepRatio_eq
    {k : Nat} (hk : 2 ≤ k) :
    iwaniecLogKernelTwoStepRatio k =
      (((k : Real) + 2) / (k : Real)) *
        (Real.log ((k : Real) + 2) / Real.log (k : Real)) := by
  have hkPos : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
  have hkTwoPos : (0 : Real) < (k : Real) + 2 := by positivity
  have hkLog : Real.log (k : Real) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hkPos (by norm_cast; omega)
  have hkTwoLog : Real.log ((k : Real) + 2) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hkTwoPos (by norm_cast; omega)
  unfold iwaniecLogKernelTwoStepRatio iwaniecLogKernel
  push_cast
  field_simp [hkPos.ne', hkLog, hkTwoLog]

theorem one_le_iwaniecLogKernelTwoStepRatio
    {k : Nat} (hk : 2 ≤ k) :
    1 ≤ iwaniecLogKernelTwoStepRatio k := by
  have hkKernelPos : 0 < iwaniecLogKernel (k + 2 : Nat) := by
    apply iwaniecLogKernel_pos
    norm_cast
    omega
  unfold iwaniecLogKernelTwoStepRatio
  rw [le_div_iff₀ hkKernelPos]
  have hanti := iwaniecLogKernel_antitoneOn_Ici_two
    (a := (k : Real)) (b := (k + 2 : Nat))
  simpa using hanti
    (show (2 : Real) ≤ (k : Real) by exact_mod_cast hk)
    (show (2 : Real) ≤ ((k + 2 : Nat) : Real) by
      exact_mod_cast (show 2 ≤ k + 2 by omega))
    (show (k : Real) ≤ ((k + 2 : Nat) : Real) by
      exact_mod_cast (show k ≤ k + 2 by omega))

theorem tendsto_log_nat_add_two_div_log_nat :
    Tendsto
      (fun k : Nat => Real.log ((k : Real) + 2) / Real.log (k : Real))
      atTop (nhds 1) := by
  have hdiff : Tendsto
      (fun k : Nat => Real.log ((k : Real) + 2) - Real.log (k : Real))
      atTop (nhds 0) :=
    (Real.tendsto_log_comp_add_sub_log 2).comp
      tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun k : Nat => Real.log (k : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hquot : Tendsto
      (fun k : Nat =>
        (Real.log ((k : Real) + 2) - Real.log (k : Real)) /
          Real.log (k : Real)) atTop (nhds 0) :=
    hdiff.div_atTop hden
  have hone : Tendsto
      (fun k : Nat => 1 +
        (Real.log ((k : Real) + 2) - Real.log (k : Real)) /
          Real.log (k : Real)) atTop (nhds 1) := by
    convert (tendsto_const_nhds.add hquot) using 1 <;> norm_num
  apply hone.congr'
  filter_upwards [eventually_gt_atTop 1] with k hk
  have hkPos : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
  have hkLog : Real.log (k : Real) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hkPos (by norm_cast; omega)
  field_simp [hkLog]
  ring

theorem tendsto_nat_add_two_div_nat :
    Tendsto (fun k : Nat => ((k : Real) + 2) / (k : Real))
      atTop (nhds 1) := by
  have h := tendsto_add_mul_div_add_mul_atTop_nhds
    (2 : Real) 0 1 (d := (1 : Real)) one_ne_zero
  convert h using 1
  · funext k
    push_cast
    ring
  · norm_num

/-- Unit-interval distortion of the logarithmic kernel tends to one.  This
is the qualitative replacement for the paper's local `1 + O(1/n)` factor. -/
theorem tendsto_iwaniecLogKernelTwoStepRatio_one :
    Tendsto iwaniecLogKernelTwoStepRatio atTop (nhds 1) := by
  have hprod := tendsto_nat_add_two_div_nat.mul
    tendsto_log_nat_add_two_div_log_nat
  have heq :
      (fun k : Nat => ((k : Real) + 2) / (k : Real) *
        (Real.log ((k : Real) + 2) / Real.log (k : Real))) =ᶠ[atTop]
        iwaniecLogKernelTwoStepRatio := by
    filter_upwards [eventually_ge_atTop 2] with k hk
    exact (iwaniecLogKernelTwoStepRatio_eq hk).symm
  simpa using hprod.congr' heq

theorem iwaniecLogLogIncrement_le_ratio_mul_next
    {n : Nat} (hn : 3 ≤ n) :
    iwaniecLogLogValue n - iwaniecLogLogValue (n - 1) ≤
      iwaniecLogKernelTwoStepRatio (n - 1) *
        (iwaniecLogLogValue (n + 1) - iwaniecLogLogValue n) := by
  have hk : 2 ≤ n - 1 := by omega
  have hratioNonneg : 0 ≤ iwaniecLogKernelTwoStepRatio (n - 1) :=
    (one_le_iwaniecLogKernelTwoStepRatio hk).trans' zero_le_one
  have hnextKernelPos :
      iwaniecLogKernel ((n + 1 : Nat) : Real) ≠ 0 := by
    exact (iwaniecLogKernel_pos (by norm_cast; omega)).ne'
  have hratioKernel :
      iwaniecLogKernel ((n - 1 : Nat) : Real) =
        iwaniecLogKernelTwoStepRatio (n - 1) *
          iwaniecLogKernel ((n + 1 : Nat) : Real) := by
    unfold iwaniecLogKernelTwoStepRatio
    have hindex : n - 1 + 2 = n + 1 := by omega
    rw [hindex]
    exact (div_mul_cancel₀ _ hnextKernelPos).symm
  calc
    iwaniecLogLogValue n - iwaniecLogLogValue (n - 1) ≤
        iwaniecLogKernel ((n - 1 : Nat) : Real) :=
      logLogIncrement_le_iwaniecLogKernel_at_pred hn
    _ = iwaniecLogKernelTwoStepRatio (n - 1) *
        iwaniecLogKernel ((n + 1 : Nat) : Real) := hratioKernel
    _ ≤ iwaniecLogKernelTwoStepRatio (n - 1) *
        (iwaniecLogLogValue (n + 1) - iwaniecLogLogValue n) := by
      apply mul_le_mul_of_nonneg_left
        (iwaniecLogKernel_at_nat_le_logLogIncrement
          (show 3 ≤ n + 1 by omega)) hratioNonneg

theorem iwaniecWeightedLogLogIncrement_le_ratio_mul_next
    (b : Nat → Real) {n : Nat} (hn : 3 ≤ n)
    (hbNonneg : 0 ≤ b n) (hbStep : b n ≤ b (n + 1)) :
    b n * (iwaniecLogLogValue n - iwaniecLogLogValue (n - 1)) ≤
      iwaniecLogKernelTwoStepRatio (n - 1) *
        (b (n + 1) *
          (iwaniecLogLogValue (n + 1) - iwaniecLogLogValue n)) := by
  have hincNonneg :
      0 ≤ iwaniecLogLogValue (n + 1) - iwaniecLogLogValue n := by
    exact (iwaniecLogKernel_at_nat_le_logLogIncrement
      (show 3 ≤ n + 1 by omega)).trans' (iwaniecLogKernel_pos
        (show (1 : Real) < (n + 1 : Nat) by norm_cast; omega)).le
  have hratioNonneg : 0 ≤ iwaniecLogKernelTwoStepRatio (n - 1) :=
    (one_le_iwaniecLogKernelTwoStepRatio (by omega)).trans' zero_le_one
  calc
    b n * (iwaniecLogLogValue n - iwaniecLogLogValue (n - 1)) ≤
      b n * (iwaniecLogKernelTwoStepRatio (n - 1) *
        (iwaniecLogLogValue (n + 1) - iwaniecLogLogValue n)) := by
      exact mul_le_mul_of_nonneg_left
        (iwaniecLogLogIncrement_le_ratio_mul_next hn) hbNonneg
    _ = iwaniecLogKernelTwoStepRatio (n - 1) *
        (b n * (iwaniecLogLogValue (n + 1) - iwaniecLogLogValue n)) := by
      ring
    _ ≤ iwaniecLogKernelTwoStepRatio (n - 1) *
        (b (n + 1) *
          (iwaniecLogLogValue (n + 1) - iwaniecLogLogValue n)) := by
      apply mul_le_mul_of_nonneg_left _ hratioNonneg
      exact mul_le_mul_of_nonneg_right hbStep hincNonneg

theorem eventually_iwaniecLogKernelTwoStepRatio_le_one_add
    {delta : Real} (hdelta : 0 < delta) :
    ∀ᶠ k : Nat in atTop,
      iwaniecLogKernelTwoStepRatio k ≤ 1 + delta := by
  have hmetric := Metric.tendsto_atTop.mp
    tendsto_iwaniecLogKernelTwoStepRatio_one delta hdelta
  obtain ⟨K₀, hK₀⟩ := hmetric
  filter_upwards [eventually_ge_atTop K₀] with k hk
  have hdist := hK₀ k hk
  rw [Real.dist_eq] at hdist
  have hupper := (le_abs_self
    (iwaniecLogKernelTwoStepRatio k - 1)).trans hdist.le
  linarith

end

end Erdos1212Kernel
