import Erdos1212Kernel.IwaniecMonotoneWeightedKernel

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1600000

/-- Quantitative discrete-to-integral error with the original endpoints.
The weight is only assumed nonnegative and increasing on [B,A]. -/
theorem iwaniecWeightedLogLog_quadrature_bounds (b : Real → Real) {B A : Nat}
    (hB : 3 ≤ B) (hBA : B ≤ A)
    (hbMono : MonotoneOn b (Set.Icc (B : Real) (A : Real)))
    (hbNonneg : ∀ x ∈ Set.Icc (B : Real) (A : Real), 0 ≤ b x) :
    0 ≤ iwaniecLogLogIncrementWeightedInterval (fun n => b n) B A - iwaniecWeightedLogKernelIntegral b B A ∧
    iwaniecLogLogIncrementWeightedInterval (fun n => b n) B A - iwaniecWeightedLogKernelIntegral b B A ≤
      b A * iwaniecLogKernel ((B - 1 : Nat) : Real) := by
  revert hbMono hbNonneg
  induction A, hBA using Nat.le_induction with
  | base =>
      intro _hbMono hbNonneg
      have hb : 0 ≤ b B := hbNonneg B ⟨le_rfl, le_rfl⟩
      have hK := iwaniecLogKernel_pos (x := (B : Real)) (by exact_mod_cast (show 1 < B by omega))
      have hlow := iwaniecLogKernel_at_nat_le_logLogIncrement hB
      have hhigh := logLogIncrement_le_iwaniecLogKernel_at_pred hB
      simp only [iwaniecLogLogIncrementWeightedInterval, Finset.Icc_self, Finset.sum_singleton,
        iwaniecWeightedLogKernelIntegral, intervalIntegral.integral_same, sub_zero]
      exact ⟨mul_nonneg hb (hK.le.trans hlow), mul_le_mul_of_nonneg_left hhigh hb⟩
  | succ A hBA ih =>
      intro hbMono hbNonneg
      have hBAreal : (B : Real) ≤ (A : Real) := by exact_mod_cast hBA
      have hAsucc : (A : Real) ≤ ((A + 1 : Nat) : Real) := by exact_mod_cast Nat.le_succ A
      have hprevSet : Set.Icc (B : Real) A ⊆ Set.Icc (B : Real) (A + 1 : Nat) := by
        intro x hx
        exact ⟨hx.1, hx.2.trans hAsucc⟩
      have hunitSet : Set.Icc (A : Real) (A + 1 : Nat) ⊆ Set.Icc (B : Real) (A + 1 : Nat) := by
        intro x hx
        exact ⟨hBAreal.trans hx.1, hx.2⟩
      have hprev := ih (hbMono.mono hprevSet) (fun x hx => hbNonneg x (hprevSet hx))
      have hunitMono := hbMono.mono hunitSet
      have hunit := iwaniecMonotoneWeightedLogKernel_unit_error b (n := A) (by omega) hunitMono
      have hBreal : (1 : Real) < B := by exact_mod_cast (show 1 < B by omega)
      have hAreal : (1 : Real) < A := hBreal.trans_le hBAreal
      have hiPrev := iwaniecMonotoneWeightedLogKernel_intervalIntegrable b hBreal hBAreal (hbMono.mono hprevSet)
      have hiUnit := iwaniecMonotoneWeightedLogKernel_intervalIntegrable b hAreal hAsucc hunitMono
      have hIntegral := intervalIntegral.integral_add_adjacent_intervals hiPrev hiUnit
      change iwaniecWeightedLogKernelIntegral b B A + iwaniecWeightedLogKernelIntegral b A (A + 1 : Nat) =
        iwaniecWeightedLogKernelIntegral b B (A + 1 : Nat) at hIntegral
      have hSum : iwaniecLogLogIncrementWeightedInterval (fun n => b n) B (A + 1) =
          iwaniecLogLogIncrementWeightedInterval (fun n => b n) B A +
            b (A + 1 : Nat) * (iwaniecLogLogValue (A + 1) - iwaniecLogLogValue A) := by
        unfold iwaniecLogLogIncrementWeightedInterval
        rw [Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]
      have hId : iwaniecLogLogIncrementWeightedInterval (fun n => b n) B (A + 1) -
          iwaniecWeightedLogKernelIntegral b B (A + 1 : Nat) =
        (iwaniecLogLogIncrementWeightedInterval (fun n => b n) B A - iwaniecWeightedLogKernelIntegral b B A) +
        (b (A + 1 : Nat) * (iwaniecLogLogValue (A + 1) - iwaniecLogLogValue A) -
          iwaniecWeightedLogKernelIntegral b A (A + 1 : Nat)) := by rw [hSum, ← hIntegral]; ring
      have hK : iwaniecLogKernel A ≤ iwaniecLogKernel ((B - 1 : Nat) : Real) := by
        apply iwaniecLogKernel_antitoneOn_Ici_two
        · change (2 : Real) ≤ ((B - 1 : Nat) : Real)
          exact_mod_cast (show 2 ≤ B - 1 by omega)
        · change (2 : Real) ≤ (A : Real)
          exact_mod_cast (show 2 ≤ A by omega)
        · exact_mod_cast (show B - 1 ≤ A by omega)
      have hdelta : 0 ≤ b (A + 1 : Nat) - b A :=
        sub_nonneg.mpr (hunitMono ⟨le_rfl, hAsucc⟩ ⟨hAsucc, le_rfl⟩ hAsucc)
      have hLocal := hunit.2.trans (mul_le_mul_of_nonneg_left hK hdelta)
      rw [hId]
      constructor
      · exact add_nonneg hprev.1 hunit.1
      · calc
          _ ≤ b A * iwaniecLogKernel ((B - 1 : Nat) : Real) +
              (b (A + 1 : Nat) - b A) * iwaniecLogKernel ((B - 1 : Nat) : Real) := add_le_add hprev.2 hLocal
          _ = _ := by ring

theorem iwaniecWeightedLogLog_quadrature_error (b : Real → Real) {B A : Nat}
    (hB : 3 ≤ B) (hBA : B ≤ A)
    (hbMono : MonotoneOn b (Set.Icc (B : Real) (A : Real)))
    (hbNonneg : ∀ x ∈ Set.Icc (B : Real) (A : Real), 0 ≤ b x) :
    |iwaniecLogLogIncrementWeightedInterval (fun n => b n) B A - iwaniecWeightedLogKernelIntegral b B A| ≤
      b A / (((B - 1 : Nat) : Real) * Real.log ((B - 1 : Nat) : Real)) := by
  have h := iwaniecWeightedLogLog_quadrature_bounds b hB hBA hbMono hbNonneg
  rw [abs_of_nonneg h.1]
  simpa only [iwaniecLogKernel, mul_one_div] using h.2

end

end Erdos1212Kernel
