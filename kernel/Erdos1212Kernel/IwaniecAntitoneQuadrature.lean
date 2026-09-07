import Erdos1212Kernel.IwaniecAntitoneWeightedKernel

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory intervalIntegral

set_option maxHeartbeats 600000

/-- Exact decreasing-weight quadrature with the original endpoints.
The lower bound retains the telescoping decrement; the initial endpoint
contribution supplies the upper bound. -/
theorem iwaniecWeightedLogLog_antitone_quadrature_bounds (b : Real → Real) {B A : Nat}
    (hB : 3 ≤ B) (hBA : B ≤ A)
    (hbAnti : AntitoneOn b (Set.Icc (B : Real) (A : Real)))
    (hbNonneg : ∀ x ∈ Set.Icc (B : Real) (A : Real), 0 ≤ b x) :
    (b A - b B) * iwaniecLogKernel ((B - 1 : Nat) : Real) ≤ iwaniecLogLogIncrementWeightedInterval (fun n => b n) B A - iwaniecWeightedLogKernelIntegral b B A ∧
    iwaniecLogLogIncrementWeightedInterval (fun n => b n) B A - iwaniecWeightedLogKernelIntegral b B A ≤
      b B * iwaniecLogKernel ((B - 1 : Nat) : Real) := by
  revert hbAnti hbNonneg
  induction A, hBA using Nat.le_induction with
  | base =>
      intro _hbAnti hbNonneg
      have hb : 0 ≤ b B := hbNonneg B ⟨le_rfl, le_rfl⟩
      have hK := iwaniecLogKernel_pos (x := (B : Real)) (by exact_mod_cast (show 1 < B by omega))
      have hlow := iwaniecLogKernel_at_nat_le_logLogIncrement hB
      have hhigh := logLogIncrement_le_iwaniecLogKernel_at_pred hB
      simp only [iwaniecLogLogIncrementWeightedInterval, Finset.Icc_self, Finset.sum_singleton,
        iwaniecWeightedLogKernelIntegral, intervalIntegral.integral_same, sub_zero, sub_self, zero_mul]
      exact ⟨mul_nonneg hb (hK.le.trans hlow), mul_le_mul_of_nonneg_left hhigh hb⟩
  | succ A hBA ih =>
      intro hbAnti hbNonneg
      have hBAreal : (B : Real) ≤ (A : Real) := by exact_mod_cast hBA
      have hAsucc : (A : Real) ≤ ((A + 1 : Nat) : Real) := by exact_mod_cast Nat.le_succ A
      have hprevSet : Set.Icc (B : Real) A ⊆ Set.Icc (B : Real) (A + 1 : Nat) := by
        intro x hx
        exact ⟨hx.1, hx.2.trans hAsucc⟩
      have hunitSet : Set.Icc (A : Real) (A + 1 : Nat) ⊆ Set.Icc (B : Real) (A + 1 : Nat) := by
        intro x hx
        exact ⟨hBAreal.trans hx.1, hx.2⟩
      have hprev := ih (hbAnti.mono hprevSet) (fun x hx => hbNonneg x (hprevSet hx))
      have hunitMono := hbAnti.mono hunitSet
      have hunit := iwaniecAntitoneWeightedLogKernel_unit_error b (n := A) (by omega) hunitMono
      have hBreal : (1 : Real) < B := by exact_mod_cast (show 1 < B by omega)
      have hAreal : (1 : Real) < A := hBreal.trans_le hBAreal
      have hiPrev := iwaniecAntitoneWeightedLogKernel_intervalIntegrable b hBreal hBAreal (hbAnti.mono hprevSet)
      have hiUnit := iwaniecAntitoneWeightedLogKernel_intervalIntegrable b hAreal hAsucc hunitMono
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
      have hdelta : 0 ≤ b A - b (A + 1 : Nat) :=
        sub_nonneg.mpr (hunitMono ⟨le_rfl, hAsucc⟩ ⟨hAsucc, le_rfl⟩ hAsucc)
      have hLocal := hunit.2.trans (mul_le_mul_of_nonneg_left hK hdelta)
      rw [hId]
      constructor
      · nlinarith only [hprev.1, hLocal]
      · linarith only [hprev.2, hunit.1]

theorem iwaniecWeightedLogLog_antitone_quadrature_error (b : Real → Real) {B A : Nat}
    (hB : 3 ≤ B) (hBA : B ≤ A)
    (hbAnti : AntitoneOn b (Set.Icc (B : Real) (A : Real)))
    (hbNonneg : ∀ x ∈ Set.Icc (B : Real) (A : Real), 0 ≤ b x) :
    |iwaniecLogLogIncrementWeightedInterval (fun n => b n) B A -
      iwaniecWeightedLogKernelIntegral b B A| ≤
        b B * iwaniecLogKernel ((B - 1 : Nat) : Real) := by
  have h := iwaniecWeightedLogLog_antitone_quadrature_bounds b hB hBA hbAnti hbNonneg
  have hbA : 0 ≤ b A := hbNonneg A ⟨by exact_mod_cast hBA, le_rfl⟩
  have hK : 0 ≤ iwaniecLogKernel ((B - 1 : Nat) : Real) :=
    (iwaniecLogKernel_pos (by exact_mod_cast (show 1 < B - 1 by omega))).le
  apply abs_le.mpr
  constructor
  · nlinarith only [h.1, mul_nonneg hbA hK]
  · exact h.2

end

end Erdos1212Kernel
