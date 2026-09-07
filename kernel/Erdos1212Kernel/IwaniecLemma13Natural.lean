import Erdos1212Kernel.IwaniecEffectivePrimeRemainder
import Erdos1212Kernel.IwaniecQuadratureSourceRate

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory intervalIntegral Set

set_option maxHeartbeats 650000

/-- Integer-endpoint form with the exact coefficient-one source rate.
The constant is uniform over endpoints and all nonnegative increasing
weights on the original interval; no analytic premise remains. -/
theorem exists_iwaniecLemma13_natural_constant :
    ∃ C : Real, 0 < C ∧ ∀ (b : Real → Real) (B A : Nat), 3 ≤ B → B ≤ A →
      MonotoneOn b (Icc (B : Real) (A : Real)) →
      (∀ x ∈ Icc (B : Real) (A : Real), 0 ≤ b x) →
      |iwaniecPrimeReciprocalWeightedInterval (fun n => b n) B A -
        (∫ x in (B : Real)..(A : Real), b x / (x * Real.log x))| ≤
          C * b A * Real.exp (-Real.sqrt (Real.log (B : Real))) := by
  obtain ⟨M, hM, hrem⟩ := exists_iwaniecPrimeReciprocalRemainder_unit_error_all
  let C := iwaniecQuadratureSourceConstant + 2 * M * Real.exp 1
  have hC : 0 < C := by
    have hq := iwaniecQuadratureSourceConstant_pos
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro b B A hB hBA hbMono hbNonneg
  let e := M * Real.exp 1 * Real.exp (-Real.sqrt (Real.log (B : Real)))
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hBn : (3 : Real) ≤ B := by exact_mod_cast hB
  have hbN : ∀ n ∈ Finset.Icc B A, 0 ≤ b n := by
    intro n hn
    obtain ⟨hnB, hnA⟩ := Finset.mem_Icc.mp hn
    exact hbNonneg n ⟨by exact_mod_cast hnB, by exact_mod_cast hnA⟩
  have hbI : ∀ n ∈ Finset.Ico B A, b n ≤ b (n + 1 : Nat) := by
    intro n hn
    obtain ⟨hnB, hnA⟩ := Finset.mem_Ico.mp hn
    apply hbMono
    · exact ⟨by exact_mod_cast hnB, by exact_mod_cast hnA.le⟩
    · exact ⟨by exact_mod_cast (show B ≤ n + 1 by omega), by exact_mod_cast (show n + 1 ≤ A by omega)⟩
    · exact_mod_cast Nat.le_succ n
  have hremI : ∀ n ∈ Finset.Icc (B - 1) A, |iwaniecPrimeReciprocalRemainder n| ≤ e := by
    intro n hn
    have hnlower := (Finset.mem_Icc.mp hn).1
    have hpred : ((B - 1 : Nat) : Real) = (B : Real) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ B), Nat.cast_one]
    have hny : (B : Real) - 1 ≤ (n : Real) := by rw [← hpred]; exact_mod_cast hnlower
    have hd := iwaniec_unit_decay_le_pred_envelope hBn hny
    have hm := (hrem n).trans (mul_le_mul_of_nonneg_left hd hM.le)
    simpa only [e, mul_assoc] using hm
  have hAbel := abs_iwaniecPrimeReciprocalRemainderAbel_le (fun n => b n) hBA he hbN hbI hremI
  have hQuad := iwaniecWeightedPrimeIntegral_isolated_source_error b hB hBA hbMono hbNonneg
  let W := iwaniecPrimeReciprocalWeightedInterval (fun n => b n) B A
  let J := ∫ x in (B : Real)..(A : Real), b x / (x * Real.log x)
  let R := iwaniecPrimeReciprocalRemainderAbel (fun n => b n) B A
  have htri := abs_add_le (W - J - R) R
  rw [sub_add_cancel] at htri
  calc
    _ ≤ |W - J - R| + |R| := htri
    _ ≤ iwaniecQuadratureSourceConstant * b A * Real.exp (-Real.sqrt (Real.log (B : Real))) +
        2 * e * b A := add_le_add hQuad hAbel
    _ = _ := by dsimp [C, e]; ring

end

end Erdos1212Kernel
