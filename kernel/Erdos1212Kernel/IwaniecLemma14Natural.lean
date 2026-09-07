import Erdos1212Kernel.IwaniecLemma14Integral
import Erdos1212Kernel.IwaniecShortWeightedIntegral

namespace Erdos1212Kernel

noncomputable section

open Set

set_option maxHeartbeats 500000

def iwaniecPrimeLogReciprocalNatInterval (B A : Nat) : Real :=
  ∑ p ∈ (Nat.primesLE A).filter (fun p => B ≤ p), 1 / ((p : Real) * Real.log (p : Real))

theorem iwaniecPrimeLogReciprocalNatInterval_eq_weighted (B A : Nat) :
    iwaniecPrimeLogReciprocalNatInterval B A =
      iwaniecPrimeReciprocalWeightedInterval (fun n => (Real.log (n : Real))⁻¹) B A := by
  unfold iwaniecPrimeLogReciprocalNatInterval iwaniecPrimeReciprocalWeightedInterval
  apply Finset.sum_congr rfl
  intro p hp
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

theorem iwaniecPrimeLogReciprocalNatInterval_eq_zero_of_lt {B A : Nat} (h : A < B) :
    iwaniecPrimeLogReciprocalNatInterval B A = 0 := by
  unfold iwaniecPrimeLogReciprocalNatInterval
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨hpA, hpB⟩ := Finset.mem_filter.mp hp
  have hpupper := (Nat.mem_primesLE.mp hpA).1
  omega

/-- Literal Lemma 14 at integer endpoints at least 3, proved by the
decreasing-weight Abel argument with the effective Mertens input. -/
theorem exists_iwaniecLemma14_natural_three_constant :
    ∃ C : Real, 0 < C ∧ ∀ B A : Nat, 3 ≤ B → B ≤ A →
      |iwaniecPrimeLogReciprocalNatInterval B A -
        ((Real.log (B : Real))⁻¹ - (Real.log (A : Real))⁻¹)| ≤
          C * Real.exp (-Real.sqrt (Real.log (B : Real))) := by
  obtain ⟨C, hC, hsrc⟩ := exists_iwaniecAntitonePrime_natural_constant
  refine ⟨2 * C, by positivity, ?_⟩
  intro B A hB hBA
  have hB1 : (1 : Real) < B := by exact_mod_cast (show 1 < B by omega)
  have hBAreal : (B : Real) ≤ A := by exact_mod_cast hBA
  have hsub : Icc (B : Real) (A : Real) ⊆ Ioi 1 := fun x hx => hB1.trans_le hx.1
  have hanti := iwaniec_inv_log_antitoneOn.mono hsub
  have hnonneg : ∀ x ∈ Icc (B : Real) (A : Real), 0 ≤ (Real.log x)⁻¹ := by
    intro x hx
    exact inv_nonneg.mpr (Real.log_pos (hsub hx)).le
  have hh := hsrc (fun x => (Real.log x)⁻¹) B A hB hBA hanti hnonneg
  rw [iwaniec_inv_log_integral hB1 hBAreal] at hh
  rw [iwaniecPrimeLogReciprocalNatInterval_eq_weighted]
  have hhalf : (1 / 2 : Real) ≤ Real.log (B : Real) :=
    iwaniec_half_le_log_two.trans (Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ B by omega)))
  have hweight : (Real.log (B : Real))⁻¹ ≤ 2 := by
    have hw : (1 : Real) / Real.log (B : Real) ≤ 2 :=
      (div_le_iff₀ (Real.log_pos hB1)).mpr (by linarith)
    simpa only [one_div] using hw
  calc
    _ ≤ C * (Real.log (B : Real))⁻¹ * Real.exp (-Real.sqrt (Real.log (B : Real))) := hh
    _ ≤ C * 2 * Real.exp (-Real.sqrt (Real.log (B : Real))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hweight hC.le) (Real.exp_pos _).le
    _ = _ := by ring

theorem iwaniecPrimeLogReciprocalNatInterval_initial_two {A : Nat} (hA : 2 ≤ A) :
    iwaniecPrimeLogReciprocalNatInterval 2 A =
      1 / (2 * Real.log 2) + iwaniecPrimeLogReciprocalNatInterval 3 A := by
  rw [iwaniecPrimeLogReciprocalNatInterval_eq_weighted,
    iwaniecPrimeLogReciprocalNatInterval_eq_weighted]
  rw [iwaniecWeightedPrimeInterval_initial_two _ hA]
  norm_num only [Nat.cast_ofNat]
  ring

end

end Erdos1212Kernel
