import Erdos1212Kernel.IwaniecLemma14Natural

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 500000

/-- Include the actual prime 2, uniformly in the upper endpoint.
All constants precede both interval endpoints. -/
theorem exists_iwaniecLemma14_natural_two_constant :
    ∃ C : Real, 0 < C ∧ ∀ B A : Nat, 2 ≤ B → B ≤ A →
      |iwaniecPrimeLogReciprocalNatInterval B A -
        ((Real.log (B : Real))⁻¹ - (Real.log (A : Real))⁻¹)| ≤
          C * Real.exp (-Real.sqrt (Real.log (B : Real))) := by
  obtain ⟨C₃, hC₃, hthree⟩ := exists_iwaniecLemma14_natural_three_constant
  let T : Real := 1 / (2 * Real.log 2)
  let D : Real := T - (Real.log 2)⁻¹ + (Real.log 3)⁻¹
  let K : Real := C₃ + |D| + |T| + 1
  let E₂ : Real := Real.exp (-Real.sqrt (Real.log 2))
  let C : Real := max C₃ (K / E₂)
  have hC : 0 < C := hC₃.trans_le (le_max_left _ _)
  have hK : K ≤ C * E₂ := (div_le_iff₀ (Real.exp_pos _)).mp (le_max_right C₃ (K / E₂))
  refine ⟨C, hC, ?_⟩
  intro B A hB hBA
  by_cases hB2 : B = 2
  · subst B
    change |iwaniecPrimeLogReciprocalNatInterval 2 A -
      ((Real.log 2)⁻¹ - (Real.log (A : Real))⁻¹)| ≤ C * E₂
    apply le_trans _ hK
    by_cases hA3 : 3 ≤ A
    · have hh := hthree 3 A (by omega) hA3
      norm_num only [Nat.cast_ofNat] at hh
      have he3 : Real.exp (-Real.sqrt (Real.log (3 : Real))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.sqrt_nonneg _))
      have hsrc : |iwaniecPrimeLogReciprocalNatInterval 3 A -
          ((Real.log 3)⁻¹ - (Real.log (A : Real))⁻¹)| ≤ C₃ :=
        hh.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left he3 hC₃.le)
      have hsplit : iwaniecPrimeLogReciprocalNatInterval 2 A -
          ((Real.log 2)⁻¹ - (Real.log (A : Real))⁻¹) =
          (iwaniecPrimeLogReciprocalNatInterval 3 A -
            ((Real.log 3)⁻¹ - (Real.log (A : Real))⁻¹)) + D := by
        rw [iwaniecPrimeLogReciprocalNatInterval_initial_two hBA]
        dsimp [D, T]
        ring
      rw [hsplit]
      calc
        _ ≤ |iwaniecPrimeLogReciprocalNatInterval 3 A -
            ((Real.log 3)⁻¹ - (Real.log (A : Real))⁻¹)| + |D| := abs_add_le _ _
        _ ≤ C₃ + |D| := add_le_add hsrc le_rfl
        _ ≤ K := by dsimp [K]; linarith [abs_nonneg T]
    · have hA2 : A = 2 := by omega
      subst A
      rw [iwaniecPrimeLogReciprocalNatInterval_initial_two (le_refl 2),
        iwaniecPrimeLogReciprocalNatInterval_eq_zero_of_lt (by omega : 2 < 3)]
      norm_num only [Nat.cast_ofNat, add_zero, sub_self, sub_zero]
      change |T| ≤ K
      dsimp [K]
      linarith [abs_nonneg D]
  · have hB3 : 3 ≤ B := by omega
    exact (hthree B A hB3 hBA).trans
      (mul_le_mul_of_nonneg_right (le_max_left C₃ (K / E₂)) (Real.exp_pos _).le)

end

end Erdos1212Kernel
