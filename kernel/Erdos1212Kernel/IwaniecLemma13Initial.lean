import Erdos1212Kernel.IwaniecShortWeightedIntegral

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory intervalIntegral Set

set_option maxHeartbeats 600000

theorem exists_iwaniecLemma13_initial_constant :
    ∃ C : Real, 0 < C ∧ ∀ (b : Real → Real) (A : Nat), 2 ≤ A →
      MonotoneOn b (Icc 2 (A : Real)) →
      (∀ x ∈ Icc 2 (A : Real), 0 ≤ b x) →
      |iwaniecPrimeReciprocalWeightedInterval (fun n => b n) 2 A -
        (∫ x in (2 : Real)..(A : Real), b x / (x * Real.log x))| ≤
          C * b A * Real.exp (-Real.sqrt (Real.log 2)) := by
  obtain ⟨C₀, hC₀, hsource⟩ := exists_iwaniecLemma13_natural_constant
  let D := C₀ + 1 / 2 + iwaniecLogKernel 2
  let C := D * Real.exp (Real.sqrt (Real.log 2))
  have hK : 0 < iwaniecLogKernel 2 := iwaniecLogKernel_pos (by norm_num)
  have hD : 0 < D := by dsimp [D]; linarith
  have hC : 0 < C := mul_pos hD (Real.exp_pos _)
  refine ⟨C, hC, ?_⟩
  intro b A hA hbMono hbNonneg
  have hAreal : (2 : Real) ≤ A := by exact_mod_cast hA
  have hbA : 0 ≤ b A := hbNonneg A ⟨hAreal, le_rfl⟩
  have hb2 : 0 ≤ b 2 := hbNonneg 2 ⟨le_rfl, hAreal⟩
  have hb2A : b 2 ≤ b A := hbMono ⟨le_rfl, hAreal⟩ ⟨hAreal, le_rfl⟩ hAreal
  have hCeq : C * b A * Real.exp (-Real.sqrt (Real.log 2)) = D * b A := by
    calc
      _ = D * b A * (Real.exp (Real.sqrt (Real.log 2)) * Real.exp (-Real.sqrt (Real.log 2))) := by
        dsimp [C]
        ring
      _ = D * b A := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  rw [hCeq]
  by_cases hA3 : 3 ≤ A
  · have hA3real : (3 : Real) ≤ A := by exact_mod_cast hA3
    have hmono23 : MonotoneOn b (Icc (2 : Real) 3) :=
      hbMono.mono (fun _ hx => ⟨hx.1, hx.2.trans hA3real⟩)
    have hmono3A : MonotoneOn b (Icc (3 : Real) A) :=
      hbMono.mono (fun _ hx => ⟨by linarith [hx.1], hx.2⟩)
    have hnonneg3A : ∀ x ∈ Icc (3 : Real) A, 0 ≤ b x :=
      fun x hx => hbNonneg x ⟨by linarith [hx.1], hx.2⟩
    have hsrc := hsource b 3 A (by omega) hA3 hmono3A hnonneg3A
    have hdecay : Real.exp (-Real.sqrt (Real.log (3 : Real))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.sqrt_nonneg _))
    have hsrc' : |iwaniecPrimeReciprocalWeightedInterval (fun n => b n) 3 A -
        (∫ x in (3 : Real)..(A : Real), b x / (x * Real.log x))| ≤ C₀ * b A := by
      have hm := mul_le_mul_of_nonneg_left hdecay (mul_nonneg hC₀.le hbA)
      exact hsrc.trans (by simpa only [mul_one, Nat.cast_ofNat] using hm)
    have hi23 := iwaniecWeightedIntegral_intervalIntegrable b (by norm_num : (1 : Real) < 2)
      (by norm_num : (2 : Real) ≤ 3) hmono23
    have hi3A := iwaniecWeightedIntegral_intervalIntegrable b (by norm_num : (1 : Real) < 3)
      hA3real hmono3A
    have hisplit := intervalIntegral.integral_add_adjacent_intervals hi23 hi3A
    have hshort := iwaniecShortWeightedIntegral_bound b (B := 2) (u := 2) (v := 3) (M := b A)
      (by norm_num) le_rfl (by norm_num) (by
        intro x hx
        have hxA : x ∈ Icc (2 : Real) A := ⟨hx.1, hx.2.trans hA3real⟩
        exact ⟨hbNonneg x hxA, hbMono hxA ⟨hAreal, le_rfl⟩ hxA.2⟩)
    norm_num only [show (3 : Real) - 2 = 1 by norm_num, one_mul] at hshort
    have hsum := iwaniecWeightedPrimeInterval_initial_two (fun n => b n) hA
    have hdecomp : iwaniecPrimeReciprocalWeightedInterval (fun n => b n) 2 A -
        (∫ x in (2 : Real)..(A : Real), b x / (x * Real.log x)) =
        (iwaniecPrimeReciprocalWeightedInterval (fun n => b n) 3 A -
          (∫ x in (3 : Real)..(A : Real), b x / (x * Real.log x))) +
        ((1 / 2 : Real) * b 2 - (∫ x in (2 : Real)..3, b x / (x * Real.log x))) := by
      rw [hsum, ← hisplit]
      norm_num only [Nat.cast_ofNat]
      ring
    rw [hdecomp]
    have hhalf : |(1 / 2 : Real) * b 2| ≤ (1 / 2 : Real) * b A := by
      rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hb2A (by norm_num)
    calc
      _ ≤ |iwaniecPrimeReciprocalWeightedInterval (fun n => b n) 3 A -
          (∫ x in (3 : Real)..(A : Real), b x / (x * Real.log x))| +
          |(1 / 2 : Real) * b 2 - (∫ x in (2 : Real)..3, b x / (x * Real.log x))| := abs_add_le _ _
      _ ≤ C₀ * b A + ((1 / 2 : Real) * b A + b A * iwaniecLogKernel 2) :=
        add_le_add hsrc' ((abs_sub _ _).trans (add_le_add hhalf hshort))
      _ = _ := by dsimp [D]; ring
  · have hAtwo : A = 2 := by omega
    subst A
    have hzero : iwaniecPrimeReciprocalWeightedInterval (fun n => b n) 3 2 = 0 := by
      unfold iwaniecPrimeReciprocalWeightedInterval
      apply Finset.sum_eq_zero
      intro p hp
      obtain ⟨hp2, hp3⟩ := Finset.mem_filter.mp hp
      have hpupper := (Nat.mem_primesLE.mp hp2).1
      omega
    have hsum : iwaniecPrimeReciprocalWeightedInterval (fun n => b n) 2 2 = (1 / 2 : Real) * b 2 := by
      simpa only [hzero, Nat.cast_ofNat, add_zero] using
        iwaniecWeightedPrimeInterval_initial_two (fun n => b n) (le_refl 2)
    rw [hsum]
    norm_num only [Nat.cast_ofNat, intervalIntegral.integral_same, sub_zero]
    rw [abs_of_nonneg (by positivity)]
    have hcoeff : (1 / 2 : Real) ≤ D := by dsimp [D]; linarith
    exact mul_le_mul_of_nonneg_right hcoeff hb2

theorem exists_iwaniecLemma13_natural_two_constant :
    ∃ C : Real, 0 < C ∧ ∀ (b : Real → Real) (B A : Nat), 2 ≤ B → B ≤ A →
      MonotoneOn b (Icc (B : Real) (A : Real)) →
      (∀ x ∈ Icc (B : Real) (A : Real), 0 ≤ b x) →
      |iwaniecPrimeReciprocalWeightedInterval (fun n => b n) B A -
        (∫ x in (B : Real)..(A : Real), b x / (x * Real.log x))| ≤
          C * b A * Real.exp (-Real.sqrt (Real.log (B : Real))) := by
  obtain ⟨C₃, hC₃, hthree⟩ := exists_iwaniecLemma13_natural_constant
  obtain ⟨C₂, _hC₂, htwo⟩ := exists_iwaniecLemma13_initial_constant
  refine ⟨max C₃ C₂, hC₃.trans_le (le_max_left _ _), ?_⟩
  intro b B A hB hBA hbMono hbNonneg
  have hbA : 0 ≤ b A := hbNonneg A ⟨by exact_mod_cast hBA, le_rfl⟩
  by_cases hBtwo : B = 2
  · subst B
    have hh := htwo b A hBA hbMono hbNonneg
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right C₃ C₂) hbA) (Real.exp_pos _).le)
  · have hBthree : 3 ≤ B := by omega
    exact (hthree b B A hBthree hBA hbMono hbNonneg).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left C₃ C₂) hbA)
        (Real.exp_pos _).le)

end

end Erdos1212Kernel
