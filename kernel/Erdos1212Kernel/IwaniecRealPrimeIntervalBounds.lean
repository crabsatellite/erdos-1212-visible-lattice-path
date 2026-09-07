import Erdos1212Kernel.IwaniecRealPrimeInterval

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 650000

theorem iwaniecWeightedRealInterval_mono_scaled (b c : Real → Real)
    {B A M : Real} (hB : 2 ≤ B) (hBA : B ≤ A)
    (hweight : ∀ x ∈ Set.Icc B A, b x ≤ M * c x) :
    iwaniecPrimeReciprocalWeightedRealInterval b B A ≤
      M * iwaniecPrimeReciprocalWeightedRealInterval c B A := by
  unfold iwaniecPrimeReciprocalWeightedRealInterval
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hprime, hpB, hpA⟩ := (iwaniec_real_prime_interval_mem (by linarith : 0 ≤ A) p).mp hp
  have hh := div_le_div_of_nonneg_right (hweight p ⟨hpB, hpA⟩) (Nat.cast_nonneg p : (0 : Real) ≤ p)
  convert hh using 1 <;> ring

/-- Closed intervals overlap only at the middle endpoint. Keeping both
copies gives this valid upper bound for nonnegative literal weights. -/
theorem iwaniecWeightedRealInterval_split_upper (b : Real → Real)
    {B M A : Real} (hB : 2 ≤ B) (hBM : B ≤ M) (hMA : M ≤ A)
    (hb : ∀ x ∈ Set.Icc B A, 0 ≤ b x) :
    iwaniecPrimeReciprocalWeightedRealInterval b B A ≤
      iwaniecPrimeReciprocalWeightedRealInterval b B M +
        iwaniecPrimeReciprocalWeightedRealInterval b M A := by
  classical
  have hM0 : 0 ≤ M := by linarith
  have hA0 : 0 ≤ A := by linarith
  let S := (Nat.primesLE (Nat.floor A)).filter (fun p : Nat => B ≤ (p : Real))
  let f : Nat → Real := fun p => b p / (p : Real)
  have hloSet : (Nat.primesLE (Nat.floor M)).filter (fun p : Nat => B ≤ (p : Real)) =
      S.filter (fun p : Nat => (p : Real) ≤ M) := by
    ext p
    simp only [S, Finset.mem_filter, Nat.mem_primesLE, Nat.le_floor_iff hM0, Nat.le_floor_iff hA0]
    constructor
    · rintro ⟨⟨hpM, hp⟩, hpB⟩
      exact ⟨⟨⟨hpM.trans hMA, hp⟩, hpB⟩, hpM⟩
    · rintro ⟨⟨⟨_hpA, hp⟩, hpB⟩, hpM⟩
      exact ⟨⟨hpM, hp⟩, hpB⟩
  have hhiSet : (Nat.primesLE (Nat.floor A)).filter (fun p : Nat => M ≤ (p : Real)) =
      S.filter (fun p : Nat => M ≤ (p : Real)) := by
    ext p
    simp only [S, Finset.mem_filter, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hpA, hp⟩, hpM⟩
      exact ⟨⟨⟨hpA, hp⟩, hBM.trans hpM⟩, hpM⟩
    · rintro ⟨⟨⟨hpA, hp⟩, _hpB⟩, hpM⟩
      exact ⟨⟨hpA, hp⟩, hpM⟩
  have hlo : iwaniecPrimeReciprocalWeightedRealInterval b B M =
      ∑ p ∈ S, if (p : Real) ≤ M then f p else 0 := by
    unfold iwaniecPrimeReciprocalWeightedRealInterval
    rw [hloSet, Finset.sum_filter]
  have hhi : iwaniecPrimeReciprocalWeightedRealInterval b M A =
      ∑ p ∈ S, if M ≤ (p : Real) then f p else 0 := by
    unfold iwaniecPrimeReciprocalWeightedRealInterval
    rw [hhiSet, Finset.sum_filter]
  rw [hlo, hhi, ← Finset.sum_add_distrib]
  change (∑ p ∈ S, f p) ≤ _
  apply Finset.sum_le_sum
  intro p hp
  have hpdata := (iwaniec_real_prime_interval_mem hA0 p).mp hp
  have hfp : 0 ≤ f p := div_nonneg (hb p ⟨hpdata.2.1, hpdata.2.2⟩) (Nat.cast_nonneg p)
  by_cases hpM : (p : Real) ≤ M
  · by_cases hMp : M ≤ (p : Real)
    · simp only [if_pos hpM, if_pos hMp]
      linarith only [hfp]
    · simp only [if_pos hpM, if_neg hMp, add_zero, le_refl]
  · have hMp : M ≤ (p : Real) := le_of_not_ge hpM
    simp only [if_neg hpM, if_pos hMp, zero_add, le_refl]

end

end Erdos1212Kernel
