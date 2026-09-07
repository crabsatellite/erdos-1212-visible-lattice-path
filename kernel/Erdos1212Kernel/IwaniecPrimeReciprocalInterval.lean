import Erdos1212Kernel.IwaniecReferencePrimeCutoff

namespace Erdos1212Kernel

noncomputable section

open Filter

set_option maxHeartbeats 1200000

def iwaniecPrimeReciprocalRemainder (N : Nat) : Real :=
  Erdos696.Mertens.primeReciprocalSum N -
    Real.log (Real.log N) - Erdos696.Mertens.meisselMertensConstant

theorem tendsto_iwaniecPrimeReciprocalRemainder_zero :
    Tendsto iwaniecPrimeReciprocalRemainder atTop (nhds 0) := by
  have h := Erdos696.Mertens.mertens_second_theorem.sub_const
    Erdos696.Mertens.meisselMertensConstant
  simpa [iwaniecPrimeReciprocalRemainder] using h

def iwaniecPrimeReciprocalInterval (B A : Nat) : Real :=
  ∑ p ∈ (Nat.primesLE A).filter (fun p => B ≤ p), (p : Real)⁻¹

theorem primesLE_sdiff_eq_interval
    {B A : Nat} (hBA : B ≤ A) :
    Nat.primesLE A \ Nat.primesLE (B - 1) =
      (Nat.primesLE A).filter (fun p => B ≤ p) := by
  ext p
  simp only [Finset.mem_sdiff, Nat.mem_primesLE, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hpA, hpPrime⟩, hnot⟩
    refine ⟨⟨hpA, hpPrime⟩, ?_⟩
    have hnotLe : ¬p ≤ B - 1 := by
      intro hp
      exact hnot ⟨hp, hpPrime⟩
    omega
  · rintro ⟨⟨hpA, hpPrime⟩, hpB⟩
    refine ⟨⟨hpA, hpPrime⟩, ?_⟩
    intro hsmall
    have hpSmall := hsmall.1
    have hpTwo := hpPrime.two_le
    omega

theorem primesLE_pred_subset
    {B A : Nat} (hBA : B ≤ A) :
    Nat.primesLE (B - 1) ⊆ Nat.primesLE A := by
  intro p hp
  have hdata := Nat.mem_primesLE.mp hp
  exact Nat.mem_primesLE.mpr ⟨by omega, hdata.2⟩

theorem iwaniecPrimeReciprocalInterval_eq_sub
    {B A : Nat} (hBA : B ≤ A) :
    iwaniecPrimeReciprocalInterval B A =
      Erdos696.Mertens.primeReciprocalSum A -
        Erdos696.Mertens.primeReciprocalSum (B - 1) := by
  unfold iwaniecPrimeReciprocalInterval
  rw [← primesLE_sdiff_eq_interval hBA]
  have hsum := Finset.sum_sdiff
    (f := fun p : Nat => (p : Real)⁻¹) (primesLE_pred_subset hBA)
  calc
    ∑ p ∈ Nat.primesLE A \ Nat.primesLE (B - 1), (p : Real)⁻¹ =
        (∑ p ∈ Nat.primesLE A, (p : Real)⁻¹) -
          ∑ p ∈ Nat.primesLE (B - 1), (p : Real)⁻¹ := by linarith
    _ = Erdos696.Mertens.primeReciprocalSum A -
        Erdos696.Mertens.primeReciprocalSum (B - 1) := by
      simp only [Erdos696.Mertens.primeReciprocalSum,
        Nat.primesLE_eq_filter_range, one_div]

theorem iwaniecPrimeReciprocalInterval_error_eq
    {B A : Nat} (hB : 1 ≤ B) (hBA : B ≤ A) :
    iwaniecPrimeReciprocalInterval B A -
        (Real.log (Real.log A) - Real.log (Real.log (B - 1))) =
      iwaniecPrimeReciprocalRemainder A -
        iwaniecPrimeReciprocalRemainder (B - 1) := by
  rw [iwaniecPrimeReciprocalInterval_eq_sub hBA]
  unfold iwaniecPrimeReciprocalRemainder
  rw [Nat.cast_sub hB]
  norm_num
  ring

/-- Uniform tail form of the Mertens input in Iwaniec 1971, Lemma 13.
The later effective estimate must strengthen its right side, but the exact
finite-interval transport and quantifier order are already fixed here. -/
theorem eventually_iwaniecPrimeReciprocalInterval_error_lt
    {ε : Real} (hε : 0 < ε) :
    ∃ N₀ : Nat, ∀ B A : Nat,
      N₀ + 1 ≤ B → B ≤ A →
      |iwaniecPrimeReciprocalInterval B A -
        (Real.log (Real.log A) - Real.log (Real.log (B - 1)))| < 2 * ε := by
  rcases Metric.tendsto_atTop.mp tendsto_iwaniecPrimeReciprocalRemainder_zero
      ε hε with ⟨N₀, hN₀⟩
  refine ⟨N₀, ?_⟩
  intro B A hB hBA
  rw [iwaniecPrimeReciprocalInterval_error_eq (by omega : 1 ≤ B) hBA]
  have hA0 : N₀ ≤ A := by omega
  have hB0 : N₀ ≤ B - 1 := by omega
  have hA := hN₀ A hA0
  have hB' := hN₀ (B - 1) hB0
  rw [dist_zero_right, Real.norm_eq_abs] at hA hB'
  calc
    |iwaniecPrimeReciprocalRemainder A -
        iwaniecPrimeReciprocalRemainder (B - 1)| ≤
      |iwaniecPrimeReciprocalRemainder A| +
        |iwaniecPrimeReciprocalRemainder (B - 1)| := abs_sub _ _
    _ < 2 * ε := by linarith

end

end Erdos1212Kernel
