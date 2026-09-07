import Erdos1212Kernel.IwaniecRealEndpointBounds

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 550000

def iwaniecPrimeReciprocalWeightedRealInterval (b : Real → Real) (B A : Real) : Real :=
  ∑ p ∈ (Nat.primesLE (Nat.floor A)).filter (fun p : Nat => B ≤ (p : Real)), b p / (p : Real)

theorem iwaniec_real_prime_interval_mem {B A : Real} (hA : 0 ≤ A) (p : Nat) :
    p ∈ (Nat.primesLE (Nat.floor A)).filter (fun p : Nat => B ≤ (p : Real)) ↔
      p.Prime ∧ B ≤ (p : Real) ∧ (p : Real) ≤ A := by
  simp only [Finset.mem_filter, Nat.mem_primesLE, Nat.le_floor_iff hA]
  tauto

theorem iwaniecWeightedRealInterval_eq_ceil_floor (b : Real → Real) (B A : Real) :
    iwaniecPrimeReciprocalWeightedRealInterval b B A =
      iwaniecPrimeReciprocalWeightedInterval (fun n => b n) (Nat.ceil B) (Nat.floor A) := by
  unfold iwaniecPrimeReciprocalWeightedRealInterval iwaniecPrimeReciprocalWeightedInterval
  apply Finset.sum_congr
  · ext p
    simp only [Finset.mem_filter, Nat.ceil_le]
  · intro p _hp
    ring

theorem iwaniecWeightedRealInterval_eq_zero_of_no_integer (b : Real → Real) {B A : Real}
    (h : Nat.floor A < Nat.ceil B) :
    iwaniecPrimeReciprocalWeightedRealInterval b B A = 0 := by
  rw [iwaniecWeightedRealInterval_eq_ceil_floor]
  unfold iwaniecPrimeReciprocalWeightedInterval
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨hpA, hpB⟩ := Finset.mem_filter.mp hp
  have hpupper := (Nat.mem_primesLE.mp hpA).1
  omega

end

end Erdos1212Kernel
