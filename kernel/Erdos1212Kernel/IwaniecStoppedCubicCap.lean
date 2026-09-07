import Erdos1212Kernel.IwaniecStoppedPowerSupport

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 550000

theorem iwaniecStrictPrimePool_cubic_filter {level : Real} (hy : 0 < level) (z : Real) :
    (iwaniecStrictPrimePool z).filter (fun p : Nat => (p : Real) ^ 3 < level) =
      iwaniecStrictPrimePool (min z (Real.exp (Real.log level / 3))) := by
  classical
  ext p
  have hc : (p : Real) ^ 3 < level ↔ (p : Real) < Real.exp (Real.log level / 3) := by
    simpa only [not_le] using not_congr (iwaniec_cube_root_band_iff hy p)
  simp only [Finset.mem_filter, mem_iwaniecStrictPrimePool, lt_min_iff, hc]
  tauto

/-- Every higher odd-offset layer ignores first primes failing the
initial cubic test. The statement deliberately excludes the rank-one layer. -/
theorem iwaniecPaperStoppedLayer_odd_cubic_cap {level : Real} (hy : 0 < level) (z : Real) (k : Nat) :
    iwaniecPaperStoppedLayer 1 level z (k + 2) =
      iwaniecPaperStoppedLayer 1 level (min z (Real.exp (Real.log level / 3))) (k + 2) := by
  classical
  have hodd : ¬Even (1 : Nat) := by decide
  have hk : k + 1 ≠ 0 := by omega
  have hks : k + 2 = (k + 1) + 1 := by omega
  rw [hks, iwaniecPaperStoppedLayer_first_prime 1 level z (k + 1),
    iwaniecPaperStoppedLayer_first_prime 1 level (min z (Real.exp (Real.log level / 3))) (k + 1)]
  simp only [hodd, false_or, if_neg hk]
  conv_lhs => rw [← Finset.sum_filter]
  rw [iwaniecStrictPrimePool_cubic_filter hy z]
  apply Finset.sum_congr rfl
  intro p hp
  have hfilter : p ∈ (iwaniecStrictPrimePool z).filter (fun p : Nat => (p : Real) ^ 3 < level) := by
    rwa [iwaniecStrictPrimePool_cubic_filter hy z]
  rw [if_pos (Finset.mem_filter.mp hfilter).2]

theorem iwaniecPaperStoppedLayer_one_cubic_cap {level : Real} (hy : 0 < level) (z : Real) :
    iwaniecPaperStoppedLayer 1 level (min z (Real.exp (Real.log level / 3))) 1 = 0 := by
  classical
  rw [iwaniecPaperStoppedLayer_one_odd]
  apply Finset.sum_eq_zero
  intro p hp
  have hfilter : p ∈ (iwaniecStrictPrimePool z).filter (fun p : Nat => (p : Real) ^ 3 < level) := by
    rwa [iwaniecStrictPrimePool_cubic_filter hy z]
  rw [if_neg (not_le.mpr (Finset.mem_filter.mp hfilter).2)]

theorem iwaniecPaperStoppedPartial_add_two (offset : Nat) (level z : Real) (depth : Nat) :
    iwaniecPaperStoppedPartial (offset + 2) level z depth = iwaniecPaperStoppedPartial offset level z depth := by
  rw [iwaniecPaperStoppedPartial_eq_sum, iwaniecPaperStoppedPartial_eq_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact iwaniecPaperStoppedLayer_add_two offset level z k

/-- The removed rank-one failure is explicit. In the even Q recursion
its outer aggregate will be exactly d2. -/
theorem iwaniecPaperStoppedPartial_odd_cubic_cap {level : Real} (hy : 0 < level) (z : Real) (depth : Nat) :
    iwaniecPaperStoppedPartial 1 level z (depth + 1) = iwaniecPaperStoppedLayer 1 level z 1 +
      iwaniecPaperStoppedPartial 1 level (min z (Real.exp (Real.log level / 3))) (depth + 1) := by
  have hcap1 : iwaniecPaperStoppedPartial 1 level (min z (Real.exp (Real.log level / 3))) 1 = 0 := by
    have hh := iwaniecPaperStoppedPartial_succ 1 level (min z (Real.exp (Real.log level / 3))) 0
    simpa only [iwaniecPaperStoppedPartial_zero, iwaniecPaperStoppedLayer_one_cubic_cap hy z, zero_add] using hh
  induction depth with
  | zero =>
      rw [iwaniecPaperStoppedPartial_succ, iwaniecPaperStoppedPartial_zero, hcap1, zero_add, add_zero]
  | succ depth ih =>
      rw [iwaniecPaperStoppedPartial_succ 1 level z (depth + 1),
        iwaniecPaperStoppedPartial_succ 1 level (min z (Real.exp (Real.log level / 3))) (depth + 1),
        ih, iwaniecPaperStoppedLayer_odd_cubic_cap hy z depth]
      ring

end

end Erdos1212Kernel
