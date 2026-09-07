import Erdos1212Kernel.IwaniecPaperSupportFinite
import Erdos1212Kernel.IwaniecPaperARecursion

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 650000

theorem iwaniecPaperA_zero_of_one_lt {level : Real} (hy : 1 < level) (s : Real) :
    iwaniecPaperA 0 level s = 1 := by
  unfold iwaniecPaperA iwaniecPaperSupportCount
  simp [iwaniecCubicRealProductCount, iwaniecCubicRealAdmissible, hy]

theorem iwaniecPaperA_one_eq_prime_card {level s : Real} (hy : 1 < level) (hs : 2 ≤ s) :
    iwaniecPaperA 1 level s =
      1 + (iwaniecStrictPrimePool (Real.exp (Real.log level / s))).card := by
  have hh := iwaniecPaperA_odd_recursion 0 hy hs
  norm_num only [Nat.mul_zero, Nat.zero_add] at hh
  rw [hh]
  have hsum : (∑ p ∈ iwaniecStrictPrimePool (Real.exp (Real.log level / s)),
      iwaniecPaperA 0 (level / (p : Real)) (Real.log level / Real.log (p : Real) - 1)) =
      ∑ _p ∈ iwaniecStrictPrimePool (Real.exp (Real.log level / s)), (1 : Nat) := by
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨hpPrime, hpUpper⟩ := mem_iwaniecStrictPrimePool.mp hp
    have hp0 : (0 : Real) < p := by exact_mod_cast hpPrime.pos
    have hpLevel := hpUpper.trans_le (iwaniecPaperCutoff_le_level hy (by linarith))
    have hchild : 1 < level / (p : Real) := (one_lt_div hp0).mpr hpLevel
    exact iwaniecPaperA_zero_of_one_lt hchild _
  rw [hsum]
  simp

theorem iwaniecStrictPrimePool_card_add_one_le {z : Real} (hz : 1 ≤ z) :
    ((iwaniecStrictPrimePool z).card : Real) + 1 ≤ z := by
  have hsub : iwaniecStrictPrimePool z ⊆ Finset.Icc 2 (Nat.floor z) := by
    intro p hp
    obtain ⟨hprime, hpz⟩ := mem_iwaniecStrictPrimePool.mp hp
    exact Finset.mem_Icc.mpr ⟨hprime.two_le, Nat.le_floor hpz.le⟩
  have hfloor : 1 ≤ Nat.floor z := by exact (Nat.le_floor_iff (by linarith)).mpr (by simpa using hz)
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have hn : (iwaniecStrictPrimePool z).card + 1 ≤ Nat.floor z := by omega
  have hh : ((iwaniecStrictPrimePool z).card : Real) + 1 ≤ (Nat.floor z : Real) := by exact_mod_cast hn
  exact hh.trans (Nat.floor_le (by linarith))

theorem iwaniecPaperA_one_le_sqrt {level s : Real} (hy : 1 < level) (hs : 2 ≤ s) :
    (iwaniecPaperA 1 level s : Real) ≤ Real.sqrt level := by
  have hL := Real.log_pos hy
  have hcutoff : 1 ≤ Real.exp (Real.log level / s) := Real.one_le_exp (by positivity)
  rw [iwaniecPaperA_one_eq_prime_card hy hs, Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ Real.exp (Real.log level / s) := by
      have hh := iwaniecStrictPrimePool_card_add_one_le hcutoff
      linarith only [hh]
    _ ≤ Real.exp (Real.log level / 2) :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hL.le (by norm_num) hs)
    _ = Real.sqrt level := by rw [Real.exp_half, Real.exp_log (by linarith)]

end

end Erdos1212Kernel
