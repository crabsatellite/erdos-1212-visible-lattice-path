import Erdos1212Kernel.IwaniecPaperAEvenInitial
import Erdos1212Kernel.IwaniecPaperAChildWeightTransport

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 650000

theorem iwaniecAuxGStart_add_two (rank : Nat) : iwaniecAuxGStart (rank + 2) = iwaniecAuxGStart rank := by
  simp [iwaniecAuxGStart, Nat.even_add]

theorem iwaniecPaperA_recursion_parameter (rank : Nat) {level s : Real}
    (hy : 1 < level) (hs : iwaniecAuxGStart (rank + 1) ≤ s) :
    iwaniecPaperA rank level s = iwaniecPaperA rank level (max (iwaniecCorollaryThreeDomainStart rank) s) ∧
      iwaniecAuxG (rank + 1) (max (iwaniecCorollaryThreeDomainStart rank) s) = iwaniecAuxG (rank + 1) s := by
  by_cases hr : Even rank
  · have hstart : iwaniecCorollaryThreeDomainStart rank = 3 := by
      norm_num [iwaniecCorollaryThreeDomainStart, iwaniecAuxGStart, hr]
    have hs1 : 1 ≤ s := by simpa [iwaniecAuxGStart, Nat.even_add_one, hr] using hs
    rw [hstart]
    by_cases hs3 : 3 ≤ s
    · rw [max_eq_right hs3]
      exact ⟨rfl, rfl⟩
    · have hsle : s ≤ 3 := le_of_not_ge hs3
      rw [max_eq_left hsle]
      refine ⟨iwaniecPaperA_even_initial hr hy (by linarith) hsle, ?_⟩
      simp only [iwaniecAuxG, Nat.even_add_one, hr, not_true_eq_false, if_false]
      rw [iwaniecAuxUpper_initial (le_refl 3), iwaniecAuxUpper_initial hsle]
  · have hstart : iwaniecCorollaryThreeDomainStart rank = 2 := by
      norm_num [iwaniecCorollaryThreeDomainStart, iwaniecAuxGStart, hr]
    have hs2 : 2 ≤ s := by simpa [iwaniecAuxGStart, Nat.even_add_one, hr] using hs
    rw [hstart, max_eq_right hs2]
    exact ⟨rfl, rfl⟩

theorem iwaniecPaperA_successor_band_recursion (n : Nat) {level s T : Real}
    (hy : 1 < level) (hs : iwaniecCorollaryThreeDomainStart (n + 1) ≤ s) (hsT : s ≤ T) :
    iwaniecPaperA (n + 1) level s = iwaniecPaperA (n + 1) level T +
      ∑ p ∈ iwaniecStrictPrimeBand (Real.exp (Real.log level / T)) (Real.exp (Real.log level / s)),
        iwaniecPaperA n (level / (p : Real)) (Real.log level / Real.log (p : Real) - 1) := by
  by_cases hn : Even n
  · obtain ⟨k, hk⟩ := hn
    have heq : n = 2 * k := by omega
    clear hk
    subst n
    have hs2 : 2 ≤ s := by
      norm_num [iwaniecCorollaryThreeDomainStart, iwaniecAuxGStart, Nat.even_add_one] at hs
      exact hs
    exact iwaniecPaperA_odd_band_recursion k hy hs2 hsT
  · obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hn
    have heq : n = 2 * k + 1 := by omega
    clear hk
    subst n
    have hs3 : 3 ≤ s := by
      norm_num [iwaniecCorollaryThreeDomainStart, iwaniecAuxGStart, Nat.even_add_one] at hs
      exact hs
    simpa only [Nat.add_assoc, show (1 : Nat) + 1 = 2 by norm_num] using
      iwaniecPaperA_even_band_recursion k hy hs3 hsT

theorem iwaniecWeightPower_max_bound {level s : Real} (hs : 1 ≤ s) :
    iwaniecAuxWeightPower level (max iwaniecAuxSZero s) ≤
      iwaniecAuxWeightPower level s * iwaniecAuxWeightPower level iwaniecAuxSZero := by
  have hs0 : 1 ≤ iwaniecAuxSZero := by linarith [iwaniecAuxSZero_large]
  have hW : 1 ≤ iwaniecAuxWeightPower level s :=
    Real.one_le_rpow (iwaniecAuxWeightBase_one_le level hs) (by linarith)
  have hW0 : 1 ≤ iwaniecAuxWeightPower level iwaniecAuxSZero :=
    Real.one_le_rpow (iwaniecAuxWeightBase_one_le level hs0) (by linarith)
  by_cases hsmall : s ≤ iwaniecAuxSZero
  · rw [max_eq_left hsmall]
    have hh := mul_le_mul_of_nonneg_right hW (by linarith : 0 ≤ iwaniecAuxWeightPower level iwaniecAuxSZero)
    simpa only [one_mul] using hh
  · rw [max_eq_right (le_of_not_ge hsmall)]
    have hh := mul_le_mul_of_nonneg_left hW0 (by linarith : 0 ≤ iwaniecAuxWeightPower level s)
    simpa only [mul_one] using hh

end

end Erdos1212Kernel
