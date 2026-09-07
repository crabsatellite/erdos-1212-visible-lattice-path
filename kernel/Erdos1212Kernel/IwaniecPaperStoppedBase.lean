import Erdos1212Kernel.IwaniecPaperStoppedPartial
import Erdos1212Kernel.IwaniecLemma16

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 550000

theorem iwaniecPaperStoppedLayer_one_odd (level z : Real) :
    iwaniecPaperStoppedLayer 1 level z 1 = ∑ p ∈ iwaniecStrictPrimePool z,
      if level ≤ (p : Real) ^ 3 then iwaniecPaperR (p : Real) / p else 0 := by
  classical
  rw [show (1 : Nat) = 0 + 1 by rfl, iwaniecPaperStoppedLayer_first_prime]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hf : level ≤ (p : Real) ^ 3
  · have hn : ¬(p : Real) ^ 3 < level := not_lt.mpr hf
    norm_num [hf, hn] <;> ring
  · have hl : (p : Real) ^ 3 < level := lt_of_not_ge hf
    norm_num [hf, hl] <;> ring

/-- The new exact layer is the previously proved literal d₂ sum,
not a second independent model of that base case. -/
theorem iwaniecPaperStoppedLayer_two_eq_d2 (level z : Real) :
    iwaniecPaperStoppedLayer 0 level z 2 = iwaniecPaperD2At level z := by
  classical
  have hevenZero : Even (0 : Nat) := ⟨0, rfl⟩
  rw [show (2 : Nat) = 1 + 1 by rfl, iwaniecPaperStoppedLayer_first_prime]
  norm_num only [hevenZero, true_or, if_true, zero_add]
  unfold iwaniecPaperD2At
  apply Finset.sum_congr rfl
  intro p hp
  rw [iwaniecPaperStoppedLayer_one_odd, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hf : level / p ≤ (q : Real) ^ 3
  · rw [if_pos hf, if_pos hf]
    ring
  · rw [if_neg hf, if_neg hf, mul_zero]

theorem iwaniecPaperStoppedPartial_two_eq_d2 (level z : Real) :
    iwaniecPaperStoppedPartial 0 level z 2 = iwaniecPaperD2At level z := by
  have hl1 : iwaniecPaperStoppedLayer 0 level z 1 = 0 :=
    iwaniecPaperStoppedLayer_parity 0 level z 1 (by decide)
  have hp1 : iwaniecPaperStoppedPartial 0 level z 1 = 0 := by
    have hh := iwaniecPaperStoppedPartial_succ 0 level z 0
    simpa only [iwaniecPaperStoppedPartial_zero, hl1, zero_add] using hh
  have hh := iwaniecPaperStoppedPartial_succ 0 level z 1
  rw [hp1, zero_add] at hh
  exact hh.trans (iwaniecPaperStoppedLayer_two_eq_d2 level z)

/-- Consume the existing unconditional Lemma 16 as the base estimate
for the cumulative stopped mass now connected to the original main term. -/
theorem exists_iwaniecPaperStoppedPartial_two_bound :
    ∃ C : Real, 0 < C ∧ ∀ level s : Real, 1 < level → 2 ≤ s →
      Real.exp Real.eulerMascheroniConstant *
        iwaniecPaperStoppedPartial 0 level (Real.exp (Real.log level / s)) 2 <
      iwaniecGTwo s / Real.log level + C * Real.exp (-Real.sqrt (Real.log level / 6)) := by
  obtain ⟨C, hC, hbase⟩ := exists_iwaniecLemma16_constant
  refine ⟨C, hC, ?_⟩
  intro level s hy hs
  rw [iwaniecPaperStoppedPartial_two_eq_d2]
  exact hbase level s hy hs

end

end Erdos1212Kernel
