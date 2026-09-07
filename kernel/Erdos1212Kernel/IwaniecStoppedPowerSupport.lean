import Erdos1212Kernel.IwaniecPaperQSource

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 550000

/-- If the complete prime cutoff cannot support the final failed
cubic product, the exact stopped layer is empty. -/
theorem iwaniecPaperStoppedLayer_eq_zero_of_power (k : Nat) (offset : Nat) (level z : Real)
    (hpower : z ^ (k + 2) ≤ level) : iwaniecPaperStoppedLayer offset level z k = 0 := by
  induction k generalizing offset level z with
  | zero => simp
  | succ k ih =>
      rw [iwaniecPaperStoppedLayer_first_prime]
      apply Finset.sum_eq_zero
      intro p hp
      obtain ⟨hpPrime, hpz⟩ := mem_iwaniecStrictPrimePool.mp hp
      have hp0 : (0 : Real) < p := by exact_mod_cast hpPrime.pos
      have hstrict : (p : Real) ^ ((k + 1) + 2) < level :=
        (pow_lt_pow_left₀ hpz hp0.le (by omega)).trans_le hpower
      have hchild : (p : Real) ^ (k + 2) ≤ level / p := by
        apply (le_div_iff₀ hp0).mpr
        calc
          (p : Real) ^ (k + 2) * p = (p : Real) ^ ((k + 1) + 2) := by
            rw [← pow_succ] <;> congr 1 <;> omega
          _ ≤ level := hstrict.le
      by_cases hc : Even offset ∨ (p : Real) ^ 3 < level
      · rw [if_pos hc, ih (offset + 1) (level / p) p hchild, mul_zero]
      · rw [if_neg hc]
        by_cases hk : k = 0
        · subst k
          exact (hc (Or.inr hstrict)).elim
        · rw [if_neg hk]

theorem iwaniecPaperStoppedLayer_child_zero_below (k offset : Nat) (level : Real) {p : Nat}
    (hp : 0 < p) (hpower : (p : Real) ^ (k + 3) ≤ level) :
    iwaniecPaperStoppedLayer offset (level / p) p k = 0 := by
  apply iwaniecPaperStoppedLayer_eq_zero_of_power
  have hp0 : (0 : Real) < p := by exact_mod_cast hp
  apply (le_div_iff₀ hp0).mpr
  calc
    (p : Real) ^ (k + 2) * p = (p : Real) ^ (k + 3) := by rw [← pow_succ]
    _ ≤ level := hpower

/-- Removing first primes below the polynomial cutoff is an exact
zero-term removal; both child and immediate-failure branches are retained. -/
theorem iwaniecPaperStoppedLayer_first_prime_power_band (offset : Nat) (level z : Real) (k : Nat) :
    iwaniecPaperStoppedLayer offset level z (k + 1) =
      ∑ p ∈ (iwaniecStrictPrimePool z).filter (fun p : Nat => level ≤ (p : Real) ^ (k + 3)),
        if Even offset ∨ (p : Real) ^ 3 < level then
          (p : Real)⁻¹ * iwaniecPaperStoppedLayer (offset + 1) (level / p) p k
        else if k = 0 then (p : Real)⁻¹ * iwaniecPaperR (p : Real) else 0 := by
  classical
  rw [iwaniecPaperStoppedLayer_first_prime, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hband : level ≤ (p : Real) ^ (k + 3)
  · rw [if_pos hband]
  · rw [if_neg hband]
    have hsmall : (p : Real) ^ (k + 3) < level := lt_of_not_ge hband
    have hp0 := (mem_iwaniecStrictPrimePool.mp hp).1.pos
    by_cases hc : Even offset ∨ (p : Real) ^ 3 < level
    · rw [if_pos hc, iwaniecPaperStoppedLayer_child_zero_below k (offset + 1) level hp0 hsmall.le, mul_zero]
    · rw [if_neg hc]
      by_cases hk : k = 0
      · subst k
        exact (hc (Or.inr hsmall)).elim
      · rw [if_neg hk]

end

end Erdos1212Kernel
