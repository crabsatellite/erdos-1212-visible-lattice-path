import Erdos1212Kernel.IwaniecStoppedRootSupport

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

/-- Odd d recurrence before deletion of zero first-prime terms. -/
theorem iwaniecPaperD_odd_recursion_unbanded (n : Nat) {level s : Real}
    (hy : 1 < level) (hs : 3 ≤ s) :
    iwaniecPaperD (2 * n + 1) level s =
      ∑ p ∈ iwaniecStrictPrimePool (Real.exp (Real.log level / s)),
        iwaniecPaperD (2 * n) (level / p) (Real.log level / Real.log (p : Real) - 1) / (p : Real) := by
  classical
  have ho : ¬Even (2 * n + 1) := Nat.not_even_iff_odd.mpr ⟨n, by omega⟩
  have he : Even (2 * n) := ⟨n, by omega⟩
  conv_lhs => simp only [iwaniecPaperD, if_neg ho, max_eq_right hs]
  rw [iwaniecPaperStoppedLayer_first_prime 1 level _ (2 * n)]
  apply Finset.sum_congr rfl
  intro p hp
  have hprime := (mem_iwaniecStrictPrimePool.mp hp).1
  have hp1 : (1 : Real) < p := by exact_mod_cast hprime.one_lt
  have hchild := (iwaniecStoppedChild_domain hy (show 1 ≤ s by linarith) hp).1
  have hcube := iwaniecPaperCutoff_prime_cube_lt hy hs hp
  rw [if_pos (Or.inr hcube), iwaniecPaperStoppedLayer_add_two 0 (level / p) p (2 * n),
    ← iwaniecPaperChild_logParameter (zero_lt_one.trans hy) hprime,
    iwaniecPaperD_even_logRatio he hchild hp1]
  ring

/-- The even recurrence applies to d4 and higher. The d2 base is not
silently replaced by a capped rank-one child. -/
theorem iwaniecPaperD_even_recursion_unbanded (n : Nat) (hn : 1 ≤ n) {level s : Real}
    (hy : 1 < level) (hs : 2 ≤ s) :
    iwaniecPaperD (2 * n + 2) level s =
      ∑ p ∈ iwaniecStrictPrimePool (Real.exp (Real.log level / s)),
        iwaniecPaperD (2 * n + 1) (level / p) (Real.log level / Real.log (p : Real) - 1) / (p : Real) := by
  classical
  have he : Even (2 * n + 2) := ⟨n + 1, by omega⟩
  have ho : ¬Even (2 * n + 1) := Nat.not_even_iff_odd.mpr ⟨n, by omega⟩
  have he0 : Even (0 : Nat) := ⟨0, rfl⟩
  conv_lhs => simp only [iwaniecPaperD, if_pos he]
  rw [iwaniecPaperStoppedLayer_first_prime 0 level _ (2 * n + 1)]
  simp only [he0, true_or, if_true, zero_add]
  apply Finset.sum_congr rfl
  intro p hp
  have hprime := (mem_iwaniecStrictPrimePool.mp hp).1
  have hp1 : (1 : Real) < p := by exact_mod_cast hprime.one_lt
  have hchild := (iwaniecStoppedChild_domain hy (show 1 ≤ s by linarith) hp).1
  rw [← iwaniecPaperChild_logParameter (zero_lt_one.trans hy) hprime,
    iwaniecPaperD_odd_logRatio ho hchild hp1]
  have hcap := iwaniecPaperStoppedLayer_odd_cubic_cap (zero_lt_one.trans hchild) (p : Real) (2 * n - 1)
  have hk : 2 * n - 1 + 2 = 2 * n + 1 := by omega
  rw [hk] at hcap
  rw [hcap]
  ring

end

end Erdos1212Kernel
