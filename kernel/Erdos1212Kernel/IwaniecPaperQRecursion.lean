import Erdos1212Kernel.IwaniecPaperDRecursion

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

theorem iwaniecPaperD2_eq_first_odd_failure (level z : Real) :
    iwaniecPaperD2At level z = ∑ p ∈ iwaniecStrictPrimePool z,
      (p : Real)⁻¹ * iwaniecPaperStoppedLayer 1 (level / p) p 1 := by
  have he0 : Even (0 : Nat) := ⟨0, rfl⟩
  have hh := iwaniecPaperStoppedLayer_first_prime 0 level z 1
  simpa only [show (1 : Nat) + 1 = 2 by rfl, iwaniecPaperStoppedLayer_two_eq_d2,
    he0, true_or, if_true, zero_add] using hh

theorem iwaniecPaperQ_odd_recursion_unbanded (n : Nat) {level s : Real}
    (hy : 1 < level) (hs : 3 ≤ s) :
    iwaniecPaperQ (2 * n + 1) level s =
      ∑ p ∈ iwaniecStrictPrimePool (Real.exp (Real.log level / s)),
        iwaniecPaperQ (2 * n) (level / p) (Real.log level / Real.log (p : Real) - 1) / (p : Real) := by
  classical
  have ho : ¬Even (2 * n + 1) := Nat.not_even_iff_odd.mpr ⟨n, by omega⟩
  have he : Even (2 * n) := ⟨n, by omega⟩
  rw [iwaniecPaperQ_odd_eq_partial ho, max_eq_right hs,
    iwaniecPaperStoppedPartial_first_prime 1 level _ (2 * n)]
  apply Finset.sum_congr rfl
  intro p hp
  have hprime := (mem_iwaniecStrictPrimePool.mp hp).1
  have hp1 : (1 : Real) < p := by exact_mod_cast hprime.one_lt
  have hchild := (iwaniecStoppedChild_domain hy (show 1 ≤ s by linarith) hp).1
  have hcube := iwaniecPaperCutoff_prime_cube_lt hy hs hp
  rw [if_pos (Or.inr hcube), iwaniecPaperStoppedPartial_add_two 0 (level / p) p (2 * n),
    ← iwaniecPaperChild_logParameter (zero_lt_one.trans hy) hprime,
    iwaniecPaperQ_even_logRatio he hchild hp1]
  ring

/-- The even Q recurrence retains the exact d2 correction from the
uncapped child's first failure. This includes the base n=0. -/
theorem iwaniecPaperQ_even_recursion_unbanded (n : Nat) {level s : Real}
    (hy : 1 < level) (hs : 2 ≤ s) :
    iwaniecPaperQ (2 * n + 2) level s =
      (∑ p ∈ iwaniecStrictPrimePool (Real.exp (Real.log level / s)),
        iwaniecPaperQ (2 * n + 1) (level / p) (Real.log level / Real.log (p : Real) - 1) / (p : Real)) +
      iwaniecPaperD2 level s := by
  classical
  have he : Even (2 * n + 2) := ⟨n + 1, by omega⟩
  have ho : ¬Even (2 * n + 1) := Nat.not_even_iff_odd.mpr ⟨n, by omega⟩
  have he0 : Even (0 : Nat) := ⟨0, rfl⟩
  rw [iwaniecPaperQ_even_eq_partial he,
    iwaniecPaperStoppedPartial_first_prime 0 level _ (2 * n + 1)]
  simp only [he0, true_or, if_true, zero_add]
  calc
    _ = ∑ p ∈ iwaniecStrictPrimePool (Real.exp (Real.log level / s)),
        ((p : Real)⁻¹ * iwaniecPaperStoppedLayer 1 (level / p) p 1 +
          iwaniecPaperQ (2 * n + 1) (level / p) (Real.log level / Real.log (p : Real) - 1) / (p : Real)) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hprime := (mem_iwaniecStrictPrimePool.mp hp).1
      have hp1 : (1 : Real) < p := by exact_mod_cast hprime.one_lt
      have hchild := (iwaniecStoppedChild_domain hy (show 1 ≤ s by linarith) hp).1
      rw [iwaniecPaperStoppedPartial_odd_cubic_cap (zero_lt_one.trans hchild) (p : Real) (2 * n),
        ← iwaniecPaperChild_logParameter (zero_lt_one.trans hy) hprime,
        iwaniecPaperQ_odd_logRatio ho hchild hp1]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← iwaniecPaperD2_eq_first_odd_failure]
      unfold iwaniecPaperD2
      exact add_comm _ _

end

end Erdos1212Kernel
