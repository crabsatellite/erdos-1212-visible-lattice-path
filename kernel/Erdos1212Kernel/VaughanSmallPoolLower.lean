import Erdos1212Kernel.IwaniecStrictPoolReference

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 700000

theorem vaughanSieveCutoff_one_le {A level : Real}
    (hA : 1 ≤ A) (hy : 1 < level) (hlog : 6 * A ≤ Real.log level) :
    1 ≤ vaughanSieveCutoff A level := by
  rw [vaughanSieveCutoff_eq_exp A (zero_lt_one.trans hy)]
  have harg : 2 ≤ Real.log level / 2 - A := by linarith only [hA, hlog]
  have hh := Real.add_one_le_exp (Real.log level / 2 - A)
  linarith only [harg, hh]

theorem vaughanSieveCutoff_add_one_le_sqrt {A level : Real}
    (hA : 1 ≤ A) (hy : 1 < level) (hlog : 6 * A ≤ Real.log level) :
    vaughanSieveCutoff A level + 1 ≤ Real.sqrt level := by
  have hlogle := Real.log_le_sub_one_of_pos (zero_lt_one.trans hy)
  have hy4 : (4 : Real) ≤ level := by linarith only [hA, hlog, hlogle]
  have hroot := Real.sqrt_le_sqrt hy4
  norm_num at hroot
  have hExp : (2 : Real) ≤ Real.exp A :=
    Real.exp_one_gt_two.le.trans (Real.exp_le_exp.mpr hA)
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 2) hExp
  have hdecay : Real.exp (-A) ≤ (1 / 2 : Real) := by
    rw [Real.exp_neg]
    simpa only [one_div] using hinv
  have hscaled := mul_le_mul_of_nonneg_left hdecay (Real.sqrt_nonneg level)
  unfold vaughanSieveCutoff
  nlinarith only [hscaled, hroot]

theorem vaughanSieve_reference_square {A : Real} {level : Nat}
    (hA : 1 ≤ A) (hy : 1 < (level : Real)) (hlog : 6 * A ≤ Real.log (level : Real)) :
    iwaniecStrictReferenceCutoff (iwaniecStrictPrimePool (vaughanSieveCutoff A level)).card ^ 2 ≤ level := by
  let Z := iwaniecStrictReferenceCutoff (iwaniecStrictPrimePool (vaughanSieveCutoff A level)).card
  have hZ := iwaniecStrictReferenceCutoff_card_le_add_one
    (vaughanSieveCutoff_one_le hA hy hlog)
  have hroot := hZ.trans (vaughanSieveCutoff_add_one_le_sqrt hA hy hlog)
  have hsq := pow_le_pow_left₀ (show (0 : Real) ≤ Z by positivity) hroot 2
  have hlevel0 : (0 : Real) ≤ level := by positivity
  rw [Real.sq_sqrt hlevel0] at hsq
  exact_mod_cast hsq

/-- Vaughan's small-prime pool main term, before the interval support
error. The coefficient 3A retains one unit of A for each later loss. -/
theorem exists_vaughanSieve_main_lower :
    ∃ A₀ Y : Real, 1 ≤ A₀ ∧ 1 < Y ∧ ∀ (A : Real) (level : Nat),
      A₀ ≤ A → Y ≤ (level : Real) → 6 * A ≤ Real.log (level : Real) →
      3 * A / Real.log (level : Real) ^ 2 <
        iwaniecCubicWeightedMainExpansion
          ((iwaniecStrictPrimePool (vaughanSieveCutoff A level)).card + 1) level
          (iwaniecStrictPrimePool (vaughanSieveCutoff A level)) := by
  obtain ⟨B, Y, hB, hY, hmain⟩ := exists_iwaniecCubicMain_uniform_small_parameter
  let A₀ := max 1 B
  refine ⟨A₀, Y, le_max_left _ _, hY, ?_⟩
  intro A level hA hlevel hlog
  have hA0 : 0 ≤ A := by linarith only [(le_max_left (1 : Real) B).trans hA]
  have hy := hY.trans_le hlevel
  have hδ := vaughanSieveDelta_bounds hA0 hy hlog
  have hm := hmain level (vaughanSieveDelta A level) hlevel hδ.1 hδ.2
  rw [vaughanSieve_cutoff_transport hy hlog] at hm
  have hL := Real.log_pos hy
  have hdelta := div_le_div_of_nonneg_right (vaughanSieveDelta_lower hA0 hy hlog) hL.le
  have hdelta' : 4 * A / Real.log (level : Real) ^ 2 ≤
      vaughanSieveDelta A level / Real.log (level : Real) := by
    convert hdelta using 1 <;> ring
  have hBA : B / Real.log (level : Real) ^ 2 ≤ A / Real.log (level : Real) ^ 2 :=
    div_le_div_of_nonneg_right ((le_max_right (1 : Real) B).trans hA) (sq_nonneg (Real.log (level : Real)))
  have hpaid : 3 * A / Real.log (level : Real) ^ 2 ≤
      vaughanSieveDelta A level / Real.log (level : Real) - B / Real.log (level : Real) ^ 2 := by
    calc
      _ = 4 * A / Real.log (level : Real) ^ 2 - A / Real.log (level : Real) ^ 2 := by ring
      _ ≤ _ := sub_le_sub hdelta' hBA
  exact hpaid.trans_lt hm

/-- The actual S in Vaughan (10), on the literal strict real cutoff.
The current D*h/log^2(h) support error has been consumed, giving a
coefficient 2A lower bound uniform in the interval origin. -/
theorem exists_vaughanSieve_smallPool_count_lower :
    ∃ A₀ Y : Real, 1 ≤ A₀ ∧ 1 < Y ∧ ∀ (A : Real) (level lower : Nat),
      A₀ ≤ A → Y ≤ (level : Real) → 6 * A ≤ Real.log (level : Real) →
      2 * A * (level : Real) / Real.log (level : Real) ^ 2 <
        (primeStateAvoidingIndices (iwaniecStrictPrimePool (vaughanSieveCutoff A level)) lower level).card := by
  obtain ⟨A₁, Y, hA₁, hY, hmain⟩ := exists_vaughanSieve_main_lower
  obtain ⟨D, hD, herror⟩ := exists_iwaniecStrictPrimePool_interval_error_bound
  let A₀ := max A₁ (D + 1)
  refine ⟨A₀, Y, hA₁.trans (le_max_left _ _), hY, ?_⟩
  intro A level lower hA hlevel hlog
  have hA₁A : A₁ ≤ A := (le_max_left _ _).trans hA
  have hDA : D ≤ A := by linarith only [(le_max_right A₁ (D + 1)).trans hA]
  have hmain' := hmain A level hA₁A hlevel hlog
  have hy := hY.trans_le hlevel
  have hlevel0 : (0 : Real) < level := zero_lt_one.trans hy
  have hscaled := mul_lt_mul_of_pos_left hmain' hlevel0
  have hscaled' : 3 * A * (level : Real) / Real.log (level : Real) ^ 2 <
      (level : Real) * iwaniecCubicWeightedMainExpansion
        ((iwaniecStrictPrimePool (vaughanSieveCutoff A level)).card + 1) level
        (iwaniecStrictPrimePool (vaughanSieveCutoff A level)) := by
    convert hscaled using 1 <;> ring
  have hDterm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hDA hlevel0.le) (sq_nonneg (Real.log (level : Real)))
  have herr := herror ((iwaniecStrictPrimePool (vaughanSieveCutoff A level)).card + 1)
    level lower level (vaughanSieveCutoff A level) (by omega)
    (vaughanSieve_reference_square (hA₁.trans hA₁A) hy hlog)
  have hbudget : 2 * A * (level : Real) / Real.log (level : Real) ^ 2 ≤
      3 * A * (level : Real) / Real.log (level : Real) ^ 2 -
        D * (level : Real) / Real.log (level : Real) ^ 2 := by
    calc
      _ = 3 * A * (level : Real) / Real.log (level : Real) ^ 2 -
          A * (level : Real) / Real.log (level : Real) ^ 2 := by ring
      _ ≤ _ := sub_le_sub_left hDterm _
  exact hbudget.trans_lt ((sub_lt_sub_right hscaled'
    (D * (level : Real) / Real.log (level : Real) ^ 2)).trans_le herr)

end

end Erdos1212Kernel
