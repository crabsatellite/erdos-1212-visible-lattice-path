import Erdos1212Kernel.IwaniecPaperD2OuterBoundary
import Erdos1212Kernel.IwaniecCorollaryTwoSource
import Erdos1212Kernel.IwaniecSieveFunctions

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 650000

/-- Exact separation into the two prime sums displayed in Lemma 16. -/
theorem iwaniecPaperD2_closed_main_split {level : Real} (hy : 0 < level) (s : Real) :
    iwaniecPaperD2ClosedOuterMain level s =
      3 * iwaniecPrimeReciprocalWeightedRealInterval (iwaniecReciprocalLogConstantWeight (Real.log level))
        (Real.exp (Real.log level / 4)) (Real.exp (Real.log level / s)) -
      iwaniecPrimeLogReciprocalRealInterval (Real.exp (Real.log level / 4)) (Real.exp (Real.log level / s)) := by
  unfold iwaniecPaperD2ClosedOuterMain iwaniecPaperD2ClosedOuterBand iwaniecClosedPrimeBand
    iwaniecPrimeReciprocalWeightedRealInterval iwaniecPrimeLogReciprocalRealInterval
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hpPrime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
  have hp0 : (0 : Real) < p := by exact_mod_cast hpPrime.pos
  rw [iwaniecReciprocalLogConstantWeight_eq, Real.log_div hy.ne' hp0.ne']
  ring

/-- The paper's g₂ profile is obtained from the actual closed outer
sum by Corollary 2 and Lemma 14, with their original parameters. -/
theorem exists_iwaniecPaperD2_closed_outer_error :
    ∃ C : Real, 0 < C ∧ ∀ level s : Real, 1 < level → 8 ≤ Real.log level → 2 ≤ s → s ≤ 4 →
      |iwaniecPaperD2ClosedOuterMain level s - iwaniecGTwo s / Real.log level| ≤
        C * Real.exp (-Real.sqrt (Real.log level / 4)) := by
  obtain ⟨A, hA, hcor⟩ := exists_iwaniecCorollaryTwo_source_constant
  obtain ⟨B, hB, hlemma⟩ := exists_iwaniecLemma14_real_constant
  refine ⟨3 * A + B, by positivity, ?_⟩
  intro level s hy hL8 hs hs4
  let L := Real.log level
  let S := iwaniecPrimeReciprocalWeightedRealInterval (iwaniecReciprocalLogConstantWeight L)
    (Real.exp (L / 4)) (Real.exp (L / s))
  let T := iwaniecPrimeLogReciprocalRealInterval (Real.exp (L / 4)) (Real.exp (L / s))
  have hL : 0 < L := Real.log_pos hy
  have hs0 : 0 < s := by linarith
  have hc := hcor L s 4 hs hs4 (by dsimp [L]; linarith)
  norm_num only [show (4 : Real) - 1 = 3 by norm_num] at hc
  have hlow : 2 ≤ Real.exp (L / 4) :=
    Real.exp_one_gt_two.le.trans (Real.exp_le_exp.mpr (by dsimp [L]; linarith))
  have horder : Real.exp (L / 4) ≤ Real.exp (L / s) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hL.le hs0 hs4)
  have ht := hlemma (Real.exp (L / 4)) (Real.exp (L / s)) hlow horder
  rw [Real.log_exp, Real.log_exp] at ht
  have htmain : (L / 4)⁻¹ - (L / s)⁻¹ = (4 - s) / L := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  rw [htmain] at ht
  have hsplit : iwaniecPaperD2ClosedOuterMain level s - iwaniecGTwo s / Real.log level =
      3 * (S - Real.log (3 / (s - 1)) * L⁻¹) - (T - (4 - s) / L) := by
    rw [iwaniecPaperD2_closed_main_split (zero_lt_one.trans hy) s, iwaniecGTwo_eq hs hs4]
    dsimp [S, T, L]
    ring
  rw [hsplit]
  calc
    _ ≤ |3 * (S - Real.log (3 / (s - 1)) * L⁻¹)| + |T - (4 - s) / L| := abs_sub _ _
    _ ≤ 3 * (A * Real.exp (-Real.sqrt (L / 4))) + B * Real.exp (-Real.sqrt (L / 4)) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : Real) < 3)]
      exact add_le_add (mul_le_mul_of_nonneg_left hc (by norm_num)) ht
    _ = _ := by dsimp [L]; ring

end

end Erdos1212Kernel
