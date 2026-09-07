import Erdos1212Kernel.IwaniecAuxSharpSandwich
import Erdos1212Kernel.IwaniecAuxSharpCompact

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1200000

theorem iwaniecAuxG_sharp_log_bound :
    ∃ C : Real, 0 < C ∧ ∀ rank : Nat, ∀ s : Real, 2 ≤ s →
      |Real.log (iwaniecAuxG rank s) + iwaniecAuxSharpExponent s| ≤ C * s := by
  obtain ⟨S₀, hS₀⟩ := eventually_atTop.mp eventually_iwaniecAuxG_sharp_log_bounds
  let S := max S₀ 3
  obtain ⟨B, hB, hcompact⟩ := iwaniecAuxG_sharp_log_compact_bound S
  let C := max (2 : Real) B
  have hC2 : 2 ≤ C := le_max_left _ _
  have hBC : B ≤ C := le_max_right _ _
  have hC : 0 < C := by linarith
  refine ⟨C, hC, ?_⟩
  intro rank s hs
  by_cases hsS : s ≤ S
  · have h := hcompact rank s ⟨hs, hsS⟩
    have hCs : C ≤ C * s := by nlinarith
    exact h.trans (hBC.trans hCs)
  · have hlarge : S₀ ≤ s := (le_max_left S₀ 3).trans (lt_of_not_ge hsS).le
    have h := hS₀ s hlarge rank
    have hnonneg : 0 ≤ Real.log (iwaniecAuxG rank s) + iwaniecAuxSharpExponent s := by linarith [h.1]
    rw [abs_of_nonneg hnonneg]
    exact h.2.trans (mul_le_mul_of_nonneg_right hC2 (by linarith))

/-- Full rank-uniform two-sided exponential form of source Lemma 9,
including the common initial domain s>=2. -/
theorem iwaniecAuxiliary_lemma_nine :
    ∃ C : Real, 0 < C ∧ ∀ rank : Nat, ∀ s : Real, 2 ≤ s →
      Real.exp (-C * s) ≤ iwaniecAuxG rank s * Real.exp (s * Real.log s + s * Real.log (Real.log s)) ∧
      iwaniecAuxG rank s * Real.exp (s * Real.log s + s * Real.log (Real.log s)) ≤ Real.exp (C * s) := by
  obtain ⟨C, hC, hbound⟩ := iwaniecAuxG_sharp_log_bound
  refine ⟨C, hC, ?_⟩
  intro rank s hs
  have h := abs_le.mp (hbound rank s hs)
  have hG := iwaniecAuxG_pos rank hs
  have he : Real.exp (Real.log (iwaniecAuxG rank s) + iwaniecAuxSharpExponent s) =
      iwaniecAuxG rank s * Real.exp (s * Real.log s + s * Real.log (Real.log s)) := by
    rw [Real.exp_add, Real.exp_log hG]
    rfl
  constructor
  · have hx := Real.exp_le_exp.mpr h.1
    simpa only [he, neg_mul] using hx
  · simpa only [he] using Real.exp_le_exp.mpr h.2

theorem iwaniecAuxG_sharp_decay_bounds :
    ∃ C : Real, 0 < C ∧ ∀ rank : Nat, ∀ s : Real, 2 ≤ s →
      Real.exp (-iwaniecAuxSharpExponent s - C * s) ≤ iwaniecAuxG rank s ∧
      iwaniecAuxG rank s ≤ Real.exp (-iwaniecAuxSharpExponent s + C * s) := by
  obtain ⟨C, hC, hbound⟩ := iwaniecAuxG_sharp_log_bound
  refine ⟨C, hC, ?_⟩
  intro rank s hs
  have h := abs_le.mp (hbound rank s hs)
  have hG := iwaniecAuxG_pos rank hs
  constructor
  · have hx := Real.exp_le_exp.mpr (show -iwaniecAuxSharpExponent s - C * s ≤ Real.log (iwaniecAuxG rank s) by linarith [h.1])
    simpa only [Real.exp_log hG] using hx
  · have hx := Real.exp_le_exp.mpr (show Real.log (iwaniecAuxG rank s) ≤ -iwaniecAuxSharpExponent s + C * s by linarith [h.2])
    simpa only [Real.exp_log hG] using hx

end

end Erdos1212Kernel
