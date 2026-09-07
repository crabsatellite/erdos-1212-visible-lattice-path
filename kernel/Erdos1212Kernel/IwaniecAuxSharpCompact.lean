import Erdos1212Kernel.IwaniecAuxSharpExponent
import Erdos1212Kernel.IwaniecAuxiliaryProfiles
import Mathlib.Analysis.Normed.Group.Bounded

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1200000

/-- A single compact bound for both literal parity profiles, hence for
every rank at once. No rank-dependent compactness constant is selected. -/
theorem iwaniecAuxG_sharp_log_compact_bound (S : Real) :
    ∃ B : Real, 0 < B ∧ ∀ rank : Nat, ∀ s ∈ Set.Icc (2 : Real) S,
      |Real.log (iwaniecAuxG rank s) + iwaniecAuxSharpExponent s| ≤ B := by
  have hset : Set.Icc (2 : Real) S ⊆ Set.Ioi (1 : Real) := by intro s hs; change 1 < s; linarith [hs.1]
  have hcL : ContinuousOn (fun s : Real => Real.log (iwaniecAuxLower s) + iwaniecAuxSharpExponent s) (Set.Icc 2 S) :=
    ((iwaniecAuxLower_continuousOn.mono hset).log (fun s hs => (iwaniecAuxLower_pos hs.1).ne')).add
      (iwaniecAuxSharpExponent_continuousOn.mono hset)
  have hcU : ContinuousOn (fun s : Real => Real.log (iwaniecAuxUpper s) + iwaniecAuxSharpExponent s) (Set.Icc 2 S) :=
    ((iwaniecAuxUpper_continuousOn.mono hset).log (fun s hs => (iwaniecAuxUpper_pos (by linarith [hs.1])).ne')).add
      (iwaniecAuxSharpExponent_continuousOn.mono hset)
  obtain ⟨BL, hBL⟩ := isCompact_Icc.exists_bound_of_continuousOn hcL
  obtain ⟨BU, hBU⟩ := isCompact_Icc.exists_bound_of_continuousOn hcU
  refine ⟨|BL| + |BU| + 1, by positivity, ?_⟩
  intro rank s hs
  by_cases hr : Even rank
  · rw [iwaniecAuxG, if_pos hr]
    have h := hBL s hs
    rw [Real.norm_eq_abs] at h
    linarith [le_abs_self BL, abs_nonneg BU]
  · rw [iwaniecAuxG, if_neg hr]
    have h := hBU s hs
    rw [Real.norm_eq_abs] at h
    linarith [le_abs_self BU, abs_nonneg BL]

end

end Erdos1212Kernel
