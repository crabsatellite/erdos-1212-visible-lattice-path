import Erdos1212Kernel.IwaniecPaperD2EulerError

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

theorem exists_iwaniecPaperD2_summed_inner_error :
    ∃ C : Real, 0 < C ∧ ∀ level s : Real, 64 ≤ level → 2 ≤ s →
      |iwaniecPaperD2LogSum level s - iwaniecPaperD2OuterMain level s| ≤
        C * Real.exp (-Real.sqrt (Real.log level / 6)) := by
  obtain ⟨A, hA, hinner⟩ := exists_iwaniecPaperD2LogInner_source_rate
  obtain ⟨K, hK, hmass⟩ := exists_iwaniecPaperD2_pair_mass_bound
  refine ⟨A * K, mul_pos hA hK, ?_⟩
  intro level s hy hs
  let E := Real.exp (-Real.sqrt (Real.log level / 6))
  have he : 0 ≤ E := (Real.exp_pos _).le
  have hout := (hmass level s hy hs).1
  rw [iwaniecPaperD2_outer_remainder_identity]
  calc
    _ ≤ ∑ p ∈ iwaniecPaperD2OuterBand level s,
        |(p : Real)⁻¹ * (iwaniecPaperD2LogInner level p -
          (3 / Real.log (level / p) - (Real.log (p : Real))⁻¹))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ iwaniecPaperD2OuterBand level s, (p : Real)⁻¹ * (A * E) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))]
      exact mul_le_mul_of_nonneg_left (hinner level s p hy hs hp) (inv_nonneg.mpr (Nat.cast_nonneg p))
    _ = A * E * (∑ p ∈ iwaniecPaperD2OuterBand level s, (p : Real)⁻¹) := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ A * E * K := mul_le_mul_of_nonneg_left hout (mul_nonneg hA.le he)
    _ = _ := by dsimp [E]; ring

/-- Both actual errors have now been summed. The remaining main term
is the literal outer prime sum, with the paper's exp(gamma) normalization. -/
theorem exists_iwaniecPaperD2_outer_main_error :
    ∃ C : Real, 0 < C ∧ ∀ level s : Real, 64 ≤ level → 2 ≤ s →
      |Real.exp Real.eulerMascheroniConstant * iwaniecPaperD2 level s -
        iwaniecPaperD2OuterMain level s| ≤ C * Real.exp (-Real.sqrt (Real.log level / 6)) := by
  obtain ⟨A, hA, hR⟩ := exists_iwaniecPaperD2_Euler_replacement_error
  obtain ⟨B, hB, hinner⟩ := exists_iwaniecPaperD2_summed_inner_error
  refine ⟨Real.exp Real.eulerMascheroniConstant * A + B, by positivity, ?_⟩
  intro level s hy hs
  have hgamma : Real.exp Real.eulerMascheroniConstant * Real.exp (-Real.eulerMascheroniConstant) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hsplit : Real.exp Real.eulerMascheroniConstant * iwaniecPaperD2 level s -
      iwaniecPaperD2OuterMain level s =
      Real.exp Real.eulerMascheroniConstant *
        (iwaniecPaperD2 level s - Real.exp (-Real.eulerMascheroniConstant) * iwaniecPaperD2LogSum level s) +
        (iwaniecPaperD2LogSum level s - iwaniecPaperD2OuterMain level s) := by
    rw [mul_sub, ← mul_assoc, hgamma, one_mul]
    ring
  rw [hsplit]
  calc
    _ ≤ |Real.exp Real.eulerMascheroniConstant *
        (iwaniecPaperD2 level s - Real.exp (-Real.eulerMascheroniConstant) * iwaniecPaperD2LogSum level s)| +
        |iwaniecPaperD2LogSum level s - iwaniecPaperD2OuterMain level s| := abs_add_le _ _
    _ ≤ Real.exp Real.eulerMascheroniConstant * (A * Real.exp (-Real.sqrt (Real.log level / 6))) +
        B * Real.exp (-Real.sqrt (Real.log level / 6)) := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact add_le_add (mul_le_mul_of_nonneg_left (hR level s hy hs) (Real.exp_pos _).le)
        (hinner level s hy hs)
    _ = _ := by ring

end

end Erdos1212Kernel
