import Erdos1212Kernel.IwaniecPaperD2RemainderIdentity

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

/-- The actual total error from replacing the last-prime Euler product.
The double reciprocal mass is uniformly bounded by a proved producer. -/
theorem exists_iwaniecPaperD2_Euler_replacement_error :
    ∃ C : Real, 0 < C ∧ ∀ level s : Real, 64 ≤ level → 2 ≤ s →
      |iwaniecPaperD2 level s - Real.exp (-Real.eulerMascheroniConstant) * iwaniecPaperD2LogSum level s| ≤
        C * Real.exp (-Real.sqrt (Real.log level / 6)) := by
  obtain ⟨A, hA, hR⟩ := exists_iwaniecPaperD2_lastPrime_unit_error
  obtain ⟨K, hK, hmass⟩ := exists_iwaniecPaperD2_pair_mass_bound
  refine ⟨A * K ^ 2, by positivity, ?_⟩
  intro level s hy hs
  let E := Real.exp (-Real.sqrt (Real.log level / 6))
  have he : 0 ≤ E := (Real.exp_pos _).le
  have htotal := (hmass level s hy hs).2
  rw [iwaniecPaperD2_log_remainder_identity]
  calc
    _ ≤ ∑ p ∈ iwaniecPaperD2OuterBand level s,
        |∑ q ∈ iwaniecPaperD2InnerPool level p,
          (iwaniecPaperR (q : Real) - Real.exp (-Real.eulerMascheroniConstant) / Real.log (q : Real)) /
            ((p : Real) * q)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ iwaniecPaperD2OuterBand level s,
        ∑ q ∈ iwaniecPaperD2InnerPool level p,
          |(iwaniecPaperR (q : Real) - Real.exp (-Real.eulerMascheroniConstant) / Real.log (q : Real)) /
            ((p : Real) * q)| := by
      apply Finset.sum_le_sum
      intro p hp
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ iwaniecPaperD2OuterBand level s,
        ∑ q ∈ iwaniecPaperD2InnerPool level p, A * E * (1 / ((p : Real) * q)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPool := (Finset.mem_filter.mp hp).1
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨hqPool, hf⟩ := Finset.mem_filter.mp hq
      have hh := hR level s p q (by linarith) hs hpPool hqPool hf
      have hden : 0 ≤ (p : Real) * q := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      rw [abs_div, abs_of_nonneg hden]
      calc
        _ ≤ A * E / ((p : Real) * q) := div_le_div_of_nonneg_right hh hden
        _ = _ := by ring
    _ = A * E * iwaniecPaperD2PairMass level s := by
      unfold iwaniecPaperD2PairMass
      simp only [Finset.mul_sum]
    _ ≤ A * E * K ^ 2 := mul_le_mul_of_nonneg_left htotal (mul_nonneg hA.le he)
    _ = _ := by dsimp [E]; ring

end

end Erdos1212Kernel
