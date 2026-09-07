import Erdos1212Kernel.TaoPNTFixedContourLogDerivative
import Mathlib.Analysis.Normed.Group.Bounded

namespace Erdos1212Kernel

noncomputable section

open Metric Set

set_option maxHeartbeats 1900000

theorem exists_taoPNT_low_frequency_poleRemoved_bound
    (A : Real) (hA : 0 ≤ A) :
    ∃ e K : Real, 0 < e ∧ e ≤ 1 / 2 ∧ 0 < K ∧
      ∀ t γ : Real,
        taoLogFrequency t ≤ A →
        1 - e ≤ γ → γ ≤ 1 + e →
        taoZetaPoleRemoved ((γ : Complex) + (t : Complex) * Complex.I) ≠ 0 ∧
        ‖logDeriv taoZetaPoleRemoved
          ((γ : Complex) + (t : Complex) * Complex.I)‖ ≤ K := by
  obtain ⟨g, hg, hzero⟩ := exists_bounded_frequency_zeta_zero_free_strip A hA
  let e : Real := min (g / 2) (1 / 2)
  have he : 0 < e := lt_min (by positivity) (by norm_num)
  have hehalf : e ≤ 1 / 2 := min_le_right _ _
  have heg : e < g := (min_le_left (g / 2) (1 / 2)).trans_lt (half_lt_self hg)
  let T : Real := (2 * Real.pi) * A
  let S : Set Complex := Set.Icc (1 - e) (1 + e) ×ℂ Set.Icc (-T) T
  have hcompact : IsCompact S := by
    exact isCompact_Icc.reProdIm isCompact_Icc
  have hHnz : ∀ s ∈ S, taoZetaPoleRemoved s ≠ 0 := by
    intro s hs
    rw [Complex.mem_reProdIm] at hs
    by_cases hs1 : s = 1
    · subst s
      simp
    · apply taoZetaPoleRemoved_ne_zero_of_eq_one_or_zeta_ne_zero
      right
      have hfreq : taoLogFrequency s.im ≤ A := by
        unfold taoLogFrequency
        have him : |s.im| ≤ T := abs_le.mpr hs.2
        dsimp [T] at him
        have hden : 0 < 2 * Real.pi := by positivity
        exact (div_le_iff₀ hden).2 (by simpa [mul_comm] using him)
      have hre : 1 - g < s.re := by
        have := hs.1.1
        linarith
      have hz := hzero s.im s.re hfreq hre
      simpa only [Complex.re_add_im] using hz
  have hcont : ContinuousOn (logDeriv taoZetaPoleRemoved) S := by
    intro s hs
    exact (analyticAt_logDeriv_taoZetaPoleRemoved (hHnz s hs)).continuousAt.continuousWithinAt
  obtain ⟨K₀, hK₀⟩ := hcompact.exists_bound_of_continuousOn hcont
  let K : Real := |K₀| + 1
  have hK : 0 < K := by dsimp [K]; linarith [abs_nonneg K₀]
  refine ⟨e, K, he, hehalf, hK, ?_⟩
  intro t γ ht hγ0 hγ1
  have htAbs : |t| ≤ T := by
    unfold taoLogFrequency at ht
    have hden : 0 < 2 * Real.pi := by positivity
    have := (div_le_iff₀ hden).1 ht
    simpa only [T, mul_comm] using this
  have hmem : ((γ : Complex) + (t : Complex) * Complex.I) ∈ S := by
    rw [Complex.mem_reProdIm]
    simpa using (show γ ∈ Set.Icc (1 - e) (1 + e) ∧ t ∈ Set.Icc (-T) T from
      ⟨⟨hγ0, hγ1⟩, abs_le.mp htAbs⟩)
  refine ⟨hHnz _ hmem, ?_⟩
  have hb := hK₀ _ hmem
  dsimp [K]
  exact hb.trans (by linarith [le_abs_self K₀])

end

end Erdos1212Kernel
