import Erdos1212Kernel.IwaniecAuxiliaryMProperties

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

theorem iwaniecAuxMWindowWeight_lt_of_lt {x y : Real} (hx : 2 ≤ x) (hxy : x < y) :
    iwaniecAuxMWindowWeight x < iwaniecAuxMWindowWeight y := by
  have hxPos : 0 < x := by linarith
  have hden : 0 < 2 * x ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hxPos)
  have hdenLt : 2 * x ^ 2 < 2 * y ^ 2 := by nlinarith
  have hinv := one_div_lt_one_div_of_lt hden hdenLt
  unfold iwaniecAuxMWindowWeight
  linarith

/-- Exact coefficient at the last weighted-window substitution in Lemma 7.
It is `(s-1)^2/s`, which is strictly smaller than `s-1`; the printed
display's last equality can therefore be replaced by an inequality. -/
theorem iwaniecAuxM_window_div_left_weight {s : Real} (hs : 3 ≤ s) :
    (∫ x in (s - 1)..s, iwaniecAuxMWindowKernel x) /
      iwaniecAuxMWindowWeight (s - 1) = (s - 1) ^ 2 / s * iwaniecAuxM s := by
  have hw := iwaniecAuxM_window_identity hs
  change iwaniecAuxMCoefficient s * iwaniecAuxM s =
    ∫ x in (s - 1)..s, iwaniecAuxMWindowKernel x at hw
  rw [← hw]
  have hsNe : s ≠ 0 := by linarith
  have hsubNe : s - 1 ≠ 0 := by linarith
  apply (div_eq_iff (iwaniecAuxMWindowWeight_pos (by linarith : 2 ≤ s - 1)).ne').2
  unfold iwaniecAuxMCoefficient iwaniecAuxMWindowWeight
  field_simp [hsNe, hsubNe] <;> ring

theorem iwaniecAuxM_unweighted_window_lt {s : Real} (hs : 3 ≤ s) :
    (∫ x in (s - 1)..s, iwaniecAuxM x) < (s - 1) * iwaniecAuxM s := by
  let w := iwaniecAuxMWindowWeight (s - 1)
  have hwPos : 0 < w := iwaniecAuxMWindowWeight_pos (by linarith)
  have hcontM : ContinuousOn iwaniecAuxM (Set.Icc (s - 1) s) := by
    apply iwaniecAuxM_continuousOn.mono
    intro x hx
    change (2 : Real) ≤ x
    linarith [hx.1]
  have hcontW : ContinuousOn (fun x => iwaniecAuxMWindowKernel x / w)
      (Set.Icc (s - 1) s) := by
    apply (iwaniecAuxMWindowKernel_continuousOn.div_const w).mono
    intro x hx
    change (1 : Real) < x
    linarith [hx.1]
  have hpoint : ∀ x : Real, s - 1 < x →
      iwaniecAuxM x < iwaniecAuxMWindowKernel x / w := by
    intro x hx
    rw [lt_div_iff₀ hwPos]
    have hweight := iwaniecAuxMWindowWeight_lt_of_lt (by linarith : 2 ≤ s - 1) hx
    have hmul := mul_lt_mul_of_pos_right hweight (iwaniecAuxM_pos (s := x) (by linarith))
    simpa only [w, iwaniecAuxMWindowKernel, mul_comm] using hmul
  have hIntegral : (∫ x in (s - 1)..s, iwaniecAuxM x) <
      ∫ x in (s - 1)..s, iwaniecAuxMWindowKernel x / w := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (by linarith) hcontM hcontW
    · intro x hx
      exact (hpoint x hx.1).le
    · exact ⟨s, ⟨by linarith, le_rfl⟩, hpoint s (by linarith)⟩
  rw [intervalIntegral.integral_div] at hIntegral
  change (∫ x in (s - 1)..s, iwaniecAuxM x) <
    (∫ x in (s - 1)..s, iwaniecAuxMWindowKernel x) /
      iwaniecAuxMWindowWeight (s - 1) at hIntegral
  rw [iwaniecAuxM_window_div_left_weight hs] at hIntegral
  have hcoef : (s - 1) ^ 2 / s < s - 1 := by
    rw [div_lt_iff₀ (show 0 < s by linarith)]
    nlinarith
  exact hIntegral.trans (mul_lt_mul_of_pos_right hcoef (iwaniecAuxM_pos (by linarith)))

end

end Erdos1212Kernel
