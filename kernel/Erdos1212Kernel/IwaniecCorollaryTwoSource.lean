import Erdos1212Kernel.IwaniecEffectiveWeightedCorollaries

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

/-- Corollary 2 in the paper's alpha,beta coordinates, writing L=log y.
The original range 2 <= alpha <= beta <= L/2 is retained. -/
theorem exists_iwaniecCorollaryTwo_source_constant :
    ∃ C : Real, 0 < C ∧ ∀ L α β : Real, 2 ≤ α → α ≤ β → β ≤ L / 2 →
      |iwaniecPrimeReciprocalWeightedRealInterval (iwaniecReciprocalLogConstantWeight L)
          (Real.exp (L / β)) (Real.exp (L / α)) -
        Real.log ((β - 1) / (α - 1)) * L⁻¹| ≤
          C * Real.exp (-Real.sqrt (L / β)) := by
  obtain ⟨C, hC, hcore⟩ := exists_iwaniecPrimeWeightedCorollaryTwo_effective
  refine ⟨C, hC, ?_⟩
  intro L α β hα hαβ hβ
  have hαpos : 0 < α := by linarith
  have hβpos : 0 < β := by linarith
  have hL : 0 < L := by linarith
  have hL4 : 4 ≤ L := by linarith
  let A := Real.exp (L / α)
  let B := Real.exp (L / β)
  have hquotβ : 2 ≤ L / β := (le_div_iff₀ hβpos).mpr (by linarith)
  have hB : 2 ≤ B := Real.exp_one_gt_two.le.trans
    (Real.exp_le_exp.mpr (show 1 ≤ L / β by linarith))
  have hBA : B ≤ A := Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hL.le hαpos hαβ)
  have hquotα : L / α ≤ L / 2 := div_le_div_of_nonneg_left hL.le (by norm_num) hα
  have hA : A < Real.exp L := Real.exp_lt_exp.mpr (by linarith)
  have hmain : iwaniecCorollaryTwoMain L B A = Real.log ((β - 1) / (α - 1)) * L⁻¹ := by
    have hdivA : L / Real.log A = α := by
      dsimp [A]
      rw [Real.log_exp]
      field_simp [hL.ne', hαpos.ne']
    have hdivB : L / Real.log B = β := by
      dsimp [B]
      rw [Real.log_exp]
      field_simp [hL.ne', hβpos.ne']
    unfold iwaniecCorollaryTwoMain
    rw [hdivA, hdivB, mul_comm]
  have hden : 1 ≤ L - Real.log A := by dsimp [A]; rw [Real.log_exp]; linarith
  have hweight : (L - Real.log A)⁻¹ ≤ 1 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hden
    simpa only [one_div, inv_one] using hh
  have hh := hcore L B A hL hB hBA hA
  rw [hmain] at hh
  have herr := hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hweight hC.le) (Real.exp_pos _).le)
  simpa only [B, A, Real.log_exp, mul_one] using herr

end

end Erdos1212Kernel
