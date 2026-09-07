import Erdos1212Kernel.IwaniecPaperABaseCount
import Erdos1212Kernel.IwaniecPaperABoundedLevel
import Erdos1212Kernel.IwaniecInductionBaseScale

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 600000

/-- The base case of the actual count induction, simultaneously for all
real levels, with the source rank prefactor still present. -/
theorem exists_iwaniecPaperA_rank_one_constant :
    ∃ C₀ : Real, 0 < C₀ ∧ ∀ C : Real, C₀ ≤ C → ∀ level s : Real,
      1 < level → 2 ≤ s → s ≤ iwaniecPaperXi level →
        (iwaniecPaperA 1 level s : Real) ≤ iwaniecPaperAMajorant C 1 level s := by
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1 eventually_iwaniec_sqrt_le_aux_normalization
  let Y := max (Y₀ + 1) (Real.exp 12288)
  let C₀ := max 2 ((1 + Real.log Y) ^ 3 / iwaniecAuxM (2 * Real.log Y))
  have hC₀2 : 2 ≤ C₀ := le_max_left _ _
  have hlogY : 12288 ≤ Real.log Y := by
    have hh := Real.log_le_log (Real.exp_pos (12288 : Real)) (le_max_right (Y₀ + 1) (Real.exp 12288))
    simpa only [Real.log_exp] using hh
  refine ⟨C₀, by linarith, ?_⟩
  intro C hC level s hy hs hsξ
  have hC2 : 2 ≤ C := hC₀2.trans hC
  have hStart : iwaniecAuxGStart (1 + 1) ≤ s := by simpa [iwaniecAuxGStart] using hs
  by_cases hyY : level ≤ Y
  · exact iwaniecPaperA_bounded_level_bound hlogY ((le_max_right _ _).trans hC)
      (le_refl 1) hy hyY hStart hsξ
  · have hYlevel : Y₀ ≤ level := by
      have hYlow : Y₀ + 1 ≤ Y := le_max_left _ _
      linarith
    have hnormal := (hY₀ level hYlevel).2 2 s hStart hsξ
    have hW : 1 ≤ iwaniecAuxWeightPower level s :=
      Real.one_le_rpow (iwaniecAuxWeightBase_one_le level (by linarith)) (by linarith)
    have hcf : 1 ≤ C / 2 := by linarith only [hC2]
    have hcoef : 1 ≤ (C / 2) * iwaniecAuxWeightPower level s := by
      have hh := mul_le_mul hcf hW (by norm_num : (0 : Real) ≤ 1) (by linarith : 0 ≤ C / 2)
      simpa only [one_mul] using hh
    have hT : 0 ≤ (level / Real.log level ^ 2) * iwaniecAuxG 2 s :=
      mul_nonneg (div_nonneg (by linarith) (sq_nonneg _)) (iwaniecAuxG_pos 2 hs).le
    have hscaled := mul_le_mul_of_nonneg_right hcoef hT
    calc
      _ ≤ Real.sqrt level := iwaniecPaperA_one_le_sqrt hy hs
      _ ≤ (level / Real.log level ^ 2) * iwaniecAuxG 2 s := hnormal
      _ ≤ iwaniecPaperAMajorant C 1 level s := by
        unfold iwaniecPaperAMajorant
        norm_num only [Nat.cast_one, show (1 : Nat) + 1 = 2 by norm_num, show (1 : Real) + 1 = 2 by norm_num]
        convert hscaled using 1 <;> ring

end

end Erdos1212Kernel
