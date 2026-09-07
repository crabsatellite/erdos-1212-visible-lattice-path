import Erdos1212Kernel.IwaniecPaperACountBound
import Erdos1212Kernel.IwaniecAuxTauUniform

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 650000

theorem exists_iwaniecPaperA_uniform_count_bound :
    ∃ D : Real, 0 < D ∧ ∀ rank : Nat, 1 ≤ rank → ∀ level s : Real,
      1 < level → 2 ≤ s → (iwaniecPaperA rank level s : Real) ≤ D * level / Real.log level ^ 2 := by
  obtain ⟨C, hC, hcount⟩ := exists_iwaniecPaperA_count_bound
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1 eventually_iwaniecAuxTau_le_four
  let Y := max Y₀ (Real.exp 1)
  let D := max (4 * C) (Real.log Y ^ 2)
  have hD : 0 < D := (mul_pos (by norm_num) hC).trans_le (le_max_left _ _)
  refine ⟨D, hD, ?_⟩
  intro rank hr level s hy hs
  have hL := Real.log_pos hy
  have hYpos : 0 < Y := (Real.exp_pos 1).trans_le (le_max_right _ _)
  by_cases hyY : level ≤ Y
  · have hlog := Real.log_le_log (by linarith : 0 < level) hyY
    have hsq : Real.log level ^ 2 ≤ Real.log Y ^ 2 := by nlinarith only [hL, hlog]
    have hLD : Real.log level ^ 2 ≤ D := hsq.trans (le_max_right _ _)
    have hbase := iwaniecPaperSupportCount_le_level rank (z := Real.exp (Real.log level / s)) hy
    apply hbase.trans
    apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
    have hh := mul_le_mul_of_nonneg_right hLD (show 0 ≤ level by linarith)
    nlinarith only [hh]
  · have hYlevel : Y₀ ≤ level := (le_max_left _ _).trans (le_of_not_ge hyY)
    obtain ⟨_hy, hξ2, hTau⟩ := hY₀ level hYlevel
    let t := min s (iwaniecPaperXi level)
    have ht2 : 2 ≤ t := le_min hs hξ2
    have htξ : t ≤ iwaniecPaperXi level := min_le_right _ _
    have hts : t ≤ s := min_le_left _ _
    have hstart : iwaniecAuxGStart (rank + 1) ≤ t := by unfold iwaniecAuxGStart; split_ifs <;> linarith only [ht2]
    have hc := hcount rank hr level t hy hstart htξ
    have hmono := iwaniecPaperA_antitone_parameter rank hy (show 0 < t by linarith) hts
    have hcf : 0 ≤ (rank : Real) / ((rank : Real) + 1) := by positivity
    have hrf : (rank : Real) / ((rank : Real) + 1) ≤ 1 :=
      (div_le_one₀ (by positivity)).mpr (by linarith)
    have htau := hTau rank t ht2 htξ
    have hTau0 := (iwaniecAuxTau_pos rank level ht2).le
    have hfirst := (mul_le_mul_of_nonneg_right hrf hTau0).trans (by simpa only [one_mul] using htau)
    have hscaled := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfirst hC.le) (sq_nonneg (Real.log level))) (show 0 ≤ level by linarith)
    have hmain : iwaniecPaperAMajorant C rank level t ≤ (4 * C) * level / Real.log level ^ 2 := by
      convert hscaled using 1 <;> (try dsimp only [iwaniecPaperAMajorant, iwaniecAuxTau]) <;> ring
    have hCD := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left (4 * C) (Real.log Y ^ 2)) (show 0 ≤ level by linarith)) (sq_nonneg (Real.log level))
    exact (show (iwaniecPaperA rank level s : Real) ≤ iwaniecPaperA rank level t by exact_mod_cast hmono).trans
      (hc.trans (hmain.trans hCD))

end

end Erdos1212Kernel
