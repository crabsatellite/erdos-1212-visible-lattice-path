import Erdos1212Kernel.IwaniecPaperAChildCountSum
import Erdos1212Kernel.IwaniecPaperAFarRelative
import Erdos1212Kernel.IwaniecInductionRankSlack

namespace Erdos1212Kernel

noncomputable section

open Filter Topology
open scoped BigOperators

set_option maxHeartbeats 800000

/-- The genuine middle-rank induction step. Its only induction input is
the count theorem at rank n, on the literal child levels and parameters. -/
theorem eventually_iwaniecPaperA_middle_step :
    ∀ᶠ level : Real in atTop, 1 < level ∧ ∀ (C : Real) (n : Nat) (s : Real),
      2 ≤ C → 1 ≤ n → iwaniecAuxGStart ((n + 1) + 1) ≤ s → s ≤ iwaniecPaperXi level →
      (n : Real) + 1 ≤ 2 * Real.log level / Real.log (Real.log level) →
      (∀ y t : Real, 1 < y → iwaniecAuxGStart (n + 1) ≤ t → t ≤ iwaniecPaperXi y →
        (iwaniecPaperA n y t : Real) ≤ iwaniecPaperAMajorant C n y t) →
      (iwaniecPaperA (n + 1) level s : Real) ≤ iwaniecPaperAMajorant C (n + 1) level s := by
  obtain ⟨K, hK, hchildBound⟩ := exists_iwaniecPaperBand_child_majorant_bound
  filter_upwards [eventually_iwaniecPaperA_far_relative_bound,
    eventually_iwaniec_rank_step_absorption (C := 1) (by norm_num),
    eventually_iwaniecXi_error_le_inv_log_sq (100 * K),
    tendsto_iwaniecPaperXi_atTop.eventually_ge_atTop iwaniecAuxSZero,
    Real.tendsto_log_atTop.eventually_gt_atTop 1]
    with level hfar hslack herror hξ hlog
  have hy := hfar.1
  refine ⟨hy, ?_⟩
  intro C n s hC hn hs hsξ hnRange hIH
  have hC0 : 0 ≤ C := by linarith only [hC]
  have hlevel0 : 0 ≤ level := by linarith only [hy]
  let L := Real.log level
  let ξ := iwaniecPaperXi level
  let S := max (iwaniecCorollaryThreeDomainStart (n + 1)) s
  let q := (L ^ 2)⁻¹
  let B := (iwaniecAuxWeightPower level s * iwaniecAuxG ((n + 1) + 1) s / L ^ 2) * level
  let W₀ := iwaniecAuxWeightPower level iwaniecAuxSZero
  let f := (n : Real) / ((n : Real) + 1)
  let fp := ((n : Real) + 1) / ((n : Real) + 2)
  have hL : 0 < L := Real.log_pos hy
  have hq : 0 ≤ q := inv_nonneg.mpr (sq_nonneg L)
  have hq1 : q ≤ 1 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) (one_le_pow₀ hlog.le : 1 ≤ L ^ 2)
    simpa only [one_div, inv_one] using hh
  have hstart1 : 1 ≤ iwaniecAuxGStart ((n + 1) + 1) := by unfold iwaniecAuxGStart; split_ifs <;> norm_num
  have hs1 : 1 ≤ s := hstart1.trans hs
  have hW := (iwaniecAuxWeightPower_pos level hs1).le
  have hG := (iwaniecAuxG_pos_exactDomain ((n + 1) + 1) hs).le
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hW₀1 : 1 ≤ W₀ := Real.one_le_rpow
    (iwaniecAuxWeightBase_one_le level (by linarith [iwaniecAuxSZero_large])) (by linarith [iwaniecAuxSZero_large])
  have hW₀ : 0 ≤ W₀ := by linarith
  have hf : (1 / 2 : Real) ≤ f := iwaniec_rank_ratio_ge_half hn
  have hfp : (1 / 2 : Real) ≤ fp := by
    have hh := iwaniec_rank_ratio_ge_half (show 1 ≤ n + 1 by omega)
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, show (1 : Real) + 1 = 2 by norm_num] using hh
  have hmainId : iwaniecPaperAMajorant C (n + 1) level s = C * fp * B := by
    unfold iwaniecPaperAMajorant
    simp only [Nat.cast_add, Nat.cast_one, add_assoc, show (1 : Real) + 1 = 2 by norm_num]
    dsimp [fp, B]
    ring
  obtain ⟨hcountEq, hGEq⟩ := iwaniecPaperA_recursion_parameter (n + 1) hy hs
  have hSdom : iwaniecCorollaryThreeDomainStart (n + 1) ≤ S := le_max_left _ _
  have hDoms0 : iwaniecCorollaryThreeDomainStart (n + 1) ≤ iwaniecAuxSZero := by
    have hh := (iwaniecCorollaryThreeDomainStart_bounds (n + 1)).2
    linarith [iwaniecAuxSZero_large]
  have hSξ : S ≤ ξ := max_le (hDoms0.trans hξ) hsξ
  have hS2 : 2 ≤ S := (iwaniecCorollaryThreeDomainStart_bounds (n + 1)).1.trans hSdom
  have hξsub : 0 < ξ - 1 := by linarith [iwaniecAuxSZero_large]
  have hfarBound : (iwaniecPaperA (n + 1) level (ξ - 1) : Real) ≤ B * q := by
    have hh := hfar.2 (n + 1) s hs hsξ
    convert hh using 1 <;> dsimp [B, q, L, ξ] <;> field_simp [hL.ne'] <;> ring
  rw [hmainId]
  by_cases hST : S ≤ ξ - 1
  · let E := Real.exp (-Real.sqrt (L / ξ))
    let e := 100 * K * ξ ^ 2 * E
    let M := (iwaniecAuxWeightPower level (max iwaniecAuxSZero S) * iwaniecAuxG ((n + 1) + 1) S / L ^ 2) * level
    let childSum := ∑ p ∈ iwaniecStrictPrimeBand (Real.exp (L / (ξ - 1))) (Real.exp (L / S)),
      iwaniecPaperChildMajorantTerm (n + 1) level p
    have he : e ≤ q := herror.2
    have he0 : 0 ≤ e := by dsimp [e, E]; positivity
    have hmaxS : max iwaniecAuxSZero S = max iwaniecAuxSZero s := by
      dsimp [S]
      rw [← max_assoc, max_eq_left hDoms0]
    have hweight : iwaniecAuxWeightPower level (max iwaniecAuxSZero S) ≤ iwaniecAuxWeightPower level s * W₀ := by
      rw [hmaxS]
      exact iwaniecWeightPower_max_bound hs1
    have hM : M ≤ B * W₀ := by
      have hh := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hweight hG) (sq_nonneg L))
        (show 0 ≤ level by linarith)
      dsimp [M]
      rw [hGEq]
      convert hh using 1 <;> dsimp [B] <;> ring
    have hsource := hchildBound (n + 1) level S hy hξ hSdom hSξ
    have hsource' : childSum ≤ M * (1 + e) := by
      convert hsource using 1 <;> dsimp [childSum, iwaniecPaperChildMajorantTerm, M, e, E, L, ξ] <;> ring
    have hchildSum : childSum ≤ B * W₀ * (1 + q) :=
      hsource'.trans (mul_le_mul hM (add_le_add le_rfl he) (by linarith) (mul_nonneg hB hW₀))
    have hcounts := iwaniecPaperA_child_count_sum_le n hy hξ hSdom hIH
    have hcountBound : (iwaniecPaperA (n + 1) level s : Real) ≤ B * q + C * f * (B * W₀ * (1 + q)) := by
      rw [hcountEq, iwaniecPaperA_successor_band_recursion n hy hSdom hST, Nat.cast_add]
      exact add_le_add hfarBound (hcounts.trans
        (mul_le_mul_of_nonneg_left hchildSum (mul_nonneg hC0 (show 0 ≤ f by linarith only [hf]))))
    have hbudget := iwaniec_middle_step_budget hB hq hC hf hW₀1
    have hstep : f * (1 + 4 * q) * W₀ ≤ fp := by
      have hh := (hslack n hnRange).le
      convert hh using 1 <;> dsimp [f, fp, W₀, q, L] <;> ring
    have hscaled := mul_le_mul_of_nonneg_left hstep (show 0 ≤ C * B by positivity)
    have hh := hcountBound.trans (hbudget.trans hscaled)
    convert hh using 1 <;> ring
  · have horder := iwaniecPaperA_antitone_parameter (n + 1) hy hξsub (le_of_not_ge hST)
    have hcount : (iwaniecPaperA (n + 1) level s : Real) ≤ B * q := by
      rw [hcountEq]
      exact (show (iwaniecPaperA (n + 1) level S : Real) ≤ iwaniecPaperA (n + 1) level (ξ - 1) by
        exact_mod_cast horder).trans hfarBound
    have hCfp : 1 ≤ C * fp := by
      have hh := mul_le_mul hC hfp (by norm_num : (0 : Real) ≤ 1 / 2) (by linarith : 0 ≤ C)
      nlinarith only [hh]
    have hlast := mul_le_mul_of_nonneg_right hCfp hB
    have hfirst : B * q ≤ B := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hq1 hB
    exact hcount.trans (hfirst.trans (by simpa only [one_mul] using hlast))

end

end Erdos1212Kernel
