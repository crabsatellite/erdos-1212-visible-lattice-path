import Erdos1212Kernel.IwaniecQMiddleBudget

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 900000

/-- The full middle-rank Q step, on the literal parity domain. The
rank-r induction hypothesis is consumed on every actual child y/p.
Both sides of the xi-1 cut and the constant odd extension are included. -/
theorem eventually_iwaniecPaperQ_middle_step :
    ∀ᶠ level : Real in atTop, 1 < level ∧ ∀ (C : Real) (n : Nat) (s : Real),
      2 ≤ C → 1 ≤ n → iwaniecAuxGStart (n + 1) ≤ s → s ≤ iwaniecPaperXi level →
      (n : Real) + 1 ≤ 2 * Real.log level / Real.log (Real.log level) →
      (∀ y t : Real, 1 < y → iwaniecAuxGStart n ≤ t → t ≤ iwaniecPaperXi y →
        Real.exp Real.eulerMascheroniConstant * iwaniecPaperQ n y t < iwaniecPaperQMajorant C n y t) →
      Real.exp Real.eulerMascheroniConstant * iwaniecPaperQ (n + 1) level s <
        iwaniecPaperQMajorant C (n + 1) level s := by
  obtain ⟨Kmain, Kerr, D, hKmain, hKerr, hD, hcombined⟩ := exists_iwaniecPaperQ_middle_expansion
  filter_upwards [eventually_iwaniecQ_prime_error_absorbed hKmain.le,
    eventually_iwaniecQ_d2_error_absorbed hD.le, eventually_iwaniecQ_far_normalized,
    eventually_iwaniec_rank_step_absorption (C := 2) (by norm_num),
    eventually_iwaniecXi_error_le_inv_log_sq (100 * Kerr),
    tendsto_iwaniecPaperXi_atTop.eventually_ge_atTop iwaniecAuxSZero,
    Real.tendsto_log_atTop.eventually_ge_atTop 2]
    with level hprime hbase hfar hslack herror hξ hlog
  have hy := hfar.1
  refine ⟨hy, ?_⟩
  intro C n s hC hn hs hsξ hnRange hIH
  have hC0 : 0 ≤ C := by linarith only [hC]
  have hCpos : 0 < C := by linarith only [hC]
  let L := Real.log level
  let ξ := iwaniecPaperXi level
  let S := max (iwaniecCorollaryThreeDomainStart n) s
  let q := (L ^ 2)⁻¹
  let B := iwaniecAuxWeightPower level s * iwaniecAuxG (n + 1) s / L ^ 2
  let W₀ := iwaniecAuxWeightPower level iwaniecAuxSZero
  let f := (n : Real) / ((n : Real) + 1)
  let fp := ((n : Real) + 1) / ((n : Real) + 2)
  let F := iwaniecParitySieveProfile (n + 1) s / L
  have hL : 0 < L := Real.log_pos hy
  have hq : 0 ≤ q := inv_nonneg.mpr (sq_nonneg L)
  have hstart : 1 ≤ iwaniecAuxGStart (n + 1) := by unfold iwaniecAuxGStart; split <;> norm_num
  have hs1 : 1 ≤ s := hstart.trans hs
  have hW := iwaniecAuxWeightPower_pos level hs1
  have hG := iwaniecAuxG_pos_exactDomain (n + 1) hs
  have hB : 0 < B := by dsimp [B]; positivity
  have hF : 0 ≤ F := div_nonneg (iwaniecParitySieveProfile_nonneg_exactDomain (n + 1) hs) hL.le
  have hW₀1 : 1 ≤ W₀ := Real.one_le_rpow
    (iwaniecAuxWeightBase_one_le level (by linarith [iwaniecAuxSZero_large])) (by linarith [iwaniecAuxSZero_large])
  have hW₀ : 0 ≤ W₀ := by linarith
  have hf : (1 / 2 : Real) ≤ f := iwaniec_rank_ratio_ge_half hn
  have hf0 : 0 ≤ f := by linarith only [hf]
  have hfp : (1 / 2 : Real) ≤ fp := by
    have hh := iwaniec_rank_ratio_ge_half (show 1 ≤ n + 1 by omega)
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, show (1 : Real) + 1 = 2 by norm_num] using hh
  have hmainId : iwaniecPaperQMajorant C (n + 1) level s = F + C * fp * B := by
    unfold iwaniecPaperQMajorant
    simp only [Nat.cast_add, Nat.cast_one, add_assoc, show (1 : Real) + 1 = 2 by norm_num]
    dsimp [F, fp, B, L]
    ring
  obtain ⟨hQEq, hGEq, hFEq⟩ := iwaniecPaperQ_recursion_parameter n hs
  have hSdom : iwaniecCorollaryThreeDomainStart n ≤ S := le_max_left _ _
  have hDoms0 : iwaniecCorollaryThreeDomainStart n ≤ iwaniecAuxSZero := by
    have hh := (iwaniecCorollaryThreeDomainStart_bounds n).2
    linarith [iwaniecAuxSZero_large]
  have hSξ : S ≤ ξ := max_le (hDoms0.trans hξ) hsξ
  have hSstart : iwaniecAuxGStart (n + 1) ≤ S := hs.trans (le_max_right _ _)
  have hξfour : 4 ≤ ξ - 1 := by dsimp [ξ]; linarith [iwaniecAuxSZero_large]
  have hfarBound : Real.exp Real.eulerMascheroniConstant * iwaniecPaperQ (n + 1) level (ξ - 1) < 3 * B * q :=
    hfar.2 (n + 1) s hs hsξ
  rw [hmainId]
  by_cases hST : S ≤ ξ - 1
  · let E := Real.exp (-Real.sqrt (L / ξ))
    let e := 100 * Kerr * ξ ^ 2 * E
    let M := iwaniecAuxWeightPower level (max iwaniecAuxSZero S) * iwaniecAuxG (n + 1) S / L ^ 2
    have he : e ≤ q := herror.2
    have he0 : 0 ≤ e := by dsimp [e, E]; positivity
    have hmaxS : max iwaniecAuxSZero S = max iwaniecAuxSZero s := by
      dsimp [S]
      rw [← max_assoc, max_eq_left hDoms0]
    have hweight : iwaniecAuxWeightPower level (max iwaniecAuxSZero S) ≤ iwaniecAuxWeightPower level s * W₀ := by
      rw [hmaxS]
      exact iwaniecWeightPower_max_bound hs1
    have hM : M ≤ B * W₀ := by
      have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hweight hG.le) (sq_nonneg L)
      dsimp [M]
      rw [hGEq]
      convert hh using 1 <;> dsimp [B] <;> ring
    have hchild : C * f * (M * (1 + e)) ≤ C * f * (B * W₀ * (1 + q)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hM (add_le_add le_rfl he) (by linarith only [he0]) (mul_nonneg hB.le hW₀))
        (mul_nonneg hC0 hf0)
    have hp : Kmain * iwaniecParityReciprocalLogWeight n L (Real.exp (L / S)) * E ≤ B * q := by
      have hh := hprime.2 n S hSdom hSξ
      rw [hGEq] at hh
      exact hh.trans (iwaniecQ_inv_four_le_weighted (n + 1) hy hs)
    have hd : (if Even (n + 1) ∧ S < 4 then D * Real.exp (-Real.sqrt (L / 6)) else 0) ≤ B * q := by
      have hh := hbase.2 (n + 1) S hSstart
      rw [hGEq] at hh
      exact hh.trans (iwaniecQ_inv_four_le_weighted (n + 1) hy hs)
    have hraw : Real.exp Real.eulerMascheroniConstant * iwaniecPaperQ (n + 1) level s ≤
        F + 5 * B * q + C * f * (B * W₀ * (1 + q)) := by
      rw [hQEq]
      have hh := hcombined C n level S hC0 hy hξ hSdom hST hIH
      rw [hFEq] at hh
      change Real.exp Real.eulerMascheroniConstant * iwaniecPaperQ (n + 1) level S ≤
        F + Kmain * iwaniecParityReciprocalLogWeight n L (Real.exp (L / S)) * E +
        C * f * (M * (1 + e)) +
        (if Even (n + 1) ∧ S < 4 then D * Real.exp (-Real.sqrt (L / 6)) else 0) +
        Real.exp Real.eulerMascheroniConstant * iwaniecPaperQ (n + 1) level (ξ - 1) at hh
      linarith only [hh, hp, hd, hchild, hfarBound.le]
    have hbudget := iwaniecQ_middle_step_budget hB.le hq hC hf hW₀1
    have hstep : f * (1 + 8 * q) * W₀ < fp := by
      have hh := hslack n hnRange
      convert hh using 1 <;> dsimp [f, fp, q, W₀, L] <;> ring
    have hscaled := mul_lt_mul_of_pos_left hstep (mul_pos hCpos hB)
    have hpaid : 5 * B * q + C * f * (B * W₀ * (1 + q)) < C * fp * B := by
      have hh := hbudget.trans_lt hscaled
      convert hh using 1 <;> ring
    linarith only [hraw, hpaid]
  · have horder := iwaniecPaperQ_successor_antitone_high n hy hξfour (le_of_not_ge hST)
    have hQfar : Real.exp Real.eulerMascheroniConstant * iwaniecPaperQ (n + 1) level s < 3 * B * q := by
      rw [hQEq]
      exact (mul_le_mul_of_nonneg_left horder (Real.exp_pos Real.eulerMascheroniConstant).le).trans_lt hfarBound
    have hqsmall : 3 * q ≤ 1 := by
      have hh : (3 : Real) / L ^ 2 ≤ 1 := (div_le_one₀ (sq_pos_of_pos hL)).mpr (by
        change 2 ≤ L at hlog
        nlinarith only [hlog])
      simpa only [q, div_eq_mul_inv] using hh
    have hCfp : 1 ≤ C * fp := by
      have hh := mul_le_mul hC hfp (by norm_num : (0 : Real) ≤ 1 / 2) hC0
      nlinarith only [hh]
    have hsmall := mul_le_mul_of_nonneg_left hqsmall hB.le
    have hpaid := mul_le_mul_of_nonneg_right hCfp hB.le
    nlinarith only [hQfar, hsmall, hpaid, hF]

end

end Erdos1212Kernel
