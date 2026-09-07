import Erdos1212Kernel.IwaniecQPrimeEndpoint
import Erdos1212Kernel.IwaniecInductionExponentialError

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 650000

theorem eventually_iwaniecQ_prime_error_absorbed {K : Real} (hK : 0 ≤ K) :
    ∀ᶠ level : Real in atTop, 1 < level ∧ ∀ (rank : Nat) (s : Real),
      iwaniecCorollaryThreeDomainStart rank ≤ s → s ≤ iwaniecPaperXi level →
      K * iwaniecParityReciprocalLogWeight rank (Real.log level) (Real.exp (Real.log level / s)) *
        Real.exp (-Real.sqrt (Real.log level / iwaniecPaperXi level)) ≤
          iwaniecAuxG (rank + 1) s / Real.log level ^ 4 := by
  have hlim := (tendsto_iwaniecXi_log_weighted_error 3 (c := 1) (by norm_num)).const_mul (192 * K)
  simp only [neg_one_mul, mul_zero] at hlim
  filter_upwards [eventually_gt_atTop (1 : Real),
    hlim.eventually (Iio_mem_nhds (show (0 : Real) < 1 by norm_num))] with level hy hsmall
  refine ⟨hy, ?_⟩
  intro rank s hs hsξ
  let L := Real.log level
  let ξ := iwaniecPaperXi level
  let E := Real.exp (-Real.sqrt (L / ξ))
  have hL : 0 < L := Real.log_pos hy
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hs2 := (iwaniecCorollaryThreeDomainStart_bounds rank).1.trans hs
  have hsq : s ^ 2 ≤ ξ ^ 2 := by dsimp [ξ]; nlinarith only [hs2, hsξ]
  have hG := (iwaniecAuxG_pos_exactDomain (rank + 1)
    ((iwaniecAuxGStart_le_recursion_start rank).trans hs)).le
  have hendpoint := (iwaniecQ_prime_endpoint_bound rank hy hs).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : Real) ≤ 192)) hG) hL.le)
  have hnormal : 192 * K * ξ ^ 2 * E / L ≤ 1 / L ^ 4 := by
    apply (div_le_div_iff₀ hL (pow_pos hL 4)).mpr
    have hh := mul_le_mul_of_nonneg_right hsmall.le hL.le
    change 192 * K * (L ^ 3 * ξ ^ 2 * E) * L ≤ 1 * L at hh
    nlinarith only [hh]
  calc
    _ ≤ K * (192 * ξ ^ 2 * iwaniecAuxG (rank + 1) s / L) * E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hendpoint hK) hE
    _ = (192 * K * ξ ^ 2 * E / L) * iwaniecAuxG (rank + 1) s := by ring
    _ ≤ (1 / L ^ 4) * iwaniecAuxG (rank + 1) s := mul_le_mul_of_nonneg_right hnormal hG
    _ = _ := by dsimp [L]; ring

/-- Source (4.3), with coefficient one: the fixed-rank endpoint is
uniform over parity and is used only after its positive lower anchor. -/
theorem eventually_iwaniec_source_four_three {D : Real} (hD : 0 ≤ D) :
    ∀ᶠ level : Real in atTop, 1 < level ∧ ∀ rank : Nat,
      D * Real.exp (-Real.sqrt (Real.log level / 6)) <
        iwaniecAuxG rank 4 / Real.log level ^ 4 := by
  let m := iwaniecAuxM 4 / 3
  have hm : 0 < m := div_pos (iwaniecAuxM_pos (by norm_num)) (by norm_num)
  have hlim := (tendsto_iwaniecXi_log_weighted_error 4 (c := 1) (by norm_num)).const_mul D
  simp only [neg_one_mul, mul_zero] at hlim
  filter_upwards [eventually_gt_atTop (1 : Real),
    tendsto_iwaniecPaperXi_atTop.eventually_ge_atTop 6,
    hlim.eventually (Iio_mem_nhds hm)] with level hy hξ hsmall
  refine ⟨hy, ?_⟩
  intro rank
  let L := Real.log level
  let ξ := iwaniecPaperXi level
  let E := Real.exp (-Real.sqrt (L / ξ))
  have hL : 0 < L := Real.log_pos hy
  have hξone : 1 ≤ ξ := by dsimp [ξ]; linarith
  have hξsq : 1 ≤ ξ ^ 2 := one_le_pow₀ hξone
  have hE : Real.exp (-Real.sqrt (L / 6)) ≤ E := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hL.le (by norm_num) hξ))
  have hcomp : Real.exp (-Real.sqrt (L / 6)) ≤ ξ ^ 2 * E :=
    hE.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hξsq (Real.exp_pos _).le)
  have hscaled := mul_le_mul_of_nonneg_left hcomp (show 0 ≤ D * L ^ 4 by positivity)
  apply (lt_div_iff₀ (pow_pos hL 4)).mpr
  calc
    _ ≤ D * (L ^ 4 * ξ ^ 2 * E) := by convert hscaled using 1 <;> ring
    _ < m := hsmall
    _ ≤ iwaniecAuxG rank 4 := (iwaniecAuxG_bounds rank (by norm_num : (2 : Real) ≤ 4)).1

theorem eventually_iwaniecQ_d2_error_absorbed {D : Real} (hD : 0 ≤ D) :
    ∀ᶠ level : Real in atTop, 1 < level ∧ ∀ (rank : Nat) (s : Real),
      iwaniecAuxGStart rank ≤ s →
      (if Even rank ∧ s < 4 then D * Real.exp (-Real.sqrt (Real.log level / 6)) else 0) ≤
        iwaniecAuxG rank s / Real.log level ^ 4 := by
  filter_upwards [eventually_iwaniec_source_four_three hD] with level hlevel
  refine ⟨hlevel.1, ?_⟩
  intro rank s hs
  by_cases hcase : Even rank ∧ s < 4
  · rw [if_pos hcase]
    exact (hlevel.2 rank).le.trans (div_le_div_of_nonneg_right
      (iwaniecAuxG_antitoneOn_exactDomain rank hs (hs.trans hcase.2.le) hcase.2.le)
      (pow_nonneg (Real.log_pos hlevel.1).le 4))
  · rw [if_neg hcase]
    exact div_nonneg (iwaniecAuxG_pos_exactDomain rank hs).le (pow_nonneg (Real.log_pos hlevel.1).le 4)

end

end Erdos1212Kernel
