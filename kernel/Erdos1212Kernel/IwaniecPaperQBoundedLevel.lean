import Erdos1212Kernel.IwaniecPaperQInitialAnchor
import Erdos1212Kernel.IwaniecSieveSeriesMonotonicity

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

/-- The literal Q main/error expression in Theorem 4: the full parity
profile, and G at rank r (not the support-count rank r+1). -/
def iwaniecPaperQMajorant (C : Real) (rank : Nat) (level s : Real) : Real :=
  iwaniecParitySieveProfile rank s / Real.log level +
    C * ((rank : Real) / ((rank : Real) + 1)) * iwaniecAuxWeightPower level s *
      iwaniecAuxG rank s / Real.log level ^ 2

theorem iwaniecPaperQMajorant_pos {C level s : Real} {rank : Nat}
    (hC : 0 < C) (hr : 1 ≤ rank) (hy : 1 < level)
    (hs : iwaniecAuxGStart rank ≤ s) : 0 < iwaniecPaperQMajorant C rank level s := by
  have hstart : 1 ≤ iwaniecAuxGStart rank := by unfold iwaniecAuxGStart; split <;> norm_num
  have hf := iwaniecParitySieveProfile_nonneg_exactDomain rank hs
  have hW := iwaniecAuxWeightPower_pos level (hstart.trans hs)
  have hG := iwaniecAuxG_pos_exactDomain rank hs
  have hr0 : (0 : Real) < rank := by exact_mod_cast (show 0 < rank by omega)
  have hlog := Real.log_pos hy
  unfold iwaniecPaperQMajorant
  exact add_pos_of_nonneg_of_pos (div_nonneg hf hlog.le) (by positivity)

theorem iwaniecPaperQMajorant_factor_lower {C X M f W G : Real}
    (hX : 0 ≤ X) (hM : 0 < M) (hC : (1 + X) ^ 3 / M ≤ C)
    (hf : (1 / 2 : Real) ≤ f) (hW : 1 ≤ W) (hG : X * M / 3 ≤ G) :
    (1 + X) ^ 3 * X / 6 ≤ C * f * W * G := by
  have hC0 : 0 ≤ C := (div_nonneg (by positivity) hM.le).trans hC
  have hf0 : 0 ≤ f := by linarith
  have hW0 : 0 ≤ W := by linarith
  have hfirst := mul_le_mul hC hf (by norm_num : (0 : Real) ≤ 1 / 2) hC0
  have hsecond := mul_le_mul hfirst hW (by norm_num : (0 : Real) ≤ 1) (mul_nonneg hC0 hf0)
  have hthird := mul_le_mul hsecond hG (by positivity : 0 ≤ X * M / 3)
    (mul_nonneg (mul_nonneg hC0 hf0) hW0)
  have heq : ((1 + X) ^ 3 / M) * (1 / 2) * 1 * (X * M / 3) = (1 + X) ^ 3 * X / 6 := by
    field_simp [hM.ne']
    <;> ring
  rwa [heq] at hthird

theorem iwaniecPaperQ_initial_polynomial_budget {L X : Real}
    (hL : 0 ≤ L) (hLX : L ≤ X) (hX : 64 ≤ X) :
    3 * (1 + X) * L ^ 2 ≤ (1 + X) ^ 3 * X / 6 := by
  have hX0 : 0 ≤ X := by linarith
  have hsq : L ^ 2 ≤ X ^ 2 := by nlinarith only [hL, hLX]
  have hpoly : 18 * X ≤ (1 + X) ^ 2 := by
    have hh := mul_nonneg hX0 (show 0 ≤ X - 16 by linarith)
    nlinarith only [hh]
  have hscaled := mul_le_mul_of_nonneg_right hpoly (show 0 ≤ (1 + X) * X by positivity)
  have hsmall := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 3 * (1 + X) by positivity)
  nlinarith only [hscaled, hsmall]

/-- The bounded-level case of source (4.8), with exp(gamma), the rank
prefactor, and the actual weighted Q all paid by the source c7 term.
Zero mass is separated before deriving a nonempty-carrier parameter bound. -/
theorem iwaniecPaperQ_bounded_level_bound {C Y level s : Real} {rank : Nat}
    (hlogY : 64 ≤ Real.log Y)
    (hC : (1 + Real.log Y) ^ 3 / iwaniecAuxM (2 * Real.log Y) ≤ C)
    (hr : 1 ≤ rank) (hy : 1 < level) (hyY : level ≤ Y)
    (hs : iwaniecAuxGStart rank ≤ s) :
    Real.exp Real.eulerMascheroniConstant * iwaniecPaperQ rank level s <
      iwaniecPaperQMajorant C rank level s := by
  let X := Real.log Y
  let L := Real.log level
  let M := iwaniecAuxM (2 * X)
  have hX : 64 ≤ X := hlogY
  have hX0 : 0 ≤ X := by linarith
  have hL : 0 < L := Real.log_pos hy
  have hM : 0 < M := iwaniecAuxM_pos (by dsimp [X]; linarith)
  have hC0 : 0 < C := (div_pos (by positivity : 0 < (1 + X) ^ 3) hM).trans_le hC
  by_cases hQ : 0 < iwaniecPaperQ rank level s
  · have hmargin := iwaniecPaperQ_positive_bounded_margin rank hy hyY (by linarith) hs hQ
    have hanchor := iwaniecAuxG_bounded_shifted_anchor rank (by linarith : 2 ≤ X) hs hmargin
    have hstart : 1 ≤ iwaniecAuxGStart rank := by unfold iwaniecAuxGStart; split <;> norm_num
    have hs1 : 1 ≤ s := hstart.trans hs
    have hW : 1 ≤ iwaniecAuxWeightPower level s :=
      Real.one_le_rpow (iwaniecAuxWeightBase_one_le level hs1) (by linarith)
    have hrR : (1 : Real) ≤ rank := by exact_mod_cast hr
    have hratio : (1 / 2 : Real) ≤ (rank : Real) / ((rank : Real) + 1) := by
      apply (le_div_iff₀ (show 0 < (rank : Real) + 1 by positivity)).mpr
      linarith only [hrR]
    have hfactor := iwaniecPaperQMajorant_factor_lower hX0 hM hC hratio hW hanchor
    have hlog := Real.log_le_log (zero_lt_one.trans hy) hyY
    have hpoly := iwaniecPaperQ_initial_polynomial_budget hL.le hlog hlogY
    have hnormalized : 3 * (1 + X) ≤
        C * ((rank : Real) / ((rank : Real) + 1)) * iwaniecAuxWeightPower level s *
          iwaniecAuxG rank s / L ^ 2 :=
      (le_div_iff₀ (sq_pos_of_pos hL)).mpr (hpoly.trans hfactor)
    have hprofile : 0 ≤ iwaniecParitySieveProfile rank s / Real.log level :=
      div_nonneg (iwaniecParitySieveProfile_nonneg_exactDomain rank hs) hL.le
    have hexp : Real.exp Real.eulerMascheroniConstant < 3 :=
      (Real.exp_lt_exp.mpr (show Real.eulerMascheroniConstant < 1 by
        linarith [Real.eulerMascheroniConstant_lt_two_thirds])).trans Real.exp_one_lt_three
    have hmass := iwaniecPaperQ_bounded_level_log_bound rank hy hyY hs
    have hscaled : Real.exp Real.eulerMascheroniConstant * iwaniecPaperQ rank level s < 3 * (1 + X) :=
      (mul_lt_mul_of_pos_left hmass (Real.exp_pos _)).trans
        (mul_lt_mul_of_pos_right hexp (by positivity : 0 < 1 + X))
    unfold iwaniecPaperQMajorant
    have hh := hscaled.trans_le hnormalized
    dsimp [L] at hh
    linarith only [hh, hprofile]
  · have hz : iwaniecPaperQ rank level s = 0 :=
      le_antisymm (le_of_not_gt hQ) (iwaniecPaperQ_nonneg rank level s)
    rw [hz, mul_zero]
    exact iwaniecPaperQMajorant_pos hC0 hr hy hs

end

end Erdos1212Kernel
