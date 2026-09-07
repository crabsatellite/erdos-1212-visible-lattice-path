import Erdos1212Kernel.IwaniecPaperSupportFinite
import Erdos1212Kernel.IwaniecAuxiliaryXiRange
import Erdos1212Kernel.IwaniecAuxiliaryWeightCalculus

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 650000

def iwaniecPaperAMajorant (C : Real) (rank : Nat) (level s : Real) : Real :=
  C * ((rank : Real) / ((rank : Real) + 1)) * iwaniecAuxWeightPower level s *
    iwaniecAuxG (rank + 1) s / Real.log level ^ 2 * level

theorem iwaniecAuxG_lower_anchor (rank : Nat) {s T : Real}
    (hs : iwaniecAuxGStart rank ≤ s) (hT : 2 ≤ T) (hsT : s ≤ T) :
    iwaniecAuxM T / 3 ≤ iwaniecAuxG rank s :=
  (iwaniecAuxG_bounds rank hT).1.trans
    (iwaniecAuxG_antitoneOn_exactDomain rank hs (hs.trans hsT) hsT)

theorem iwaniecPaperXi_le_bounded_log {level Y : Real}
    (hy : 1 < level) (hY : level ≤ Y) (hlogY : 12288 ≤ Real.log Y) :
    iwaniecPaperXi level ≤ 2 * Real.log Y := by
  by_cases hu : Real.log (Real.log (3 * level)) ≤ 1
  · have hh := iwaniecPaperXi_le_small_when_loglog_small hy hu
    linarith
  · have hu1 : 1 ≤ Real.log (Real.log (3 * level)) := (lt_of_not_ge hu).le
    have hpow := Real.one_le_rpow hu1 (by norm_num : (0 : Real) ≤ 11 / 5)
    have hlog := Real.log_le_log (by linarith : 0 < level) hY
    have hxi : iwaniecPaperXi level ≤ Real.log level := div_le_self (Real.log_pos hy).le hpow
    linarith

theorem iwaniecPaperAMajorant_factor_lower {C L M f W G : Real}
    (hM : 0 < M) (hC : 6 * L ^ 2 / M ≤ C) (hf : (1 / 2 : Real) ≤ f)
    (hW : 1 ≤ W) (hG : M / 3 ≤ G) :
    L ^ 2 ≤ C * f * W * G := by
  have hC0 : 0 ≤ C := (div_nonneg (by positivity) hM.le).trans hC
  have hf0 : 0 ≤ f := by linarith
  have hW0 : 0 ≤ W := by linarith
  have hfirst := mul_le_mul hC hf (by norm_num : (0 : Real) ≤ 1 / 2) hC0
  have hsecond := mul_le_mul hfirst hW (by norm_num : (0 : Real) ≤ 1) (mul_nonneg hC0 hf0)
  have hthird := mul_le_mul hsecond hG (by positivity : 0 ≤ M / 3) (mul_nonneg (mul_nonneg hC0 hf0) hW0)
  have heq : (6 * L ^ 2 / M) * (1 / 2) * 1 * (M / 3) = L ^ 2 := by
    field_simp [hM.ne']
    <;> ring
  rwa [heq] at hthird

/-- The actual bounded-level branch of the count induction, using the
first term of the paper's c7 choice and its original rank prefactor. -/
theorem iwaniecPaperA_bounded_level_bound {C Y level s : Real} {rank : Nat}
    (hlogY : 12288 ≤ Real.log Y)
    (hC : (1 + Real.log Y) ^ 3 / iwaniecAuxM (2 * Real.log Y) ≤ C)
    (hr : 1 ≤ rank) (hy : 1 < level) (hyY : level ≤ Y)
    (hs : iwaniecAuxGStart (rank + 1) ≤ s) (hsxi : s ≤ iwaniecPaperXi level) :
    (iwaniecPaperA rank level s : Real) ≤ iwaniecPaperAMajorant C rank level s := by
  let LY := Real.log Y
  let L := Real.log level
  let M := iwaniecAuxM (2 * LY)
  have hL : 0 < L := Real.log_pos hy
  have hLY : 0 < LY := by dsimp [LY]; linarith
  have hM : 0 < M := iwaniecAuxM_pos (by dsimp [LY]; linarith)
  have hLLY : L ≤ LY := Real.log_le_log (by linarith) hyY
  have hLsq : L ^ 2 ≤ LY ^ 2 := by nlinarith only [hL, hLLY]
  have hpoly : 6 * LY ^ 2 ≤ (1 + LY) ^ 3 := by
    have hLY3 : 3 ≤ LY := by dsimp [LY]; linarith
    have hh : 0 ≤ LY ^ 2 * (LY - 3) := mul_nonneg (sq_nonneg LY) (sub_nonneg.mpr hLY3)
    nlinarith only [hh, hLY]
  have hCsmall : 6 * L ^ 2 / M ≤ C :=
    (div_le_div_of_nonneg_right (by nlinarith only [hLsq, hpoly] : 6 * L ^ 2 ≤ (1 + LY) ^ 3) hM.le).trans hC
  have hstart1 : 1 ≤ iwaniecAuxGStart (rank + 1) := by unfold iwaniecAuxGStart; split_ifs <;> norm_num
  have hs1 : 1 ≤ s := hstart1.trans hs
  have hW : 1 ≤ iwaniecAuxWeightPower level s :=
    Real.one_le_rpow (iwaniecAuxWeightBase_one_le level hs1) (by linarith)
  have hanchor := iwaniecAuxG_lower_anchor (rank + 1) hs
    (show 2 ≤ 2 * LY by dsimp [LY]; linarith) (hsxi.trans (iwaniecPaperXi_le_bounded_log hy hyY hlogY))
  have hrR : (1 : Real) ≤ rank := by exact_mod_cast hr
  have hratio : (1 / 2 : Real) ≤ (rank : Real) / ((rank : Real) + 1) := by
    apply (le_div_iff₀ (show 0 < (rank : Real) + 1 by positivity)).mpr
    linarith only [hrR]
  have hfactor := iwaniecPaperAMajorant_factor_lower hM hCsmall hratio hW hanchor
  have hnormalized : 1 ≤ (C * ((rank : Real) / ((rank : Real) + 1)) * iwaniecAuxWeightPower level s *
      iwaniecAuxG (rank + 1) s) / L ^ 2 := (le_div_iff₀ (sq_pos_of_pos hL)).mpr (by simpa using hfactor)
  have hcount := iwaniecPaperSupportCount_le_level rank (z := Real.exp (Real.log level / s)) hy
  have hscaled := mul_le_mul_of_nonneg_right hnormalized (show 0 ≤ level by linarith)
  exact hcount.trans (by simpa only [one_mul, iwaniecPaperAMajorant, L] using hscaled)

end

end Erdos1212Kernel
