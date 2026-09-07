import Erdos1212Kernel.TaoLittlewoodLargeScalar

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 1900000

def taoLittlewoodR (T : Real) : Nat :=
  Nat.ceil (8 * Real.log T / Real.log (Real.log T))

def taoLittlewoodJ (T : Real) : Nat :=
  Nat.floor (Real.log T / Real.log 2)

theorem taoLittlewoodR_lower (T : Real) :
    8 * Real.log T / Real.log (Real.log T) ≤ (taoLittlewoodR T : Real) := by
  exact Nat.le_ceil _

theorem taoLittlewoodJ_top {T : Real} (hT : 1 < T) :
    (((2 ^ taoLittlewoodJ T : Nat) : Real)) ≤ T := by
  let x : Real := Real.log T / Real.log 2
  have hx0 : 0 ≤ x := by
    unfold x
    exact div_nonneg (Real.log_nonneg hT.le) (Real.log_pos (by norm_num)).le
  have hJ : ((taoLittlewoodJ T : Nat) : Real) ≤ x := by
    unfold taoLittlewoodJ
    exact Nat.floor_le hx0
  have hpow : (2 : Real) ^ (taoLittlewoodJ T : Real) ≤ (2 : Real) ^ x :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hJ
  have hright : (2 : Real) ^ x = T := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    unfold x
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    have hcancel : Real.log 2 * (Real.log T / Real.log 2) = Real.log T := by
      field_simp
    rw [hcancel, Real.exp_log (by linarith : 0 < T)]
  have hleft : (2 : Real) ^ (taoLittlewoodJ T : Real) =
      (((2 ^ taoLittlewoodJ T : Nat) : Real)) := by
    rw [Real.rpow_natCast]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  rwa [hleft, hright] at hpow

theorem taoLittlewoodJ_bottom {T : Real} (hT : 1 < T) :
    T / 2 < (((2 ^ taoLittlewoodJ T : Nat) : Real)) := by
  let x : Real := Real.log T / Real.log 2
  have hx0 : 0 ≤ x := by
    unfold x
    exact div_nonneg (Real.log_nonneg hT.le) (Real.log_pos (by norm_num)).le
  have hxJ : x < (taoLittlewoodJ T : Real) + 1 := by
    unfold taoLittlewoodJ
    exact Nat.lt_floor_add_one x
  have hpow : (2 : Real) ^ x <
      (2 : Real) ^ ((taoLittlewoodJ T : Real) + 1) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hxJ
  have hleft : (2 : Real) ^ x = T := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    unfold x
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    have hcancel : Real.log 2 * (Real.log T / Real.log 2) = Real.log T := by
      field_simp
    rw [hcancel, Real.exp_log (by linarith : 0 < T)]
  have hright : (2 : Real) ^ ((taoLittlewoodJ T : Real) + 1) =
      2 * (((2 ^ taoLittlewoodJ T : Nat) : Real)) := by
    rw [Real.rpow_add (by norm_num : (0 : Real) < 2), Real.rpow_one,
      Real.rpow_natCast]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    ring
  rw [hleft, hright] at hpow
  linarith

theorem eventually_taoLittlewood_scale_separation :
    ∀ᶠ T : Real in atTop, taoLittlewoodR T ≤ taoLittlewoodJ T := by
  have hloglog : ∀ᶠ T : Real in atTop,
      16 * Real.log 2 ≤ Real.log (Real.log T) :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop
      (16 * Real.log 2)
  have hlog : ∀ᶠ T : Real in atTop,
      2 * Real.log 2 ≤ Real.log T :=
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * Real.log 2)
  filter_upwards [hloglog, hlog, eventually_gt_atTop (Real.exp 1)] with T hll hL hT
  let L : Real := Real.log T
  let l : Real := Real.log L
  let x : Real := L / Real.log 2
  let a : Real := 8 * L / l
  have hLp : 0 < L := by unfold L; exact Real.log_pos ((Real.one_lt_exp_iff.mpr one_pos).trans hT)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlp : 0 < l := by
    unfold l L
    nlinarith
  have ha_half : a ≤ x / 2 := by
    unfold a
    apply (div_le_iff₀ hlp).2
    have hratio : 8 ≤ l / (2 * Real.log 2) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log 2)).2
      unfold l L
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hratio hLp.le
    unfold x
    convert hmul using 1 <;> field_simp <;> ring
  have hx2 : 2 ≤ x := by
    unfold x L
    exact (le_div_iff₀ hlog2).2 hL
  have ha : a ≤ x - 1 := ha_half.trans (by linarith)
  have hfloor : x - 1 < ((taoLittlewoodJ T : Nat) : Real) := by
    have h := Nat.lt_floor_add_one x
    unfold taoLittlewoodJ
    linarith
  apply (Nat.ceil_le).2
  change a ≤ ((taoLittlewoodJ T : Nat) : Real)
  unfold a
  exact ha.trans hfloor.le

end

end Erdos1212Kernel
