import Erdos1212Kernel.TaoLittlewoodExtendedCanonical

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 1900000

theorem taoLittlewoodJ_cast_le_two_log {T : Real} (hT : 1 ≤ T) :
    (taoLittlewoodJ T : Real) ≤ 2 * Real.log T := by
  have hx0 : 0 ≤ Real.log T / Real.log 2 := by
    exact div_nonneg (Real.log_nonneg hT) (Real.log_pos (by norm_num)).le
  have hfloor : (taoLittlewoodJ T : Real) ≤ Real.log T / Real.log 2 := by
    unfold taoLittlewoodJ
    exact Nat.floor_le hx0
  have hhalf : (1 : Real) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : Real) < 2)
    norm_num at h
    exact h
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hratio : Real.log T / Real.log 2 ≤ 2 * Real.log T := by
    apply (div_le_iff₀ (Real.log_pos (by norm_num))).2
    nlinarith [mul_le_mul_of_nonneg_left hhalf hlog0]
  exact hfloor.trans hratio

theorem taoLittlewood_log_two_add_le_two_log {T : Real} (hT : 2 ≤ T) :
    Real.log (2 + T) ≤ 2 * Real.log T := by
  have hsq : 2 + T ≤ T ^ 2 := by nlinarith
  calc
    Real.log (2 + T) ≤ Real.log (T ^ 2) :=
      Real.log_le_log (by linarith : 0 < 2 + T) hsq
    _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num

theorem taoLittlewoodWidth_le_log_power {T : Real} {R : Nat}
    (hL : 1 < Real.log T) (hR : 1 ≤ R)
    (hRlow : 8 * Real.log T / Real.log (Real.log T) ≤ (R : Real))
    (hlarge :
      Real.log (Real.log T) ^ 2 /
          (8 * Real.log 2 * Real.log T) ≤
        1 / (4 * (Real.log T) ^ (1 / 8 : Real))) :
    taoLittlewoodWidth T R ≤
      1 / (4 * (Real.log T) ^ (1 / 8 : Real)) := by
  let L : Real := Real.log T
  let l : Real := Real.log L
  let r : Real := R
  have hLp : 0 < L := by unfold L; linarith
  have hlp : 0 < l := by unfold l; exact Real.log_pos hL
  have hrp : 0 < r := by unfold r; exact_mod_cast hR
  have hlog2 : (0 : Real) < Real.log 2 := Real.log_pos (by norm_num)
  have hdenOrder : 8 * L * Real.log 2 / l ≤ r * Real.log 2 := by
    have h := mul_le_mul_of_nonneg_right hRlow hlog2.le
    dsimp only [L, l, r] at h ⊢
    convert h using 1 <;> ring
  have hdenLow : 0 < 8 * L * Real.log 2 / l := by positivity
  have hwidthFirst : l / (r * Real.log 2) ≤ l / (8 * L * Real.log 2 / l) :=
    div_le_div_of_nonneg_left hlp.le hdenLow hdenOrder
  have hquotient : l / (8 * L * Real.log 2 / l) =
      l ^ 2 / (8 * Real.log 2 * L) := by field_simp
  unfold taoLittlewoodWidth
  dsimp only [L, l, r] at hwidthFirst hlarge ⊢
  rw [hquotient] at hwidthFirst
  exact hwidthFirst.trans hlarge

theorem eventually_taoLittlewoodWidth_le_eighth :
    ∀ᶠ T : Real in atTop,
      taoLittlewoodWidth T (taoLittlewoodR T) ≤ (1 : Real) / 8 := by
  have hroot : ∀ᶠ T : Real in atTop,
      2 ≤ (Real.log T) ^ (1 / 8 : Real) := by
    have ht := (tendsto_rpow_atTop (by norm_num : (0 : Real) < 1 / 8)).comp
      Real.tendsto_log_atTop
    exact ht.eventually_ge_atTop 2
  filter_upwards [eventually_taoLittlewoodFrequencyConditions, hroot] with T hcond hrootT
  have hupper := taoLittlewoodWidth_le_log_power hcond.2.1
    (taoLittlewoodR_one hcond.1 hcond.2.1) (taoLittlewoodR_lower T) hcond.2.2.1
  have hden : 0 < 4 * (Real.log T) ^ (1 / 8 : Real) := by positivity
  have hquarter : 1 / (4 * (Real.log T) ^ (1 / 8 : Real)) ≤ (1 : Real) / 8 := by
    apply (div_le_div_iff₀ hden (by norm_num : (0 : Real) < 8)).2
    nlinarith
  exact hupper.trans hquarter

theorem eventually_log_le_quarter_rpow :
    ∀ᶠ T : Real in atTop, Real.log T ≤ T ^ (1 / 4 : Real) := by
  have htend : Tendsto (fun T : Real => Real.log T / T ^ (1 / 4 : Real))
      atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : Real) < 1 / 4)).tendsto_div_nhds_zero
  have hratio : ∀ᶠ T : Real in atTop,
      Real.log T / T ^ (1 / 4 : Real) ≤ 1 := by
    have h := (tendsto_order.1 htend).2 1 (by norm_num)
    exact h.mono fun T hT => hT.le
  filter_upwards [hratio, eventually_gt_atTop 0] with T hratioT hT
  exact (div_le_one (Real.rpow_pos_of_pos hT _)).mp hratioT

end

end Erdos1212Kernel
