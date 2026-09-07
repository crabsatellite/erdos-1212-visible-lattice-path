import Erdos1212Kernel.IwaniecInductionFixedWeight

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 650000

theorem eventually_iwaniec_source_four_six {C : Real} (hC : 0 ≤ C) :
    ∀ᶠ level : Real in atTop, 1 < Real.log level ∧
      (1 - Real.log (Real.log level) ^ 2 / (4 * Real.log level ^ 2)) *
        (1 + 4 * C / Real.log level ^ 2) * iwaniecAuxWeightPower level iwaniecAuxSZero < 1 := by
  let K := 10 * iwaniecAuxSZero ^ 3 * Real.log iwaniecAuxSZero ^ 5
  let D := 4 * C + K + (4 * C) * K
  have hs0 : 1 ≤ iwaniecAuxSZero := by linarith [iwaniecAuxSZero_large]
  have hK : 0 ≤ K := by have hh := Real.log_nonneg hs0; dsimp [K]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  filter_upwards [eventually_iwaniecWeightPower_fixed_linear_bound hs0,
    Real.tendsto_log_atTop.eventually_gt_atTop 1,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (2 * (D + 1))]
    with level hweight hL hlarge
  let L := Real.log level
  let q := 1 / L ^ 2
  let v := Real.log L ^ 2 / 4
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hq : 0 < q := one_div_pos.mpr (sq_pos_of_pos hLpos)
  have hLsq : 1 ≤ L ^ 2 := one_le_pow₀ hL.le
  have hq1 : q ≤ 1 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hLsq
    simpa only [one_div_one] using hh
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL.le
  have hlogle : Real.log L ≤ L := by have hh := Real.log_le_sub_one_of_pos hLpos; linarith
  have hlogsq : Real.log L ^ 2 ≤ L ^ 2 := by nlinarith only [hlog0, hlogle]
  have hvq : v * q ≤ 1 := by
    have hh : Real.log L ^ 2 / (4 * L ^ 2) ≤ 1 :=
      (div_le_one₀ (by positivity : 0 < 4 * L ^ 2)).mpr (by nlinarith only [hlogsq, sq_nonneg L])
    convert hh using 1 <;> dsimp [v, q] <;> ring
  have hDlarge : D < v := by
    have hsquare := pow_le_pow_left₀ (show 0 ≤ 2 * (D + 1) by positivity) hlarge 2
    change D < Real.log L ^ 2 / 4
    change (2 * (D + 1)) ^ 2 ≤ Real.log L ^ 2 at hsquare
    nlinarith only [hsquare, hD, sq_nonneg D]
  have hscalar := iwaniec_induction_slack_scalar hq hq1 (show 0 ≤ 4 * C by positivity) hK hvq hDlarge
  have hW : iwaniecAuxWeightPower level iwaniecAuxSZero ≤ 1 + K * q := by
    have hh := hweight.2
    convert hh using 1 <;> dsimp [K, q, L] <;> ring
  have hm := mul_le_mul_of_nonneg_left hW
    (mul_nonneg (show 0 ≤ 1 - v * q by linarith) (show 0 ≤ 1 + 4 * C * q by positivity))
  refine ⟨hL, ?_⟩
  have hh := hm.trans_lt hscalar
  convert hh using 1 <;> dsimp [v, q, L] <;> ring

theorem iwaniecRankRatio_step_identity (n : Nat) :
    (n : Real) / ((n : Real) + 1) =
      (((n : Real) + 1) / ((n : Real) + 2)) * (1 - 1 / ((n : Real) + 1) ^ 2) := by
  field_simp
  <;> ring

theorem iwaniecRankRange_inverse_square {L : Real} (hL : 1 < L) (n : Nat)
    (hn : (n : Real) + 1 ≤ 2 * L / Real.log L) :
    Real.log L ^ 2 / (4 * L ^ 2) ≤ 1 / ((n : Real) + 1) ^ 2 := by
  have hlog := Real.log_pos hL
  have hprod := (le_div_iff₀ hlog).mp hn
  have hsq := pow_le_pow_left₀ (show 0 ≤ ((n : Real) + 1) * Real.log L by positivity) hprod 2
  apply (div_le_div_iff₀ (show 0 < 4 * L ^ 2 by positivity) (show 0 < ((n : Real) + 1) ^ 2 by positivity)).mpr
  nlinarith only [hsq]

theorem eventually_iwaniec_rank_step_absorption {C : Real} (hC : 0 ≤ C) :
    ∀ᶠ level : Real in atTop, ∀ n : Nat,
      (n : Real) + 1 ≤ 2 * Real.log level / Real.log (Real.log level) →
      ((n : Real) / ((n : Real) + 1)) * (1 + 4 * C / Real.log level ^ 2) *
        iwaniecAuxWeightPower level iwaniecAuxSZero < ((n : Real) + 1) / ((n : Real) + 2) := by
  filter_upwards [eventually_iwaniec_source_four_six hC] with level hlevel
  intro n hn
  have hsmall := iwaniecRankRange_inverse_square hlevel.1 n hn
  have hweight : 0 ≤ iwaniecAuxWeightPower level iwaniecAuxSZero :=
    (iwaniecAuxWeightPower_pos level (by linarith [iwaniecAuxSZero_large])).le
  have hsecond : 0 ≤ 1 + 4 * C / Real.log level ^ 2 := by positivity
  have hfirst := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (sub_le_sub_left hsmall 1) hsecond) hweight
  have hstep : 0 < ((n : Real) + 1) / ((n : Real) + 2) := by positivity
  have hbound := mul_le_mul_of_nonneg_left hfirst hstep.le
  have hstrict := mul_lt_mul_of_pos_left hlevel.2 hstep
  have hh := hbound.trans_lt hstrict
  rw [iwaniecRankRatio_step_identity n]
  convert hh using 1 <;> ring

end

end Erdos1212Kernel
