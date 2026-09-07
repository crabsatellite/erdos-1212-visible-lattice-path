import Erdos1212Kernel.TaoPerronArbitraryParameter
import Erdos1212Kernel.TaoPerronHeightChoice

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

theorem taoPerron_unit_height_power_bounds {q : Real} (hq : 1 ≤ q) :
    let H := Real.exp (32 * q)
    let L := Real.log (3 + H)
    (Real.exp (q ^ 2)) ^ (1 - 512 / L) ≤ Real.exp (q ^ 2) * Real.exp (-8 * q) ∧
    (Real.exp (q ^ 2)) ^ (1 + 512 / L) / H ≤ Real.exp (q ^ 2) * Real.exp (-8 * q) := by
  let H := Real.exp (32 * q)
  let L := Real.log (3 + H)
  change (Real.exp (q ^ 2)) ^ (1 - 512 / L) ≤ Real.exp (q ^ 2) * Real.exp (-8 * q) ∧
    (Real.exp (q ^ 2)) ^ (1 + 512 / L) / H ≤ Real.exp (q ^ 2) * Real.exp (-8 * q)
  have hlogs := taoPerron_height_log_bounds (d := 31) (by norm_num) hq
  norm_num only [show (31 : Real) + 1 = 32 by norm_num, show (31 : Real) + 4 = 35 by norm_num] at hlogs
  have hlow : 32 * q ≤ L := hlogs.1
  have hhigh : L ≤ 35 * q := hlogs.2
  have hqpos : 0 < q := by linarith only [hq]
  have hLpos : 0 < L := by linarith only [hlow, hq]
  have hleft : 8 * q ≤ 512 * q ^ 2 / L := by
    apply (le_div_iff₀ hLpos).mpr
    have hm := mul_le_mul_of_nonneg_left hhigh (show 0 ≤ 8 * q by positivity)
    nlinarith only [hm, sq_nonneg q]
  have hright : 512 * q ^ 2 / L ≤ 16 * q := by
    apply (div_le_iff₀ hLpos).mpr
    have hm := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 16 * q by positivity)
    nlinarith only [hm]
  constructor
  · rw [← Real.exp_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [show q ^ 2 * (1 - 512 / L) = q ^ 2 - 512 * q ^ 2 / L by ring]
    linarith only [hleft]
  · change (Real.exp (q ^ 2)) ^ (1 + 512 / L) / Real.exp (32 * q) ≤ _
    rw [← Real.exp_mul, ← Real.exp_sub, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [show q ^ 2 * (1 + 512 / L) = q ^ 2 + 512 * q ^ 2 / L by ring]
    linarith only [hright, hqpos]

theorem exists_taoVonMangoldtRieszSum_four_exp_sq_error :
    ∃ A Q₀ : Real, 0 < A ∧ 1 ≤ Q₀ ∧ ∀ q : Real, Q₀ ≤ q →
      ‖taoVonMangoldtRieszSum (Real.exp (q ^ 2)) - (Real.exp (q ^ 2) : Complex) / 2‖ ≤
        A * Real.exp (q ^ 2) * Real.exp (-4 * q) := by
  obtain ⟨D, H₀, hD, hH₀, herr⟩ :=
    exists_taoVonMangoldtRieszSum_two_term_error_any_parameter 512 (by norm_num)
  let A := (1225 / 4 : Real) * D
  let Q₀ := max 1 (Real.log H₀)
  refine ⟨A, Q₀, by positivity, le_max_left _ _, ?_⟩
  intro q hq
  have hq1 : 1 ≤ q := (le_max_left _ _).trans hq
  have hq0 : 0 ≤ q := by linarith only [hq1]
  let H := Real.exp (32 * q)
  let L := Real.log (3 + H)
  have hH : H₀ ≤ H := by
    have hh : Real.log H₀ ≤ 32 * q := by linarith [(le_max_right 1 (Real.log H₀)).trans hq]
    simpa only [Real.exp_log (show 0 < H₀ by linarith)] using Real.exp_le_exp.mpr hh
  have hraw := herr H (Real.exp (q ^ 2)) hH (Real.one_le_exp (sq_nonneg q))
  have hlogs := taoPerron_height_log_bounds (d := 31) (by norm_num) hq1
  norm_num only [show (31 : Real) + 1 = 32 by norm_num, show (31 : Real) + 4 = 35 by norm_num] at hlogs
  have hL0 : 0 ≤ L := by linarith only [hlogs.1, hq1]
  have hLs : L ^ 2 ≤ 1225 * q ^ 2 := by
    have hh := mul_self_le_mul_self hL0 hlogs.2
    nlinarith only [hh]
  obtain ⟨hp1, hp2⟩ := taoPerron_unit_height_power_bounds hq1
  have hsum : (Real.exp (q ^ 2)) ^ (1 - 512 / L) + (Real.exp (q ^ 2)) ^ (1 + 512 / L) / H ≤
      2 * Real.exp (q ^ 2) * Real.exp (-8 * q) := by
    have hh := add_le_add hp1 hp2
    simpa only [two_mul, add_mul] using hh
  have habsorb := tao_sq_mul_exp_decay_le (b := 8) (by norm_num) hq0
  norm_num only [show (8 : Real) ^ 2 = 64 by norm_num, show (8 : Real) / 64 = 1 / 8 by norm_num,
    show (8 : Real) / 2 = 4 by norm_num] at habsorb
  calc
    _ ≤ D * L ^ 2 * ((Real.exp (q ^ 2)) ^ (1 - 512 / L) +
        (Real.exp (q ^ 2)) ^ (1 + 512 / L) / H) := hraw
    _ ≤ D * (1225 * q ^ 2) * (2 * Real.exp (q ^ 2) * Real.exp (-8 * q)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hLs hD.le) hsum (by positivity) (by positivity)
    _ = (2450 * D) * Real.exp (q ^ 2) * (q ^ 2 * Real.exp (-8 * q)) := by ring
    _ ≤ (2450 * D) * Real.exp (q ^ 2) * ((1 / 8) * Real.exp (-4 * q)) :=
      mul_le_mul_of_nonneg_left habsorb (by positivity)
    _ = _ := by dsimp [A]; ring

end

end Erdos1212Kernel
