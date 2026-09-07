import Erdos1212Kernel.TaoPerronErrorSimplification

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

theorem taoPerron_height_log_bounds {d q : Real} (hd : 0 < d) (hq : 1 ≤ q) :
    (d + 1) * q ≤ Real.log (3 + Real.exp ((d + 1) * q)) ∧
      Real.log (3 + Real.exp ((d + 1) * q)) ≤ (d + 4) * q := by
  have hH : 1 ≤ Real.exp ((d + 1) * q) := Real.one_le_exp (by positivity)
  have hlow := Real.log_le_log (Real.exp_pos ((d + 1) * q))
    (show Real.exp ((d + 1) * q) ≤ 3 + Real.exp ((d + 1) * q) by linarith)
  rw [Real.log_exp] at hlow
  have harg : 3 + Real.exp ((d + 1) * q) ≤ 4 * Real.exp ((d + 1) * q) := by linarith
  have hu := Real.log_le_log (by positivity : 0 < 3 + Real.exp ((d + 1) * q)) harg
  rw [Real.log_mul (by norm_num : (4 : Real) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at hu
  have hlog4 : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 4)
    norm_num at h
    exact h
  exact ⟨hlow, by linarith⟩

theorem taoPerron_height_power_bounds {d q : Real} (hd : 0 < d) (hq : 1 ≤ q) :
    let H := Real.exp ((d + 1) * q)
    let L := Real.log (3 + H)
    let b := d / (d + 4)
    (Real.exp (q ^ 2)) ^ (1 - d / L) ≤ Real.exp (q ^ 2) * Real.exp (-b * q) ∧
      (Real.exp (q ^ 2)) ^ (1 + d / L) / H ≤ Real.exp (q ^ 2) * Real.exp (-b * q) := by
  let H := Real.exp ((d + 1) * q)
  let L := Real.log (3 + H)
  let b := d / (d + 4)
  change (Real.exp (q ^ 2)) ^ (1 - d / L) ≤ Real.exp (q ^ 2) * Real.exp (-b * q) ∧
    (Real.exp (q ^ 2)) ^ (1 + d / L) / H ≤ Real.exp (q ^ 2) * Real.exp (-b * q)
  obtain ⟨hlow, hupp⟩ := taoPerron_height_log_bounds hd hq
  change (d + 1) * q ≤ L at hlow
  change L ≤ (d + 4) * q at hupp
  have hqpos : 0 < q := by linarith
  have hLpos : 0 < L := (mul_pos (by linarith) hqpos).trans_le hlow
  have hLq : q ≤ L := by nlinarith
  have hb : 0 < b := div_pos hd (by linarith)
  have hb1 : b ≤ 1 := (div_le_one₀ (by linarith : 0 < d + 4)).2 (by linarith)
  have hgap : b * q ≤ d * q ^ 2 / L := by
    apply (le_div_iff₀ hLpos).2
    calc
      b * q * L ≤ b * q * ((d + 4) * q) := mul_le_mul_of_nonneg_left hupp (by positivity)
      _ = d * q ^ 2 := by dsimp [b]; field_simp
  have hright : d * q ^ 2 / L ≤ d * q := by
    apply (div_le_iff₀ hLpos).2
    simpa only [pow_two, mul_assoc] using mul_le_mul_of_nonneg_left hLq
      (show 0 ≤ d * q by positivity)
  constructor
  · rw [← Real.exp_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [show q ^ 2 * (1 - d / L) = q ^ 2 - d * q ^ 2 / L by ring]
    linarith
  · change (Real.exp (q ^ 2)) ^ (1 + d / L) / Real.exp ((d + 1) * q) ≤ _
    rw [← Real.exp_mul, ← Real.exp_sub, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [show q ^ 2 * (1 + d / L) = q ^ 2 + d * q ^ 2 / L by ring]
    nlinarith

theorem tao_sq_mul_exp_decay_le {b q : Real} (hb : 0 < b) (hq : 0 ≤ q) :
    q ^ 2 * Real.exp (-b * q) ≤ (8 / b ^ 2) * Real.exp (-(b / 2) * q) := by
  have ht := Real.pow_div_factorial_le_exp (x := b * q / 2) (by positivity) 2
  norm_num at ht
  have hqexp : q ^ 2 ≤ (8 / b ^ 2) * Real.exp (b * q / 2) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sq_pos_of_pos hb)).2
    nlinarith
  calc
    _ ≤ ((8 / b ^ 2) * Real.exp (b * q / 2)) * Real.exp (-b * q) :=
      mul_le_mul_of_nonneg_right hqexp (Real.exp_pos _).le
    _ = (8 / b ^ 2) * Real.exp (-(b / 2) * q) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

end

end Erdos1212Kernel
