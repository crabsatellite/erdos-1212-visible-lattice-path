import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators
open MeasureTheory

set_option maxHeartbeats 1600000

/-- The source average of negative powers, with its uniform constant
proved by sum-integral comparison rather than a logarithmic substitute. -/
theorem taoVdc_sum_negative_rpow (H : Nat) (hH : 0 < H) {p : Real}
    (hp : 0 ≤ p) (hp1 : p < 1) :
    (∑ h ∈ Finset.Icc 1 H, (h : Real) ^ (-p)) ≤ (H : Real) ^ (1 - p) / (1 - p) := by
  have hH1 : 1 ≤ H := hH
  have hpden : 0 < 1 - p := by linarith
  have htail : (∑ d ∈ Finset.Ico 2 (H + 1), (d : Real) ^ (-p)) ≤
      ((H : Real) ^ (1 - p) - 1) / (1 - p) := by
    calc
      _ = ∑ d ∈ Finset.Ico 2 (H + 1), (((d + 1 : Nat) : Real) - 1) ^ (-p) := by
        simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
      _ ≤ ∫ x in (2 : Real)..(H + 1 : Nat), (x - 1) ^ (-p) := by
        apply @AntitoneOn.sum_le_integral_Ico 2 (H + 1) (fun x : Real => (x - 1) ^ (-p)) (by omega)
        intro x hx y hy hxy
        norm_num at hx hy
        exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) (by linarith) (by linarith)
      _ = ∫ x in (1 : Real)..(H : Real), x ^ (-p) := by
        simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, show (2 : Real) - 1 = 1 by norm_num] using
          (intervalIntegral.integral_comp_sub_right (a := 2) (b := (H + 1 : Nat)) (fun x : Real => x ^ (-p)) 1)
      _ = _ := by
        rw [integral_rpow (Or.inl (by linarith : -1 < -p))]
        simp only [Real.one_rpow, show -p + 1 = 1 - p by ring]
  rw [← Finset.sum_erase_add (Finset.Icc 1 H) _ (Finset.left_mem_Icc.mpr hH1), add_comm,
    Nat.cast_one, Real.one_rpow, Finset.Icc_erase_left]
  have hnum : 1 + (((H : Real) ^ (1 - p) - 1) / (1 - p)) ≤ (H : Real) ^ (1 - p) / (1 - p) := by
    calc
      _ = ((H : Real) ^ (1 - p) - p) / (1 - p) := by field_simp
        <;> ring
      _ ≤ _ := (div_le_div_iff_of_pos_right hpden).2 (by linarith)
  exact (add_le_add le_rfl htail).trans hnum

theorem taoVdc_average_negative_rpow (H : Nat) (hH : 0 < H) {p : Real}
    (hp : 0 ≤ p) (hphalf : p ≤ 1 / 2) :
    (1 / (H : Real)) * (∑ h ∈ Finset.Icc 1 H, (h : Real) ^ (-p)) ≤ 2 * (H : Real) ^ (-p) := by
  have hHp : 0 < (H : Real) := by exact_mod_cast hH
  have hp1 : p < 1 := by linarith
  have hsum := taoVdc_sum_negative_rpow H hH hp hp1
  have hcoef : 1 / (1 - p) ≤ (2 : Real) := (div_le_iff₀ (by linarith : 0 < 1 - p)).2 (by linarith)
  have he : (H : Real) ^ (1 - p) = (H : Real) * (H : Real) ^ (-p) := by
    rw [sub_eq_add_neg, Real.rpow_add hHp, Real.rpow_one]
  calc
    _ ≤ (1 / (H : Real)) * ((H : Real) ^ (1 - p) / (1 - p)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (1 / (1 - p)) * (H : Real) ^ (-p) := by rw [he]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hHp.le _)

theorem taoVdc_average_positive_rpow (H : Nat) (hH : 0 < H) {p : Real} (hp : 0 ≤ p) :
    (1 / (H : Real)) * (∑ h ∈ Finset.Icc 1 H, (h : Real) ^ p) ≤ (H : Real) ^ p := by
  have hHp : 0 < (H : Real) := by exact_mod_cast hH
  have hsum : (∑ h ∈ Finset.Icc 1 H, (h : Real) ^ p) ≤ (H : Real) * (H : Real) ^ p := by
    calc
      _ ≤ ∑ _h ∈ Finset.Icc 1 H, (H : Real) ^ p := by
        apply Finset.sum_le_sum
        intro h hh
        exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast (Finset.mem_Icc.mp hh).2) hp
      _ = _ := by simp [Nat.card_Icc, nsmul_eq_mul]
  calc
    _ ≤ (1 / (H : Real)) * ((H : Real) * (H : Real) ^ p) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp

end

end Erdos1212Kernel
