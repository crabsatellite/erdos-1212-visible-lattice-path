import Erdos1212Kernel.TaoPerronRieszError

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

def taoPerronScalarConstant (d C : Real) : Real :=
  2 * (Real.log 4 + 4) * (1 + 1 / d) +
    2 * Real.pi * (1 / d + C) + 2 * (1 + C)

theorem taoPerronScalarConstant_pos {d C : Real} (hd : 0 < d) (hC : 0 ≤ C) :
    0 < taoPerronScalarConstant d C := by
  unfold taoPerronScalarConstant
  have hp : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  positivity

theorem taoPerronErrorBudget_simplified
    {d C L H x : Real} (hd : 0 < d) (hC : 0 ≤ C) (hL : 1 ≤ L)
    (hH : 1 ≤ H) (hx : 0 < x) (hhalf : d / L ≤ 1 / 2) :
    taoPerronErrorBudget (d / L) C L H x / (2 * Real.pi) ≤
      taoPerronScalarConstant d C * L ^ 2 *
        (x ^ (1 - d / L) + x ^ (1 + d / L) / H) := by
  let δ : Real := d / L
  let P : Real := Real.log 4 + 4
  let Z : Real := x ^ (1 - δ) + x ^ (1 + δ) / H
  have hLpos : 0 < L := by linarith
  have hHpos : 0 < H := by linarith
  have hδ : 0 < δ := div_pos hd hLpos
  have hP : 0 ≤ P := by dsimp [P]; linarith [Real.log_nonneg (by norm_num : (1 : Real) ≤ 4)]
  have hS1 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hLS : L ≤ L ^ 2 := by nlinarith
  have hrecip : 1 / δ = L / d := by dsimp [δ]; field_simp
  have hrecipBound : 1 / δ ≤ (1 / d) * L ^ 2 := by
    rw [hrecip]
    calc
      L / d = (1 / d) * L := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hLS (by positivity)
  have hleftCoeff : 1 / δ + C * L ^ 2 ≤ (1 / d + C) * L ^ 2 := by
    calc
      _ ≤ (1 / d) * L ^ 2 + C * L ^ 2 := add_le_add hrecipBound le_rfl
      _ = _ := by ring
  have hrightCoeff : 1 + 1 / δ ≤ (1 + 1 / d) * L ^ 2 := by
    calc
      _ ≤ L ^ 2 + (1 / d) * L ^ 2 := add_le_add hS1 hrecipBound
      _ = _ := by ring
  have hbeta : 1 / 2 ≤ 1 - δ := by dsimp [δ]; linarith
  have hpi : Real.pi / (1 - δ) ≤ 2 * Real.pi := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - δ)).2
    nlinarith [Real.pi_pos]
  have h1H : 1 / H ≤ 1 := (div_le_one₀ hHpos).2 hH
  have h1HSq : 1 / H ^ 2 ≤ 1 / H :=
    one_div_le_one_div_of_le hHpos (by nlinarith)
  have hhorizontalCoeff : 1 / H + C * L ^ 2 ≤ (1 + C) * L ^ 2 := by
    calc
      _ ≤ L ^ 2 + C * L ^ 2 := add_le_add (h1H.trans hS1) le_rfl
      _ = _ := by ring
  have hZ0 : 0 ≤ Z := by dsimp [Z]; positivity
  have hZleft : x ^ (1 - δ) ≤ Z := le_add_of_nonneg_right (by positivity)
  have hZright : x ^ (1 + δ) / H ≤ Z := le_add_of_nonneg_left (by positivity)
  have ht : (taoPerronRightLineConstant (1 + δ) * x ^ (1 + δ)) * (2 / H) ≤
      (2 * P * (1 + 1 / d)) * L ^ 2 * Z := by
    have hconst : taoPerronRightLineConstant (1 + δ) = P * (1 + 1 / δ) := by
      unfold taoPerronRightLineConstant
      simp only [add_sub_cancel_left, P]
    rw [hconst]
    calc
      _ = 2 * P * (1 + 1 / δ) * (x ^ (1 + δ) / H) := by ring
      _ ≤ 2 * P * ((1 + 1 / d) * L ^ 2) * Z := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hrightCoeff (by positivity)
        · exact hZright
        · positivity
        · positivity
      _ = _ := by ring
  have hl : (1 / δ + C * L ^ 2) * x ^ (1 - δ) * (Real.pi / (1 - δ)) ≤
      (2 * Real.pi * (1 / d + C)) * L ^ 2 * Z := by
    calc
      _ ≤ ((1 / d + C) * L ^ 2) * Z * (2 * Real.pi) := by
        apply mul_le_mul
        · exact mul_le_mul hleftCoeff hZleft (by positivity) (by positivity)
        · exact hpi
        · positivity
        · positivity
      _ = _ := by ring
  have hh : 4 * δ * (1 / H + C * L ^ 2) * x ^ (1 + δ) * (1 / H ^ 2) ≤
      (2 * (1 + C)) * L ^ 2 * Z := by
    have hδhalf : 4 * δ ≤ 2 := by dsimp [δ]; linarith
    calc
      _ ≤ 2 * ((1 + C) * L ^ 2) * x ^ (1 + δ) * (1 / H) := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx.le _)
          exact mul_le_mul hδhalf hhorizontalCoeff (by positivity) (by norm_num)
        · exact h1HSq
        · positivity
        · positivity
      _ = (2 * (1 + C)) * L ^ 2 * (x ^ (1 + δ) / H) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hZright (by positivity)
  have hb : taoPerronErrorBudget δ C L H x ≤ taoPerronScalarConstant d C * L ^ 2 * Z := by
    have hs := add_le_add ht (add_le_add hl hh)
    simpa only [taoPerronErrorBudget, taoPerronScalarConstant, P, add_mul, add_assoc] using hs
  have hbudget0 : 0 ≤ taoPerronErrorBudget δ C L H x := by
    unfold taoPerronErrorBudget
    have hδ1 : 0 < 1 - δ := by linarith
    have hpc := (taoPerronRightLineConstant_pos (show 1 < 1 + δ by linarith)).le
    positivity
  exact (div_le_self hbudget0 (by nlinarith [Real.pi_gt_three] : 1 ≤ 2 * Real.pi)).trans hb

theorem exists_taoVonMangoldtRieszSum_two_term_error :
    ∃ d D H₀ : Real, 0 < d ∧ 0 < D ∧ 1 ≤ H₀ ∧
      ∀ H x : Real, H₀ ≤ H → 1 ≤ x →
        let L := Real.log (3 + H)
        ‖taoVonMangoldtRieszSum x - (x : Complex) / 2‖ ≤
          D * L ^ 2 * (x ^ (1 - d / L) + x ^ (1 + d / L) / H) := by
  obtain ⟨d, C, H₁, hd, hC, hH₁, herr⟩ := exists_taoVonMangoldtRieszSum_quantitative_error
  let B : Real := max 1 (2 * d)
  let H₀ : Real := max H₁ (Real.exp B)
  refine ⟨d, taoPerronScalarConstant d C, H₀, hd,
    taoPerronScalarConstant_pos hd hC.le, hH₁.trans (le_max_left _ _), ?_⟩
  intro H x hH hx
  have hH1 : H₁ ≤ H := (le_max_left _ _).trans hH
  have hHone : 1 ≤ H := hH₁.trans hH1
  have hB : B ≤ Real.log (3 + H) := by
    have harg : Real.exp B ≤ 3 + H := by linarith [(le_max_right H₁ (Real.exp B)).trans hH]
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos B) harg
  have hL : 1 ≤ Real.log (3 + H) := (le_max_left 1 (2 * d)).trans hB
  have hhalf : d / Real.log (3 + H) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log (3 + H))).2
    linarith [le_max_right 1 (2 * d)]
  exact (herr H x hH1 hx).2.2.trans
    (taoPerronErrorBudget_simplified hd hC.le hL hHone (by linarith) hhalf)

end

end Erdos1212Kernel
