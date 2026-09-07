import Erdos1212Kernel.TaoPerronRightLine

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory Set Complex

set_option maxHeartbeats 600000

def taoPerronErrorBudget (δ C L H x : Real) : Real :=
  (taoPerronRightLineConstant (1 + δ) * x ^ (1 + δ)) * (2 / H) +
  ((1 / δ + C * L ^ 2) * x ^ (1 - δ) * (Real.pi / (1 - δ)) +
    4 * δ * (1 / H + C * L ^ 2) * x ^ (1 + δ) * (1 / H ^ 2))

theorem taoVonMangoldtRieszSum_error_of_strip
    {δ C L H x : Real} (hδ : 0 < δ) (hδ1 : δ < 1) (hC : 0 ≤ C)
    (hH : 0 < H) (hx : 1 ≤ x)
    (hstrip : ∀ t u : Real, |t| ≤ H → 1 - δ ≤ u → u ≤ 1 + δ →
      taoZetaPoleRemoved ((u : Complex) + (t : Complex) * I) ≠ 0 ∧
      ‖logDeriv taoZetaPoleRemoved ((u : Complex) + (t : Complex) * I)‖ ≤ C * L ^ 2) :
    ‖taoVonMangoldtRieszSum x - (x : Complex) / 2‖ ≤
      taoPerronErrorBudget δ C L H x / (2 * Real.pi) := by
  have hσ : 1 < 1 + δ := by linarith
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  let J : Complex := ∫ t : Real,
    taoPerronFullIntegrand x (((1 + δ : Real) : Complex) + (t : Complex) * I)
  let JH : Complex := ∫ t : Real in (-H)..H,
    taoPerronFullIntegrand x (((1 + δ : Real) : Complex) + (t : Complex) * I)
  have htail := taoPerron_right_line_tail_bound hσ hx0 hH
  have hfinite := taoPerron_truncated_right_error_of_strip hδ hδ1 hC hH hx hstrip
  have herror : ‖J - (x : Complex) * Real.pi‖ ≤ taoPerronErrorBudget δ C L H x := by
    calc
      ‖J - (x : Complex) * Real.pi‖ ≤ ‖J - JH‖ + ‖JH - (x : Complex) * Real.pi‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := add_le_add htail hfinite
  have hperron : taoVonMangoldtRieszSum x = ((1 / (2 * Real.pi) : Real) : Complex) * J := by
    simpa only [J, taoPerronFullIntegrand, taoPerronAnalyticFactor, mul_assoc] using
      taoVonMangoldtRieszSum_perron_identity hσ hx0
  have hid : taoVonMangoldtRieszSum x - (x : Complex) / 2 =
      ((1 / (2 * Real.pi) : Real) : Complex) * (J - (x : Complex) * Real.pi) := by
    rw [hperron]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    <;> ring
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  calc
    _ ≤ (1 / (2 * Real.pi)) * taoPerronErrorBudget δ C L H x :=
      mul_le_mul_of_nonneg_left herror (by positivity)
    _ = _ := by ring

theorem exists_taoVonMangoldtRieszSum_quantitative_error :
    ∃ d C H₀ : Real, 0 < d ∧ 0 < C ∧ 1 ≤ H₀ ∧
      ∀ H x : Real, H₀ ≤ H → 1 ≤ x →
        let L := Real.log (3 + H)
        let δ := d / L
        0 < δ ∧ δ < 1 ∧
          ‖taoVonMangoldtRieszSum x - (x : Complex) / 2‖ ≤
            taoPerronErrorBudget δ C L H x / (2 * Real.pi) := by
  obtain ⟨d, C, H₁, hd, hC, hstrip⟩ := exists_taoPNT_fixed_holomorphic_global_strip
  refine ⟨d, C, max H₁ 1, hd, hC, le_max_right _ _, ?_⟩
  intro H x hH hx
  let L : Real := Real.log (3 + H)
  let δ : Real := d / L
  have hH1 : H₁ ≤ H := (le_max_left H₁ 1).trans hH
  have hHone : 1 ≤ H := (le_max_right H₁ 1).trans hH
  have hHpos : 0 < H := by linarith
  have hLpos : 0 < L := Real.log_pos (by linarith)
  have hδpos : 0 < δ := div_pos hd hLpos
  have hδ1 : δ < 1 := by
    have hβ := (hstrip H 0 1 hH1 (by simpa using hHpos.le)).1
    change 0 < 1 - δ at hβ
    linarith
  refine ⟨hδpos, hδ1, ?_⟩
  apply taoVonMangoldtRieszSum_error_of_strip hδpos hδ1 hC.le hHpos hx
  intro t u ht hu0 hu1
  exact (hstrip H t u hH1 ht).2.2 hu0 hu1

end

end Erdos1212Kernel
