import Erdos1212Kernel.IwaniecPaperQUniformBound
import Erdos1212Kernel.IwaniecSieveMainMargin

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 700000

theorem exists_iwaniecPaperR_cutoff_lower :
    ∃ D : Real, 0 < D ∧ ∀ level s : Real, 1 < level → 0 < s →
      2 ≤ Real.exp (Real.log level / s) →
      s / Real.log level - D * Real.exp (-Real.sqrt (Real.log level / s)) ≤
        Real.exp Real.eulerMascheroniConstant * iwaniecPaperR (Real.exp (Real.log level / s)) := by
  obtain ⟨K, hK, hR⟩ := exists_iwaniecPaperR_unit_error
  let D := Real.exp Real.eulerMascheroniConstant * K
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro level s hy hs hcut
  have hL := Real.log_pos hy
  have herr := hR (Real.exp (Real.log level / s)) hcut
  rw [Real.log_exp] at herr
  have hlower : Real.exp (-Real.eulerMascheroniConstant) / (Real.log level / s) -
      K * Real.exp (-Real.sqrt (Real.log level / s)) ≤ iwaniecPaperR (Real.exp (Real.log level / s)) := by
    have hh := (abs_le.mp herr).1
    linarith only [hh]
  have hcancel : Real.exp Real.eulerMascheroniConstant * Real.exp (-Real.eulerMascheroniConstant) = 1 := by
    rw [← Real.exp_add]
    simp
  have hnorm : Real.exp Real.eulerMascheroniConstant *
      (Real.exp (-Real.eulerMascheroniConstant) / (Real.log level / s)) = s / Real.log level := by
    calc
      _ = (Real.exp Real.eulerMascheroniConstant * Real.exp (-Real.eulerMascheroniConstant)) * s / Real.log level := by
        field_simp [hL.ne', hs.ne']
        <;> ring
      _ = _ := by rw [hcancel, one_mul]
  have hh := mul_le_mul_of_nonneg_left hlower (Real.exp_pos Real.eulerMascheroniConstant).le
  rw [mul_sub, hnorm] at hh
  simpa only [D, mul_assoc] using hh

/-- The uniform Q theorem consumed by the canonical finite weighted
tree. The successful depth tail is removed only under its exact proved
cardinality condition; the unrelated outer-history terminal charge is
not identified with that finite tail. -/
theorem exists_iwaniecCubicMain_lower_bound :
    ∃ C D : Real, 0 < C ∧ 0 < D ∧ ∀ (r y : Nat) (s : Real), 0 < r →
      1 < (y : Real) → 2 ≤ s → s ≤ iwaniecPaperXi (y : Real) →
      2 ≤ Real.exp (Real.log (y : Real) / s) →
      (iwaniecStrictPrimePool (Real.exp (Real.log (y : Real) / s))).card < 2 * r →
      (s - iwaniecEvenSieveSeries s) / Real.log (y : Real) -
        D * Real.exp (-Real.sqrt (Real.log (y : Real) / s)) -
        C * iwaniecAuxWeightPower y s * iwaniecAuxG 2 s / Real.log (y : Real) ^ 2 <
      Real.exp Real.eulerMascheroniConstant *
        iwaniecCubicWeightedMainExpansion r y (iwaniecStrictPrimePool (Real.exp (Real.log (y : Real) / s))) := by
  obtain ⟨C, hC, hQ⟩ := exists_iwaniecTheorem4_constant
  obtain ⟨D, hD, hR⟩ := exists_iwaniecPaperR_cutoff_lower
  refine ⟨C, D, hC, hD, ?_⟩
  intro r y s hr hy hs hsξ hcut hcard
  have he : Even (2 * r) := ⟨r, by omega⟩
  have hsdom : iwaniecAuxGStart (2 * r) ≤ s := by simpa only [iwaniecAuxGStart, if_pos he] using hs
  have hq := hQ (2 * r) (by omega) y s hy hsdom hsξ
  have hrank : ((2 * r : Nat) : Real) / (((2 * r : Nat) : Real) + 1) ≤ 1 :=
    (div_le_one₀ (by positivity)).mpr (by linarith)
  have hW := (iwaniecAuxWeightPower_pos (y : Real) (by linarith : 1 ≤ s)).le
  have hG := (iwaniecAuxG_pos 2 hs).le
  have hGsame : iwaniecAuxG (2 * r) s = iwaniecAuxG 2 s := by
    simp only [iwaniecAuxG, he, even_two, if_true]
  have hprofile : iwaniecParitySieveProfile (2 * r) s = iwaniecEvenSieveSeries s := by
    simp only [iwaniecParitySieveProfile, he, if_true]
  rw [hGsame, hprofile] at hq
  have herror := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrank hC.le) hW) hG) (sq_nonneg (Real.log (y : Real)))
  simp only [mul_one] at herror
  have hq' := hq.trans_le (add_le_add le_rfl herror)
  have hr' := hR y s hy (by linarith) hcut
  rw [iwaniecCubicWeightedMainExpansion_paperQ_no_tail hr s hcard, mul_sub, sub_div]
  linarith only [hq', hr']

/-- The actual finite tree at the moving 2+delta sieve limit. Its
depth is chosen explicitly to discharge the successful-tail condition.
The remaining error terms must fit in this quantitative positive gap. -/
theorem exists_iwaniecCubicMain_moving_margin :
    ∃ C D : Real, 0 < C ∧ 0 < D ∧ ∀ (y : Nat) (δ : Real),
      1 < (y : Real) → 0 ≤ δ → δ ≤ 1 → 2 + δ ≤ iwaniecPaperXi (y : Real) →
      2 ≤ Real.exp (Real.log (y : Real) / (2 + δ)) →
      (2 + δ) * δ / (3 * Real.log (y : Real)) -
        D * Real.exp (-Real.sqrt (Real.log (y : Real) / (2 + δ))) -
        C * iwaniecAuxWeightPower y (2 + δ) * iwaniecAuxG 2 (2 + δ) / Real.log (y : Real) ^ 2 <
      Real.exp Real.eulerMascheroniConstant *
        iwaniecCubicWeightedMainExpansion
          ((iwaniecStrictPrimePool (Real.exp (Real.log (y : Real) / (2 + δ)))).card + 1) y
          (iwaniecStrictPrimePool (Real.exp (Real.log (y : Real) / (2 + δ)))) := by
  obtain ⟨C, D, hC, hD, hmain⟩ := exists_iwaniecCubicMain_lower_bound
  refine ⟨C, D, hC, hD, ?_⟩
  intro y δ hy hδ hδ1 hsξ hcut
  have hL := Real.log_pos hy
  have hs : 0 < 2 + δ := by linarith
  have hmargin := mul_le_mul_of_nonneg_left (iwaniecNormalizedLowerMain_two_add_margin hδ hδ1)
    (div_nonneg hs.le hL.le)
  have hmargin' : (2 + δ) * δ / (3 * Real.log (y : Real)) ≤
      ((2 + δ) - iwaniecEvenSieveSeries (2 + δ)) / Real.log (y : Real) := by
    dsimp only [iwaniecNormalizedLowerMain] at hmargin
    convert hmargin using 1 <;> field_simp [hL.ne', hs.ne'] <;> ring
  have hh := hmain ((iwaniecStrictPrimePool (Real.exp (Real.log (y : Real) / (2 + δ)))).card + 1)
    y (2 + δ) (by omega) hy (by linarith) hsξ hcut (by omega)
  linarith only [hmargin', hh]

end

end Erdos1212Kernel
