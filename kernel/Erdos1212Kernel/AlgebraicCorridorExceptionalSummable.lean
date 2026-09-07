import Erdos1212Kernel.AlgebraicCorridorComplexExceptionalSet
import Mathlib.Analysis.PSeries

namespace Erdos1212Kernel.CorridorScale

noncomputable section

open Filter MeasureTheory

def dyadicScale (j : ℕ) : ℝ := (2 : ℝ) ^ j

theorem ell_dyadicScale (j : ℕ) :
    ell (dyadicScale j) = (j : ℝ) * Real.log 2 := by
  unfold ell dyadicScale
  rw [Real.log_pow]

theorem eventually_dyadic_decay_le_cube :
    ∀ᶠ j : ℕ in atTop,
      Real.exp (-ell (dyadicScale j) /
          (40000 * L (dyadicScale j))) ≤
        (1 : ℝ) / (j + 1 : ℕ) ^ 3 := by
  have hlittle := isLittleO_log_rpow_rpow_atTop 2
    (show (0 : ℝ) < 1 by norm_num)
  have heps : (0 : ℝ) < 1 / 480000 := by norm_num
  have hboundReal := hlittle.bound heps
  have hshift : Tendsto (fun j : ℕ => ((j + 1 : ℕ) : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hbound := hshift.eventually hboundReal
  filter_upwards [hbound, eventually_ge_atTop (4 : ℕ)] with j hsmall hj
  have hjPos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hjOne : (1 : ℝ) < (j + 1 : ℕ) := by exact_mod_cast (show 1 < j + 1 by omega)
  have hlogJPos : 0 < Real.log ((j + 1 : ℕ) : ℝ) := Real.log_pos hjOne
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTwoHalf : (1 / 2 : ℝ) < Real.log 2 :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hlogTwoOne : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hell : ell (dyadicScale j) = (j : ℝ) * Real.log 2 := ell_dyadicScale j
  have hellPos : 0 < ell (dyadicScale j) := by rw [hell]; positivity
  have hellOne : 1 < ell (dyadicScale j) := by
    rw [hell]
    have hmul := mul_lt_mul_of_pos_left hlogTwoHalf hjPos
    have hjR : (4 : ℝ) ≤ j := by exact_mod_cast hj
    nlinarith
  have hLPos : 0 < L (dyadicScale j) := by
    unfold L
    exact Real.log_pos hellOne
  have hLUpper : L (dyadicScale j) ≤ Real.log ((j + 1 : ℕ) : ℝ) := by
    unfold L
    apply Real.log_le_log hellPos
    rw [hell]
    have hjLe : (j : ℝ) ≤ (j + 1 : ℕ) := by norm_num
    nlinarith
  rw [Real.rpow_two] at hsmall
  have hleftNorm : ‖Real.log ((j + 1 : ℕ) : ℝ) ^ 2‖ =
      Real.log ((j + 1 : ℕ) : ℝ) ^ 2 :=
    Real.norm_of_nonneg (sq_nonneg _)
  have hrightNorm : ‖(((j + 1 : ℕ) : ℝ) ^ (1 : ℝ))‖ =
      ((j + 1 : ℕ) : ℝ) := by
    rw [Real.rpow_one]
    exact Real.norm_of_nonneg (by positivity)
  rw [hleftNorm, hrightNorm] at hsmall
  have hlogSq : 240000 * Real.log ((j + 1 : ℕ) : ℝ) ^ 2 ≤ (j : ℝ) := by
    have hjShift : ((j + 1 : ℕ) : ℝ) ≤ 2 * (j : ℝ) := by
      push_cast
      nlinarith
    nlinarith
  have hellLower : 120000 * Real.log ((j + 1 : ℕ) : ℝ) ^ 2 ≤
      ell (dyadicScale j) := by
    rw [hell]
    nlinarith
  have hratio : 3 * Real.log ((j + 1 : ℕ) : ℝ) ≤
      ell (dyadicScale j) / (40000 * L (dyadicScale j)) := by
    apply (le_div_iff₀ (by positivity : 0 < 40000 * L (dyadicScale j))).mpr
    have hmul := mul_le_mul_of_nonneg_left hLUpper
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 120000) hlogJPos.le)
    nlinarith
  have hexp := Real.exp_le_exp.mpr (neg_le_neg hratio)
  calc
    Real.exp (-ell (dyadicScale j) / (40000 * L (dyadicScale j))) ≤
        Real.exp (-3 * Real.log ((j + 1 : ℕ) : ℝ)) := by
      convert hexp using 1 <;> ring
    _ = (1 : ℝ) / (j + 1 : ℕ) ^ 3 := by
      have hpow : Real.exp (3 * Real.log ((j + 1 : ℕ) : ℝ)) =
          (((j + 1 : ℕ) : ℝ) ^ 3) := by
        calc
          Real.exp (3 * Real.log ((j + 1 : ℕ) : ℝ)) =
              Real.exp (Real.log ((j + 1 : ℕ) : ℝ)) ^ 3 :=
            Real.exp_nat_mul _ 3
          _ = _ := by rw [Real.exp_log (by positivity)]
      rw [show -3 * Real.log ((j + 1 : ℕ) : ℝ) =
          -(3 * Real.log ((j + 1 : ℕ) : ℝ)) by ring,
        Real.exp_neg, hpow]
      push_cast
      ring

theorem summable_dyadic_exceptionalMajorant :
    Summable (fun j : ℕ => algebraicCorridorExceptionalMajorant
      (dyadicScale j)) := by
  have hdecay := (show Tendsto dyadicScale atTop atTop by
    unfold dyadicScale
    exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually
      eventually_algebraicCorridorExceptionalMajorant_le_exp_decay
  have hcube := eventually_dyadic_decay_le_cube
  have hmajorant : ∀ᶠ j : ℕ in atTop,
      ‖algebraicCorridorExceptionalMajorant (dyadicScale j)‖ ≤
        (1 : ℝ) / (j + 1 : ℕ) ^ 3 := by
    filter_upwards [hdecay, hcube] with j hdecay hcube
    rw [Real.norm_of_nonneg (by
      unfold algebraicCorridorExceptionalMajorant rho
      positivity)]
    exact hdecay.trans hcube
  have hpseries : Summable (fun j : ℕ => (1 : ℝ) / (j + 1 : ℕ) ^ 3) := by
    simpa [one_div] using (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3))
  exact hpseries.of_norm_bounded_eventually_nat hmajorant

theorem dyadic_exceptional_measure_tsum_ne_top :
    (∑' j : ℕ, volume (algebraicCorridorExceptionalSet (dyadicScale j))) ≠
      (⊤ : ENNReal) := by
  have hmajorantTop :
      (∑' j : ℕ, ENNReal.ofReal
        (algebraicCorridorExceptionalMajorant (dyadicScale j))) ≠
        (⊤ : ENNReal) :=
    summable_dyadic_exceptionalMajorant.tsum_ofReal_ne_top
  apply ne_top_of_le_ne_top hmajorantTop
  apply ENNReal.tsum_le_tsum
  intro j
  exact algebraicCorridorExceptionalSet_measure_le_ofReal _

theorem ae_eventually_outside_dyadic_algebraicCorridorExceptionalSet :
    ∀ᵐ α : ℝ ∂volume, ∀ᶠ j : ℕ in atTop,
      α ∉ algebraicCorridorExceptionalSet (dyadicScale j) :=
  ae_eventually_outside_exceptional_sets
    (fun j => algebraicCorridorExceptionalSet (dyadicScale j))
    dyadic_exceptional_measure_tsum_ne_top

end

end Erdos1212Kernel.CorridorScale
