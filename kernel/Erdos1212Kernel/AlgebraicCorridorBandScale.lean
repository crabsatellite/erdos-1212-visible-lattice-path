import Erdos1212Kernel.AlgebraicCorridorBandCard
import Erdos1212Kernel.AlgebraicCorridorScales

namespace Erdos1212Kernel.CorridorScale

noncomputable section

open Filter

def bandPrimeStateConstant : ℝ :=
  20000 * (Real.log 4 + 1) / Real.log 2

theorem bandPrimeStateConstant_pos : 0 < bandPrimeStateConstant := by
  unfold bandPrimeStateConstant
  positivity

/-- The paper's `k = O((log N)^3)` state-size estimate for any actual band
lying below `4N`. -/
theorem eventually_bandPrimeState_card_le :
    ∀ᶠ N : ℝ in atTop, ∀ lower : ℕ,
      1 < lower → lower + band N - 1 ≤ Nat.floor (4 * N) →
      (corridorBandPrimeFactors lower (band N)).card ≤
        Nat.ceil (bandPrimeStateConstant * ell N ^ 3) := by
  filter_upwards [eventually_large_domain] with N hdom
  intro lower hlower hupper
  have hN : 0 < N := zero_lt_one.trans hdom.1
  have hell : 1 ≤ ell N := hdom.2.1
  have hbandPos : 0 < band N := by
    unfold band
    have hpos : (0 : ℝ) < 10000 * ell N ^ 2 := by positivity
    exact Nat.ceil_pos.mpr hpos
  have hU : ∀ i ∈ Finset.range (band N),
      lower + i ≤ Nat.floor (4 * N) := by
    intro i hi
    have hiLt := Finset.mem_range.mp hi
    omega
  have hcard := corridorBandPrimeFactors_card_le_mul_logb
    (B := band N) (U := Nat.floor (4 * N)) (by omega) hU
  have hbandBound : (band N : ℝ) ≤ 20000 * ell N ^ 2 := by
    have hceil : (band N : ℝ) ≤ 10000 * ell N ^ 2 + 1 := by
      unfold band
      exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ 10000 * ell N ^ 2)).le
    have hsquare : (1 : ℝ) ≤ ell N ^ 2 := one_le_pow₀ hell
    linarith
  have hfloorPosNat : 0 < Nat.floor (4 * N) := by
    have hfour : (1 : ℝ) ≤ 4 * N := by nlinarith
    exact Nat.floor_pos.mpr hfour
  have hfloorPos : (0 : ℝ) < Nat.floor (4 * N) := by exact_mod_cast hfloorPosNat
  have hfloorLe : (Nat.floor (4 * N) : ℝ) ≤ 4 * N :=
    Nat.floor_le (by positivity)
  have hlogFloor : Real.log (Nat.floor (4 * N) : ℝ) ≤ Real.log (4 * N) :=
    Real.log_le_log hfloorPos hfloorLe
  have hlogFourN : Real.log (4 * N) = Real.log 4 + ell N := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hN.ne']
    rfl
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogbBound : Real.logb 2 (Nat.floor (4 * N) : ℝ) ≤
      ((Real.log 4 + 1) / Real.log 2) * ell N := by
    unfold Real.logb
    rw [hlogFourN] at hlogFloor
    have hnum : Real.log 4 + ell N ≤ (Real.log 4 + 1) * ell N := by
      have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      nlinarith
    have hdiv := div_le_div_of_nonneg_right (hlogFloor.trans hnum) hlogTwo.le
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv
  have hlogbNonneg : 0 ≤ Real.logb 2 (Nat.floor (4 * N) : ℝ) := by
    unfold Real.logb
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hfloorPosNat)) hlogTwo.le
  have hproduct := mul_le_mul hbandBound hlogbBound
    hlogbNonneg
    (by positivity : 0 ≤ 20000 * ell N ^ 2)
  have hreal : ((corridorBandPrimeFactors lower (band N)).card : ℝ) ≤
      bandPrimeStateConstant * ell N ^ 3 := by
    calc
      _ ≤ (band N : ℝ) * Real.logb 2 (Nat.floor (4 * N) : ℝ) := hcard
      _ ≤ (20000 * ell N ^ 2) *
          (((Real.log 4 + 1) / Real.log 2) * ell N) := hproduct
      _ = bandPrimeStateConstant * ell N ^ 3 := by
        unfold bandPrimeStateConstant
        ring
  have hceil : bandPrimeStateConstant * ell N ^ 3 ≤
      (Nat.ceil (bandPrimeStateConstant * ell N ^ 3) : ℝ) := Nat.le_ceil _
  exact_mod_cast hreal.trans hceil

end

end Erdos1212Kernel.CorridorScale
