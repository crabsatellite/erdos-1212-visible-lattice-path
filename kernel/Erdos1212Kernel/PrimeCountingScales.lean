import Mathlib.Analysis.Complex.ExponentialBounds
import Erdos1212Kernel.PrimeCorridorBaseline

namespace Erdos1212Kernel

open Filter Topology
open scoped Nat.Prime

theorem primeCounting_div_self_tendsto_zero :
    Tendsto
      (fun N : Nat ↦ (Nat.primeCounting N : Real) / (N : Real))
      atTop (nhds 0) := by
  have hchebReal :=
    Chebyshev.eventually_primeCounting_le (ε := (1 : Real)) (by norm_num)
  have hchebNat :
      ∀ᶠ N : Nat in atTop,
        (Nat.primeCounting N : Real) ≤
          (Real.log 4 + 1) * (N : Real) / Real.log (N : Real) := by
    have hcomp := (tendsto_natCast_atTop_atTop.eventually hchebReal)
    simpa using hcomp
  have hlog :
      Tendsto (fun N : Nat ↦ Real.log (N : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmajorant :
      Tendsto (fun N : Nat ↦ (Real.log 4 + 1) / Real.log (N : Real))
        atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hlog
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (show Tendsto (fun _ : Nat ↦ (0 : Real)) atTop (nhds 0) from
        tendsto_const_nhds)
      hmajorant
  · exact Filter.Eventually.of_forall fun _ ↦ by positivity
  · filter_upwards [hchebNat, eventually_gt_atTop (0 : Nat)] with N hpi hN
    have hNReal : 0 < (N : Real) := by positivity
    have hlogNonneg : 0 ≤ Real.log (N : Real) :=
      Real.log_nonneg (by exact_mod_cast hN)
    calc
      (Nat.primeCounting N : Real) / (N : Real)
          ≤ ((Real.log 4 + 1) * (N : Real) / Real.log (N : Real)) /
              (N : Real) := by gcongr
      _ = (Real.log 4 + 1) / Real.log (N : Real) := by field_simp

theorem corridorPrimes_eventually_lower :
    ∀ᶠ N : Nat in atTop,
      (N : Real) / (10 * Real.log (N : Real)) ≤
        ((corridorPrimes N).card : Real) := by
  have hchebUpperReal :=
    Chebyshev.eventually_primeCounting_le
      (ε := (1 / 100 : Real)) (by norm_num)
  have hchebUpperNat :
      ∀ᶠ N : Nat in atTop,
        (Nat.primeCounting N : Real) ≤
          (Real.log 4 + 1 / 100) * (N : Real) / Real.log (N : Real) := by
    have hcomp := (tendsto_natCast_atTop_atTop.eventually hchebUpperReal)
    simpa using hcomp
  filter_upwards [hchebUpperNat, eventually_ge_atTop 2000] with N hupper hN
  have hNpos : 0 < (N : Real) := by positivity
  have hNReal : (2000 : Real) ≤ (N : Real) := by exact_mod_cast hN
  have hNone : 1 < (N : Real) := by exact_mod_cast (show 1 < N by omega)
  have hlogNpos : 0 < Real.log (N : Real) := Real.log_pos hNone
  have hsqrtNonneg : 0 ≤ Real.sqrt (4 * (N : Real) + 1) := Real.sqrt_nonneg _
  have hsqrtSq :
      (Real.sqrt (4 * (N : Real) + 1)) ^ 2 = 4 * (N : Real) + 1 := by
    rw [Real.sq_sqrt]
    positivity
  have hsqrtBound :
      Real.sqrt (4 * (N : Real) + 1) ≤ (N : Real) / 20 := by
    nlinarith
  have hlogError :
      Real.log (4 * (N : Real) + 1) ≤ (N : Real) / 10 := by
    have hsqrtPos : 0 < Real.sqrt (4 * (N : Real) + 1) := by positivity
    have hlogSqrt := Real.log_le_sub_one_of_pos hsqrtPos
    have hlogEq := Real.log_sqrt (show 0 ≤ 4 * (N : Real) + 1 by positivity)
    nlinarith
  have hlogFourN :
      Real.log (4 * (N : Real)) ≤ (3 / 2 : Real) * Real.log (N : Real) := by
    have h16N : (16 : Real) ≤ (N : Real) := by exact_mod_cast (show 16 ≤ N by omega)
    have hlog16N := Real.log_le_log (by norm_num) h16N
    have hlog16 : Real.log (16 : Real) = 2 * Real.log 4 := by
      rw [show (16 : Real) = 4 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have hlogMul :
        Real.log (4 * (N : Real)) = Real.log 4 + Real.log (N : Real) := by
      rw [Real.log_mul (by norm_num : (4 : Real) ≠ 0) (ne_of_gt hNpos)]
    rw [hlog16] at hlog16N
    rw [hlogMul]
    linarith
  have hlogFourNpos : 0 < Real.log (4 * (N : Real)) := by
    apply Real.log_pos
    nlinarith
  have hlower := Chebyshev.pi_ge (4 * N)
  have hlowerReal :
      ((4 * (N : Real)) * Real.log 2 -
          Real.log (4 * (N : Real) + 1)) /
          Real.log (4 * (N : Real)) ≤
        (Nat.primeCounting (4 * N) : Real) := by
    simpa [Nat.cast_mul, Nat.cast_add] using hlower
  have hpiFourLower :
      (8 / 5 : Real) * (N : Real) / Real.log (N : Real) ≤
        (Nat.primeCounting (4 * N) : Real) := by
    have hlogTwoLower : (69 / 100 : Real) < Real.log 2 := by
      exact (by norm_num : (69 / 100 : Real) < 0.6931471803).trans
        Real.log_two_gt_d9
    rw [div_le_iff₀ hlogFourNpos] at hlowerReal
    rw [div_le_iff₀ hlogNpos]
    nlinarith
  have hlogFourUpper : Real.log 4 < (7 / 5 : Real) := by
    rw [show (4 : Real) = 2 ^ 2 by norm_num, Real.log_pow]
    nlinarith [Real.log_two_lt_d9]
  have hpiUpper :
      (Nat.primeCounting N : Real) ≤
        (3 / 2 : Real) * (N : Real) / Real.log (N : Real) := by
    calc
      (Nat.primeCounting N : Real)
          ≤ (Real.log 4 + 1 / 100) * (N : Real) /
              Real.log (N : Real) := hupper
      _ ≤ (3 / 2 : Real) * (N : Real) /
              Real.log (N : Real) := by
            gcongr
            linarith
  have hcountMono :
      Nat.primeCounting N ≤ Nat.primeCounting (4 * N) :=
    Nat.monotone_primeCounting (by omega)
  rw [corridorPrimes_card]
  rw [Nat.cast_sub hcountMono]
  calc
    (N : Real) / (10 * Real.log (N : Real)) =
        (8 / 5 : Real) * (N : Real) / Real.log (N : Real) -
          (3 / 2 : Real) * (N : Real) / Real.log (N : Real) := by
            field_simp
            ring
    _ ≤ (Nat.primeCounting (4 * N) : Real) -
          (Nat.primeCounting N : Real) := sub_le_sub hpiFourLower hpiUpper

theorem primeCorridorRoots_eventually_lower :
    ∀ᶠ N : Nat in atTop,
      (N : Real) ^ 2 / (40 * Real.log (N : Real)) ≤
        ((primeCorridorRoots N).card : Real) := by
  filter_upwards [corridorPrimes_eventually_lower, eventually_ge_atTop 2000]
      with N hprime hN
  have hNpos : 0 < (N : Real) := by positivity
  have hNReal : (2000 : Real) ≤ (N : Real) := by exact_mod_cast hN
  have hlogNpos : 0 < Real.log (N : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hheight :
      (N : Real) / 3 ≤ ((corridorHeights N).card : Real) := by
    rw [corridorHeights_card]
    have hdivOne : 1 ≤ N / 2 := by omega
    rw [Nat.cast_sub hdivOne]
    push_cast
    have hmod : N % 2 < 2 := Nat.mod_lt N (by omega)
    have hdecomp : N % 2 + 2 * (N / 2) = N := Nat.mod_add_div N 2
    have hmodReal : ((N % 2 : Nat) : Real) < 2 := by exact_mod_cast hmod
    have hdecompReal :
        ((N % 2 : Nat) : Real) + 2 * ((N / 2 : Nat) : Real) = (N : Real) := by
      exact_mod_cast hdecomp
    nlinarith
  rw [show (primeCorridorRoots N).card =
      (corridorPrimes N).card * (corridorHeights N).card by
        simp [primeCorridorRoots]]
  push_cast
  calc
    (N : Real) ^ 2 / (40 * Real.log (N : Real)) ≤
        ((N : Real) / (10 * Real.log (N : Real))) * ((N : Real) / 3) := by
          field_simp [ne_of_gt hlogNpos]
          nlinarith [sq_nonneg (N : Real)]
    _ ≤ ((corridorPrimes N).card : Real) *
          ((corridorHeights N).card : Real) := by
          exact mul_le_mul hprime hheight (by positivity) (by positivity)

theorem primeCounting_four_eventually_upper :
    ∀ᶠ N : Nat in atTop,
      (Nat.primeCounting (4 * N) : Real) ≤
        12 * (N : Real) / Real.log (N : Real) := by
  have hchebReal :=
    Chebyshev.eventually_primeCounting_le (ε := (1 : Real)) (by norm_num)
  have hchebNat :
      ∀ᶠ n : Nat in atTop,
        (Nat.primeCounting n : Real) ≤
          (Real.log 4 + 1) * (n : Real) / Real.log (n : Real) := by
    have hcomp := (tendsto_natCast_atTop_atTop.eventually hchebReal)
    simpa using hcomp
  have hfour : Tendsto (fun N : Nat ↦ 4 * N) atTop atTop := by
    simpa [nsmul_eq_mul, mul_comm] using
      (tendsto_id.atTop_nsmul_const (r := (4 : Nat)) (by omega))
  have hchebFour := hfour.eventually hchebNat
  filter_upwards [hchebFour, eventually_ge_atTop 2] with N hupper hN
  have hNone : 1 < (N : Real) := by exact_mod_cast hN
  have hlogNpos : 0 < Real.log (N : Real) := Real.log_pos hNone
  have hlogMono : Real.log (N : Real) ≤ Real.log (4 * (N : Real)) := by
    apply Real.log_le_log (by positivity)
    nlinarith
  have hlogFourUpper : Real.log 4 < (7 / 5 : Real) := by
    rw [show (4 : Real) = 2 ^ 2 by norm_num, Real.log_pow]
    nlinarith [Real.log_two_lt_d9]
  calc
    (Nat.primeCounting (4 * N) : Real)
        ≤ (Real.log 4 + 1) * (4 * (N : Real)) /
            Real.log (4 * (N : Real)) := by
          simpa [Nat.cast_mul] using hupper
    _ ≤ (Real.log 4 + 1) * (4 * (N : Real)) /
            Real.log (N : Real) := by
          exact div_le_div_of_nonneg_left (by positivity) hlogNpos hlogMono
    _ ≤ 12 * (N : Real) / Real.log (N : Real) := by
          field_simp [ne_of_gt hlogNpos]
          nlinarith

theorem primePair_over_corridor_tendsto_zero_real :
    Tendsto
      (fun N : Nat ↦
        (Nat.primeCounting (4 * N) : Real) ^ 2 /
          ((primeCorridorRoots N).card : Real))
      atTop (nhds 0) := by
  have hlog :
      Tendsto (fun N : Nat ↦ Real.log (N : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmajorant :
      Tendsto (fun N : Nat ↦ (5760 : Real) / Real.log (N : Real))
        atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hlog
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (show Tendsto (fun _ : Nat ↦ (0 : Real)) atTop (nhds 0) from
        tendsto_const_nhds)
      hmajorant
  · exact Filter.Eventually.of_forall fun _ ↦ by positivity
  · filter_upwards [primeCorridorRoots_eventually_lower,
        primeCounting_four_eventually_upper, eventually_ge_atTop 2000]
      with N hbase hpi hN
    have hNpos : 0 < (N : Real) := by positivity
    have hlogNpos : 0 < Real.log (N : Real) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hbaseLowerPos :
        0 < (N : Real) ^ 2 / (40 * Real.log (N : Real)) := by positivity
    have hbasePos : 0 < ((primeCorridorRoots N).card : Real) :=
      hbaseLowerPos.trans_le hbase
    have hpiNonneg : 0 ≤ (Nat.primeCounting (4 * N) : Real) := by positivity
    have hpiMajorantNonneg :
        0 ≤ 12 * (N : Real) / Real.log (N : Real) := by positivity
    have hpiSq :
        (Nat.primeCounting (4 * N) : Real) ^ 2 ≤
          (12 * (N : Real) / Real.log (N : Real)) ^ 2 := by
      nlinarith
    calc
      (Nat.primeCounting (4 * N) : Real) ^ 2 /
            ((primeCorridorRoots N).card : Real)
          ≤ (12 * (N : Real) / Real.log (N : Real)) ^ 2 /
              ((primeCorridorRoots N).card : Real) := by
                gcongr
      _ ≤ (12 * (N : Real) / Real.log (N : Real)) ^ 2 /
              ((N : Real) ^ 2 / (40 * Real.log (N : Real))) := by
                gcongr
      _ = (5760 : Real) / Real.log (N : Real) := by
            field_simp [ne_of_gt hNpos, ne_of_gt hlogNpos]
            ring

def primeCorridorBaselineScale (N : Nat) : NNReal :=
  (primeCorridorRoots N).card

def primeCorridorTwoPrimeScale (N : Nat) : NNReal :=
  (Nat.primeCounting (4 * N)) ^ 2

theorem primeCorridorBaselineScale_eventually_pos :
    ∀ᶠ N : Nat in atTop, 0 < primeCorridorBaselineScale N := by
  filter_upwards [primeCorridorRoots_eventually_lower,
      eventually_ge_atTop 2000] with N hlower hN
  have hNpos : 0 < (N : Real) := by positivity
  have hlogNpos : 0 < Real.log (N : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlowerPos :
      0 < (N : Real) ^ 2 / (40 * Real.log (N : Real)) := by positivity
  have hcardReal : 0 < ((primeCorridorRoots N).card : Real) :=
    hlowerPos.trans_le hlower
  simpa [primeCorridorBaselineScale] using hcardReal

theorem primePair_over_corridor_tendsto_zero :
    Tendsto
      (fun N : Nat ↦
        primeCorridorTwoPrimeScale N / primeCorridorBaselineScale N)
      atTop (nhds 0) := by
  apply NNReal.tendsto_coe.mp
  simpa [primeCorridorTwoPrimeScale, primeCorridorBaselineScale]
    using primePair_over_corridor_tendsto_zero_real

end Erdos1212Kernel
