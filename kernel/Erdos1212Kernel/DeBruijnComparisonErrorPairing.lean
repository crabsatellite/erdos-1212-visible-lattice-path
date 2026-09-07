import Erdos1212Kernel.DeBruijnComparisonErrorLimits
import Erdos1212Kernel.DeBruijnF1AdjointNormalization
import Erdos1212Kernel.DeBruijnRhoAdjointNormalization

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1200000

def deBruijnComparisonErrorPairing (C a : Real) : Real :=
  (∫ u in (a - 1)..a, deBruijnComparisonError C u * deBruijn1951G1 u) -
    a * deBruijnComparisonError C a * deBruijn1951G1 (a - 1)

theorem deBruijnComparisonErrorG1_identity (C : Real) :
    (fun u : Real => deBruijnComparisonError C u * deBruijn1951G1 u) =
      (fun u : Real => deBruijnF1G1Integrand u - C * deBruijnRhoG1Integrand u) := by
  funext u
  unfold deBruijnComparisonError deBruijnF1G1Integrand deBruijnRhoG1Integrand
  ring

theorem deBruijnComparisonErrorG1_intervalIntegrable (C : Real) {a b : Real} (ha : -1 < a) (hb : -1 < b) :
    IntervalIntegrable (fun u : Real => deBruijnComparisonError C u * deBruijn1951G1 u) volume a b := by
  rw [deBruijnComparisonErrorG1_identity]
  exact (deBruijnF1G1Integrand_intervalIntegrable ha hb).sub ((deBruijnRhoG1Integrand_intervalIntegrable ha hb).const_mul C)

theorem deBruijnComparisonErrorPairing_linear (C : Real) {a : Real} (ha : 0 < a) :
    deBruijnComparisonErrorPairing C a = deBruijnF1G1Pairing a - C * deBruijnRhoG1Pairing a := by
  unfold deBruijnComparisonErrorPairing
  rw [deBruijnComparisonErrorG1_identity,
    intervalIntegral.integral_sub (deBruijnF1G1Integrand_intervalIntegrable (by linarith : -1 < a - 1) (by linarith : -1 < a))
      ((deBruijnRhoG1Integrand_intervalIntegrable (by linarith : -1 < a - 1) (by linarith : -1 < a)).const_mul C),
    intervalIntegral.integral_const_mul]
  unfold deBruijnComparisonError deBruijnF1G1Pairing deBruijnRhoG1Pairing deBruijnF1G1Integrand deBruijnRhoG1Integrand
  ring

theorem tendsto_deBruijnComparisonErrorPairing {C : Real} (hC : 0 < C)
    (hInv : Tendsto (fun u : Real => deBruijnRho u / deBruijnF1 u) atTop (nhds (1 / C))) :
    Tendsto (deBruijnComparisonErrorPairing C) atTop (nhds 0) := by
  have hi : ∀ᶠ a : Real in atTop,
      IntervalIntegrable (fun u : Real => deBruijnComparisonError C u * deBruijn1951G1 u) volume (a - 1) a := by
    filter_upwards [eventually_gt_atTop (0 : Real)] with a ha
    exact deBruijnComparisonErrorG1_intervalIntegrable C (by linarith : -1 < a - 1) (by linarith : -1 < a)
  have hw := deBruijn_unit_window_integral_limit (deBruijnComparisonError_product_limit hC hInv) hi
  simpa only [sub_zero] using hw.sub (deBruijnComparisonError_shifted_product_limit hC hInv)

theorem deBruijnComparisonErrorPairing_zero {C : Real} (hC : 0 < C)
    (hInv : Tendsto (fun u : Real => deBruijnRho u / deBruijnF1 u) atTop (nhds (1 / C))) {a : Real} (ha : 0 < a) :
    deBruijnComparisonErrorPairing C a = 0 := by
  have hconst : Tendsto (deBruijnComparisonErrorPairing C) atTop (nhds (deBruijnComparisonErrorPairing C a)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : Real)] with t ht
    rw [deBruijnComparisonErrorPairing_linear C ht, deBruijnComparisonErrorPairing_linear C ha,
      deBruijnF1G1Pairing_constant ht ha, deBruijnRhoG1Pairing_constant ht ha]
  exact tendsto_nhds_unique hconst (tendsto_deBruijnComparisonErrorPairing hC hInv)

theorem deBruijnComparisonConstant_eq {C : Real} (hC : 0 < C)
    (hInv : Tendsto (fun u : Real => deBruijnRho u / deBruijnF1 u) atTop (nhds (1 / C))) :
    C = Real.exp (-Real.eulerMascheroniConstant) := by
  have hzero := deBruijnComparisonErrorPairing_zero hC hInv (a := 1) (by norm_num)
  rw [deBruijnComparisonErrorPairing_linear C (by norm_num : (0 : Real) < 1),
    deBruijnF1G1Pairing_normalization (by norm_num : (0 : Real) < 1),
    deBruijnRhoG1Pairing_normalization (by norm_num : (0 : Real) < 1)] at hzero
  have hm : C * Real.exp Real.eulerMascheroniConstant = 1 := by linarith
  have hEq : C = 1 / Real.exp Real.eulerMascheroniConstant :=
    (eq_div_iff (Real.exp_pos _).ne').mpr hm
  simpa only [one_div, Real.exp_neg] using hEq

end

end Erdos1212Kernel
