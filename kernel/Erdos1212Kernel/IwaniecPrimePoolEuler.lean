import Erdos1212Kernel.VaughanIwaniecPrimePoolReduction
import Erdos1212Kernel.Analytic.BrunTitchmarsh

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1400000

theorem iwaniecListEulerProduct_descendingFactors
    (factors : Finset Nat) :
    iwaniecListEulerProduct iwaniecReciprocalFactorWeight
        (iwaniecDescendingFactors factors) =
      ∏ p ∈ factors, (1 - (p : Real)⁻¹) := by
  let weight := fun p : Nat => 1 - (p : Real)⁻¹
  have hperm := Finset.sort_perm_toList factors
    (fun left right : Nat => right ≤ left)
  unfold iwaniecListEulerProduct iwaniecReciprocalFactorWeight
  change ((iwaniecDescendingFactors factors).map weight).prod = _
  calc
    ((iwaniecDescendingFactors factors).map weight).prod =
        (factors.toList.map weight).prod :=
      List.Perm.prod_eq (hperm.map weight)
    _ = ∏ p ∈ factors, weight p := Finset.prod_map_toList factors weight
    _ = _ := rfl

theorem vaughanPrimePool_euler_eq_mertensProd (cutoff : Nat) :
    iwaniecListEulerProduct iwaniecReciprocalFactorWeight
        (iwaniecDescendingFactors (vaughanPrimePool cutoff)) =
      Erdos696.Mertens.mertensProd cutoff := by
  rw [iwaniecListEulerProduct_descendingFactors]
  simp [vaughanPrimePool, Nat.primesLE_eq_filter_range,
    Erdos696.Mertens.mertensProd, one_div]

theorem vaughanPrimePool_reciprocalSum_eq_mertens
    (cutoff : Nat) :
    (∑ p ∈ vaughanPrimePool cutoff, (p : Real)⁻¹) =
      Erdos696.Mertens.primeReciprocalSum cutoff := by
  simp [vaughanPrimePool, Nat.primesLE_eq_filter_range,
    Erdos696.Mertens.primeReciprocalSum, one_div]

theorem vaughanPrimePool_euler_log_tendsto :
    Filter.Tendsto
      (fun cutoff : Nat =>
        iwaniecListEulerProduct iwaniecReciprocalFactorWeight
          (iwaniecDescendingFactors (vaughanPrimePool cutoff)) *
            Real.log cutoff)
      Filter.atTop
      (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
  simpa only [vaughanPrimePool_euler_eq_mertensProd] using
    Erdos696.Mertens.mertens_equation_15

theorem vaughanPrimePool_reciprocalSum_sub_loglog_tendsto :
    Filter.Tendsto
      (fun cutoff : Nat =>
        (∑ p ∈ vaughanPrimePool cutoff, (p : Real)⁻¹) -
          Real.log (Real.log cutoff))
      Filter.atTop
      (nhds Erdos696.Mertens.meisselMertensConstant) := by
  simpa only [vaughanPrimePool_reciprocalSum_eq_mertens] using
    Erdos696.Mertens.mertens_second_theorem

end

end Erdos1212Kernel
