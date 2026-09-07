import Erdos1212Kernel.DeBruijnComplexPhaseDerivative
import Erdos1212Kernel.DeBruijnComplexPhaseTransport

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1200000

/-- The unchanged integrand in de Bruijn 1951 (2.4). -/
def deBruijnF1Integrand (u z : Complex) : Complex := Complex.exp (-u * z + deBruijnComplexExpIntegral z)

theorem deBruijnF1Integrand_continuous (u : Complex) : Continuous (deBruijnF1Integrand u) :=
  Complex.continuous_exp.comp ((continuous_const.mul continuous_id).add deBruijnComplexExpIntegral_continuous)

theorem deBruijnF1Integrand_hasDerivAt_parameter (u z : Complex) :
    HasDerivAt (fun v : Complex => deBruijnF1Integrand v z) (-z * deBruijnF1Integrand u z) u := by
  have hinner : HasDerivAt (fun v : Complex => -v * z + deBruijnComplexExpIntegral z) (-z) u := by
    simpa only [Pi.neg_apply, id_eq, neg_one_mul] using ((hasDerivAt_id u).neg.mul_const z).add_const (deBruijnComplexExpIntegral z)
  exact hinner.cexp.congr_deriv (by unfold deBruijnF1Integrand; ring)

theorem deBruijnF1Integrand_continuous_parameter (z : Complex) :
    Continuous (fun u : Complex => deBruijnF1Integrand u z) :=
  continuous_iff_continuousAt.mpr (fun u => (deBruijnF1Integrand_hasDerivAt_parameter u z).continuousAt)

theorem deBruijnF1Integrand_hasDerivAt (u z : Complex) :
    HasDerivAt (deBruijnF1Integrand u) ((-u + deBruijnComplexExpAverage z) * deBruijnF1Integrand u z) z := by
  have h := (((hasDerivAt_id z).const_mul (-u)).add (deBruijnComplexExpIntegral_hasDerivAt z)).cexp
  apply h.congr_deriv
  simp only [mul_one, id_eq, Pi.add_apply]
  unfold deBruijnF1Integrand
  ring

theorem deBruijnF1Integrand_conj (u z : Complex) :
    deBruijnF1Integrand (starRingEnd Complex u) (starRingEnd Complex z) = starRingEnd Complex (deBruijnF1Integrand u z) := by
  unfold deBruijnF1Integrand
  rw [deBruijnComplexExpIntegral_conj, ← Complex.exp_conj]
  congr 1
  simp only [map_add, map_mul, map_neg]

end

end Erdos1212Kernel
