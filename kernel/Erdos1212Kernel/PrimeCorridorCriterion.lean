import Erdos1212Kernel.PrimeCountingScales
import Erdos1212Kernel.RelativeBaselineClosure

namespace Erdos1212Kernel

open Filter

/-!
The concrete relative-baseline criterion for the prime corridor.

The escape set at scale `N` is not an abstract mass.  It is exactly the finite
set of prime-corridor roots from which no safe path reaches arbitrarily far.
Thus, if every safe component is bounded, every corridor root belongs to this
set.  This file removes the freedom to choose a surrogate escape event at the
last analytic endpoint.
-/

noncomputable def boundedPrimeCorridorRoots (N : Nat) : Finset (Nat × Nat) := by
  classical
  exact (primeCorridorRoots N).filter fun r =>
    ¬ ArbitrarilyFarSafeReachable (primeCorridorPoint r)

noncomputable def boundedPrimeCorridorRootMass (N : Nat) : NNReal :=
  (boundedPrimeCorridorRoots N).card

theorem boundedPrimeCorridorRoots_eq_of_all_bounded
    (hbounded : AllSafeComponentsBounded) (N : Nat) :
    boundedPrimeCorridorRoots N = primeCorridorRoots N := by
  classical
  apply Finset.filter_eq_self.mpr
  intro r _hr
  exact hbounded (primeCorridorPoint r)

noncomputable def primeCorridorEscapeCriterion :
    RelativeContourEscapeCriterion where
  baselineMass := primeCorridorBaselineScale
  escapeMass := boundedPrimeCorridorRootMass
  baselinePositive := primeCorridorBaselineScale_eventually_pos
  boundedComponentsForceEscape := by
    intro hbounded N
    rw [boundedPrimeCorridorRootMass, primeCorridorBaselineScale,
      boundedPrimeCorridorRoots_eq_of_all_bounded hbounded N]

@[simp] theorem primeCorridorEscapeCriterion_baselineMass (N : Nat) :
    primeCorridorEscapeCriterion.baselineMass N =
      primeCorridorBaselineScale N := rfl

@[simp] theorem primeCorridorEscapeCriterion_escapeMass (N : Nat) :
    primeCorridorEscapeCriterion.escapeMass N =
      boundedPrimeCorridorRootMass N := rfl

end Erdos1212Kernel
