import Erdos1212Kernel.FiniteReachability
import Erdos1212Kernel.RenewalKernel

namespace Erdos1212Kernel

open Filter Topology

def AllSafeComponentsBounded : Prop :=
  forall start : LatticePoint, ¬ ArbitrarilyFarSafeReachable start

/-!
The exact last contradiction in the contour route.  `baselineDensity` is the
positive density retained from the infinite component of the full visible
lattice.  If every component after deleting prime--prime vertices were
bounded, every one of these roots would have to contribute to the escaping
contour tail.  A tail tending to zero is incompatible with that fixed
positive lower bound.
-/
structure ContourEscapeCriterion where
  baselineDensity : NNReal
  escapeMass : Nat -> NNReal
  baselinePositive : 0 < baselineDensity
  boundedComponentsForceEscape :
    AllSafeComponentsBounded -> forall cutoff,
      baselineDensity <= escapeMass cutoff

theorem fullClose_of_contour_noEscape (criterion : ContourEscapeCriterion)
    (hnoEscape : NoEscape criterion.escapeMass) :
    Erdos1212FullClose := by
  by_contra hfull
  have hbounded : AllSafeComponentsBounded := by
    intro start hreached
    exact hfull (fullClose_of_arbitrarily_far_safe_reachable start hreached)
  have heventually : ∀ᶠ cutoff in atTop,
      criterion.escapeMass cutoff < criterion.baselineDensity :=
    (tendsto_order.1 hnoEscape).2 _ criterion.baselinePositive
  obtain ⟨cutoff, hcutoff⟩ := heventually.exists
  exact (not_lt_of_ge
    (criterion.boundedComponentsForceEscape hbounded cutoff)) hcutoff

end Erdos1212Kernel
