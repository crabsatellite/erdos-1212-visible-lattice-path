import Erdos1212Kernel.NoEscapeClosure

namespace Erdos1212Kernel

open Filter Topology

/-!
An explicit sparse-baseline replacement for the Vardi-density endpoint.

The argument does not require a baseline of positive asymptotic density.
It is enough to exhibit, in each large box, a positive family of roots already
connected in the full visible lattice and to prove that the complete mass of
canonical bad separators is little-o of that family.  In the concrete route
the baseline consists of safe points below long prime columns and has order
`T^2 / log T`; retaining the root-prime condition makes the separator mass
of order at most `T^2 / log^2 T`.
-/

structure RelativeContourEscapeCriterion where
  baselineMass : Nat → NNReal
  escapeMass : Nat → NNReal
  baselinePositive :
    Filter.Eventually (fun T : Nat ↦ 0 < baselineMass T) atTop
  boundedComponentsForceEscape :
    AllSafeComponentsBounded → ∀ T, baselineMass T ≤ escapeMass T

def RelativeEscapeNegligible (criterion : RelativeContourEscapeCriterion) : Prop :=
  Tendsto
    (fun T ↦ criterion.escapeMass T / criterion.baselineMass T)
    atTop (nhds 0)

/--
If every safe component were bounded, the normalized escape mass would be at
least one on every sufficiently large box.  Relative negligibility forces it
below one, so an unbounded safe component exists and the finite-reachability
dictionary extracts the required infinite path.
-/
theorem fullClose_of_relativeContourEscape
    (criterion : RelativeContourEscapeCriterion)
    (hnegligible : RelativeEscapeNegligible criterion) :
    Erdos1212FullClose := by
  by_contra hfull
  have hbounded : AllSafeComponentsBounded := by
    intro start hreached
    exact hfull (fullClose_of_arbitrarily_far_safe_reachable start hreached)
  have hratioSmall :
      Filter.Eventually
        (fun T : Nat ↦
          criterion.escapeMass T / criterion.baselineMass T < 1)
        atTop :=
    (tendsto_order.1 hnegligible).2 1 zero_lt_one
  obtain ⟨T, hbase, hsmall⟩ :=
    (criterion.baselinePositive.and hratioSmall).exists
  have hratioLarge :
      1 ≤ criterion.escapeMass T / criterion.baselineMass T := by
    rw [le_div_iff₀ hbase]
    simpa using criterion.boundedComponentsForceEscape hbounded T
  exact (not_lt_of_ge hratioLarge) hsmall

end Erdos1212Kernel
