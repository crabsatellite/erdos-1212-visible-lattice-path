import Erdos1212Kernel.ConcreteComponentBoundary
import Erdos1212Kernel.PrimeCorridorHighBaseline
import Erdos1212Kernel.RankTailKernel

namespace Erdos1212Kernel

open Filter Topology

noncomputable section

/-!
# Exact rank stratification of the original bounded-root event

This file removes the semantic field formerly sitting between the canonical
rank coefficient and the original graph.  For an actually bounded safe
component we take its actual finite exterior vertex boundary, assign to every
boundary site the least common-prime divisor of its coordinates, discard the
permanent labels at most eleven, and count the distinct remaining labels.

The high-corridor rank mass is then the literal cardinality of original
bounded corridor roots of each exact rank, divided by the literal corridor
baseline.  Its total mass is proved equal to the original bounded-root ratio.
Consequently fixed-rank vanishing plus rank tightness now closes Erdős 1212
without a contour-domination assumption, a Vardi-density input, or a moved
prime cut.
-/

def commonPrimeLabel (p : LatticePoint) : Nat :=
  (Nat.gcd p.x p.y).minFac

theorem commonPrimeLabel_spec_of_not_visible
    {p : LatticePoint} (hnotVisible : ¬ Visible p) :
    Nat.Prime (commonPrimeLabel p) ∧
      commonPrimeLabel p ∣ p.x ∧ commonPrimeLabel p ∣ p.y := by
  have hgcdNeOne : Nat.gcd p.x p.y ≠ 1 := hnotVisible
  have hlabelDvd : commonPrimeLabel p ∣ Nat.gcd p.x p.y :=
    Nat.minFac_dvd (Nat.gcd p.x p.y)
  exact ⟨Nat.minFac_prime hgcdNeOne,
    hlabelDvd.trans (Nat.gcd_dvd_left p.x p.y),
    hlabelDvd.trans (Nat.gcd_dvd_right p.x p.y)⟩

noncomputable def exactNonpermanentBoundaryLabels
    (start : LatticePoint)
    (hbounded : ¬ ArbitrarilyFarSafeReachable start) : Finset Nat :=
  ((finiteSafeComponentFrontier start hbounded).image commonPrimeLabel).filter
    fun prime ↦ 11 < prime

noncomputable def exactBoundaryLabelRank (start : LatticePoint) : Nat := by
  classical
  exact if hbounded : ¬ ArbitrarilyFarSafeReachable start then
    (exactNonpermanentBoundaryLabels start hbounded).card
  else
    0

def boundedHighCorridorRootsOfRank (N K : Nat) : Finset (Nat × Nat) := by
  classical
  exact (boundedHighPrimeCorridorRoots N).filter fun root ↦
    exactBoundaryLabelRank (primeCorridorPoint root) = K

def highCorridorRankSupport (N : Nat) : Finset Nat :=
  (boundedHighPrimeCorridorRoots N).image fun root ↦
    exactBoundaryLabelRank (primeCorridorPoint root)

def highCorridorRawRankMass (N K : Nat) : NNReal :=
  (boundedHighCorridorRootsOfRank N K).card

def highCorridorRankMass (N K : Nat) : NNReal :=
  highCorridorRawRankMass N K / highPrimeCorridorBaselineScale N

theorem highCorridorRawRankMass_eq_zero_of_not_mem_support
    {N K : Nat} (hK : K ∉ highCorridorRankSupport N) :
    highCorridorRawRankMass N K = 0 := by
  have hempty : boundedHighCorridorRootsOfRank N K = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro root hroot
    have hfiltered := Finset.mem_filter.mp hroot
    apply hK
    rw [highCorridorRankSupport, Finset.mem_image]
    exact ⟨root, hfiltered.1, hfiltered.2⟩
  simp [highCorridorRawRankMass, hempty]

theorem highCorridorRawRankMass_summable (N : Nat) :
    Summable (highCorridorRawRankMass N) := by
  apply summable_of_hasFiniteSupport
  exact (highCorridorRankSupport N).finite_toSet.subset <| by
    intro K hK
    by_contra hnotSupport
    exact hK (highCorridorRawRankMass_eq_zero_of_not_mem_support hnotSupport)

theorem highCorridorRankMass_summable (N : Nat) :
    Summable (highCorridorRankMass N) := by
  apply summable_of_hasFiniteSupport
  exact (highCorridorRankSupport N).finite_toSet.subset <| by
    intro K hK
    by_contra hnotSupport
    apply hK
    rw [highCorridorRankMass,
      highCorridorRawRankMass_eq_zero_of_not_mem_support hnotSupport]
    simp

theorem highCorridorRawRankMass_tsum (N : Nat) :
    ∑' K, highCorridorRawRankMass N K =
      (boundedHighPrimeCorridorRoots N).card := by
  rw [tsum_eq_sum (fun K hK ↦
    highCorridorRawRankMass_eq_zero_of_not_mem_support hK)]
  change
    (∑ K ∈ highCorridorRankSupport N,
      ((boundedHighCorridorRootsOfRank N K).card : NNReal)) =
        ((boundedHighPrimeCorridorRoots N).card : NNReal)
  exact_mod_cast
    (Finset.card_eq_sum_card_image
      (fun root ↦ exactBoundaryLabelRank (primeCorridorPoint root))
      (boundedHighPrimeCorridorRoots N)).symm

theorem totalHighCorridorRankMass_eq_boundedRootRatio (N : Nat) :
    totalRankMass highCorridorRankMass N =
      boundedHighPrimeCorridorRootMass N /
        highPrimeCorridorBaselineScale N := by
  rw [totalRankMass]
  change
    (∑' K, highCorridorRawRankMass N K /
      highPrimeCorridorBaselineScale N) = _
  rw [tsum_div_const, highCorridorRawRankMass_tsum]
  rfl

/--
The direct concrete close.  Both hypotheses refer to the exact rank of the
actual finite safe component boundary above; no user-supplied criterion,
coefficient, domination map, or semantic structure remains.
-/
theorem fullClose_of_concreteHighCorridorRankEstimates
    (hfixed : ∀ K,
      Tendsto (fun N ↦ highCorridorRankMass N K) atTop (nhds 0))
    (htight : AsymptoticRankTight highCorridorRankMass) :
    Erdos1212FullClose := by
  have htotal :
      Tendsto (totalRankMass highCorridorRankMass) atTop (nhds 0) :=
    totalRankMass_tendsto_zero_of_asymptotic_rank_tight
      highCorridorRankMass highCorridorRankMass_summable hfixed htight
  have hnegligible :
      RelativeEscapeNegligible highPrimeCorridorEscapeCriterion := by
    apply htotal.congr'
    filter_upwards with N
    rw [totalHighCorridorRankMass_eq_boundedRootRatio]
    rfl
  exact fullClose_of_relativeContourEscape
    highPrimeCorridorEscapeCriterion hnegligible

end

end Erdos1212Kernel
