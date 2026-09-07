import Erdos1212Kernel.IwaniecShiftedSubsetTransport
import Erdos1212Kernel.IwaniecCubicMainExpansion

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1400000

def iwaniecCubicShiftedSubsetCoefficient
    (r y : Nat) (S : Finset Nat) : Real :=
  iwaniecCubicLowerMoebius r y (S.prod id)

def iwaniecCubicShiftedMain
    (r y : Nat) (reference : Finset Nat)
    (actualDenominator : Nat → Nat) : Real :=
  iwaniecShiftedSubsetMain reference
    (fun p => (actualDenominator p : Real))
    (iwaniecCubicShiftedSubsetCoefficient r y)

theorem iwaniecCubicShiftedSubsetCoefficient_empty
    (r y : Nat) :
    iwaniecCubicShiftedSubsetCoefficient r y ∅ = 1 := by
  simp [iwaniecCubicShiftedSubsetCoefficient,
    iwaniecCubicLowerMoebius, iwaniecCubicLowerMoebiusInt,
    iwaniecLowerContinuationTerm, iwaniecDescendingFactors]

theorem iwaniecCubicShiftedSubsetCumulative_eq_divisorSum
    {r y : Nat} {T : Finset Nat}
    (hprime : ∀ p ∈ T, Nat.Prime p) :
    iwaniecShiftedSubsetCumulative
        (iwaniecCubicShiftedSubsetCoefficient r y) T =
      ∑ d ∈ (T.prod id).divisors,
        iwaniecCubicLowerMoebius r y d := by
  have hsquare : Squarefree (T.prod id) := by
    simpa using primeFinsetProduct_squarefree T hprime
  have hproduct : T.prod id ≠ 0 := hsquare.ne_zero
  have hfactors :
      (UniqueFactorizationMonoid.normalizedFactors
        (T.prod id)).toFinset = T := by
    simpa using product_normalizedFactors_toFinset T hprime
  unfold iwaniecShiftedSubsetCumulative
    iwaniecCubicShiftedSubsetCoefficient
  calc
    (∑ S ∈ T.powerset,
        iwaniecCubicLowerMoebius r y (S.prod id)) =
        ∑ S ∈
            (UniqueFactorizationMonoid.normalizedFactors
              (T.prod id)).toFinset.powerset,
          iwaniecCubicLowerMoebius r y S.val.prod := by
      rw [hfactors]
      apply Finset.sum_congr rfl
      intro S _hS
      rw [Finset.prod_val]
    _ = ∑ d ∈ (T.prod id).divisors with Squarefree d,
          iwaniecCubicLowerMoebius r y d :=
      (Nat.sum_divisors_filter_squarefree hproduct).symm
    _ = ∑ d ∈ (T.prod id).divisors,
          iwaniecCubicLowerMoebius r y d := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro d hd hnot
      have hdDvd := (Nat.mem_divisors.mp hd).1
      exact (hnot (Finset.mem_filter.mpr
        ⟨hd, Squarefree.squarefree_of_dvd hdDvd hsquare⟩)).elim

theorem iwaniecCubicShiftedSubsetCumulative_nonpos
    {r y : Nat} (hr : 0 < r) {U T : Finset Nat}
    (hprime : ∀ p ∈ U, Nat.Prime p)
    (hT : T ∈ U.powerset) (hTNonempty : T.Nonempty) :
    iwaniecShiftedSubsetCumulative
        (iwaniecCubicShiftedSubsetCoefficient r y) T ≤ 0 := by
  have hTSubset := Finset.mem_powerset.mp hT
  have hprimeT : ∀ p ∈ T, Nat.Prime p := by
    intro p hp
    exact hprime p (hTSubset hp)
  rw [iwaniecCubicShiftedSubsetCumulative_eq_divisorSum hprimeT]
  have hprodNeOne : T.prod id ≠ 1 := by
    intro hprod
    obtain ⟨p, hp⟩ := hTNonempty
    have hpDvd : p ∣ T.prod id := Finset.dvd_prod_of_mem id hp
    rw [hprod] at hpDvd
    exact (hprimeT p hp).not_dvd_one hpDvd
  have hlower := iwaniecCubicLowerMoebius_isLower
    r y hr (T.prod id)
  rw [if_neg hprodNeOne] at hlower
  exact hlower

/-- Cubic specialization of Iwaniec's 1978 shifted-sieve Lemma 1.  The
coefficient and every subset occurrence stay on the reference prime carrier;
only its paired divisor denominator is transported. -/
theorem iwaniecCubic_shifted_normalized_main_mono
    {r y : Nat} (hr : 0 < r) (reference : Finset Nat)
    (actualDenominator : Nat → Nat)
    (hprime : ∀ p ∈ reference, Nat.Prime p)
    (hordered : ∀ p ∈ reference, p ≤ actualDenominator p) :
    iwaniecShiftedSubsetEuler reference
          (fun p => (actualDenominator p : Real)) *
        iwaniecCubicShiftedMain r y reference id ≤
      iwaniecShiftedSubsetEuler reference (fun p => (p : Real)) *
        iwaniecCubicShiftedMain r y reference actualDenominator := by
  unfold iwaniecCubicShiftedMain
  apply iwaniec_shifted_normalized_main_mono
  · intro p hp
    exact_mod_cast (hprime p hp).one_lt
  · intro p hp
    exact_mod_cast hordered p hp
  · exact iwaniecCubicShiftedSubsetCoefficient_empty r y
  · intro T hT hTNonempty
    exact iwaniecCubicShiftedSubsetCumulative_nonpos
      hr hprime hT hTNonempty

theorem finsetNat_reciprocalProduct (S : Finset Nat) :
    (∏ p ∈ S, (p : Real)⁻¹) =
      ((S.prod (fun p : Nat => p) : Nat) : Real)⁻¹ := by
  push_cast
  exact Finset.prod_inv_distrib _

/-- The unshifted reference main is exactly the already formalized literal
cubic weighted tree expansion. -/
theorem iwaniecCubicShiftedMain_id_eq_weightedExpansion
    (r y : Nat) (reference : Finset Nat)
    (hprime : ∀ p ∈ reference, Nat.Prime p) :
    iwaniecCubicShiftedMain r y reference id =
      iwaniecCubicWeightedMainExpansion r y reference := by
  let product := ∏ p ∈ reference, p
  have hfactors :
      (UniqueFactorizationMonoid.normalizedFactors product).toFinset =
        reference := by
    simpa [product] using
      product_normalizedFactors_toFinset reference hprime
  unfold iwaniecCubicShiftedMain iwaniecShiftedSubsetMain
    iwaniecCubicShiftedSubsetCoefficient
  calc
    (∑ S ∈ reference.powerset,
        iwaniecCubicLowerMoebius r y (S.prod id) *
          ∏ p ∈ S, ((id p : Nat) : Real)⁻¹) =
      ∑ S ∈ reference.powerset,
        iwaniecWeightedContinuationTerm r
          (iwaniecCubicEvenRestriction y)
          iwaniecReciprocalFactorWeight []
          (iwaniecDescendingFactors S) := by
      apply Finset.sum_congr rfl
      intro S hS
      have hSSubset := Finset.mem_powerset.mp hS
      have hSPrime : ∀ p ∈ S, Nat.Prime p := by
        intro p hp
        exact hprime p (hSSubset hp)
      have hcoefficient := iwaniecCubicLowerMoebiusInt_subset_prod
        (n := product) (r := r) (y := y) S (by
          rw [hfactors]
          exact hS)
      rw [Finset.prod_val] at hcoefficient
      have hweighted := iwaniecWeightedContinuationTerm_reciprocal_eq
        r y [] (iwaniecDescendingFactors S) (by
          intro p hp
          have hpMem : p ∈ S := by
            simpa [iwaniecDescendingFactors] using hp
          exact (hSPrime p hpMem).ne_zero)
      unfold iwaniecCubicLowerMoebius
      rw [hcoefficient]
      simp only [id_eq]
      rw [finsetNat_reciprocalProduct]
      rw [hweighted, iwaniecDescendingFactors_prod]
    _ = ∑ ordered ∈ iwaniecOrderedFactorSublists reference,
        iwaniecWeightedContinuationTerm r
          (iwaniecCubicEvenRestriction y)
          iwaniecReciprocalFactorWeight [] ordered :=
      sum_powerset_iwaniecDescendingFactors reference _
    _ = _ :=
      sum_iwaniecOrderedFactorSublists_eq_weightedExpansion r y reference

end

end Erdos1212Kernel
