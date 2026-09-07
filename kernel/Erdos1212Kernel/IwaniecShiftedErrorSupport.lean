import Erdos1212Kernel.IwaniecShiftedIntervalLowerSieve

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1400000

def iwaniecCubicShiftedErrorSupport
    (r y : Nat) (Q : Finset Nat) : Finset (Finset Nat) :=
  (iwaniecReferencePrimePool Q.card).powerset.filter fun S =>
    iwaniecCubicShiftedSubsetCoefficient r y S ≠ 0

theorem abs_iwaniecCubicLowerMoebius_eq_one_of_ne_zero
    {r y n : Nat} (hcoeff : iwaniecCubicLowerMoebius r y n ≠ 0) :
    |iwaniecCubicLowerMoebius r y n| = 1 := by
  have hcoeffInt : iwaniecCubicLowerMoebiusInt r y n ≠ 0 := by
    intro hzero
    exact hcoeff (by simp [iwaniecCubicLowerMoebius, hzero])
  have habsIntLe := abs_iwaniecCubicLowerMoebiusInt_le_one r y n
  have habsIntNe : |iwaniecCubicLowerMoebiusInt r y n| ≠ 0 := by
    exact abs_ne_zero.mpr hcoeffInt
  have habsIntNonneg :
      (0 : Int) ≤ |iwaniecCubicLowerMoebiusInt r y n| := abs_nonneg _
  have habsInt : |iwaniecCubicLowerMoebiusInt r y n| = 1 := by omega
  unfold iwaniecCubicLowerMoebius
  exact_mod_cast habsInt

theorem iwaniecCubicShiftedErrorMass_eq_supportCard
    (r y : Nat) (Q : Finset Nat) :
    iwaniecCubicShiftedErrorMass r y Q =
      (iwaniecCubicShiftedErrorSupport r y Q).card := by
  have hfilter :
      iwaniecCubicShiftedErrorMass r y Q =
        ∑ S ∈ iwaniecCubicShiftedErrorSupport r y Q,
          |iwaniecCubicShiftedSubsetCoefficient r y S| := by
    unfold iwaniecCubicShiftedErrorMass
      iwaniecCubicShiftedErrorSupport
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S hS hnot
    have hzero : iwaniecCubicShiftedSubsetCoefficient r y S = 0 := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨hS, hne⟩)
    simp [hzero]
  rw [hfilter]
  calc
    (∑ S ∈ iwaniecCubicShiftedErrorSupport r y Q,
        |iwaniecCubicShiftedSubsetCoefficient r y S|) =
      ∑ _S ∈ iwaniecCubicShiftedErrorSupport r y Q, (1 : Real) := by
      apply Finset.sum_congr rfl
      intro S hS
      have hne := (Finset.mem_filter.mp hS).2
      unfold iwaniecCubicShiftedSubsetCoefficient at hne ⊢
      exact abs_iwaniecCubicLowerMoebius_eq_one_of_ne_zero hne
    _ = (iwaniecCubicShiftedErrorSupport r y Q).card := by simp

theorem iwaniecCubicShiftedErrorSupport_card_lt
    {r y : Nat} (hr : 0 < r) (Q : Finset Nat)
    {S : Finset Nat}
    (hS : S ∈ iwaniecCubicShiftedErrorSupport r y Q) :
    S.card < 2 * r := by
  have hdata := Finset.mem_filter.mp hS
  let reference := iwaniecReferencePrimePool Q.card
  let product := ∏ p ∈ reference, p
  have hprime := iwaniecReferencePrimePool_prime Q.card
  have hfactors :
      (UniqueFactorizationMonoid.normalizedFactors product).toFinset =
        reference := by
    simpa [product, reference] using
      product_normalizedFactors_toFinset reference hprime
  have hcoefficient := iwaniecCubicLowerMoebiusInt_subset_prod
    (n := product) (r := r) (y := y) S (by
      rw [hfactors]
      exact hdata.1)
  rw [Finset.prod_val] at hcoefficient
  have hcoeffIntProduct :
      iwaniecCubicLowerMoebiusInt r y (∏ p ∈ S, p) ≠ 0 := by
    intro hzero
    apply hdata.2
    simp [iwaniecCubicShiftedSubsetCoefficient,
      iwaniecCubicLowerMoebius, hzero]
  have hcoeffInt : iwaniecCubicLowerMoebiusInt r y (S.prod id) ≠ 0 := by
    simpa only [id_eq] using hcoeffIntProduct
  have hterm :
      iwaniecLowerContinuationTerm r (iwaniecCubicEvenRestriction y) []
        (iwaniecDescendingFactors S) ≠ 0 := by
    intro hzero
    apply hcoeffInt
    rw [hcoefficient, hzero]
  have hlength := iwaniecLowerContinuationTerm_ne_zero_length_lt
    (selected := ([] : List Nat)) (extension := iwaniecDescendingFactors S)
    (by simp [hr]) hterm
  simpa [iwaniecDescendingFactors] using hlength

def iwaniecCubicShiftedErrorSupportLayer
    (r y : Nat) (Q : Finset Nat) (k : Nat) : Finset (Finset Nat) :=
  (iwaniecCubicShiftedErrorSupport r y Q).filter fun S => S.card = k

theorem iwaniecCubicShiftedErrorSupport_card_eq_sum_layers
    {r y : Nat} (hr : 0 < r) (Q : Finset Nat) :
    (iwaniecCubicShiftedErrorSupport r y Q).card =
      ∑ k ∈ Finset.range (2 * r),
        (iwaniecCubicShiftedErrorSupportLayer r y Q k).card := by
  have hmap :
      (iwaniecCubicShiftedErrorSupport r y Q : Set (Finset Nat)).MapsTo
        (fun S : Finset Nat => S.card) (Finset.range (2 * r)) := by
    intro S hS
    exact Finset.mem_range.mpr
      (iwaniecCubicShiftedErrorSupport_card_lt hr Q hS)
  simpa [iwaniecCubicShiftedErrorSupportLayer] using
    (Finset.card_eq_sum_card_fiberwise hmap)

theorem iwaniecCubicShiftedSubsetCoefficient_ne_zero_iff_continuation
    {r y : Nat} {reference S : Finset Nat}
    (hprime : ∀ p ∈ reference, Nat.Prime p)
    (hS : S ∈ reference.powerset) :
    iwaniecCubicShiftedSubsetCoefficient r y S ≠ 0 ↔
      iwaniecLowerContinuationTerm r (iwaniecCubicEvenRestriction y) []
        (iwaniecDescendingFactors S) ≠ 0 := by
  let product := ∏ p ∈ reference, p
  have hfactors :
      (UniqueFactorizationMonoid.normalizedFactors product).toFinset =
        reference := by
    simpa [product] using
      product_normalizedFactors_toFinset reference hprime
  have hcoefficient := iwaniecCubicLowerMoebiusInt_subset_prod
    (n := product) (r := r) (y := y) S (by
      rw [hfactors]
      exact hS)
  rw [Finset.prod_val] at hcoefficient
  unfold iwaniecCubicShiftedSubsetCoefficient
    iwaniecCubicLowerMoebius
  rw [hcoefficient]
  exact Int.cast_ne_zero

def iwaniecCubicOrderedErrorSupportLayer
    (r y : Nat) (Q : Finset Nat) (k : Nat) : Finset (List Nat) :=
  (iwaniecOrderedFactorSublists
      (iwaniecReferencePrimePool Q.card)).filter fun ordered =>
    ordered.length = k ∧
      iwaniecLowerContinuationTerm r (iwaniecCubicEvenRestriction y) []
        ordered ≠ 0

theorem iwaniecCubicOrderedErrorSupportLayer_eq_image
    (r y : Nat) (Q : Finset Nat) (k : Nat) :
    iwaniecCubicOrderedErrorSupportLayer r y Q k =
      (iwaniecCubicShiftedErrorSupportLayer r y Q k).image
        iwaniecDescendingFactors := by
  let reference := iwaniecReferencePrimePool Q.card
  have hprime := iwaniecReferencePrimePool_prime Q.card
  ext ordered
  constructor
  · intro hordered
    have hdata := Finset.mem_filter.mp hordered
    have hsublist := mem_iwaniecOrderedFactorSublists.mp hdata.1
    let S := ordered.toFinset
    have hSPowerset : S ∈ reference.powerset := by
      apply Finset.mem_powerset.mpr
      intro p hp
      have hpOrdered : p ∈ ordered := by simpa [S] using hp
      have hpReference : p ∈ iwaniecDescendingFactors reference :=
        hsublist.subset hpOrdered
      simpa [iwaniecDescendingFactors] using hpReference
    have hdescending : iwaniecDescendingFactors S = ordered :=
      iwaniecDescendingFactors_toFinset_of_orderedSublist hsublist
    have hcoefficient :
        iwaniecCubicShiftedSubsetCoefficient r y S ≠ 0 :=
      (iwaniecCubicShiftedSubsetCoefficient_ne_zero_iff_continuation
        hprime hSPowerset).mpr (by simpa [hdescending] using hdata.2.2)
    have hnodup : ordered.Nodup :=
      (Finset.sort_nodup reference
        (fun left right : Nat => right ≤ left)).sublist hsublist
    have hcard : S.card = k := by
      simpa [S, List.toFinset_card_of_nodup hnodup] using hdata.2.1
    apply Finset.mem_image.mpr
    refine ⟨S, ?_, hdescending⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_filter.mpr ⟨hSPowerset, hcoefficient⟩, hcard⟩
  · intro himage
    obtain ⟨S, hSLayer, rfl⟩ := Finset.mem_image.mp himage
    have hSData := Finset.mem_filter.mp hSLayer
    have hSupportData := Finset.mem_filter.mp hSData.1
    apply Finset.mem_filter.mpr
    constructor
    · rw [iwaniecOrderedFactorSublists_eq_image]
      exact Finset.mem_image.mpr
        ⟨S, hSupportData.1, rfl⟩
    · constructor
      · simpa [iwaniecDescendingFactors] using hSData.2
      · exact
          (iwaniecCubicShiftedSubsetCoefficient_ne_zero_iff_continuation
            hprime hSupportData.1).mp hSupportData.2

theorem iwaniecCubicOrderedErrorSupportLayer_card
    (r y : Nat) (Q : Finset Nat) (k : Nat) :
    (iwaniecCubicOrderedErrorSupportLayer r y Q k).card =
      (iwaniecCubicShiftedErrorSupportLayer r y Q k).card := by
  rw [iwaniecCubicOrderedErrorSupportLayer_eq_image]
  exact Finset.card_image_of_injective _
    iwaniecDescendingFactors_injective

theorem iwaniecCubicShiftedErrorMass_le_supportCard
    (r y : Nat) (Q : Finset Nat) :
    iwaniecCubicShiftedErrorMass r y Q ≤
      (iwaniecCubicShiftedErrorSupport r y Q).card := by
  exact (iwaniecCubicShiftedErrorMass_eq_supportCard r y Q).le

theorem iwaniecCubicShiftedErrorSupport_prod_injOn
    (r y : Nat) (Q : Finset Nat) :
    Set.InjOn (fun S : Finset Nat => S.prod id)
      (iwaniecCubicShiftedErrorSupport r y Q : Set (Finset Nat)) := by
  intro left hleft right hright heq
  have hleftSubset : left ⊆ iwaniecReferencePrimePool Q.card := by
    have hdata := Finset.mem_filter.mp hleft
    exact Finset.mem_powerset.mp hdata.1
  have hrightSubset : right ⊆ iwaniecReferencePrimePool Q.card := by
    have hdata := Finset.mem_filter.mp hright
    exact Finset.mem_powerset.mp hdata.1
  have hleftPrime : ∀ p ∈ left, Nat.Prime p := by
    intro p hp
    exact iwaniecReferencePrimePool_prime Q.card p (hleftSubset hp)
  have hrightPrime : ∀ p ∈ right, Nat.Prime p := by
    intro p hp
    exact iwaniecReferencePrimePool_prime Q.card p (hrightSubset hp)
  calc
    left = (left.prod id).primeFactors :=
      by
        have h := (Nat.primeFactors_prod hleftPrime).symm
        simpa using h
    _ = (right.prod id).primeFactors := congrArg Nat.primeFactors heq
    _ = right := by simpa using Nat.primeFactors_prod hrightPrime

/-- Exact reference-support injection.  This is the elementary carrier part
of Iwaniec 1978 Lemma 2(5); the paper's remaining analytic gain replaces the
right side `y` by `y / log^2 y`. -/
theorem iwaniecCubicShiftedErrorSupport_card_le_level
    {r y : Nat} (Q : Finset Nat) (hy : 1 < y)
    (hreferenceLt : ∀ p ∈ iwaniecReferencePrimePool Q.card, p < y) :
    (iwaniecCubicShiftedErrorSupport r y Q).card ≤ y := by
  let support := iwaniecCubicShiftedErrorSupport r y Q
  let productMap := fun S : Finset Nat => S.prod id
  have himageSubset : support.image productMap ⊆ Finset.range y := by
    intro product hproduct
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hproduct
    have hdata := Finset.mem_filter.mp hS
    have hSSubset := Finset.mem_powerset.mp hdata.1
    have hSPrime : ∀ p ∈ S, Nat.Prime p := by
      intro p hp
      exact iwaniecReferencePrimePool_prime Q.card p (hSSubset hp)
    have hfactorLt : ∀ p ∈ (S.prod id).primeFactors, p < y := by
      intro p hp
      have hpS : p ∈ S := by
        have hpf : (S.prod id).primeFactors = S := by
          simpa using Nat.primeFactors_prod hSPrime
        rw [hpf] at hp
        exact hp
      exact hreferenceLt p (hSSubset hpS)
    have hcoeff : iwaniecCubicLowerMoebius r y (S.prod id) ≠ 0 := by
      simpa [iwaniecCubicShiftedSubsetCoefficient] using hdata.2
    exact Finset.mem_range.mpr
      (iwaniecCubicLowerMoebius_ne_zero_imp_lt hy hfactorLt hcoeff)
  have hcardImage := Finset.card_le_card himageSubset
  have hinj : Set.InjOn productMap (support : Set (Finset Nat)) := by
    simpa [support, productMap] using
      iwaniecCubicShiftedErrorSupport_prod_injOn r y Q
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hcardImage
  exact hcardImage

theorem iwaniecCubicShiftedErrorMass_le_level
    {r y : Nat} (Q : Finset Nat) (hy : 1 < y)
    (hreferenceLt : ∀ p ∈ iwaniecReferencePrimePool Q.card, p < y) :
    iwaniecCubicShiftedErrorMass r y Q ≤ y := by
  exact (iwaniecCubicShiftedErrorMass_le_supportCard r y Q).trans
    (by exact_mod_cast
      iwaniecCubicShiftedErrorSupport_card_le_level Q hy hreferenceLt)

end

end Erdos1212Kernel
