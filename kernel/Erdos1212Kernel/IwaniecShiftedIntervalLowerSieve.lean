import Erdos1212Kernel.IwaniecShiftedPrimePairing

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1400000

def iwaniecShiftedActiveReference
    (Q : Finset Nat) (value : Nat) : Finset Nat :=
  (iwaniecReferencePrimePool Q.card).filter fun p =>
    iwaniecActualPrimeForReference Q p ∣ value

def iwaniecCubicShiftedIndicatorSum
    (r y : Nat) (Q : Finset Nat) (value : Nat) : Real :=
  ∑ S ∈ (iwaniecReferencePrimePool Q.card).powerset,
    if ∀ p ∈ S, iwaniecActualPrimeForReference Q p ∣ value then
      iwaniecCubicShiftedSubsetCoefficient r y S
    else
      0

theorem iwaniecCubicShiftedIndicatorSum_eq_cumulative
    (r y : Nat) (Q : Finset Nat) (value : Nat) :
    iwaniecCubicShiftedIndicatorSum r y Q value =
      iwaniecShiftedSubsetCumulative
        (iwaniecCubicShiftedSubsetCoefficient r y)
        (iwaniecShiftedActiveReference Q value) := by
  unfold iwaniecCubicShiftedIndicatorSum
    iwaniecShiftedSubsetCumulative
  rw [← Finset.sum_filter]
  have hsets :
      (iwaniecReferencePrimePool Q.card).powerset.filter
          (fun S => ∀ p ∈ S, iwaniecActualPrimeForReference Q p ∣ value) =
        (iwaniecShiftedActiveReference Q value).powerset := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro hdata p hp
      exact Finset.mem_filter.mpr ⟨hdata.1 hp, hdata.2 p hp⟩
    · intro hsubset
      constructor
      · intro p hp
        exact (Finset.mem_filter.mp (hsubset hp)).1
      · intro p hp
        exact (Finset.mem_filter.mp (hsubset hp)).2
  rw [hsets]

theorem iwaniecShiftedActiveReference_eq_empty_iff
    (Q : Finset Nat) (value : Nat) :
    iwaniecShiftedActiveReference Q value = ∅ ↔
      ∀ q ∈ Q, ¬q ∣ value := by
  constructor
  · intro hempty q hq hqDvd
    have hqImage : q ∈
        (iwaniecReferencePrimePool Q.card).image
          (iwaniecActualPrimeForReference Q) := by
      rw [iwaniecActualPrimeForReference_image]
      exact hq
    obtain ⟨p, hp, hpEq⟩ := Finset.mem_image.mp hqImage
    have hpActive : p ∈ iwaniecShiftedActiveReference Q value := by
      apply Finset.mem_filter.mpr
      exact ⟨hp, hpEq ▸ hqDvd⟩
    rw [hempty] at hpActive
    simpa using hpActive
  · intro havoids
    ext p
    constructor
    · intro hp
      have hdata := Finset.mem_filter.mp hp
      exact (havoids _
        (iwaniecActualPrimeForReference_mem Q hdata.1) hdata.2).elim
    · intro hp
      simpa using hp

/-- Pointwise lower-sieve inequality on the literal actual prime state.  The
coefficient is carried on the first-`card Q` reference primes and transported
by the canonical ordered pairing; no large actual prime is discarded. -/
theorem iwaniecCubicShiftedIndicatorSum_le_avoiding
    {r y : Nat} (hr : 0 < r)
    (Q : Finset Nat) (value : Nat) :
    iwaniecCubicShiftedIndicatorSum r y Q value ≤
      if ∀ q ∈ Q, ¬q ∣ value then 1 else 0 := by
  rw [iwaniecCubicShiftedIndicatorSum_eq_cumulative]
  by_cases hactive : iwaniecShiftedActiveReference Q value = ∅
  · have havoids :=
      (iwaniecShiftedActiveReference_eq_empty_iff Q value).mp hactive
    rw [if_pos havoids, hactive]
    simp [iwaniecShiftedSubsetCumulative,
      iwaniecCubicShiftedSubsetCoefficient_empty]
  · have hnonempty : (iwaniecShiftedActiveReference Q value).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hactive
    have hmem : iwaniecShiftedActiveReference Q value ∈
        (iwaniecReferencePrimePool Q.card).powerset := by
      apply Finset.mem_powerset.mpr
      exact Finset.filter_subset _ _
    have hlower := iwaniecCubicShiftedSubsetCumulative_nonpos
      (y := y) hr (iwaniecReferencePrimePool_prime Q.card) hmem hnonempty
    have hnotAvoids : ¬∀ q ∈ Q, ¬q ∣ value := by
      intro havoids
      exact hactive
        ((iwaniecShiftedActiveReference_eq_empty_iff Q value).mpr havoids)
    rw [if_neg hnotAvoids]
    exact hlower

def iwaniecCubicShiftedIntervalRawSum
    (r y : Nat) (Q : Finset Nat) (lower length : Nat) : Real :=
  ∑ value ∈ Finset.Ioc lower (lower + length),
    iwaniecCubicShiftedIndicatorSum r y Q value

theorem iwaniecCubicShiftedIntervalRawSum_le_actualState
    {r y : Nat} (hr : 0 < r)
    (Q : Finset Nat) (lower length : Nat) :
    iwaniecCubicShiftedIntervalRawSum r y Q lower length ≤
      (primeStateAvoidingIndices Q lower length).card := by
  unfold iwaniecCubicShiftedIntervalRawSum
  calc
    (∑ value ∈ Finset.Ioc lower (lower + length),
        iwaniecCubicShiftedIndicatorSum r y Q value) ≤
      ∑ value ∈ Finset.Ioc lower (lower + length),
        if ∀ q ∈ Q, ¬q ∣ value then (1 : Real) else 0 := by
      apply Finset.sum_le_sum
      intro value _hvalue
      exact iwaniecCubicShiftedIndicatorSum_le_avoiding hr Q value
    _ = (((Finset.Ioc lower (lower + length)).filter fun value =>
          ∀ q ∈ Q, ¬q ∣ value).card : Real) := by
      simp
    _ = (primeStateAvoidingIndices Q lower length).card := by
      rw [primeStateAvoidingIndices_card_eq_avoidingNumbers]

def iwaniecShiftedSubsetProduct
    (Q : Finset Nat) (S : Finset Nat) : Nat :=
  ∏ p ∈ S, iwaniecActualPrimeForReference Q p

def iwaniecShiftedSubsetMultCount
    (Q : Finset Nat) (lower length : Nat) (S : Finset Nat) : Nat :=
  ((Finset.Ioc lower (lower + length)).filter fun value =>
    iwaniecShiftedSubsetProduct Q S ∣ value).card

theorem iwaniecShiftedSubsetProduct_dvd_iff
    (Q : Finset Nat) (hprime : ∀ q ∈ Q, Nat.Prime q)
    {S : Finset Nat}
    (hS : S ∈ (iwaniecReferencePrimePool Q.card).powerset)
    (value : Nat) :
    iwaniecShiftedSubsetProduct Q S ∣ value ↔
      ∀ p ∈ S, iwaniecActualPrimeForReference Q p ∣ value := by
  unfold iwaniecShiftedSubsetProduct
  exact iwaniecActualPrimeForReference_prod_dvd_iff
    Q hprime (Finset.mem_powerset.mp hS) value

theorem iwaniecCubicShiftedIntervalRawSum_eq_subsetCounts
    (r y : Nat) (Q : Finset Nat) (lower length : Nat)
    (hprime : ∀ q ∈ Q, Nat.Prime q) :
    iwaniecCubicShiftedIntervalRawSum r y Q lower length =
      ∑ S ∈ (iwaniecReferencePrimePool Q.card).powerset,
        iwaniecCubicShiftedSubsetCoefficient r y S *
          iwaniecShiftedSubsetMultCount Q lower length S := by
  unfold iwaniecCubicShiftedIntervalRawSum
    iwaniecCubicShiftedIndicatorSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  have hproduct (value : Nat) :
      (∀ p ∈ S, iwaniecActualPrimeForReference Q p ∣ value) ↔
        iwaniecShiftedSubsetProduct Q S ∣ value :=
    (iwaniecShiftedSubsetProduct_dvd_iff Q hprime hS value).symm
  calc
    (∑ value ∈ Finset.Ioc lower (lower + length),
        if ∀ p ∈ S, iwaniecActualPrimeForReference Q p ∣ value then
          iwaniecCubicShiftedSubsetCoefficient r y S
        else 0) =
      ∑ value ∈ Finset.Ioc lower (lower + length),
        if iwaniecShiftedSubsetProduct Q S ∣ value then
          iwaniecCubicShiftedSubsetCoefficient r y S
        else 0 := by
      apply Finset.sum_congr rfl
      intro value _hvalue
      simp only [hproduct value]
    _ = iwaniecCubicShiftedSubsetCoefficient r y S *
        iwaniecShiftedSubsetMultCount Q lower length S := by
      unfold iwaniecShiftedSubsetMultCount
      rw [← Finset.sum_filter]
      simp [mul_comm]

theorem iwaniecShiftedSubsetMultCount_eq
    (Q : Finset Nat) (lower length : Nat) (S : Finset Nat) :
    iwaniecShiftedSubsetMultCount Q lower length S =
      (lower + length) / iwaniecShiftedSubsetProduct Q S -
        lower / iwaniecShiftedSubsetProduct Q S := by
  unfold iwaniecShiftedSubsetMultCount
  exact card_Ioc_filter_dvd_eq_div_sub
    (iwaniecShiftedSubsetProduct Q S) lower (lower + length) (by omega)

def iwaniecShiftedSubsetRem
    (Q : Finset Nat) (lower length : Nat) (S : Finset Nat) : Real :=
  (iwaniecShiftedSubsetMultCount Q lower length S : Real) -
    (iwaniecShiftedSubsetProduct Q S : Real)⁻¹ * length

theorem iwaniecShiftedSubsetProduct_pos
    (Q : Finset Nat) (hprime : ∀ q ∈ Q, Nat.Prime q)
    {S : Finset Nat}
    (hS : S ∈ (iwaniecReferencePrimePool Q.card).powerset) :
    0 < iwaniecShiftedSubsetProduct Q S := by
  unfold iwaniecShiftedSubsetProduct
  apply Finset.prod_pos
  intro p hp
  exact (iwaniecActualPrimeForReference_prime Q hprime
    (Finset.mem_powerset.mp hS hp)).pos

theorem abs_iwaniecShiftedSubsetRem_le_one
    (Q : Finset Nat) (hprime : ∀ q ∈ Q, Nat.Prime q)
    (lower length : Nat) {S : Finset Nat}
    (hS : S ∈ (iwaniecReferencePrimePool Q.card).powerset) :
    |iwaniecShiftedSubsetRem Q lower length S| ≤ 1 := by
  let product := iwaniecShiftedSubsetProduct Q S
  have hproduct : product ≠ 0 :=
    ne_of_gt (iwaniecShiftedSubsetProduct_pos Q hprime hS)
  have hbound := vaughanIntervalSieve_abs_rem_le_one
    (∅ : Finset Nat) lower length product (by simp) hproduct
  rw [vaughanIntervalSieve_rem_eq
    (∅ : Finset Nat) lower length product (by simp) hproduct] at hbound
  unfold iwaniecShiftedSubsetRem
  rw [iwaniecShiftedSubsetMultCount_eq]
  simpa [product] using hbound

theorem iwaniecShiftedSubset_reciprocalProduct
    (Q : Finset Nat) (S : Finset Nat) :
    (∏ p ∈ S, ((iwaniecActualPrimeForReference Q p : Nat) : Real)⁻¹) =
      (iwaniecShiftedSubsetProduct Q S : Real)⁻¹ := by
  unfold iwaniecShiftedSubsetProduct
  push_cast
  exact Finset.prod_inv_distrib _

def iwaniecCubicShiftedErrorMass
    (r y : Nat) (Q : Finset Nat) : Real :=
  ∑ S ∈ (iwaniecReferencePrimePool Q.card).powerset,
    |iwaniecCubicShiftedSubsetCoefficient r y S|

theorem iwaniecCubicShiftedIntervalRawSum_eq_main_add_error
    (r y : Nat) (Q : Finset Nat) (lower length : Nat)
    (hprime : ∀ q ∈ Q, Nat.Prime q) :
    iwaniecCubicShiftedIntervalRawSum r y Q lower length =
      (length : Real) *
          iwaniecCubicShiftedMain r y
            (iwaniecReferencePrimePool Q.card)
            (iwaniecActualPrimeForReference Q) +
        ∑ S ∈ (iwaniecReferencePrimePool Q.card).powerset,
          iwaniecCubicShiftedSubsetCoefficient r y S *
            iwaniecShiftedSubsetRem Q lower length S := by
  rw [iwaniecCubicShiftedIntervalRawSum_eq_subsetCounts
    r y Q lower length hprime]
  unfold iwaniecCubicShiftedMain iwaniecShiftedSubsetMain
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _hS
  rw [iwaniecShiftedSubset_reciprocalProduct]
  unfold iwaniecShiftedSubsetRem
  ring

/-- Exact shifted-sieve interval consumer.  The only remaining error object
is Iwaniec's reference coefficient support mass, the left side of his 1978
Lemma 2(5). -/
theorem iwaniecCubicShifted_main_sub_errorMass_le_actualState
    {r y : Nat} (hr : 0 < r)
    (Q : Finset Nat) (lower length : Nat)
    (hprime : ∀ q ∈ Q, Nat.Prime q) :
    (length : Real) *
          iwaniecCubicShiftedMain r y
            (iwaniecReferencePrimePool Q.card)
            (iwaniecActualPrimeForReference Q) -
        iwaniecCubicShiftedErrorMass r y Q ≤
      (primeStateAvoidingIndices Q lower length).card := by
  have hraw := iwaniecCubicShiftedIntervalRawSum_le_actualState
    (y := y) hr Q lower length
  rw [iwaniecCubicShiftedIntervalRawSum_eq_main_add_error
    r y Q lower length hprime] at hraw
  have herror :
      -(iwaniecCubicShiftedErrorMass r y Q) ≤
        ∑ S ∈ (iwaniecReferencePrimePool Q.card).powerset,
          iwaniecCubicShiftedSubsetCoefficient r y S *
            iwaniecShiftedSubsetRem Q lower length S := by
    unfold iwaniecCubicShiftedErrorMass
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro S hS
    calc
      -|iwaniecCubicShiftedSubsetCoefficient r y S| ≤
          -|iwaniecCubicShiftedSubsetCoefficient r y S| *
            |iwaniecShiftedSubsetRem Q lower length S| := by
        have hrem := abs_iwaniecShiftedSubsetRem_le_one
          Q hprime lower length hS
        have hcoeff := abs_nonneg
          (iwaniecCubicShiftedSubsetCoefficient r y S)
        nlinarith
      _ ≤ iwaniecCubicShiftedSubsetCoefficient r y S *
            iwaniecShiftedSubsetRem Q lower length S :=
        by
          calc
            -|iwaniecCubicShiftedSubsetCoefficient r y S| *
                |iwaniecShiftedSubsetRem Q lower length S| =
              -|iwaniecCubicShiftedSubsetCoefficient r y S *
                iwaniecShiftedSubsetRem Q lower length S| := by
                  rw [abs_mul]
                  ring
            _ ≤ _ := neg_abs_le _
  linarith

def iwaniecReferencePrimePoolEuler (K : Nat) : Real :=
  iwaniecShiftedSubsetEuler (iwaniecReferencePrimePool K)
    (fun p => (p : Real))

def iwaniecActualPrimeStateEuler (Q : Finset Nat) : Real :=
  iwaniecShiftedSubsetEuler (iwaniecReferencePrimePool Q.card)
    (fun p => (iwaniecActualPrimeForReference Q p : Real))

theorem iwaniecReferencePrimePoolEuler_pos (K : Nat) :
    0 < iwaniecReferencePrimePoolEuler K := by
  unfold iwaniecReferencePrimePoolEuler
  apply iwaniecShiftedSubsetEuler_pos
  intro p hp
  exact_mod_cast (iwaniecReferencePrimePool_prime K p hp).one_lt

theorem iwaniecActualPrimeStateEuler_pos
    (Q : Finset Nat) (hprime : ∀ q ∈ Q, Nat.Prime q) :
    0 < iwaniecActualPrimeStateEuler Q := by
  unfold iwaniecActualPrimeStateEuler
  apply iwaniecShiftedSubsetEuler_pos
  intro p hp
  exact_mod_cast
    (iwaniecActualPrimeForReference_prime Q hprime hp).one_lt

theorem iwaniecActualPrimeStateEuler_eq_actualProduct (Q : Finset Nat) :
    iwaniecActualPrimeStateEuler Q =
      ∏ q ∈ Q, (1 - (q : Real)⁻¹) := by
  unfold iwaniecActualPrimeStateEuler iwaniecShiftedSubsetEuler
  calc
    (∏ p ∈ iwaniecReferencePrimePool Q.card,
        (1 - (iwaniecActualPrimeForReference Q p : Real)⁻¹)) =
      ∏ q ∈ (iwaniecReferencePrimePool Q.card).image
          (iwaniecActualPrimeForReference Q),
        (1 - (q : Real)⁻¹) :=
      by
        symm
        exact Finset.prod_image
          (iwaniecActualPrimeForReference_injOn Q)
    _ = _ := by rw [iwaniecActualPrimeForReference_image]

theorem iwaniecReferencePrimePoolEuler_le_actualPrimeStateEuler
    (Q : Finset Nat) (hprime : ∀ q ∈ Q, Nat.Prime q) :
    iwaniecReferencePrimePoolEuler Q.card ≤
      iwaniecActualPrimeStateEuler Q := by
  unfold iwaniecReferencePrimePoolEuler iwaniecActualPrimeStateEuler
    iwaniecShiftedSubsetEuler
  apply Finset.prod_le_prod
  · intro p hp
    have hpOne : (1 : Real) < p := by
      exact_mod_cast (iwaniecReferencePrimePool_prime Q.card p hp).one_lt
    exact le_of_lt (sub_pos.mpr (inv_lt_one_of_one_lt₀ hpOne))
  · intro p hp
    have hpPos : (0 : Real) < p := by
      exact_mod_cast (iwaniecReferencePrimePool_prime Q.card p hp).pos
    have hactualPos : (0 : Real) < iwaniecActualPrimeForReference Q p := by
      exact_mod_cast (iwaniecActualPrimeForReference_prime Q hprime hp).pos
    have horder : (p : Real) ≤ iwaniecActualPrimeForReference Q p := by
      exact_mod_cast
        iwaniecReferencePrime_le_actualPrimeForReference Q hprime hp
    have hinv :
        ((iwaniecActualPrimeForReference Q p : Nat) : Real)⁻¹ ≤
          (p : Real)⁻¹ :=
      (inv_le_inv₀ hactualPos hpPos).2 horder
    linarith

theorem one_le_iwaniecActual_referenceEulerRatio
    (Q : Finset Nat) (hprime : ∀ q ∈ Q, Nat.Prime q) :
    1 ≤ iwaniecActualPrimeStateEuler Q /
      iwaniecReferencePrimePoolEuler Q.card := by
  exact (le_div_iff₀ (iwaniecReferencePrimePoolEuler_pos Q.card)).2
    (by simpa using
      iwaniecReferencePrimePoolEuler_le_actualPrimeStateEuler Q hprime)

/-- Normalized main-term form of Iwaniec's shifted-sieve Lemma 1, now with
the reference expression identified with the literal cubic weighted tree. -/
theorem iwaniecCubic_referenceRatio_mul_weightedExpansion_le_shiftedMain
    {r y : Nat} (hr : 0 < r)
    (Q : Finset Nat) (hprime : ∀ q ∈ Q, Nat.Prime q) :
    (iwaniecActualPrimeStateEuler Q /
          iwaniecReferencePrimePoolEuler Q.card) *
        iwaniecCubicWeightedMainExpansion r y
          (iwaniecReferencePrimePool Q.card) ≤
      iwaniecCubicShiftedMain r y
        (iwaniecReferencePrimePool Q.card)
        (iwaniecActualPrimeForReference Q) := by
  have hmono := iwaniecCubic_arbitraryPrimeState_shifted_main
    (y := y) hr Q hprime
  rw [iwaniecCubicShiftedMain_id_eq_weightedExpansion
    r y (iwaniecReferencePrimePool Q.card)
    (iwaniecReferencePrimePool_prime Q.card)] at hmono
  change iwaniecActualPrimeStateEuler Q *
      iwaniecCubicWeightedMainExpansion r y
        (iwaniecReferencePrimePool Q.card) ≤
    iwaniecReferencePrimePoolEuler Q.card *
      iwaniecCubicShiftedMain r y
        (iwaniecReferencePrimePool Q.card)
        (iwaniecActualPrimeForReference Q) at hmono
  have href := iwaniecReferencePrimePoolEuler_pos Q.card
  have hdiv :
      (iwaniecActualPrimeStateEuler Q *
          iwaniecCubicWeightedMainExpansion r y
            (iwaniecReferencePrimePool Q.card)) /
          iwaniecReferencePrimePoolEuler Q.card ≤
        iwaniecCubicShiftedMain r y
          (iwaniecReferencePrimePool Q.card)
          (iwaniecActualPrimeForReference Q) := by
    apply (div_le_iff₀ href).2
    simpa [mul_comm] using hmono
  calc
    (iwaniecActualPrimeStateEuler Q /
          iwaniecReferencePrimePoolEuler Q.card) *
        iwaniecCubicWeightedMainExpansion r y
          (iwaniecReferencePrimePool Q.card) =
      (iwaniecActualPrimeStateEuler Q *
          iwaniecCubicWeightedMainExpansion r y
            (iwaniecReferencePrimePool Q.card)) /
        iwaniecReferencePrimePoolEuler Q.card := by ring
    _ ≤ _ := hdiv

/-- Final paper-faithful shifted interval reduction.  Both remaining
quantitative terms live on the first `card Q` primes, exactly as in Iwaniec
1978 Lemma 2(5)-(6). -/
theorem iwaniecCubic_reference_main_sub_errorMass_le_actualState
    {r y : Nat} (hr : 0 < r)
    (Q : Finset Nat) (lower length : Nat)
    (hprime : ∀ q ∈ Q, Nat.Prime q) :
    (length : Real) *
          ((iwaniecActualPrimeStateEuler Q /
              iwaniecReferencePrimePoolEuler Q.card) *
            iwaniecCubicWeightedMainExpansion r y
              (iwaniecReferencePrimePool Q.card)) -
        iwaniecCubicShiftedErrorMass r y Q ≤
      (primeStateAvoidingIndices Q lower length).card := by
  have hmain :=
    iwaniecCubic_referenceRatio_mul_weightedExpansion_le_shiftedMain
      (y := y) hr Q hprime
  have hscaled := mul_le_mul_of_nonneg_left hmain (by positivity :
    (0 : Real) ≤ length)
  have hinterval := iwaniecCubicShifted_main_sub_errorMass_le_actualState
    (y := y) hr Q lower length hprime
  linarith

end

end Erdos1212Kernel
