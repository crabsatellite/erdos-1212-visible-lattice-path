import Erdos1212Kernel.IwaniecCubicShiftedTransport
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Nat.GCD.BigOperators

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1200000

/-- The `i`-th member of any increasing finite prime set is no smaller than
the `i`-th prime.  This is the ordered prime pairing used in Iwaniec (1978). -/
theorem nthPrime_le_primeFinset_orderEmbOfFin
    (Q : Finset Nat) (hprime : ∀ q ∈ Q, Nat.Prime q)
    (i : Fin Q.card) :
    Nat.nth Nat.Prime i ≤ Q.orderEmbOfFin rfl i := by
  let embedding := (Q.orderEmbOfFin rfl).toEmbedding
  let initialImage : Finset Nat := (Finset.Iic i).map embedding
  have hsubset : initialImage ⊆
      (Finset.range (Q.orderEmbOfFin rfl i + 1)).filter Nat.Prime := by
    intro q hq
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hq
    change Q.orderEmbOfFin rfl j ∈
      (Finset.range (Q.orderEmbOfFin rfl i + 1)).filter Nat.Prime
    have hjLe : j ≤ i := Finset.mem_Iic.mp hj
    have hvalueLe : Q.orderEmbOfFin rfl j ≤ Q.orderEmbOfFin rfl i :=
      (Q.orderEmbOfFin rfl).monotone hjLe
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by omega),
      hprime _ (Q.orderEmbOfFin_mem rfl j)⟩
  have hcard := Finset.card_le_card hsubset
  have hinitialCard : initialImage.card = i + 1 := by
    simp [initialImage, embedding]
  rw [hinitialCard, ← Nat.count_eq_card_filter_range] at hcard
  have hiCount : (i : Nat) <
      Nat.count Nat.Prime (Q.orderEmbOfFin rfl i + 1) := by
    omega
  have hnthLt := Nat.nth_lt_of_lt_count hiCount
  omega

noncomputable def iwaniecNthPrimeOrderEmbedding (K : Nat) :
    Fin K ↪o Nat :=
  OrderEmbedding.ofStrictMono (fun i : Fin K => Nat.nth Nat.Prime i) (by
    intro i j hij
    exact Nat.nth_strictMono Nat.infinite_setOf_prime (by exact_mod_cast hij))

def iwaniecReferencePrimePool (K : Nat) : Finset Nat :=
  Finset.univ.map (iwaniecNthPrimeOrderEmbedding K).toEmbedding

@[simp]
theorem iwaniecReferencePrimePool_card (K : Nat) :
    (iwaniecReferencePrimePool K).card = K := by
  simp [iwaniecReferencePrimePool]

theorem iwaniecReferencePrimePool_prime (K : Nat) :
    ∀ p ∈ iwaniecReferencePrimePool K, Nat.Prime p := by
  intro p hp
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hp
  exact Nat.prime_nth_prime i

theorem iwaniecReferencePrimePool_orderEmb_eq (K : Nat) :
    (iwaniecReferencePrimePool K).orderEmbOfFin
        (iwaniecReferencePrimePool_card K) =
      iwaniecNthPrimeOrderEmbedding K := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  apply Finset.mem_map.mpr
  exact ⟨i, Finset.mem_univ i, rfl⟩

noncomputable def iwaniecActualPrimeForReference
    (Q : Finset Nat) (p : Nat) : Nat :=
  if hp : p ∈ iwaniecReferencePrimePool Q.card then
    Q.orderEmbOfFin rfl
      (((iwaniecReferencePrimePool Q.card).orderIsoOfFin
        (iwaniecReferencePrimePool_card Q.card)).symm ⟨p, hp⟩)
  else
    p

theorem iwaniecActualPrimeForReference_mem
    (Q : Finset Nat) {p : Nat}
    (hp : p ∈ iwaniecReferencePrimePool Q.card) :
    iwaniecActualPrimeForReference Q p ∈ Q := by
  unfold iwaniecActualPrimeForReference
  rw [dif_pos hp]
  exact Q.orderEmbOfFin_mem rfl _

theorem iwaniecActualPrimeForReference_prime
    (Q : Finset Nat) (hprime : ∀ q ∈ Q, Nat.Prime q)
    {p : Nat} (hp : p ∈ iwaniecReferencePrimePool Q.card) :
    Nat.Prime (iwaniecActualPrimeForReference Q p) :=
  hprime _ (iwaniecActualPrimeForReference_mem Q hp)

theorem iwaniecActualPrimeForReference_injOn (Q : Finset Nat) :
    Set.InjOn (iwaniecActualPrimeForReference Q)
      (iwaniecReferencePrimePool Q.card : Set Nat) := by
  intro left hleft right hright heq
  have hleft' : left ∈ iwaniecReferencePrimePool Q.card := by
    simpa using hleft
  have hright' : right ∈ iwaniecReferencePrimePool Q.card := by
    simpa using hright
  unfold iwaniecActualPrimeForReference at heq
  rw [dif_pos hleft', dif_pos hright'] at heq
  have hrank := (Q.orderEmbOfFin rfl).injective heq
  have hsubtype :=
    ((iwaniecReferencePrimePool Q.card).orderIsoOfFin
      (iwaniecReferencePrimePool_card Q.card)).symm.injective hrank
  exact congrArg Subtype.val hsubtype

theorem iwaniecActualPrimeForReference_image (Q : Finset Nat) :
    (iwaniecReferencePrimePool Q.card).image
        (iwaniecActualPrimeForReference Q) = Q := by
  apply Finset.eq_of_subset_of_card_le
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact iwaniecActualPrimeForReference_mem Q hp
  · rw [Finset.card_image_of_injOn
      (iwaniecActualPrimeForReference_injOn Q),
    iwaniecReferencePrimePool_card]

theorem iwaniecActualPrimeForReference_pairwise_coprime
    (Q : Finset Nat) (hprime : ∀ q ∈ Q, Nat.Prime q) :
    Set.Pairwise (iwaniecReferencePrimePool Q.card : Set Nat)
      (fun left right => Nat.Coprime
        (iwaniecActualPrimeForReference Q left)
        (iwaniecActualPrimeForReference Q right)) := by
  intro left hleft right hright hne
  have hleftPrime := iwaniecActualPrimeForReference_prime Q hprime hleft
  have hrightPrime := iwaniecActualPrimeForReference_prime Q hprime hright
  apply (Nat.coprime_primes hleftPrime hrightPrime).mpr
  intro heq
  exact hne (iwaniecActualPrimeForReference_injOn Q hleft hright heq)

theorem iwaniecActualPrimeForReference_prod_dvd_iff
    (Q : Finset Nat) (hprime : ∀ q ∈ Q, Nat.Prime q)
    {S : Finset Nat}
    (hS : S ⊆ iwaniecReferencePrimePool Q.card)
    (value : Nat) :
    (∏ p ∈ S, iwaniecActualPrimeForReference Q p) ∣ value ↔
      ∀ p ∈ S, iwaniecActualPrimeForReference Q p ∣ value := by
  constructor
  · intro hproduct p hp
    exact (Finset.dvd_prod_of_mem
      (fun next => iwaniecActualPrimeForReference Q next) hp).trans hproduct
  · intro hall
    induction S using Finset.induction_on with
    | empty => simp
    | @insert p S hpS ih =>
        rw [Finset.prod_insert hpS]
        have hpMem : p ∈ iwaniecReferencePrimePool Q.card :=
          hS (Finset.mem_insert_self p S)
        have hSSubset : S ⊆ iwaniecReferencePrimePool Q.card :=
          fun q hq => hS (Finset.mem_insert_of_mem hq)
        have hcoprime : Nat.Coprime
            (iwaniecActualPrimeForReference Q p)
            (∏ q ∈ S, iwaniecActualPrimeForReference Q q) := by
          apply Nat.Coprime.prod_right
          intro q hq
          exact iwaniecActualPrimeForReference_pairwise_coprime Q hprime
            hpMem (hSSubset hq) (by
              intro hpq
              subst q
              exact hpS hq)
        apply hcoprime.mul_dvd_of_dvd_of_dvd
        · exact hall p (Finset.mem_insert_self p S)
        · apply ih hSSubset
          intro q hq
          exact hall q (Finset.mem_insert_of_mem hq)

theorem iwaniecReferencePrime_le_actualPrimeForReference
    (Q : Finset Nat) (hprime : ∀ q ∈ Q, Nat.Prime q)
    {p : Nat} (hp : p ∈ iwaniecReferencePrimePool Q.card) :
    p ≤ iwaniecActualPrimeForReference Q p := by
  let referencePool := iwaniecReferencePrimePool Q.card
  let i : Fin Q.card :=
    (referencePool.orderIsoOfFin
      (iwaniecReferencePrimePool_card Q.card)).symm ⟨p, hp⟩
  have hforward :
      referencePool.orderEmbOfFin
          (iwaniecReferencePrimePool_card Q.card) i = p := by
    have happly := (referencePool.orderIsoOfFin
      (iwaniecReferencePrimePool_card Q.card)).apply_symm_apply ⟨p, hp⟩
    exact congrArg Subtype.val happly
  have hembedding :
      referencePool.orderEmbOfFin
          (iwaniecReferencePrimePool_card Q.card) i =
        iwaniecNthPrimeOrderEmbedding Q.card i := by
    simpa [referencePool] using congrArg
      (fun embedding : Fin Q.card ↪o Nat => embedding i)
      (iwaniecReferencePrimePool_orderEmb_eq Q.card)
  have hpEq : p = Nat.nth Nat.Prime i := by
    rw [← hforward, hembedding]
    rfl
  have horder := nthPrime_le_primeFinset_orderEmbOfFin Q hprime i
  unfold iwaniecActualPrimeForReference
  rw [dif_pos hp]
  change p ≤ Q.orderEmbOfFin rfl i
  rw [hpEq]
  exact horder

theorem iwaniecCubic_arbitraryPrimeState_shifted_main
    {r y : Nat} (hr : 0 < r)
    (Q : Finset Nat) (hprime : ∀ q ∈ Q, Nat.Prime q) :
    iwaniecShiftedSubsetEuler (iwaniecReferencePrimePool Q.card)
          (fun p => (iwaniecActualPrimeForReference Q p : Real)) *
        iwaniecCubicShiftedMain r y
          (iwaniecReferencePrimePool Q.card) id ≤
      iwaniecShiftedSubsetEuler (iwaniecReferencePrimePool Q.card)
          (fun p => (p : Real)) *
        iwaniecCubicShiftedMain r y
          (iwaniecReferencePrimePool Q.card)
          (iwaniecActualPrimeForReference Q) := by
  apply iwaniecCubic_shifted_normalized_main_mono hr
  · exact iwaniecReferencePrimePool_prime Q.card
  · intro p hp
    exact iwaniecReferencePrime_le_actualPrimeForReference Q hprime hp

end

end Erdos1212Kernel
