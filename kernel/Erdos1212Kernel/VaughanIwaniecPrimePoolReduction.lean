import Erdos1212Kernel.IwaniecCubicMainExpansion

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1400000

def vaughanPrimePool (cutoff : Nat) : Finset Nat :=
  Nat.primesLE cutoff

theorem vaughanPrimePool_prime (cutoff : Nat) :
    ∀ q ∈ vaughanPrimePool cutoff, Nat.Prime q := by
  intro q hq
  exact (Nat.mem_primesLE.mp hq).2

theorem primeStateSmallPart_subset_vaughanPrimePool
    {Q : Finset Nat} {cutoff : Nat}
    (hprime : ∀ q ∈ Q, Nat.Prime q) :
    primeStateSmallPart Q cutoff ⊆ vaughanPrimePool cutoff := by
  intro q hq
  have hdata := Finset.mem_filter.mp hq
  exact Nat.mem_primesLE.mpr ⟨hdata.2, hprime q hdata.1⟩

theorem vaughanPrimePool_avoiding_subset_smallStateAvoiding
    {Q : Finset Nat} {cutoff lower length : Nat}
    (hprime : ∀ q ∈ Q, Nat.Prime q) :
    primeStateAvoidingIndices (vaughanPrimePool cutoff) lower length ⊆
      primeStateAvoidingIndices (primeStateSmallPart Q cutoff)
        lower length := by
  intro index hindex
  have hdata := Finset.mem_filter.mp hindex
  apply Finset.mem_filter.mpr
  refine ⟨hdata.1, ?_⟩
  intro q hq
  exact hdata.2 q (primeStateSmallPart_subset_vaughanPrimePool hprime hq)

theorem vaughanPrimePool_card_le_smallState_card
    {Q : Finset Nat} {cutoff lower length : Nat}
    (hprime : ∀ q ∈ Q, Nat.Prime q) :
    (primeStateAvoidingIndices (vaughanPrimePool cutoff)
      lower length).card ≤
      (primeStateAvoidingIndices (primeStateSmallPart Q cutoff)
        lower length).card :=
  Finset.card_le_card
    (vaughanPrimePool_avoiding_subset_smallStateAvoiding hprime)

/-- Vaughan's actual-state reduction with the small part strengthened to the
complete prime pool. -/
theorem vaughanPrimePool_card_sub_largeLoss_le_actualState
    {Q : Finset Nat} {cutoff lower length : Nat}
    (hprime : ∀ q ∈ Q, Nat.Prime q) (hcutoff : 0 < cutoff) :
    (primeStateAvoidingIndices (vaughanPrimePool cutoff)
        lower length).card - Q.card * (length / cutoff + 1) ≤
      (primeStateAvoidingIndices Q lower length).card := by
  have hpool := vaughanPrimePool_card_le_smallState_card
    (Q := Q) (cutoff := cutoff) (lower := lower) (length := length) hprime
  have hlarge := primeStateAvoiding_full_card_lower
    (Q := Q) (cutoff := cutoff) (lower := lower) (length := length)
    hprime hcutoff
  omega

/-- Exact final reduction before Iwaniec's quantitative main-tree estimate.
Every term now refers to the standard full prime pool below `cutoff`. -/
theorem vaughanIwaniec_primePool_mainTree_reduction
    {Q : Finset Nat} {cutoff lower length r y : Nat}
    (hprime : ∀ q ∈ Q, Nat.Prime q) (hcutoff : 0 < cutoff)
    (hr : 0 < r) (hy : 1 < y) (hcutoffY : cutoff < y) :
    (length : Real) *
          iwaniecWeightedLowerTreeSum r (iwaniecCubicEvenRestriction y)
            iwaniecReciprocalFactorWeight []
            (iwaniecDescendingFactors (vaughanPrimePool cutoff)) -
        y - (Q.card * (length / cutoff + 1) : Nat) ≤
      (primeStateAvoidingIndices Q lower length).card := by
  have hpoolPrime := vaughanPrimePool_prime cutoff
  have hpoolLt : ∀ q ∈ vaughanPrimePool cutoff, q < y := by
    intro q hq
    exact (Nat.mem_primesLE.mp hq).1.trans_lt hcutoffY
  have hpoolLower :=
    iwaniecCubic_main_sub_level_le_primeStateAvoiding_card
      (vaughanPrimePool cutoff) lower length r y
      hpoolPrime hr hy hpoolLt
  rw [vaughanIntervalSieve_iwaniecCubic_mainSum_eq_tree] at hpoolLower
  have hpoolCard := vaughanPrimePool_card_le_smallState_card
    (Q := Q) (cutoff := cutoff) (lower := lower) (length := length) hprime
  have hlarge := primeStateAvoiding_full_card_lower
    (Q := Q) (cutoff := cutoff) (lower := lower) (length := length)
    hprime hcutoff
  let loss := Q.card * (length / cutoff + 1)
  have hsmallAdd :
      (primeStateAvoidingIndices (primeStateSmallPart Q cutoff)
          lower length).card ≤
        (primeStateAvoidingIndices Q lower length).card + loss := by
    dsimp [loss]
    omega
  have hpoolAdd :
      (primeStateAvoidingIndices (vaughanPrimePool cutoff)
          lower length).card ≤
        (primeStateAvoidingIndices Q lower length).card + loss :=
    hpoolCard.trans hsmallAdd
  have hpoolAddReal :
      ((primeStateAvoidingIndices (vaughanPrimePool cutoff)
          lower length).card : Real) ≤
        (primeStateAvoidingIndices Q lower length).card + loss := by
    exact_mod_cast hpoolAdd
  dsimp [loss] at hpoolAddReal
  linarith

end

end Erdos1212Kernel
