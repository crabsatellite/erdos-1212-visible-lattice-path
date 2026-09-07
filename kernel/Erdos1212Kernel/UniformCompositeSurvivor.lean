import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial
import Erdos1212Kernel.Target

namespace Erdos1212Kernel

/-!
# Uniform composite survivor coordinates

For a set `Q` of at most `H` prime labels, this file constructs a composite
integer in every interval of one fixed length (once the lower endpoint is
large enough) which is divisible by no member of `Q`.  The length depends
only on `H`, never on the identities or magnitudes of the primes.

The proof is elementary.  Put `M = (H + 1)#`, the primorial through `H + 1`,
and inspect `H + 1` integers in one residue class modulo `M`.  A label at
most `H + 1` divides none of them; a larger prime label divides at most one.
Since there are at most `H` labels, one candidate survives.  Multiplication
by one of the first `H + 1` primes missing from `Q` makes the survivor
composite while retaining coprimality.

Using the primorial rather than `(H + 1)!` is quantitatively decisive:
Mathlib proves `(H + 1)# ≤ 4 ^ (H + 1)`, so the resulting fixed-rank
confinement cost is exponential rather than factorial.
-/

def uniformCoprimeModulus (H : Nat) : Nat :=
  primorial (H + 1)

def uniformCoprimeBase (H lower : Nat) : Nat :=
  (lower / uniformCoprimeModulus H + 1) * uniformCoprimeModulus H + 1

def uniformCoprimeCandidate (H lower index : Nat) : Nat :=
  uniformCoprimeBase H lower + index * uniformCoprimeModulus H

theorem uniformCoprimeModulus_pos (H : Nat) :
    0 < uniformCoprimeModulus H := by
  exact primorial_pos _

theorem uniformCoprimeModulus_le_four_pow (H : Nat) :
    uniformCoprimeModulus H ≤ 4 ^ (H + 1) := by
  exact primorial_le_four_pow _

theorem uniformCoprimeModulus_mono {H K : Nat} (hHK : H ≤ K) :
    uniformCoprimeModulus H ≤ uniformCoprimeModulus K := by
  exact primorial_mono (Nat.add_le_add_right hHK 1)

theorem uniformCoprimeCandidate_gt (H lower index : Nat) :
    lower < uniformCoprimeCandidate H lower index := by
  let M := uniformCoprimeModulus H
  have hM : 0 < M := uniformCoprimeModulus_pos H
  have hmod : lower % M < M := Nat.mod_lt lower hM
  have hdecompose : lower % M + M * (lower / M) = lower :=
    Nat.mod_add_div lower M
  have hbase : lower < (lower / M + 1) * M + 1 := by
    rw [Nat.add_mul]
    rw [Nat.mul_comm M (lower / M)] at hdecompose
    omega
  exact hbase.trans_le <| by
    simp [uniformCoprimeCandidate, uniformCoprimeBase, M]

theorem uniformCoprimeCandidate_le
    {H lower index : Nat} (hindex : index ≤ H) :
    uniformCoprimeCandidate H lower index ≤
      lower + (H + 2) * uniformCoprimeModulus H := by
  let M := uniformCoprimeModulus H
  have hM : 0 < M := uniformCoprimeModulus_pos H
  have hmod : lower % M < M := Nat.mod_lt lower hM
  have hdecompose : lower % M + M * (lower / M) = lower :=
    Nat.mod_add_div lower M
  have hindexMul : index * M ≤ H * M := Nat.mul_le_mul_right M hindex
  have hbase : (lower / M + 1) * M + 1 ≤ lower + M + 1 := by
    rw [Nat.add_mul]
    rw [Nat.mul_comm M (lower / M)] at hdecompose
    omega
  change (lower / M + 1) * M + 1 + index * M ≤
    lower + (H + 2) * M
  have hHM : H * M + (M + 1) ≤ (H + 2) * M := by
    rw [Nat.add_mul]
    omega
  omega

theorem prime_not_dvd_uniformCoprimeCandidate_of_le
    {H lower index q : Nat} (hq : Nat.Prime q) (hqSmall : q ≤ H + 1) :
    ¬ q ∣ uniformCoprimeCandidate H lower index := by
  intro hqCandidate
  have hqModulus : q ∣ uniformCoprimeModulus H := by
    exact hq.dvd_primorial_iff.2 hqSmall
  let coefficient := lower / uniformCoprimeModulus H + 1 + index
  have hcandidateEq :
      uniformCoprimeCandidate H lower index =
        coefficient * uniformCoprimeModulus H + 1 := by
    simp only [uniformCoprimeCandidate, uniformCoprimeBase, coefficient]
    ring
  have hqProduct :
      q ∣ coefficient * uniformCoprimeModulus H :=
    dvd_mul_of_dvd_right hqModulus coefficient
  rw [hcandidateEq] at hqCandidate
  exact hq.not_dvd_one <| (Nat.dvd_add_iff_right hqProduct).mpr hqCandidate

def uniformKilledIndices (H lower q : Nat) : Finset Nat :=
  (Finset.range (H + 1)).filter fun index ↦
    q ∣ uniformCoprimeCandidate H lower index

theorem uniformKilledIndices_card_le_one
    {H lower q : Nat} (hq : Nat.Prime q) :
    (uniformKilledIndices H lower q).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro left right hleft hright
  have hleftData := Finset.mem_filter.mp hleft
  have hrightData := Finset.mem_filter.mp hright
  have hleftBound : left ≤ H := by
    have := Finset.mem_range.mp hleftData.1
    omega
  have hrightBound : right ≤ H := by
    have := Finset.mem_range.mp hrightData.1
    omega
  by_cases hqSmall : q ≤ H + 1
  · exact False.elim <|
      prime_not_dvd_uniformCoprimeCandidate_of_le hq hqSmall hleftData.2
  · have hqLarge : H + 1 < q := by omega
    rcases le_total left right with hle | hle
    · have hcandidatesLe :
          uniformCoprimeCandidate H lower left ≤
            uniformCoprimeCandidate H lower right := by
        simp only [uniformCoprimeCandidate]
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hle) _
      have hqDifference :
          q ∣ uniformCoprimeCandidate H lower right -
            uniformCoprimeCandidate H lower left :=
        Nat.dvd_sub hrightData.2 hleftData.2
      have hdifferenceEq :
          uniformCoprimeCandidate H lower right -
              uniformCoprimeCandidate H lower left =
            (right - left) * uniformCoprimeModulus H := by
        simp only [uniformCoprimeCandidate]
        rw [Nat.add_sub_add_left, Nat.sub_mul]
      rw [hdifferenceEq] at hqDifference
      rcases hq.dvd_mul.mp hqDifference with hqIndex | hqModulus
      · by_contra hne
        have hpositive : 0 < right - left := Nat.sub_pos_of_lt (lt_of_le_of_ne hle hne)
        have hqLe : q ≤ right - left := Nat.le_of_dvd hpositive hqIndex
        omega
      · have hqLe : q ≤ H + 1 := by
          exact hq.dvd_primorial_iff.mp
            (by simpa [uniformCoprimeModulus] using hqModulus)
        omega
    · have hcandidatesLe :
          uniformCoprimeCandidate H lower right ≤
            uniformCoprimeCandidate H lower left := by
        simp only [uniformCoprimeCandidate]
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hle) _
      have hqDifference :
          q ∣ uniformCoprimeCandidate H lower left -
            uniformCoprimeCandidate H lower right :=
        Nat.dvd_sub hleftData.2 hrightData.2
      have hdifferenceEq :
          uniformCoprimeCandidate H lower left -
              uniformCoprimeCandidate H lower right =
            (left - right) * uniformCoprimeModulus H := by
        simp only [uniformCoprimeCandidate]
        rw [Nat.add_sub_add_left, Nat.sub_mul]
      rw [hdifferenceEq] at hqDifference
      rcases hq.dvd_mul.mp hqDifference with hqIndex | hqModulus
      · by_contra hne
        have hpositive : 0 < left - right :=
          Nat.sub_pos_of_lt (lt_of_le_of_ne hle (Ne.symm hne))
        have hqLe : q ≤ left - right := Nat.le_of_dvd hpositive hqIndex
        omega
      · have hqLe : q ≤ H + 1 := by
          exact hq.dvd_primorial_iff.mp
            (by simpa [uniformCoprimeModulus] using hqModulus)
        omega

def uniformBadCandidateIndices
    (H lower : Nat) (Q : Finset Nat) : Finset Nat :=
  (Finset.range (H + 1)).filter fun index ↦
    ∃ q ∈ Q, q ∣ uniformCoprimeCandidate H lower index

theorem uniformBadCandidateIndices_eq_biUnion
    (H lower : Nat) (Q : Finset Nat) :
    uniformBadCandidateIndices H lower Q =
      Q.biUnion (uniformKilledIndices H lower) := by
  ext index
  constructor
  · intro hindex
    obtain ⟨hindexRange, q, hq, hqDvd⟩ :=
      Finset.mem_filter.mp hindex
    exact Finset.mem_biUnion.mpr
      ⟨q, hq, Finset.mem_filter.mpr ⟨hindexRange, hqDvd⟩⟩
  · intro hindex
    obtain ⟨q, hq, hindexKilled⟩ := Finset.mem_biUnion.mp hindex
    obtain ⟨hindexRange, hqDvd⟩ := Finset.mem_filter.mp hindexKilled
    exact Finset.mem_filter.mpr ⟨hindexRange, q, hq, hqDvd⟩

theorem uniformBadCandidateIndices_card_le
    {H lower : Nat} {Q : Finset Nat}
    (hprime : ∀ q ∈ Q, Nat.Prime q) :
    (uniformBadCandidateIndices H lower Q).card ≤ Q.card := by
  rw [uniformBadCandidateIndices_eq_biUnion]
  calc
    (Q.biUnion (uniformKilledIndices H lower)).card
        ≤ ∑ q ∈ Q, (uniformKilledIndices H lower q).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ Q, 1 := by
      exact Finset.sum_le_sum fun q hq ↦
        uniformKilledIndices_card_le_one (hprime q hq)
    _ = Q.card := by simp

theorem exists_uniformCoprimeCandidate
    {H lower : Nat} {Q : Finset Nat}
    (hcard : Q.card ≤ H)
    (hprime : ∀ q ∈ Q, Nat.Prime q) :
    ∃ candidate,
      lower < candidate ∧
      candidate ≤ lower + (H + 2) * uniformCoprimeModulus H ∧
      ∀ q ∈ Q, ¬ q ∣ candidate := by
  have hbadCard : (uniformBadCandidateIndices H lower Q).card ≤ H :=
    (uniformBadCandidateIndices_card_le hprime).trans hcard
  have hbadLt :
      (uniformBadCandidateIndices H lower Q).card <
        (Finset.range (H + 1)).card := by
    simpa using Nat.lt_of_le_of_lt hbadCard (Nat.lt_succ_self H)
  obtain ⟨index, hindexRange, hindexGood⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hbadLt
  have hindex : index ≤ H := by
    have := Finset.mem_range.mp hindexRange
    omega
  refine ⟨uniformCoprimeCandidate H lower index,
    uniformCoprimeCandidate_gt H lower index,
    uniformCoprimeCandidate_le hindex, ?_⟩
  intro q hq hqDvd
  apply hindexGood
  rw [uniformBadCandidateIndices, Finset.mem_filter]
  exact ⟨hindexRange, q, hq, hqDvd⟩

noncomputable def firstPrimePool (H : Nat) : Finset Nat :=
  (Finset.range (H + 1)).image (Nat.nth Nat.Prime)

theorem nthPrime_injective : Function.Injective (Nat.nth Nat.Prime) := by
  intro left right heq
  have hcount := congrArg Nat.primeCounting' heq
  simpa using hcount

theorem firstPrimePool_card (H : Nat) :
    (firstPrimePool H).card = H + 1 := by
  rw [firstPrimePool, Finset.card_image_of_injective _ nthPrime_injective]
  simp

theorem exists_missing_bounded_prime
    {H : Nat} {Q : Finset Nat} (hcard : Q.card ≤ H) :
    ∃ r,
      Nat.Prime r ∧ r ∉ Q ∧ r ≤ Nat.nth Nat.Prime H := by
  have hpoolCard : Q.card < (firstPrimePool H).card := by
    rw [firstPrimePool_card]
    omega
  obtain ⟨r, hrPool, hrQ⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hpoolCard
  obtain ⟨index, hindexRange, hindexEq⟩ :=
    Finset.mem_image.mp hrPool
  have hindex : index ≤ H := by
    have := Finset.mem_range.mp hindexRange
    omega
  refine ⟨r, ?_, hrQ, ?_⟩
  · rw [← hindexEq]
    exact Nat.prime_nth_prime index
  · rw [← hindexEq]
    exact (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone hindex

noncomputable def uniformCompositeSurvivorGap (H : Nat) : Nat :=
  (Nat.nth Nat.Prime H) * (H + 2) * uniformCoprimeModulus H

theorem uniformCompositeSurvivorGap_mono {H K : Nat} (hHK : H ≤ K) :
    uniformCompositeSurvivorGap H ≤ uniformCompositeSurvivorGap K := by
  have hnth : Nat.nth Nat.Prime H ≤ Nat.nth Nat.Prime K :=
    (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone hHK
  have hadd : H + 2 ≤ K + 2 := Nat.add_le_add_right hHK 2
  have hmodulus := uniformCoprimeModulus_mono hHK
  simp only [uniformCompositeSurvivorGap]
  exact Nat.mul_le_mul (Nat.mul_le_mul hnth hadd) hmodulus

theorem exists_uniformCompositeSurvivor
    {H lower : Nat} {Q : Finset Nat}
    (hcard : Q.card ≤ H)
    (hprime : ∀ q ∈ Q, Nat.Prime q)
    (hlower : Nat.nth Nat.Prime H ≤ lower) :
    ∃ survivor,
      lower < survivor ∧
      survivor ≤ lower + uniformCompositeSurvivorGap H ∧
      Composite survivor ∧
      ∀ q ∈ Q, ¬ q ∣ survivor := by
  obtain ⟨r, hrPrime, hrQ, hrBound⟩ :=
    exists_missing_bounded_prime hcard
  have hrPos : 0 < r := hrPrime.pos
  obtain ⟨t, htLower, htUpper, htCoprime⟩ :=
    exists_uniformCoprimeCandidate (H := H) (lower := lower / r)
      hcard hprime
  have hlowerDiv : 1 ≤ lower / r := by
    have hrLeLower : r ≤ lower := hrBound.trans hlower
    exact Nat.one_le_div_iff hrPos |>.2 hrLeLower
  have htOne : 1 < t := hlowerDiv.trans_lt htLower
  refine ⟨r * t, ?_, ?_, ?_, ?_⟩
  · have hquotient : lower < r * (lower / r + 1) := by
      have hmod : lower % r < r := Nat.mod_lt lower hrPos
      have hdecompose : lower % r + r * (lower / r) = lower :=
        Nat.mod_add_div lower r
      rw [Nat.mul_add]
      omega
    exact hquotient.trans_le (Nat.mul_le_mul_left r (by omega))
  · have htUpperMul := Nat.mul_le_mul_left r htUpper
    have hfloor : r * (lower / r) ≤ lower := Nat.mul_div_le lower r
    have hgap :
        r * ((H + 2) * uniformCoprimeModulus H) ≤
          uniformCompositeSurvivorGap H := by
      rw [uniformCompositeSurvivorGap]
      simpa [Nat.mul_assoc] using
        (Nat.mul_le_mul_right ((H + 2) * uniformCoprimeModulus H) hrBound)
    calc
      r * t ≤ r *
          (lower / r + (H + 2) * uniformCoprimeModulus H) := htUpperMul
      _ = r * (lower / r) +
          r * ((H + 2) * uniformCoprimeModulus H) := by rw [Nat.mul_add]
      _ ≤ lower + uniformCompositeSurvivorGap H :=
        Nat.add_le_add hfloor hgap
  · exact ⟨r, t, hrPrime.one_lt, htOne, rfl⟩
  · intro q hq hqProduct
    rcases (hprime q hq).dvd_mul.mp hqProduct with hqr | hqt
    · have hqEq : q = r :=
        (Nat.prime_dvd_prime_iff_eq (hprime q hq) hrPrime).mp hqr
      exact hrQ (hqEq ▸ hq)
    · exact htCoprime q hq hqt

end Erdos1212Kernel
