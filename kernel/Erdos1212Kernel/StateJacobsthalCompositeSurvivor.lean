import Erdos1212Kernel.UniformCompositeSurvivor

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1000000

/-- Exact every-interval Jacobsthal contract for one literal finite prime
state.  `J` is an interval length, not an asymptotic surrogate. -/
def PrimeStateCoprimeGapBound (Q : Finset Nat) (J : Nat) : Prop :=
  0 < J ∧ ∀ lower, ∃ candidate,
    lower < candidate ∧ candidate ≤ lower + J ∧
      ∀ q ∈ Q, ¬ q ∣ candidate

theorem primeStateProduct_pos
    {Q : Finset Nat} (hprime : ∀ q ∈ Q, Nat.Prime q) :
    0 < ∏ q ∈ Q, q := by
  apply Finset.prod_pos
  intro q hq
  exact (hprime q hq).pos

/-- The elementary product-period bound supplies the nonempty exact contract.
The later Vaughan--Iwaniec producer improves only its size. -/
theorem exists_primeStateCoprimeGapBound_product
    {Q : Finset Nat} (hprime : ∀ q ∈ Q, Nat.Prime q) :
    PrimeStateCoprimeGapBound Q ((∏ q ∈ Q, q) + 1) := by
  let M := ∏ q ∈ Q, q
  have hM : 0 < M := primeStateProduct_pos hprime
  refine ⟨by positivity, fun lower => ?_⟩
  let candidate := (lower / M + 1) * M + 1
  have hdecompose : lower % M + M * (lower / M) = lower :=
    Nat.mod_add_div lower M
  have hmod : lower % M < M := Nat.mod_lt lower hM
  have hlower : lower < candidate := by
    dsimp [candidate]
    rw [Nat.add_mul, Nat.mul_comm (lower / M) M]
    omega
  have hupper : candidate ≤ lower + (M + 1) := by
    dsimp [candidate]
    rw [Nat.add_mul, Nat.mul_comm (lower / M) M]
    omega
  refine ⟨candidate, hlower, hupper, ?_⟩
  intro q hq hqCandidate
  have hqM : q ∣ M := by
    dsimp [M]
    exact Finset.dvd_prod_of_mem id hq
  have hqProduct : q ∣ (lower / M + 1) * M :=
    dvd_mul_of_dvd_right hqM _
  have hqOne : q ∣ 1 := by
    exact (Nat.dvd_add_iff_right hqProduct).mpr (by
      simpa [candidate] using hqCandidate)
  exact (hprime q hq).not_dvd_one hqOne

/-- Paper-faithful missing-prime multiplication.  A coprime candidate `t`
becomes the composite coordinate `r*t`, where `r` is a bounded prime absent
from the actual state. -/
theorem exists_primeStateCompositeSurvivor_of_coprimeGap
    {K J lower : Nat} {Q : Finset Nat}
    (hcard : Q.card ≤ K)
    (hprime : ∀ q ∈ Q, Nat.Prime q)
    (hgap : PrimeStateCoprimeGapBound Q J)
    (hlower : Nat.nth Nat.Prime K ≤ lower) :
    ∃ survivor,
      lower < survivor ∧
      survivor ≤ lower + Nat.nth Nat.Prime K * J ∧
      Composite survivor ∧
      ∀ q ∈ Q, ¬ q ∣ survivor := by
  obtain ⟨r, hrPrime, hrMissing, hrBound⟩ :=
    exists_missing_bounded_prime hcard
  have hrPos : 0 < r := hrPrime.pos
  have hrLeLower : r ≤ lower := hrBound.trans hlower
  have hlowerDiv : 1 ≤ lower / r :=
    (Nat.one_le_div_iff hrPos).2 hrLeLower
  obtain ⟨t, htLower, htUpper, htAvoids⟩ := hgap.2 (lower / r)
  have htOne : 1 < t := hlowerDiv.trans_lt htLower
  have hlowerProduct : lower < r * t := by
    have hquotient : lower < r * (lower / r + 1) := by
      have hmod : lower % r < r := Nat.mod_lt lower hrPos
      have hdecompose : lower % r + r * (lower / r) = lower :=
        Nat.mod_add_div lower r
      rw [Nat.mul_add]
      omega
    exact hquotient.trans_le (Nat.mul_le_mul_left r (by omega))
  have hupperProduct : r * t ≤
      lower + Nat.nth Nat.Prime K * J := by
    have hmul := Nat.mul_le_mul_left r htUpper
    have hfloor : r * (lower / r) ≤ lower := Nat.mul_div_le lower r
    have hgapMul : r * J ≤ Nat.nth Nat.Prime K * J :=
      Nat.mul_le_mul_right J hrBound
    calc
      r * t ≤ r * (lower / r + J) := hmul
      _ = r * (lower / r) + r * J := by rw [Nat.mul_add]
      _ ≤ lower + Nat.nth Nat.Prime K * J :=
        Nat.add_le_add hfloor hgapMul
  refine ⟨r * t, hlowerProduct, hupperProduct,
    ⟨r, t, hrPrime.one_lt, htOne, rfl⟩, ?_⟩
  intro q hq hqProduct
  have hqPrime := hprime q hq
  rcases hqPrime.dvd_mul.mp hqProduct with hqr | hqt
  · have hqEq : q = r :=
      (Nat.prime_dvd_prime_iff_eq hqPrime hrPrime).mp hqr
    exact hrMissing (hqEq ▸ hq)
  · exact htAvoids q hq hqt

end

end Erdos1212Kernel
