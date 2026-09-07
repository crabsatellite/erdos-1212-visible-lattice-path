import Erdos1212Kernel.VaughanPolynomialPrimeStateGap

namespace Erdos1212Kernel

noncomputable section

private theorem exists_vaughanPolynomial_gapParameters :
    ∃ parameters : Real × Real,
      192 ≤ parameters.1 ∧ 1 < parameters.2 ∧ ∀ (Q : Finset Nat),
        (∀ q ∈ Q, Nat.Prime q) →
        let rank := vaughanEffectiveRank parameters.1 parameters.2 Q
        let J := vaughanIntervalLength parameters.1 rank
        PrimeStateCoprimeGapBound Q J ∧
          (J : Real) ≤ Real.exp (2 * parameters.1) * (rank : Real) ^ 2 *
            Real.log (2 * (rank : Real)) ^ 4 := by
  obtain ⟨A, Y, hA, hY, hbound⟩ := exists_vaughanPolynomial_primeStateCoprimeGapBound
  exact ⟨(A, Y), hA, hY, hbound⟩

noncomputable def vaughanPolynomialGapParameters : Real × Real :=
  Classical.choose exists_vaughanPolynomial_gapParameters

def vaughanPolynomialPrimeStateGap (Q : Finset Nat) : Nat :=
  vaughanIntervalLength vaughanPolynomialGapParameters.1
    (vaughanEffectiveRank vaughanPolynomialGapParameters.1
      vaughanPolynomialGapParameters.2 Q)

theorem vaughanPolynomialGapParameters_spec :
    192 ≤ vaughanPolynomialGapParameters.1 ∧
      1 < vaughanPolynomialGapParameters.2 ∧ ∀ (Q : Finset Nat),
        (∀ q ∈ Q, Nat.Prime q) →
        let rank := vaughanEffectiveRank vaughanPolynomialGapParameters.1
          vaughanPolynomialGapParameters.2 Q
        let J := vaughanPolynomialPrimeStateGap Q
        PrimeStateCoprimeGapBound Q J ∧
          (J : Real) ≤ Real.exp (2 * vaughanPolynomialGapParameters.1) *
            (rank : Real) ^ 2 * Real.log (2 * (rank : Real)) ^ 4 := by
  simpa only [vaughanPolynomialPrimeStateGap] using
    Classical.choose_spec exists_vaughanPolynomial_gapParameters

theorem vaughanPolynomial_primeStateCoprimeGapBound
    (Q : Finset Nat) (hprime : ∀ q ∈ Q, Nat.Prime q) :
    PrimeStateCoprimeGapBound Q (vaughanPolynomialPrimeStateGap Q) :=
  (vaughanPolynomialGapParameters_spec.2.2 Q hprime).1

theorem vaughanPolynomialPrimeStateGap_upper
    (Q : Finset Nat) (hprime : ∀ q ∈ Q, Nat.Prime q) :
    (vaughanPolynomialPrimeStateGap Q : Real) ≤
      Real.exp (2 * vaughanPolynomialGapParameters.1) *
        (vaughanEffectiveRank vaughanPolynomialGapParameters.1
          vaughanPolynomialGapParameters.2 Q : Real) ^ 2 *
        Real.log (2 * (vaughanEffectiveRank vaughanPolynomialGapParameters.1
          vaughanPolynomialGapParameters.2 Q : Real)) ^ 4 :=
  (vaughanPolynomialGapParameters_spec.2.2 Q hprime).2

/-- The named polynomial gap is consumed by the existing literal
missing-prime multiplication, yielding the composite survivor used by
the two-pin geometry. -/
theorem exists_primeStateCompositeSurvivor_of_vaughanPolynomial
    {K lower : Nat} {Q : Finset Nat}
    (hcard : Q.card ≤ K) (hprime : ∀ q ∈ Q, Nat.Prime q)
    (hlower : Nat.nth Nat.Prime K ≤ lower) :
    ∃ survivor,
      lower < survivor ∧
      survivor ≤ lower + Nat.nth Nat.Prime K * vaughanPolynomialPrimeStateGap Q ∧
      Composite survivor ∧
      ∀ q ∈ Q, ¬q ∣ survivor :=
  exists_primeStateCompositeSurvivor_of_coprimeGap hcard hprime
    (vaughanPolynomial_primeStateCoprimeGapBound Q hprime) hlower

end

end Erdos1212Kernel
