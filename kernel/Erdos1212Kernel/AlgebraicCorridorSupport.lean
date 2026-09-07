import Erdos1212Kernel.VaughanPolynomialGapConsumer
import Erdos1212Kernel.Target

namespace Erdos1212Kernel

noncomputable section

/-!
Literal safety of a composite support column.  This is the consumer needed
to turn the Vaughan missing-prime survivor into an entire safe segment over a
band whose prime divisors are contained in the actual state Q.
-/

theorem safePoint_of_composite_coprime {v y : Nat}
    (hv : 1 < v) (hy : 1 < y) (hcomp : Composite v)
    (hcop : Nat.Coprime v y) :
    SafePoint {x := v, y := y} := by
  exact ⟨hv, hy, hcop, Or.inl hcomp⟩

theorem corridor_coprime_of_state_avoids
    {Q : Finset Nat} {v y : Nat}
    (havoid : ∀ q ∈ Q, ¬ q ∣ v)
    (hstate : ∀ p, p.Prime → p ∣ y → p ∈ Q) :
    Nat.Coprime v y := by
  rw [← not_not (a := v.Coprime y), Nat.Prime.not_coprime_iff_dvd]
  push Not
  intro p hp hpv hpy
  exact havoid p (hstate p hp hpy) hpv

theorem safePoint_on_composite_support_column
    {Q : Finset Nat} {v lower B y : Nat}
    (hv : 1 < v) (hcomp : Composite v)
    (havoid : ∀ q ∈ Q, ¬ q ∣ v)
    (hlower : 1 < lower)
    (hyband : lower ≤ y ∧ y < lower + B)
    (hstate : ∀ p, p.Prime → p ∣ y → p ∈ Q) :
    SafePoint {x := v, y := y} := by
  apply safePoint_of_composite_coprime hv (by omega) hcomp
  exact corridor_coprime_of_state_avoids havoid hstate

theorem safe_segment_on_composite_support_column
    {Q : Finset Nat} {v lower B length : Nat}
    (hv : 1 < v) (hcomp : Composite v)
    (havoid : ∀ q ∈ Q, ¬ q ∣ v)
    (hlower : 1 < lower)
    (hstate : ∀ y, lower ≤ y → y < lower + B →
      ∀ p, p.Prime → p ∣ y → p ∈ Q)
    (hsegment : length < B) :
    ∀ i, i ≤ length →
      SafePoint {x := v, y := lower + i} := by
  intro i hi
  have hiB : i < B := lt_of_le_of_lt hi hsegment
  apply safePoint_on_composite_support_column hv hcomp havoid hlower
  · have hiB : i < B := lt_of_le_of_lt hi hsegment
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hiB _⟩
  · exact hstate (lower + i) (Nat.le_add_right _ _) (Nat.add_lt_add_left hiB _)

theorem vaughan_safe_segment_of_prime_state
    {Q : Finset Nat} {K xLower bandLower J B : Nat}
    (hcard : Q.card ≤ K) (hprime : ∀ q ∈ Q, q.Prime)
    (hgap : PrimeStateCoprimeGapBound Q J)
    (hK : Nat.nth Nat.Prime K ≤ xLower)
    (hxLower : 1 < xLower)
    (hbandLower : 1 < bandLower)
    (hstate : ∀ y, bandLower ≤ y → y < bandLower + B →
      ∀ p, p.Prime → p ∣ y → p ∈ Q) :
    ∃ v, xLower < v ∧ v ≤ xLower + Nat.nth Nat.Prime K * J ∧
      Composite v ∧ (∀ q ∈ Q, ¬q ∣ v) ∧
      (∀ i, i < B → SafePoint {x := v, y := bandLower + i}) := by
  obtain ⟨v, hvgt, hvle, hvcomp, hvavoid⟩ :=
    exists_primeStateCompositeSurvivor_of_coprimeGap
      hcard hprime hgap hK
  refine ⟨v, hvgt, hvle, hvcomp, hvavoid, ?_⟩
  intro i hi
  apply safePoint_on_composite_support_column
    (by omega) hvcomp hvavoid hbandLower
  · exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hi _⟩
  · exact hstate (bandLower + i) (Nat.le_add_right _ _) (Nat.add_lt_add_left hi _)

end

end Erdos1212Kernel
