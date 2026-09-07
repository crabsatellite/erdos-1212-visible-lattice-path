import Erdos1212Kernel.AlgebraicCorridorBandState
import Erdos1212Kernel.AlgebraicCorridorLocalizedCrossing

namespace Erdos1212Kernel

noncomputable section

/-! Exact two-sided support-column producer for the paper's finite band. -/

theorem exists_vaughan_safe_support_columns
    {bandLower B x K J D : ℕ}
    (hbandLower : 1 < bandLower)
    (hcard : (corridorBandPrimeFactors bandLower B).card ≤ K)
    (hgap : PrimeStateCoprimeGapBound
      (corridorBandPrimeFactors bandLower B) J)
    (hleft : Nat.nth Nat.Prime K + Nat.nth Nat.Prime K * J + 2 ≤ x)
    (hD : Nat.nth Nat.Prime K * J + 1 ≤ D) :
    ∃ west east : ℕ,
      west < x ∧ x < east ∧ west < east ∧
      x ≤ west + D ∧ east ≤ x + D ∧
      (∀ y, CorridorBandPoint bandLower B {x := west, y := y} →
        SafePoint {x := west, y := y}) ∧
      (∀ y, CorridorBandPoint bandLower B {x := east, y := y} →
        SafePoint {x := east, y := y}) := by
  let Q := corridorBandPrimeFactors bandLower B
  let gap := Nat.nth Nat.Prime K * J
  let leftBase := x - gap - 1
  have hprime : ∀ q ∈ Q, q.Prime := by
    intro q hq
    exact prime_of_mem_corridorBandPrimeFactors hq
  have hstate : ∀ y, bandLower ≤ y → y < bandLower + B →
      ∀ p, p.Prime → p ∣ y → p ∈ Q := by
    exact corridorBandPrimeFactors_state (by omega)
  have hnthPrime : (Nat.nth Nat.Prime K).Prime := Nat.prime_nth_prime K
  have hleftK : Nat.nth Nat.Prime K ≤ leftBase := by
    dsimp [leftBase, gap]
    omega
  have hleftPositive : 1 < leftBase := by
    have hnthTwo : 2 ≤ Nat.nth Nat.Prime K := by
      have := hnthPrime.one_lt
      omega
    dsimp [leftBase, gap]
    omega
  have hxK : Nat.nth Nat.Prime K ≤ x := by
    omega
  have hxPositive : 1 < x := by
    have hnthTwo : 2 ≤ Nat.nth Nat.Prime K := by
      have := hnthPrime.one_lt
      omega
    omega
  obtain ⟨west, hwestGt, hwestLe, hwestComp, hwestAvoid, hwestSafe⟩ :=
    vaughan_safe_segment_of_prime_state (Q := Q) (K := K)
      (xLower := leftBase) (bandLower := bandLower) (J := J) (B := B)
      hcard hprime hgap hleftK hleftPositive hbandLower hstate
  obtain ⟨east, heastGt, heastLe, heastComp, heastAvoid, heastSafe⟩ :=
    vaughan_safe_segment_of_prime_state (Q := Q) (K := K)
      (xLower := x) (bandLower := bandLower) (J := J) (B := B)
      hcard hprime hgap hxK hxPositive hbandLower hstate
  have hwest : west < x := by
    dsimp [leftBase, gap] at hwestLe
    omega
  have hwestNear : x ≤ west + D := by
    dsimp [leftBase, gap] at hwestGt hD
    omega
  have heastNear : east ≤ x + D := by
    omega
  have safeWest : ∀ y,
      CorridorBandPoint bandLower B {x := west, y := y} →
        SafePoint {x := west, y := y} := by
    intro y hy
    rcases hy with ⟨hyLower, hyUpper⟩
    change bandLower ≤ y at hyLower
    change y < bandLower + B at hyUpper
    have hi : y - bandLower < B := by omega
    have hyEq : bandLower + (y - bandLower) = y := by omega
    simpa [hyEq] using hwestSafe (y - bandLower) hi
  have safeEast : ∀ y,
      CorridorBandPoint bandLower B {x := east, y := y} →
        SafePoint {x := east, y := y} := by
    intro y hy
    rcases hy with ⟨hyLower, hyUpper⟩
    change bandLower ≤ y at hyLower
    change y < bandLower + B at hyUpper
    have hi : y - bandLower < B := by omega
    have hyEq : bandLower + (y - bandLower) = y := by omega
    simpa [hyEq] using heastSafe (y - bandLower) hi
  exact ⟨west, east, hwest, heastGt, hwest.trans heastGt,
    hwestNear, heastNear, safeWest, safeEast⟩

end

end Erdos1212Kernel
