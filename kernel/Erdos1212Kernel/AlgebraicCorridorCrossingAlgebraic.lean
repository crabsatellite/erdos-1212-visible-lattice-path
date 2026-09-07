import Erdos1212Kernel.AlgebraicCorridorWalkInterval
import Erdos1212Kernel.AlgebraicCorridorScaleThreshold

namespace Erdos1212Kernel.CorridorScale

noncomputable section

/-! Proposition 5.2 with the exact scale body consumed.  The remaining
inputs are precisely the preceding paper producers: selected rough composite
rows, two safe support columns around every possible chronological base, and
one original bad rectangle crossing. -/

theorem bad_crossing_algebraic_point_at_scale
    {N : ℝ} (hN : 0 < N) (hscale : AlgebraicPointAtScale N)
    {lower : ℕ}
    (row : Fin (rows N) → ℕ) (hrow : Function.Injective row)
    (hrough : ∀ i, CorridorRough (z N) (row i))
    (hrowBand : ∀ i, lower ≤ row i ∧ row i < lower + band N)
    (hBandBelowZ : (band N : ℝ) < z N)
    (hrowComposite : ∀ i, Composite (row i))
    (hsupports : ∀ x : ℕ, Nat.floor (N / 2) ≤ x → ∃ west east : ℕ,
      west < x ∧ x < east ∧ west < east ∧
      x ≤ west + supportGap N ∧ east ≤ x + supportGap N ∧
      (∀ y, CorridorBandPoint lower (band N) {x := west, y := y} →
        SafePoint {x := west, y := y}) ∧
      (∀ y, CorridorBandPoint lower (band N) {x := east, y := y} →
        SafePoint {x := east, y := y}))
    {start finish : LatticePoint}
    (walk : starLatticeGraph.Walk start finish)
    (hBandTwo : 2 ≤ band N)
    (hstartBelow : start.y ≤ lower)
    (hfinishAbove : lower + band N - 1 ≤ finish.y)
    (hcoordinate : ∀ p, p ∈ walk.support → 1 < p.x ∧ 1 < p.y)
    (hboxLower : ∀ p, p ∈ walk.support → Nat.floor (N / 2) ≤ p.x)
    (hbad : ∀ p, p ∈ walk.support → CorridorBad p)
    (hbox : ∀ p, p ∈ walk.support →
      p.x ≤ Nat.floor (4 * N) ∧ p.y ≤ Nat.floor (4 * N)) :
    ∃ base : LatticePoint, base ∈ walk.support ∧
      ∃ F : MvPolynomial (Fin 2) ℤ,
        F ≠ 0 ∧ F.totalDegree ≤ degree N ∧
        MvPolynomial.eval (corridorRoot base) F = 0 ∧
        corridorPolynomialHeight F ≤ height N := by
  obtain ⟨base, point, q, hbaseMem, hspan, hpointRow,
      hqPrime, hqLarge, hqDiv, hqInj⟩ :=
    corridor_bad_crossing_localized_rows row hrow hrough hrowBand
      hBandBelowZ hrowComposite hsupports walk hBandTwo hstartBelow
      hfinishAbove hcoordinate hboxLower hbad
  have hspanRadius : ∀ i,
      Nat.dist (point i).x base.x ≤ radius N ∧
      Nat.dist (point i).y base.y ≤ radius N := by
    intro i
    have hi := hspan i
    constructor <;> unfold radius <;> omega
  obtain ⟨F, hF, hd, hz, hh⟩ :=
    corridor_localized_rows_algebraic_point hN hscale point hspanRadius q
      hqPrime hqInj hqLarge hqDiv (hbox base hbaseMem)
  exact ⟨base, hbaseMem, F, hF, hd, hz, hh⟩

end

end Erdos1212Kernel.CorridorScale
