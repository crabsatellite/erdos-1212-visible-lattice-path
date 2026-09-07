import Erdos1212Kernel.VaughanPolynomialGapConsumer
import Erdos1212Kernel.ActualPromotedComponentConfinement

namespace Erdos1212Kernel

noncomputable section

def actualPromotedCompositeRadius (H J : Nat) : Nat :=
  Nat.nth Nat.Prime H * J

/-- The literal four-barrier geometry, parameterized only by the exact
prime-state coprime-gap contract that supplies its composite lines. -/
theorem exists_actualPromotedStarComponent_barrier_box_of_gap
    {R : Finset Nat} {anchor : LatticePoint} {H J : Nat}
    (hcard : R.card ≤ H)
    (hprime : ∀ q ∈ R, Nat.Prime q)
    (hgap : PrimeStateCoprimeGapBound R J)
    (hxLarge : Nat.nth Nat.Prime H + actualPromotedCompositeRadius H J + 1 ≤ anchor.x)
    (hyLarge : Nat.nth Nat.Prime H + actualPromotedCompositeRadius H J + 1 ≤ anchor.y) :
    ∃ west east south north,
      west < anchor.x ∧ anchor.x < east ∧
      south < anchor.y ∧ anchor.y < north ∧
      anchor.x ≤ west + actualPromotedCompositeRadius H J ∧
      east ≤ anchor.x + actualPromotedCompositeRadius H J ∧
      anchor.y ≤ south + actualPromotedCompositeRadius H J ∧
      north ≤ anchor.y + actualPromotedCompositeRadius H J ∧
      (∀ finish, ActualPromotedStarReachable R anchor finish →
        west < finish.x ∧ finish.x < east ∧
        south < finish.y ∧ finish.y < north) := by
  let radius := actualPromotedCompositeRadius H J
  let lowerX := anchor.x - radius - 1
  let lowerY := anchor.y - radius - 1
  have hnthX : Nat.nth Nat.Prime H ≤ lowerX := by
    dsimp [lowerX, radius] at hxLarge ⊢
    omega
  have hnthY : Nat.nth Nat.Prime H ≤ lowerY := by
    dsimp [lowerY, radius] at hyLarge ⊢
    omega
  have hnthAnchorX : Nat.nth Nat.Prime H ≤ anchor.x := by omega
  have hnthAnchorY : Nat.nth Nat.Prime H ≤ anchor.y := by omega
  obtain ⟨east, heastGt, heastLe, heastComposite, heastAvoids⟩ :=
    exists_primeStateCompositeSurvivor_of_coprimeGap hcard hprime hgap hnthAnchorX
  obtain ⟨west, hwestGt, hwestLe, hwestComposite, hwestAvoids⟩ :=
    exists_primeStateCompositeSurvivor_of_coprimeGap hcard hprime hgap hnthX
  obtain ⟨north, hnorthGt, hnorthLe, hnorthComposite, hnorthAvoids⟩ :=
    exists_primeStateCompositeSurvivor_of_coprimeGap hcard hprime hgap hnthAnchorY
  obtain ⟨south, hsouthGt, hsouthLe, hsouthComposite, hsouthAvoids⟩ :=
    exists_primeStateCompositeSurvivor_of_coprimeGap hcard hprime hgap hnthY
  have hwestLt : west < anchor.x := by
    change west ≤ lowerX + radius at hwestLe
    dsimp [lowerX, radius] at hwestLe hxLarge
    omega
  have hsouthLt : south < anchor.y := by
    change south ≤ lowerY + radius at hsouthLe
    dsimp [lowerY, radius] at hsouthLe hyLarge
    omega
  have hwestNear : anchor.x ≤ west + radius := by
    dsimp [lowerX, radius] at hwestGt hxLarge ⊢
    omega
  have hsouthNear : anchor.y ≤ south + radius := by
    dsimp [lowerY, radius] at hsouthGt hyLarge ⊢
    omega
  refine ⟨west, east, south, north,
    hwestLt, heastGt, hsouthLt, hnorthGt,
    hwestNear, heastLe, hsouthNear, hnorthLe, ?_⟩
  intro finish hreachable
  obtain ⟨walk, hwalkPromoted⟩ := hreachable
  have hfinishWest : west < finish.x := by
    by_contra hnot
    have hfinish : finish.x ≤ west := by omega
    obtain ⟨index, _hindex, hhit⟩ :=
      starWalk_hits_x_of_crosses_below walk hwestLt hfinish
    have hpromoted := hwalkPromoted _ (walk.getVert_mem_support index)
    have heq : walk.getVert index = verticalLinePoint west (walk.getVert index).y :=
      LatticePoint.ext hhit rfl
    rw [heq] at hpromoted
    exact actualPromotedUnsafe_not_on_vertical hwestComposite hwestAvoids hpromoted
  have hfinishEast : finish.x < east := by
    by_contra hnot
    have hfinish : east ≤ finish.x := by omega
    obtain ⟨index, _hindex, hhit⟩ :=
      starWalk_hits_x_of_crosses_above walk heastGt hfinish
    have hpromoted := hwalkPromoted _ (walk.getVert_mem_support index)
    have heq : walk.getVert index = verticalLinePoint east (walk.getVert index).y :=
      LatticePoint.ext hhit rfl
    rw [heq] at hpromoted
    exact actualPromotedUnsafe_not_on_vertical heastComposite heastAvoids hpromoted
  have hfinishSouth : south < finish.y := by
    by_contra hnot
    have hfinish : finish.y ≤ south := by omega
    obtain ⟨index, _hindex, hhit⟩ :=
      starWalk_hits_y_of_crosses_below walk hsouthLt hfinish
    have hpromoted := hwalkPromoted _ (walk.getVert_mem_support index)
    have heq : walk.getVert index = horizontalLinePoint (walk.getVert index).x south :=
      LatticePoint.ext rfl hhit
    rw [heq] at hpromoted
    exact actualPromotedUnsafe_not_on_horizontal hsouthComposite hsouthAvoids hpromoted
  have hfinishNorth : finish.y < north := by
    by_contra hnot
    have hfinish : north ≤ finish.y := by omega
    obtain ⟨index, _hindex, hhit⟩ :=
      starWalk_hits_y_of_crosses_above walk hnorthGt hfinish
    have hpromoted := hwalkPromoted _ (walk.getVert_mem_support index)
    have heq : walk.getVert index = horizontalLinePoint (walk.getVert index).x north :=
      LatticePoint.ext rfl hhit
    rw [heq] at hpromoted
    exact actualPromotedUnsafe_not_on_horizontal hnorthComposite hnorthAvoids hpromoted
  exact ⟨hfinishWest, hfinishEast, hfinishSouth, hfinishNorth⟩

theorem actualPromotedStarReachable_mem_latticeWindow_of_gap
    {R : Finset Nat} {anchor finish : LatticePoint} {H J : Nat}
    (hcard : R.card ≤ H) (hprime : ∀ q ∈ R, Nat.Prime q)
    (hgap : PrimeStateCoprimeGapBound R J)
    (hxLarge : Nat.nth Nat.Prime H + actualPromotedCompositeRadius H J + 1 ≤ anchor.x)
    (hyLarge : Nat.nth Nat.Prime H + actualPromotedCompositeRadius H J + 1 ≤ anchor.y)
    (hreachable : ActualPromotedStarReachable R anchor finish) :
    finish ∈ latticeWindow anchor (actualPromotedCompositeRadius H J) := by
  obtain ⟨west, east, south, north,
      hwest, heast, hsouth, hnorth,
      hwestNear, heastNear, hsouthNear, hnorthNear, hbox⟩ :=
    exists_actualPromotedStarComponent_barrier_box_of_gap
      hcard hprime hgap hxLarge hyLarge
  have hfinish := hbox finish hreachable
  apply mem_latticeWindow.mpr
  exact ⟨by omega, by omega, by omega, by omega⟩

def vaughanPromotedComponentRadius (H : Nat) (R : Finset Nat) : Nat :=
  actualPromotedCompositeRadius H (vaughanPolynomialPrimeStateGap R)

theorem actualPromotedStarReachable_mem_vaughanWindow
    {R : Finset Nat} {anchor finish : LatticePoint} {H : Nat}
    (hcard : R.card ≤ H) (hprime : ∀ q ∈ R, Nat.Prime q)
    (hxLarge : Nat.nth Nat.Prime H + vaughanPromotedComponentRadius H R + 1 ≤ anchor.x)
    (hyLarge : Nat.nth Nat.Prime H + vaughanPromotedComponentRadius H R + 1 ≤ anchor.y)
    (hreachable : ActualPromotedStarReachable R anchor finish) :
    finish ∈ latticeWindow anchor (vaughanPromotedComponentRadius H R) := by
  exact actualPromotedStarReachable_mem_latticeWindow_of_gap hcard hprime
    (vaughanPolynomial_primeStateCoprimeGapBound R hprime) hxLarge hyLarge hreachable

theorem vaughanPromotedComponent_window_card_le (anchor : LatticePoint) (H : Nat)
    (R : Finset Nat) :
    (latticeWindow anchor (vaughanPromotedComponentRadius H R)).card ≤
      (2 * vaughanPromotedComponentRadius H R + 1) ^ 2 :=
  latticeWindow_card_le anchor _

end

end Erdos1212Kernel
