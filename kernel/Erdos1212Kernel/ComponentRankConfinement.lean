import Erdos1212Kernel.ComponentPathCrossing

namespace Erdos1212Kernel

/-!
# Uniform geometry at fixed exact boundary rank

For exact rank `K`, the active boundary-label set has at most `K + 5`
elements.  The uniform composite-survivor theorem supplies one horizontal and
one vertical barrier on each side of the root, at a distance depending only
on `K`.  Coordinate crossing and barrier disjointness then confine the entire
actual safe component to a fixed box around its root.
-/

noncomputable def componentRankGap (K : Nat) : Nat :=
  uniformCompositeSurvivorGap (K + 5)

noncomputable def componentRankThreshold (K : Nat) : Nat :=
  Nat.nth Nat.Prime (K + 5) + componentRankGap K + 1

theorem safeComponent_confined_of_exact_rank
    {start finish : LatticePoint}
    {hbounded : ¬ ArbitrarilyFarSafeReachable start}
    {K : Nat}
    (hrank : exactBoundaryLabelRank start = K)
    (hxLarge : componentRankThreshold K ≤ start.x)
    (hyLarge : componentRankThreshold K ≤ start.y)
    (hfinish : finish ∈ safeComponent start) :
    finish.x ≤ start.x + componentRankGap K ∧
      start.x ≤ finish.x + componentRankGap K ∧
      finish.y ≤ start.y + componentRankGap K ∧
      start.y ≤ finish.y + componentRankGap K := by
  let H := K + 5
  let gap := componentRankGap K
  let Q := finiteSafeComponentActiveLabels start hbounded
  have hcard : Q.card ≤ H := by
    dsimp [Q, H]
    simpa [hrank] using
      finiteSafeComponentActiveLabels_card_le_rank_add_five start hbounded
  have hprime : ∀ q ∈ Q, Nat.Prime q := by
    intro q hq
    exact finiteSafeComponentActiveLabel_prime hq
  have hnthX : Nat.nth Nat.Prime H ≤ start.x := by
    dsimp [componentRankThreshold, H, gap] at hxLarge ⊢
    omega
  have hnthY : Nat.nth Nat.Prime H ≤ start.y := by
    dsimp [componentRankThreshold, H, gap] at hyLarge ⊢
    omega

  obtain ⟨xUpper, hxUpperGt, hxUpperLe, hxUpperComposite,
      hxUpperAvoids⟩ :=
    exists_uniformCompositeSurvivor
      (H := H) (lower := start.x) (Q := Q) hcard hprime hnthX
  have hxUpperDisjoint :
      ∀ y, verticalLinePoint xUpper y ∉ safeComponent start :=
    verticalCompositeBarrier_disjoint_component hxUpperComposite hxUpperAvoids
  have hfinishXBelow : finish.x < xUpper := by
    by_contra hnotBelow
    have hcross : xUpper ≤ finish.x := Nat.le_of_not_gt hnotBelow
    obtain ⟨y, hy⟩ :=
      safeComponent_hits_vertical_of_crosses_above hfinish hxUpperGt hcross
    exact hxUpperDisjoint y hy
  have hfinishXUpper : finish.x ≤ start.x + gap := by
    change finish.x ≤ start.x + componentRankGap K
    change xUpper ≤ start.x + componentRankGap K at hxUpperLe
    omega

  let xLowerBase := start.x - gap - 1
  have hnthXLower : Nat.nth Nat.Prime H ≤ xLowerBase := by
    dsimp [xLowerBase, componentRankThreshold, H, gap] at hxLarge ⊢
    omega
  obtain ⟨xLower, hxLowerGt, hxLowerLe, hxLowerComposite,
      hxLowerAvoids⟩ :=
    exists_uniformCompositeSurvivor
      (H := H) (lower := xLowerBase) (Q := Q) hcard hprime hnthXLower
  have hxLowerLtStart : xLower < start.x := by
    change xLower ≤ xLowerBase + componentRankGap K at hxLowerLe
    dsimp [xLowerBase, componentRankThreshold, gap] at hxLarge ⊢
    omega
  have hxLowerDisjoint :
      ∀ y, verticalLinePoint xLower y ∉ safeComponent start :=
    verticalCompositeBarrier_disjoint_component hxLowerComposite hxLowerAvoids
  have hfinishXAbove : xLower < finish.x := by
    by_contra hnotAbove
    have hcross : finish.x ≤ xLower := Nat.le_of_not_gt hnotAbove
    obtain ⟨y, hy⟩ :=
      safeComponent_hits_vertical_of_crosses_below hfinish hxLowerLtStart hcross
    exact hxLowerDisjoint y hy
  have hfinishXLower : start.x ≤ finish.x + gap := by
    dsimp [xLowerBase, componentRankThreshold, gap] at hxLarge hxLowerGt ⊢
    omega

  obtain ⟨yUpper, hyUpperGt, hyUpperLe, hyUpperComposite,
      hyUpperAvoids⟩ :=
    exists_uniformCompositeSurvivor
      (H := H) (lower := start.y) (Q := Q) hcard hprime hnthY
  have hyUpperDisjoint :
      ∀ x, horizontalLinePoint x yUpper ∉ safeComponent start :=
    horizontalCompositeBarrier_disjoint_component hyUpperComposite hyUpperAvoids
  have hfinishYBelow : finish.y < yUpper := by
    by_contra hnotBelow
    have hcross : yUpper ≤ finish.y := Nat.le_of_not_gt hnotBelow
    obtain ⟨x, hx⟩ :=
      safeComponent_hits_horizontal_of_crosses_above hfinish hyUpperGt hcross
    exact hyUpperDisjoint x hx
  have hfinishYUpper : finish.y ≤ start.y + gap := by
    change finish.y ≤ start.y + componentRankGap K
    change yUpper ≤ start.y + componentRankGap K at hyUpperLe
    omega

  let yLowerBase := start.y - gap - 1
  have hnthYLower : Nat.nth Nat.Prime H ≤ yLowerBase := by
    dsimp [yLowerBase, componentRankThreshold, H, gap] at hyLarge ⊢
    omega
  obtain ⟨yLower, hyLowerGt, hyLowerLe, hyLowerComposite,
      hyLowerAvoids⟩ :=
    exists_uniformCompositeSurvivor
      (H := H) (lower := yLowerBase) (Q := Q) hcard hprime hnthYLower
  have hyLowerLtStart : yLower < start.y := by
    change yLower ≤ yLowerBase + componentRankGap K at hyLowerLe
    dsimp [yLowerBase, componentRankThreshold, gap] at hyLarge ⊢
    omega
  have hyLowerDisjoint :
      ∀ x, horizontalLinePoint x yLower ∉ safeComponent start :=
    horizontalCompositeBarrier_disjoint_component hyLowerComposite hyLowerAvoids
  have hfinishYAbove : yLower < finish.y := by
    by_contra hnotAbove
    have hcross : finish.y ≤ yLower := Nat.le_of_not_gt hnotAbove
    obtain ⟨x, hx⟩ :=
      safeComponent_hits_horizontal_of_crosses_below hfinish hyLowerLtStart hcross
    exact hyLowerDisjoint x hx
  have hfinishYLower : start.y ≤ finish.y + gap := by
    dsimp [yLowerBase, componentRankThreshold, gap] at hyLarge hyLowerGt ⊢
    omega

  exact ⟨hfinishXUpper, hfinishXLower, hfinishYUpper, hfinishYLower⟩

end Erdos1212Kernel
