import Erdos1212Kernel.AlgebraicCorridorSupport
import Erdos1212Kernel.ActualPromotedComponentConfinement

namespace Erdos1212Kernel

noncomputable section

/-!
Local geometric consumer for Proposition 5.2. The use of the generic
Chebyshev star walk and its coordinate-hitting lemmas is independent of the
archived promoted-component route: the only predicate on walk vertices here
is `¬ SafePoint`.
-/

def CorridorBad (p : LatticePoint) : Prop := ¬ SafePoint p

def CorridorBandPoint (lower B : Nat) (p : LatticePoint) : Prop :=
  lower ≤ p.y ∧ p.y < lower + B

theorem corridor_bad_walk_hit_west_contradiction
    {lower B west : Nat}
    (safeWest : ∀ y, CorridorBandPoint lower B {x := west, y := y} →
      SafePoint {x := west, y := y})
    {start finish : LatticePoint} (walk : starLatticeGraph.Walk start finish)
    (hstart : west < start.x) (hfinish : finish.x ≤ west)
    (hband : ∀ p, p ∈ walk.support → CorridorBandPoint lower B p)
    (hbad : ∀ p, p ∈ walk.support → CorridorBad p) : False := by
  obtain ⟨index, hindex, hhit⟩ := starWalk_hits_x_of_crosses_below walk hstart hfinish
  have hmem := walk.getVert_mem_support index
  have hbandHit := hband _ hmem
  have hsafe := safeWest (walk.getVert index).y (by
    exact ⟨hhit ▸ hbandHit.1, hhit ▸ hbandHit.2⟩)
  have hbadHit := hbad _ hmem
  have heq : walk.getVert index = {x := west, y := (walk.getVert index).y} :=
    LatticePoint.ext hhit rfl
  rw [heq] at hbadHit
  exact hbadHit hsafe

theorem corridor_bad_walk_hit_east_contradiction
    {lower B east : Nat}
    (safeEast : ∀ y, CorridorBandPoint lower B {x := east, y := y} →
      SafePoint {x := east, y := y})
    {start finish : LatticePoint} (walk : starLatticeGraph.Walk start finish)
    (hstart : start.x < east) (hfinish : east ≤ finish.x)
    (hband : ∀ p, p ∈ walk.support → CorridorBandPoint lower B p)
    (hbad : ∀ p, p ∈ walk.support → CorridorBad p) : False := by
  obtain ⟨index, hindex, hhit⟩ := starWalk_hits_x_of_crosses_above walk hstart hfinish
  have hmem := walk.getVert_mem_support index
  have hbandHit := hband _ hmem
  have hsafe := safeEast (walk.getVert index).y (by
    exact ⟨hhit ▸ hbandHit.1, hhit ▸ hbandHit.2⟩)
  have hbadHit := hbad _ hmem
  have heq : walk.getVert index = {x := east, y := (walk.getVert index).y} :=
    LatticePoint.ext hhit rfl
  rw [heq] at hbadHit
  exact hbadHit hsafe

theorem corridor_bad_walk_horizontal_span
    {lower B west east : Nat}
    (safeWest : ∀ y, CorridorBandPoint lower B {x := west, y := y} →
      SafePoint {x := west, y := y})
    (safeEast : ∀ y, CorridorBandPoint lower B {x := east, y := y} →
      SafePoint {x := east, y := y})
    {start finish : LatticePoint} (walk : starLatticeGraph.Walk start finish)
    (hstartWest : west < start.x) (hstartEast : start.x < east)
    (hwestEast : west < east)
    (hband : ∀ p, p ∈ walk.support → CorridorBandPoint lower B p)
    (hbad : ∀ p, p ∈ walk.support → CorridorBad p) :
    ∀ i, i ≤ walk.length → west < (walk.getVert i).x ∧
      (walk.getVert i).x < east := by
  intro i hi
  have hmem := walk.getVert_mem_support i
  constructor
  · by_contra hnot
    have hle : (walk.getVert i).x ≤ west := by omega
    have hmem := walk.getVert_mem_support i
    exact corridor_bad_walk_hit_west_contradiction safeWest
      (walk.takeUntil (walk.getVert i) hmem) hstartWest hle
      (fun p hp => hband p ((walk.support_takeUntil_subset hmem) hp))
      (fun p hp => hbad p ((walk.support_takeUntil_subset hmem) hp))
  · by_contra hnot
    have hge : east ≤ (walk.getVert i).x := by omega
    have hmem := walk.getVert_mem_support i
    exact corridor_bad_walk_hit_east_contradiction safeEast
      (walk.takeUntil (walk.getVert i) hmem) hstartEast hge
      (fun p hp => hband p ((walk.support_takeUntil_subset hmem) hp))
      (fun p hp => hbad p ((walk.support_takeUntil_subset hmem) hp))

theorem corridor_bad_walk_offset_bound_general
    {lower bandWidth west east horizontalGap : Nat}
    (safeWest : ∀ y, CorridorBandPoint lower bandWidth {x := west, y := y} →
      SafePoint {x := west, y := y})
    (safeEast : ∀ y, CorridorBandPoint lower bandWidth {x := east, y := y} →
      SafePoint {x := east, y := y})
    {start finish : LatticePoint} (walk : starLatticeGraph.Walk start finish)
    (hstartWest : west < start.x) (hstartEast : start.x < east)
    (hwestEast : west < east)
    (hband : ∀ p, p ∈ walk.support → CorridorBandPoint lower bandWidth p)
    (hbad : ∀ p, p ∈ walk.support → CorridorBad p)
    (hwestNear : start.x ≤ west + horizontalGap)
    (heastNear : east ≤ start.x + horizontalGap) :
    ∀ i, i ≤ walk.length →
      Nat.dist (walk.getVert i).x start.x ≤ 2 * horizontalGap := by
  intro i hi
  obtain ⟨hwest, heast⟩ := corridor_bad_walk_horizontal_span
    safeWest safeEast walk hstartWest hstartEast hwestEast hband hbad i hi
  rcases le_total (walk.getVert i).x start.x with hle | hge
  · rw [Nat.dist_eq_sub_of_le hle]
    have : (walk.getVert i).x ≥ west + 1 := by omega
    omega
  · rw [Nat.dist_eq_sub_of_le_right hge]
    have : (walk.getVert i).x ≤ east - 1 := by omega
    omega

theorem corridor_bad_walk_offset_bound
    {lower B west east : Nat}
    (safeWest : ∀ y, CorridorBandPoint lower B {x := west, y := y} →
      SafePoint {x := west, y := y})
    (safeEast : ∀ y, CorridorBandPoint lower B {x := east, y := y} →
      SafePoint {x := east, y := y})
    {start finish : LatticePoint} (walk : starLatticeGraph.Walk start finish)
    (hstartWest : west < start.x) (hstartEast : start.x < east)
    (hwestEast : west < east)
    (hband : ∀ p, p ∈ walk.support → CorridorBandPoint lower B p)
    (hbad : ∀ p, p ∈ walk.support → CorridorBad p)
    (hwestNear : start.x ≤ west + B) (heastNear : east ≤ start.x + B) :
    ∀ i, i ≤ walk.length →
      Nat.dist (walk.getVert i).x start.x ≤ 2 * B := by
  intro i hi
  obtain ⟨hwest, heast⟩ := corridor_bad_walk_horizontal_span
    safeWest safeEast walk hstartWest hstartEast hwestEast hband hbad i hi
  rcases le_total (walk.getVert i).x start.x with hle | hge
  · rw [Nat.dist_eq_sub_of_le hle]
    have : (walk.getVert i).x ≥ west + 1 := by omega
    omega
  · rw [Nat.dist_eq_sub_of_le_right hge]
    have : (walk.getVert i).x ≤ east - 1 := by omega
    omega

theorem corridor_bad_walk_support_offset_bound
    {lower bandWidth west east horizontalGap : Nat}
    (safeWest : ∀ y, CorridorBandPoint lower bandWidth {x := west, y := y} →
      SafePoint {x := west, y := y})
    (safeEast : ∀ y, CorridorBandPoint lower bandWidth {x := east, y := y} →
      SafePoint {x := east, y := y})
    {start finish : LatticePoint} (walk : starLatticeGraph.Walk start finish)
    (hstartWest : west < start.x) (hstartEast : start.x < east)
    (hwestEast : west < east)
    (hband : ∀ p, p ∈ walk.support → CorridorBandPoint lower bandWidth p)
    (hbad : ∀ p, p ∈ walk.support → CorridorBad p)
    (hwestNear : start.x ≤ west + horizontalGap)
    (heastNear : east ≤ start.x + horizontalGap) :
    ∀ p, p ∈ walk.support → Nat.dist p.x start.x ≤ 2 * horizontalGap := by
  intro p hp
  obtain ⟨k, hk, hkp⟩ := List.mem_iff_getElem.mp hp
  have hklen : k ≤ walk.length := by
    have hklt : k < walk.support.length := hk
    simpa [SimpleGraph.Walk.length_support] using hklt
  have hget : walk.getVert k = p := by
    rw [walk.getVert_eq_support_getElem hklen]
    exact hkp
  rw [← hget]
  exact corridor_bad_walk_offset_bound_general safeWest safeEast walk hstartWest
    hstartEast hwestEast hband hbad hwestNear heastNear k hklen

theorem corridor_bad_walk_support_band_distance
    {lower B : Nat} {start finish p : LatticePoint}
    (walk : starLatticeGraph.Walk start finish)
    (hband : ∀ q, q ∈ walk.support → CorridorBandPoint lower B q)
    (hp : p ∈ walk.support) :
    Nat.dist p.y start.y ≤ B := by
  have hpBand := hband p hp
  have hstartBand := hband start (by simp)
  rcases hpBand with ⟨hpLower, hpUpper⟩
  rcases hstartBand with ⟨hstartLower, hstartUpper⟩
  rcases le_total p.y start.y with hle | hge
  · rw [Nat.dist_eq_sub_of_le hle]
    omega
  · rw [Nat.dist_eq_sub_of_le_right hge]
    omega

theorem corridor_bad_walk_support_span
    {lower bandWidth west east horizontalGap : Nat}
    (safeWest : ∀ y,
      CorridorBandPoint lower bandWidth {x := west, y := y} →
        SafePoint {x := west, y := y})
    (safeEast : ∀ y,
      CorridorBandPoint lower bandWidth {x := east, y := y} →
        SafePoint {x := east, y := y})
    {start finish : LatticePoint} (walk : starLatticeGraph.Walk start finish)
    (hstartWest : west < start.x) (hstartEast : start.x < east)
    (hwestEast : west < east)
    (hband : ∀ p, p ∈ walk.support → CorridorBandPoint lower bandWidth p)
    (hbad : ∀ p, p ∈ walk.support → CorridorBad p)
    (hwestNear : start.x ≤ west + horizontalGap)
    (heastNear : east ≤ start.x + horizontalGap)
    {p : LatticePoint} (hp : p ∈ walk.support) :
    Nat.dist p.x start.x ≤ 2 * horizontalGap ∧
      Nat.dist p.y start.y ≤ bandWidth := by
  constructor
  · exact corridor_bad_walk_support_offset_bound safeWest safeEast walk
      hstartWest hstartEast hwestEast hband hbad hwestNear heastNear p hp
  · exact corridor_bad_walk_support_band_distance walk hband hp

end

end Erdos1212Kernel
