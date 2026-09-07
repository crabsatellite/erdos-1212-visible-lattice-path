import Erdos1212Kernel.AlgebraicCorridorLocalizedWitness

namespace Erdos1212Kernel

noncomputable section

/-! Literal finite subwalks between two chronological indices.  This is the
path object required by the first/last band-hit paragraph of Lemma 4.2; it
does not replace that paragraph by an arbitrary walk with matching endpoints. -/

def corridorWalkInterval
    {V : Type*} {G : SimpleGraph V} {start finish : V}
    (walk : G.Walk start finish) (i j : ℕ) (hij : i ≤ j) :
    G.Walk (walk.getVert i) (walk.getVert j) :=
  ((walk.drop i).take (j - i)).copy rfl (by
    rw [SimpleGraph.Walk.drop_getVert]
    congr
    omega)

theorem corridorWalkInterval_isSubwalk
    {V : Type*} {G : SimpleGraph V} {start finish : V}
    (walk : G.Walk start finish) (i j : ℕ) (hij : i ≤ j) :
    (corridorWalkInterval walk i j hij).IsSubwalk walk := by
  have htake : ((walk.drop i).take (j - i)).IsSubwalk (walk.drop i) :=
    SimpleGraph.Walk.isSubwalk_take _ _
  have hdrop : (walk.drop i).IsSubwalk walk :=
    SimpleGraph.Walk.isSubwalk_drop _ _
  have hsub := htake.trans hdrop
  unfold corridorWalkInterval
  exact hsub.copy rfl (by
    rw [SimpleGraph.Walk.drop_getVert]
    congr
    omega) rfl rfl

theorem corridorWalkInterval_support_subset
    {V : Type*} {G : SimpleGraph V} {start finish : V}
    (walk : G.Walk start finish) (i j : ℕ) (hij : i ≤ j) :
    (corridorWalkInterval walk i j hij).support ⊆ walk.support :=
  (corridorWalkInterval_isSubwalk walk i j hij).support_subset

theorem corridor_bad_walk_interval
    {start finish : LatticePoint}
    (walk : starLatticeGraph.Walk start finish)
    {i j lower B : ℕ} (hij : i ≤ j)
    (hband : ∀ k, i ≤ k → k ≤ j →
      CorridorBandPoint lower B (walk.getVert k))
    (hcoordinate : ∀ p, p ∈ walk.support → 1 < p.x ∧ 1 < p.y)
    (hbad : ∀ p, p ∈ walk.support → CorridorBad p) :
    ∃ subwalk : starLatticeGraph.Walk (walk.getVert i) (walk.getVert j),
      (∀ p, p ∈ subwalk.support → CorridorBandPoint lower B p) ∧
      (∀ p, p ∈ subwalk.support → 1 < p.x ∧ 1 < p.y) ∧
      (∀ p, p ∈ subwalk.support → CorridorBad p) := by
  let subwalk := corridorWalkInterval walk i j hij
  refine ⟨subwalk, ?_, ?_, ?_⟩
  · intro p hp
    have hpOriginal : p ∈ walk.support :=
      corridorWalkInterval_support_subset walk i j hij hp
    obtain ⟨k, hk, hpk⟩ := List.mem_iff_getElem.mp hp
    have hklen : k ≤ subwalk.length := by
      have hklt : k < subwalk.support.length := hk
      simpa [SimpleGraph.Walk.length_support] using hklt
    have hki : i ≤ i + k := Nat.le_add_right _ _
    have hkj : i + k ≤ j := by
      dsimp [subwalk, corridorWalkInterval] at hklen
      simp only [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.take_length,
        SimpleGraph.Walk.drop_length] at hklen
      omega
    have hsubGet : subwalk.getVert k = p := by
      rw [subwalk.getVert_eq_support_getElem hklen]
      exact hpk
    have hintervalGet : subwalk.getVert k = walk.getVert (i + k) := by
      dsimp [subwalk, corridorWalkInterval]
      rw [SimpleGraph.Walk.getVert_copy, SimpleGraph.Walk.take_getVert,
        SimpleGraph.Walk.drop_getVert]
      congr
      omega
    have hget : p = walk.getVert (i + k) := hsubGet.symm.trans hintervalGet
    rw [hget]
    exact hband (i + k) hki hkj
  · intro p hp
    exact hcoordinate p (corridorWalkInterval_support_subset walk i j hij hp)
  · intro p hp
    exact hbad p (corridorWalkInterval_support_subset walk i j hij hp)

/-- The paper's chronological band restriction: take the first visit to the
upper row and the last preceding visit to the lower row.  The returned walk
is an actual subwalk of the supplied bad crossing and every one of its
vertices stays in the closed band. -/
theorem exists_corridor_bad_band_subwalk
    {start finish : LatticePoint}
    (walk : starLatticeGraph.Walk start finish)
    {lower B : ℕ} (hB : 2 ≤ B)
    (hstartBelow : start.y ≤ lower)
    (hfinishAbove : lower + B - 1 ≤ finish.y)
    (hcoordinate : ∀ p, p ∈ walk.support → 1 < p.x ∧ 1 < p.y)
    (hbad : ∀ p, p ∈ walk.support → CorridorBad p) :
    ∃ bandStart bandFinish : LatticePoint,
      ∃ subwalk : starLatticeGraph.Walk bandStart bandFinish,
        bandStart.y = lower ∧ bandFinish.y = lower + B - 1 ∧
        bandStart ∈ walk.support ∧
        (∀ p, p ∈ subwalk.support → CorridorBandPoint lower B p) ∧
        (∀ p, p ∈ subwalk.support → 1 < p.x ∧ 1 < p.y) ∧
        (∀ p, p ∈ subwalk.support → CorridorBad p) := by
  let upper := lower + B - 1
  have hlowerUpper : lower < upper := by
    dsimp [upper]
    omega
  have hexistsUpper :
      ∃ k, k ≤ walk.length ∧ upper ≤ (walk.getVert k).y := by
    refine ⟨walk.length, Nat.le_refl _, ?_⟩
    simpa [upper] using hfinishAbove
  let j := Nat.find hexistsUpper
  have hj := Nat.find_spec hexistsUpper
  have hjpos : 0 < j := by
    by_contra hnot
    have hjzero : j = 0 := by omega
    have huStart : upper ≤ start.y := by
      simpa [j, hjzero] using hj.2
    omega
  have hbeforeUpper : ∀ k, k < j → (walk.getVert k).y < upper := by
    intro k hkj
    have hklen : k ≤ walk.length := le_trans (Nat.le_of_lt hkj) hj.1
    have hnot := Nat.find_min hexistsUpper hkj
    push Not at hnot
    exact hnot hklen
  have hadjUpper :
      StarAdjacent (walk.getVert (j - 1)) (walk.getVert j) := by
    have hindex : j - 1 < walk.length := by omega
    have hstep := walk.adj_getVert_succ hindex
    have hsucc : j - 1 + 1 = j := by omega
    simpa [hsucc] using hstep
  have hjUpper : (walk.getVert j).y = upper := by
    have hprev := hbeforeUpper (j - 1) (by omega)
    have hstep := starAdjacent_y_le_succ hadjUpper
    have hjge : upper ≤ (walk.getVert j).y := by
      simpa [j] using hj.2
    omega
  let lowerHit : ℕ → Prop := fun k => (walk.getVert k).y ≤ lower
  let i := Nat.findGreatest lowerHit j
  have hzeroLower : lowerHit 0 := by
    dsimp [lowerHit]
    simpa using hstartBelow
  have hiLower : lowerHit i :=
    Nat.findGreatest_spec (P := lowerHit) (Nat.zero_le j) hzeroLower
  have hij : i ≤ j := Nat.findGreatest_le j
  have hiltj : i < j := by
    by_contra hnot
    have hijEq : i = j := by omega
    dsimp [lowerHit] at hiLower
    rw [hijEq, hjUpper] at hiLower
    omega
  have hadjLower :
      StarAdjacent (walk.getVert i) (walk.getVert (i + 1)) := by
    have hindex : i < walk.length := lt_of_lt_of_le hiltj hj.1
    exact walk.adj_getVert_succ hindex
  have hafterLower : lower < (walk.getVert (i + 1)).y := by
    have hnot := Nat.findGreatest_is_greatest (P := lowerHit)
      (show i < i + 1 by omega) (show i + 1 ≤ j by omega)
    dsimp [lowerHit] at hnot
    omega
  have hiEq : (walk.getVert i).y = lower := by
    dsimp [lowerHit] at hiLower
    have hstep := starAdjacent_y_le_succ hadjLower
    omega
  have hband : ∀ k, i ≤ k → k ≤ j →
      CorridorBandPoint lower B (walk.getVert k) := by
    intro k hik hkj
    constructor
    · rcases eq_or_lt_of_le hik with rfl | hiklt
      · exact hiEq.ge
      · have hnot := Nat.findGreatest_is_greatest (P := lowerHit) hiklt hkj
        dsimp [lowerHit] at hnot
        omega
    · rcases eq_or_lt_of_le hkj with rfl | hkjlt
      · rw [hjUpper]
        dsimp [upper]
        omega
      · have hkUpper := hbeforeUpper k hkjlt
        dsimp [upper] at hkUpper
        omega
  obtain ⟨subwalk, hsubBand, hsubCoordinate, hsubBad⟩ :=
    corridor_bad_walk_interval walk hij hband hcoordinate hbad
  exact ⟨walk.getVert i, walk.getVert j, subwalk,
    hiEq, by simpa [upper] using hjUpper, walk.getVert_mem_support i,
    hsubBand, hsubCoordinate, hsubBad⟩

/-- One literal consumer from an original bottom-to-top bad crossing to the
selected rough-row vertices and their distinct large common prime divisors. -/
theorem corridor_bad_crossing_selected_rows
    {ι : Type*} {z : ℝ} {lower B : ℕ}
    (row : ι → ℕ) (hrow : Function.Injective row)
    (hrough : ∀ i, CorridorRough z (row i))
    (hrowBand : ∀ i, lower ≤ row i ∧ row i < lower + B)
    (hBz : (B : ℝ) < z)
    (hrowComposite : ∀ i, Composite (row i))
    {start finish : LatticePoint}
    (walk : starLatticeGraph.Walk start finish)
    (hB : 2 ≤ B)
    (hstartBelow : start.y ≤ lower)
    (hfinishAbove : lower + B - 1 ≤ finish.y)
    (hcoordinate : ∀ p, p ∈ walk.support → 1 < p.x ∧ 1 < p.y)
    (hbad : ∀ p, p ∈ walk.support → CorridorBad p) :
    ∃ bandStart bandFinish : LatticePoint,
      ∃ subwalk : starLatticeGraph.Walk bandStart bandFinish,
        bandStart.y = lower ∧ bandFinish.y = lower + B - 1 ∧
        bandStart ∈ walk.support ∧
        ∃ point : ι → LatticePoint, ∃ q : ι → ℕ,
          (∀ i, point i ∈ subwalk.support) ∧
          (∀ i, (point i).y = row i) ∧
          (∀ i, (q i).Prime) ∧
          (∀ i, z < (q i : ℝ)) ∧
          (∀ i, (q i) ∣ (point i).x ∧ (q i) ∣ (point i).y) ∧
          Function.Injective q := by
  obtain ⟨bandStart, bandFinish, subwalk,
      hstartRow, hfinishRow, hstartMem, hsubBand, hsubCoordinate, hsubBad⟩ :=
    exists_corridor_bad_band_subwalk walk hB hstartBelow hfinishAbove
      hcoordinate hbad
  have hcrossBelow : ∀ i, bandStart.y ≤ row i := by
    intro i
    rw [hstartRow]
    exact (hrowBand i).1
  have hcrossAbove : ∀ i, row i ≤ bandFinish.y := by
    intro i
    rw [hfinishRow]
    have hiUpper := (hrowBand i).2
    omega
  obtain ⟨point, q, hpointMem, hpointRow, hqPrime, hqLarge, hqDiv, hqInj⟩ :=
    corridor_bad_walk_selected_rows_closed row hrow hrough hrowBand hBz
      hrowComposite subwalk hcrossBelow hcrossAbove hsubCoordinate hsubBad
  exact ⟨bandStart, bandFinish, subwalk, hstartRow, hfinishRow, hstartMem,
    point, q, hpointMem, hpointRow, hqPrime, hqLarge, hqDiv, hqInj⟩

/-- Full finite localization consumer of Lemma 4.2, once the paper's support
columns and selected rough rows have been produced.  The base is the actual
first vertex of the chronological band subcrossing. -/
theorem corridor_bad_crossing_localized_rows
    {ι : Type*} {z : ℝ} {lower B D xLower : ℕ}
    (row : ι → ℕ) (hrow : Function.Injective row)
    (hrough : ∀ i, CorridorRough z (row i))
    (hrowBand : ∀ i, lower ≤ row i ∧ row i < lower + B)
    (hBz : (B : ℝ) < z)
    (hrowComposite : ∀ i, Composite (row i))
    (hsupports : ∀ x : ℕ, xLower ≤ x → ∃ west east : ℕ,
      west < x ∧ x < east ∧ west < east ∧
      x ≤ west + D ∧ east ≤ x + D ∧
      (∀ y, CorridorBandPoint lower B {x := west, y := y} →
        SafePoint {x := west, y := y}) ∧
      (∀ y, CorridorBandPoint lower B {x := east, y := y} →
        SafePoint {x := east, y := y}))
    {start finish : LatticePoint}
    (walk : starLatticeGraph.Walk start finish)
    (hB : 2 ≤ B)
    (hstartBelow : start.y ≤ lower)
    (hfinishAbove : lower + B - 1 ≤ finish.y)
    (hcoordinate : ∀ p, p ∈ walk.support → 1 < p.x ∧ 1 < p.y)
    (hwalkXLower : ∀ p, p ∈ walk.support → xLower ≤ p.x)
    (hbad : ∀ p, p ∈ walk.support → CorridorBad p) :
    ∃ base : LatticePoint, ∃ point : ι → LatticePoint, ∃ q : ι → ℕ,
      base ∈ walk.support ∧
      (∀ i, Nat.dist (point i).x base.x ≤ 2 * D ∧
        Nat.dist (point i).y base.y ≤ B) ∧
      (∀ i, (point i).y = row i) ∧
      (∀ i, (q i).Prime) ∧
      (∀ i, z < (q i : ℝ)) ∧
      (∀ i, (q i) ∣ (point i).x ∧ (q i) ∣ (point i).y) ∧
      Function.Injective q := by
  obtain ⟨base, bandFinish, subwalk,
      hbaseRow, hfinishRow, hbaseMem, hsubBand, hsubCoordinate, hsubBad⟩ :=
    exists_corridor_bad_band_subwalk walk hB hstartBelow hfinishAbove
      hcoordinate hbad
  obtain ⟨west, east, hwest, heast, hwestEast,
      hwestNear, heastNear, safeWest, safeEast⟩ :=
    hsupports base.x (hwalkXLower base hbaseMem)
  have hcrossBelow : ∀ i, base.y ≤ row i := by
    intro i
    rw [hbaseRow]
    exact (hrowBand i).1
  have hcrossAbove : ∀ i, row i ≤ bandFinish.y := by
    intro i
    rw [hfinishRow]
    have hiUpper := (hrowBand i).2
    omega
  obtain ⟨point, q, hpointMem, hpointRow, hqPrime, hqLarge, hqDiv, hqInj⟩ :=
    corridor_bad_walk_selected_rows_closed row hrow hrough hrowBand hBz
      hrowComposite subwalk hcrossBelow hcrossAbove hsubCoordinate hsubBad
  have hspan : ∀ i, Nat.dist (point i).x base.x ≤ 2 * D ∧
      Nat.dist (point i).y base.y ≤ B := by
    intro i
    exact corridor_bad_walk_support_span safeWest safeEast subwalk hwest
      heast hwestEast hsubBand hsubBad hwestNear heastNear (hpointMem i)
  exact ⟨base, point, q, hbaseMem, hspan, hpointRow,
    hqPrime, hqLarge, hqDiv, hqInj⟩

end

end Erdos1212Kernel
