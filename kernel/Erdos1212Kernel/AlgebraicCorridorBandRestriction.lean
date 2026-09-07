import Erdos1212Kernel.AlgebraicCorridorOrbitWalk

namespace Erdos1212Kernel
noncomputable section

theorem corridor_walk_interval_band
    {start finish : LatticePoint}
    (walk : starLatticeGraph.Walk start finish)
    {i j lower B : ℕ} (hij : i ≤ j)
    (hband : ∀ k, i ≤ k → k ≤ j →
      CorridorBandPoint lower B (walk.getVert k)) :
    ∃ subwalk : starLatticeGraph.Walk (walk.getVert i) (walk.getVert j),
      (∀ p, p ∈ subwalk.support → CorridorBandPoint lower B p) ∧
      subwalk.support ⊆ walk.support := by
  let subwalk := corridorWalkInterval walk i j hij
  refine ⟨subwalk, ?_, corridorWalkInterval_support_subset walk i j hij⟩
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

theorem exists_corridor_band_subwalk
    {start finish : LatticePoint}
    (walk : starLatticeGraph.Walk start finish)
    {lower B : ℕ} (hB : 2 ≤ B)
    (hstartBelow : start.y ≤ lower)
    (hfinishAbove : lower + B - 1 ≤ finish.y) :
    ∃ bandStart bandFinish : LatticePoint,
      ∃ subwalk : starLatticeGraph.Walk bandStart bandFinish,
        bandStart.y = lower ∧ bandFinish.y = lower + B - 1 ∧
        bandStart ∈ walk.support ∧
        (∀ p, p ∈ subwalk.support → CorridorBandPoint lower B p) ∧
        subwalk.support ⊆ walk.support := by
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
  obtain ⟨subwalk, hsubBand, hsubSupport⟩ :=
    corridor_walk_interval_band walk hij hband
  exact ⟨walk.getVert i, walk.getVert j, subwalk,
    hiEq, by simpa [upper] using hjUpper, walk.getVert_mem_support i,
    hsubBand, hsubSupport⟩


theorem CorridorRectangle.bad_vertical_crossing_of_no_safe_horizontal
    (R : CorridorRectangle) (hl : 2 < R.left) (hb : 1 < R.bottom)
    (hheight : R.bottom < R.top) (hno : ¬R.SafeHorizontalCrossing) :
    ∃ a b : LatticePoint, a.y = R.bottom ∧ b.y = R.top ∧
      ∃ w : starLatticeGraph.Walk a b,
        ∀ p ∈ w.support, R.Contains p ∧ CorridorBad p := by
  obtain ⟨w, hw⟩ := R.return_orbit_walk hl hb hno
  have hB : 2 ≤ R.top - R.bottom + 1 := by omega
  have hlow : (boundaryDartOutside R.southCorner).y ≤ R.bottom := by
    simp [boundaryDartOutside, southCorner, gridStep]
  have hupp : R.bottom + (R.top - R.bottom + 1) - 1 ≤
      (boundaryDartOutside R.northCorner).y := by
    simp [boundaryDartOutside, northCorner, gridStep]
    omega
  obtain ⟨a, b, v, ha, hb', _, hvBand, hvSub⟩ :=
    exists_corridor_band_subwalk w hB hlow hupp
  refine ⟨a, b, ha, ?_, v, ?_⟩
  · omega
  · intro p hp
    have hband := hvBand p hp
    have hlo : R.bottom ≤ p.y := hband.1
    have hhi : p.y ≤ R.top := by
      have h := hband.2
      omega
    exact hw p (hvSub hp) hlo hhi

theorem CorridorScale.eventually_safe_horizontal_crossing :
    ∀ᶠ N : ℝ in Filter.atTop, ∀ (α : ℝ) (R : CorridorRectangle),
      DirectionAvoidance N α →
      2 < R.left → 1 < R.bottom → R.bottom < R.top →
      Nat.floor (N / 2) ≤ R.bottom → R.top ≤ Nat.floor (4 * N) →
      N ^ (9 / 10 : ℝ) ≤ ((R.top - R.bottom + 1 : ℕ) : ℝ) →
      (∀ p, R.Contains p → directionCorridor N α p) →
      R.SafeHorizontalCrossing := by
  filter_upwards [eventually_no_bad_vertical_crossing_of_directionAvoidance]
    with N hnoBad
  intro α R havoid hl hb hheight hlow hupp hsize hcorr
  by_contra hno
  obtain ⟨a, b, ha, hbe, w, hw⟩ :=
    R.bad_vertical_crossing_of_no_safe_horizontal hl hb hheight hno
  apply hnoBad α havoid (lower := R.bottom)
    (T := R.top - R.bottom + 1) w hlow (by omega) hsize
      (by omega) (by omega)
      (fun p hp => hcorr p (hw p hp).1)
  exact fun p hp => (hw p hp).2

end
end Erdos1212Kernel
