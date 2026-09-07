import Erdos1212Kernel.AlgebraicCorridorTranspose

namespace Erdos1212Kernel
noncomputable section

private theorem corridor_nn_y_le_succ {p q : LatticePoint} (h : Adjacent p q) :
    q.y ≤ p.y + 1 := by
  rcases h with h | h | h | h <;> omega

theorem corridor_nn_walk_interval_band
    {start finish : LatticePoint}
    (walk : latticeGraph.Walk start finish)
    {i j lower B : ℕ} (hij : i ≤ j)
    (hband : ∀ k, i ≤ k → k ≤ j →
      CorridorBandPoint lower B (walk.getVert k)) :
    ∃ subwalk : latticeGraph.Walk (walk.getVert i) (walk.getVert j),
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

theorem exists_corridor_nn_band_subwalk
    {start finish : LatticePoint}
    (walk : latticeGraph.Walk start finish)
    {lower B : ℕ} (hB : 2 ≤ B)
    (hstartBelow : start.y ≤ lower)
    (hfinishAbove : lower + B - 1 ≤ finish.y) :
    ∃ bandStart bandFinish : LatticePoint,
      ∃ subwalk : latticeGraph.Walk bandStart bandFinish,
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
      Adjacent (walk.getVert (j - 1)) (walk.getVert j) := by
    have hindex : j - 1 < walk.length := by omega
    have hstep := walk.adj_getVert_succ hindex
    have hsucc : j - 1 + 1 = j := by omega
    simpa [hsucc] using hstep
  have hjUpper : (walk.getVert j).y = upper := by
    have hprev := hbeforeUpper (j - 1) (by omega)
    have hstep := corridor_nn_y_le_succ hadjUpper
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
      Adjacent (walk.getVert i) (walk.getVert (i + 1)) := by
    have hindex : i < walk.length := lt_of_lt_of_le hiltj hj.1
    exact walk.adj_getVert_succ hindex
  have hafterLower : lower < (walk.getVert (i + 1)).y := by
    have hnot := Nat.findGreatest_is_greatest (P := lowerHit)
      (show i < i + 1 by omega) (show i + 1 ≤ j by omega)
    dsimp [lowerHit] at hnot
    omega
  have hiEq : (walk.getVert i).y = lower := by
    dsimp [lowerHit] at hiLower
    have hstep := corridor_nn_y_le_succ hadjLower
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
    corridor_nn_walk_interval_band walk hij hband
  exact ⟨walk.getVert i, walk.getVert j, subwalk,
    hiEq, by simpa [upper] using hjUpper, walk.getVert_mem_support i,
    hsubBand, hsubSupport⟩


theorem corridor_nn_restrict_y {a b : LatticePoint}
    (w : latticeGraph.Walk a b) {lo hi : ℕ}
    (hlt : lo < hi) (ha : a.y ≤ lo) (hb : hi ≤ b.y) :
    ∃ c d, ∃ v : latticeGraph.Walk c d,
      c.y = lo ∧ d.y = hi ∧
      (∀ p ∈ v.support, lo ≤ p.y ∧ p.y ≤ hi) ∧ v.support ⊆ w.support := by
  obtain ⟨c, d, v, hc, hd, _, hv, hsub⟩ :=
    exists_corridor_nn_band_subwalk w (lower := lo) (B := hi - lo + 1)
      (by omega) ha (by omega)
  refine ⟨c, d, v, hc, by omega, ?_, hsub⟩
  intro p hp
  have h := hv p hp
  rcases h with ⟨hlo, hhi⟩
  exact ⟨hlo, by omega⟩

set_option backward.isDefEq.respectTransparency false in
theorem corridor_nn_restrict_x {a b : LatticePoint}
    (w : latticeGraph.Walk a b) {lo hi : ℕ}
    (hlt : lo < hi) (ha : a.x ≤ lo) (hb : hi ≤ b.x) :
    ∃ c d, ∃ v : latticeGraph.Walk c d,
      c.x = lo ∧ d.x = hi ∧
      (∀ p ∈ v.support, lo ≤ p.x ∧ p.x ≤ hi) ∧ v.support ⊆ w.support := by
  obtain ⟨c, d, v, hc, hd, hv, hsub⟩ :=
    corridor_nn_restrict_y (w.map corridorTransposeGraphHom) hlt ha hb
  refine ⟨corridorTranspose c, corridorTranspose d,
    v.map corridorTransposeGraphHom, hc, hd, ?_, ?_⟩
  · intro p hp
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact hv q hq
  · intro p hp
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have h := hsub hq
    rw [SimpleGraph.Walk.support_map, List.mem_map] at h
    obtain ⟨r, hr, heq⟩ := h
    change corridorTranspose r = q at heq
    change corridorTranspose q ∈ w.support
    rw [← heq, corridorTranspose_twice]
    exact hr

end
end Erdos1212Kernel
