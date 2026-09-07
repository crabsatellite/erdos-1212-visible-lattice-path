import Erdos1212Kernel.AlgebraicCorridorReturnAvoidsWest

namespace Erdos1212Kernel
noncomputable section

theorem starWalk_of_sequence (p : ℕ → LatticePoint) (n : ℕ)
    (hstep : ∀ i < n, StarAdjacentOrEq (p i) (p (i + 1))) :
    ∃ w : starLatticeGraph.Walk (p 0) (p n),
      ∀ v ∈ w.support, ∃ i ≤ n, p i = v := by
  induction n with
  | zero =>
    refine ⟨.nil, ?_⟩
    intro v hv
    exact ⟨0, le_rfl, (by simpa using hv : v = p 0).symm⟩
  | succ n ih =>
    obtain ⟨w, hw⟩ := ih (fun i hi => hstep i (by omega))
    rcases hstep n (by omega) with heq | hadj
    · refine ⟨w.copy rfl heq, ?_⟩
      intro v hv
      obtain ⟨i, hi, hiv⟩ := hw v (by simpa using hv)
      exact ⟨i, by omega, hiv⟩
    · refine ⟨w.concat hadj, ?_⟩
      intro v hv
      rw [SimpleGraph.Walk.support_concat, List.mem_append] at hv
      rcases hv with hv | hv
      · obtain ⟨i, hi, hiv⟩ := hw v hv
        exact ⟨i, by omega, hiv⟩
      · exact ⟨n + 1, le_rfl, (by simpa using hv : v = p (n + 1)).symm⟩

theorem CorridorRectangle.return_orbit_walk (R : CorridorRectangle)
    (hl : 2 < R.left) (hb : 1 < R.bottom) (hno : ¬R.SafeHorizontalCrossing) :
    ∃ w : starLatticeGraph.Walk
        (boundaryDartOutside R.southCorner) (boundaryDartOutside R.northCorner),
      ∀ v ∈ w.support, R.bottom ≤ v.y → v.y ≤ R.top →
        R.Contains v ∧ CorridorBad v := by
  classical
  let f := boundaryDartSuccessorRaw R.augmentedCells
  have hex : ∃ n : ℕ, f^[n] R.southCorner = R.northCorner :=
    R.south_to_north_orbit hl hb
  let n := Nat.find hex
  have hn : f^[n] R.southCorner = R.northCorner := Nat.find_spec hex
  have hbefore : ∀ i < n, f^[i] R.southCorner ≠ R.northCorner :=
    fun i hi => Nat.find_min hex hi
  let p : ℕ → LatticePoint := fun i => boundaryDartOutside (f^[i] R.southCorner)
  have hstep : ∀ i < n, StarAdjacentOrEq (p i) (p (i + 1)) := by
    intro i hi
    change StarAdjacentOrEq (boundaryDartOutside (f^[i] R.southCorner))
      (boundaryDartOutside (f^[i + 1] R.southCorner))
    rw [Function.iterate_succ_apply']
    exact R.augmented_boundary_outside_step hl hb
      (R.augmented_raw_iterate_mem hl hb (R.southCorner_mem hl hb) i)
  obtain ⟨w, hw⟩ := starWalk_of_sequence p n hstep
  have hend : p n = boundaryDartOutside R.northCorner := by
    dsimp [p]
    rw [hn]
  refine ⟨w.copy rfl hend, ?_⟩
  intro v hv hyl hyu
  obtain ⟨i, hi, hiv⟩ := hw v (by simpa using hv)
  have hbounds : R.bottom ≤ (p i).y ∧ (p i).y ≤ R.top := by
    rw [hiv]
    exact ⟨hyl, hyu⟩
  have hinside : R.Contains (p i) := R.first_return_inside hl hb hno i
    (fun j hj => hbefore j (by omega)) hbounds
  have hbad : CorridorBad (p i) := R.augmented_boundary_outside_bad hl hb
    (R.augmented_raw_iterate_mem hl hb (R.southCorner_mem hl hb) i) hinside
  rw [hiv] at hinside hbad
  exact ⟨hinside, hbad⟩

end
end Erdos1212Kernel
