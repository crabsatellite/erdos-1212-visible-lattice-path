import Erdos1212Kernel.AlgebraicCorridorLocalizedCrossing
import Erdos1212Kernel.AlgebraicCorridorRoughBand

namespace Erdos1212Kernel

noncomputable section

/-!
The row-by-row part of Lemma 4.2. It extracts actual vertices of a bad star
walk on selected rough composite rows, and then chooses the actual common
prime divisor at each vertex. No monotone walk or artificial row is inserted.
-/

theorem exists_large_common_prime_of_bad_composite_row
    {z : ℝ} {x y : Nat} (hx : 1 < x) (hy : 1 < y)
    (hrowComposite : Composite y) (hrough : CorridorRough z y)
    (hbad : CorridorBad {x := x, y := y}) :
    ∃ q : Nat, q.Prime ∧ z < (q : ℝ) ∧ q ∣ x ∧ q ∣ y := by
  have hnotVisible : ¬ Visible {x := x, y := y} := by
    intro hvis
    apply hbad
    exact ⟨hx, hy, hvis, Or.inr hrowComposite⟩
  rw [Visible] at hnotVisible
  obtain ⟨q, hq, hqx, hqy⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnotVisible
  exact ⟨q, hq, hrough q hq hqy, hqx, hqy⟩

theorem corridor_bad_walk_selected_rows
    {ι : Type*} {z : ℝ} {lower B : Nat}
    (row : ι → Nat) (hrow : Function.Injective row)
    (hrough : ∀ i, CorridorRough z (row i))
    (hband : ∀ i, lower ≤ row i ∧ row i < lower + B)
    (hB : (B : ℝ) < z)
    (hrowComposite : ∀ i, Composite (row i))
    {start finish : LatticePoint} (walk : starLatticeGraph.Walk start finish)
    (hcrossBelow : ∀ i, start.y < row i)
    (hcrossAbove : ∀ i, row i ≤ finish.y)
    (hcoordinate : ∀ p, p ∈ walk.support → 1 < p.x ∧ 1 < p.y)
    (hbad : ∀ p, p ∈ walk.support → CorridorBad p) :
    ∃ point : ι → LatticePoint, ∃ q : ι → Nat,
      (∀ i, point i ∈ walk.support) ∧
      (∀ i, (point i).y = row i) ∧
      (∀ i, (q i).Prime) ∧
      (∀ i, z < (q i : ℝ)) ∧
      (∀ i, (q i) ∣ (point i).x ∧ (q i) ∣ (point i).y) ∧
      Function.Injective q := by
  classical
  choose index hindex hrowhit using fun i =>
    starWalk_hits_y_of_crosses_above walk (hcrossBelow i) (hcrossAbove i)
  choose q hqprime hqrough hqx hqy using fun i =>
    let hhit := hrowhit i
    have hcomp : Composite (walk.getVert (index i)).y := by
      simpa [hhit] using hrowComposite i
    have hroughPoint : CorridorRough z (walk.getVert (index i)).y := by
      simpa [hhit] using hrough i
    exists_large_common_prime_of_bad_composite_row
      (hcoordinate _ (walk.getVert_mem_support (index i))).1
      (hcoordinate _ (walk.getVert_mem_support (index i))).2
      hcomp hroughPoint
      (hbad _ (walk.getVert_mem_support (index i)))
  let point : ι → LatticePoint := fun i => walk.getVert (index i)
  have hpointmem : ∀ i, point i ∈ walk.support := by
    intro i
    exact walk.getVert_mem_support (index i)
  have hpointrow : ∀ i, (point i).y = row i := by
    intro i
    exact hrowhit i
  have hqinjective : Function.Injective q := by
    exact corridorRough_selected_primes_injective row q hrow hrough hband hB
      hqprime (fun i => by simpa only [point, hrowhit i] using hqy i)
  refine ⟨point, q, hpointmem, hpointrow, hqprime, hqrough, ?_, hqinjective⟩
  intro i
  exact ⟨hqx i, hqy i⟩

/-- Closed-band endpoint version of `corridor_bad_walk_selected_rows`.
Selected rows are allowed to equal the first row of the chronological
subcrossing, as in the paper's literal closed block. -/
theorem corridor_bad_walk_selected_rows_closed
    {ι : Type*} {z : ℝ} {lower B : Nat}
    (row : ι → Nat) (hrow : Function.Injective row)
    (hrough : ∀ i, CorridorRough z (row i))
    (hband : ∀ i, lower ≤ row i ∧ row i < lower + B)
    (hB : (B : ℝ) < z)
    (hrowComposite : ∀ i, Composite (row i))
    {start finish : LatticePoint} (walk : starLatticeGraph.Walk start finish)
    (hcrossBelow : ∀ i, start.y ≤ row i)
    (hcrossAbove : ∀ i, row i ≤ finish.y)
    (hcoordinate : ∀ p, p ∈ walk.support → 1 < p.x ∧ 1 < p.y)
    (hbad : ∀ p, p ∈ walk.support → CorridorBad p) :
    ∃ point : ι → LatticePoint, ∃ q : ι → Nat,
      (∀ i, point i ∈ walk.support) ∧
      (∀ i, (point i).y = row i) ∧
      (∀ i, (q i).Prime) ∧
      (∀ i, z < (q i : ℝ)) ∧
      (∀ i, (q i) ∣ (point i).x ∧ (q i) ∣ (point i).y) ∧
      Function.Injective q := by
  classical
  have hexistsIndex : ∀ i, ∃ index ≤ walk.length,
      (walk.getVert index).y = row i := by
    intro i
    rcases eq_or_lt_of_le (hcrossBelow i) with heq | hlt
    · exact ⟨0, Nat.zero_le _, by simpa [heq]⟩
    · exact starWalk_hits_y_of_crosses_above walk hlt (hcrossAbove i)
  choose index hindex hrowhit using hexistsIndex
  choose q hqprime hqrough hqx hqy using fun i =>
    let hhit := hrowhit i
    have hcomp : Composite (walk.getVert (index i)).y := by
      simpa [hhit] using hrowComposite i
    have hroughPoint : CorridorRough z (walk.getVert (index i)).y := by
      simpa [hhit] using hrough i
    exists_large_common_prime_of_bad_composite_row
      (hcoordinate _ (walk.getVert_mem_support (index i))).1
      (hcoordinate _ (walk.getVert_mem_support (index i))).2
      hcomp hroughPoint
      (hbad _ (walk.getVert_mem_support (index i)))
  let point : ι → LatticePoint := fun i => walk.getVert (index i)
  have hpointmem : ∀ i, point i ∈ walk.support := by
    intro i
    exact walk.getVert_mem_support (index i)
  have hpointrow : ∀ i, (point i).y = row i := by
    intro i
    exact hrowhit i
  have hqinjective : Function.Injective q := by
    exact corridorRough_selected_primes_injective row q hrow hrough hband hB
      hqprime (fun i => by simpa only [point, hrowhit i] using hqy i)
  refine ⟨point, q, hpointmem, hpointrow, hqprime, hqrough, ?_, hqinjective⟩
  intro i
  exact ⟨hqx i, hqy i⟩

end

end Erdos1212Kernel
