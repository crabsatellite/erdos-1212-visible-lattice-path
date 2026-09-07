import Erdos1212Kernel.AlgebraicCorridorRoughBand
import Erdos1212Kernel.Target
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Sort

namespace Erdos1212Kernel

noncomputable section

def corridorBlockIndex (lower B n : ℕ) : ℕ := (n - lower) / B

noncomputable def corridorRoughCompositeCandidates
    (z : ℝ) (lower T : ℕ) : Finset ℕ := by
  classical
  exact ((Finset.range T).image (fun i => lower + i)).filter
    (fun n => Composite n ∧ CorridorRough z n)

theorem mem_corridorRoughCompositeCandidates
    {z : ℝ} {lower T n : ℕ} :
    n ∈ corridorRoughCompositeCandidates z lower T ↔
      lower ≤ n ∧ n < lower + T ∧ Composite n ∧ CorridorRough z n := by
  classical
  simp only [corridorRoughCompositeCandidates, Finset.mem_filter,
    Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hcomp, hrough⟩
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hi _, hcomp, hrough⟩
  · rintro ⟨hnLower, hnUpper, hcomp, hrough⟩
    refine ⟨?_, hcomp, hrough⟩
    have hi : n - lower < T := by omega
    exact ⟨n - lower, hi, by omega⟩

/-- Exact finite averaging step behind Lemma 3.2.  The input set is the
candidate set after the terminal incomplete block has been removed. -/
theorem exists_corridor_dense_block_rows
    {lower T B r : ℕ} (candidates : Finset ℕ)
    (hB : 0 < B) (hblocks : 0 < T / B)
    (hrange : ∀ n ∈ candidates,
      lower ≤ n ∧ n < lower + (T / B) * B)
    (hcount : (T / B) * r ≤ candidates.card) :
    ∃ blockIndex : ℕ, blockIndex < T / B ∧
      ∃ row : Fin r → ℕ,
        Function.Injective row ∧
        (∀ i, row i ∈ candidates) ∧
        (∀ i, lower + blockIndex * B ≤ row i ∧
          row i < lower + (blockIndex + 1) * B) := by
  classical
  let blocks := Finset.range (T / B)
  let bucket : ℕ → ℕ := corridorBlockIndex lower B
  have hmaps : ∀ n ∈ candidates, bucket n ∈ blocks := by
    intro n hn
    have hnRange := hrange n hn
    apply Finset.mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul hB).2
    dsimp [bucket, corridorBlockIndex]
    omega
  have hblocksNonempty : blocks.Nonempty := by
    refine ⟨0, ?_⟩
    simp [blocks, hblocks]
  have hcount' : blocks.card * r ≤ candidates.card := by
    simpa [blocks] using hcount
  obtain ⟨j, hj, hjcard⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := candidates) (t := blocks) (f := bucket)
      hmaps hblocksNonempty hcount'
  let fiber := candidates.filter (fun n => bucket n = j)
  let row : Fin r → ℕ := fiber.orderEmbOfCardLe hjcard
  have hrowMem : ∀ i, row i ∈ fiber := by
    intro i
    exact Finset.orderEmbOfCardLe_mem fiber hjcard i
  refine ⟨j, Finset.mem_range.mp hj, row, (fiber.orderEmbOfCardLe hjcard).injective,
    ?_, ?_⟩
  · intro i
    exact (Finset.mem_filter.mp (hrowMem i)).1
  · intro i
    have hiFiber := Finset.mem_filter.mp (hrowMem i)
    have hiRange := hrange (row i) hiFiber.1
    have hquot : (row i - lower) / B = j := by
      simpa [bucket, corridorBlockIndex] using hiFiber.2
    have hmod := Nat.mod_lt (row i - lower) hB
    have hdecomp := Nat.mod_add_div (row i - lower) B
    rw [hquot, Nat.mul_comm B j] at hdecomp
    have hjmul : (j + 1) * B = j * B + B := by ring
    rw [hjmul]
    constructor <;> omega

/-- Lemma 3.2's exact finite averaging consumer, after the rough-composite
count has been supplied on the union of full blocks. -/
theorem exists_corridor_rough_composite_block_rows
    {z : ℝ} {lower T B r : ℕ}
    (hB : 0 < B) (hblocks : 0 < T / B)
    (hcount : (T / B) * r ≤
      (corridorRoughCompositeCandidates z lower ((T / B) * B)).card) :
    ∃ blockLower : ℕ, ∃ row : Fin r → ℕ,
      Function.Injective row ∧
      (lower ≤ blockLower ∧ blockLower + B ≤ lower + T) ∧
      (∀ i, blockLower ≤ row i ∧ row i < blockLower + B) ∧
      (∀ i, Composite (row i)) ∧
      (∀ i, CorridorRough z (row i)) := by
  let candidates := corridorRoughCompositeCandidates z lower ((T / B) * B)
  have hrange : ∀ n ∈ candidates,
      lower ≤ n ∧ n < lower + (T / B) * B := by
    intro n hn
    have hspec := mem_corridorRoughCompositeCandidates.mp hn
    exact ⟨hspec.1, hspec.2.1⟩
  obtain ⟨j, hj, row, hrow, hrowMem, hrowBlock⟩ :=
    exists_corridor_dense_block_rows candidates hB hblocks hrange hcount
  let blockLower := lower + j * B
  have hband : ∀ i, blockLower ≤ row i ∧ row i < blockLower + B := by
    intro i
    have hi := hrowBlock i
    dsimp [blockLower]
    have hmul : (j + 1) * B = j * B + B := by ring
    rw [hmul] at hi
    omega
  have hblockRange : lower ≤ blockLower ∧ blockLower + B ≤ lower + T := by
    dsimp [blockLower]
    constructor
    · omega
    · have hjNext : j + 1 ≤ T / B := by omega
      have hmul := Nat.mul_le_mul_right B hjNext
      have hfullLe : (T / B) * B ≤ T := Nat.div_mul_le_self T B
      have hjmul : (j + 1) * B = j * B + B := by ring
      rw [hjmul] at hmul
      omega
  have hcomp : ∀ i, Composite (row i) := by
    intro i
    exact (mem_corridorRoughCompositeCandidates.mp (hrowMem i)).2.2.1
  have hrough : ∀ i, CorridorRough z (row i) := by
    intro i
    exact (mem_corridorRoughCompositeCandidates.mp (hrowMem i)).2.2.2
  exact ⟨blockLower, row, hrow, hblockRange, hband, hcomp, hrough⟩

end

end Erdos1212Kernel
