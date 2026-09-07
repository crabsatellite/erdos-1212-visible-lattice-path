import Erdos1212Kernel.AlgebraicCorridorScalePiece

namespace Erdos1212Kernel.CorridorScale
noncomputable section
open Filter

theorem eventually_scalePieces_connect_next :
    ∀ᶠ N : ℝ in atTop, ∀ α ∈ algebraicCorridorSlopeInterval,
      ∀ N' : ℝ, N' = 2 * N → DirectionAvoidance N' α →
      ∀ M M' : ℕ, (M : ℝ) = N → M' = 2 * M →
      ∀ (small : CorridorScalePiece N α M) (large : CorridorScalePiece N' α M'),
      ∃ v : CorridorSafeWalk small.firstRight large.firstRight,
        ∀ p ∈ v.walk.support, directionCorridor N α p ∨ directionCorridor N' α p := by
  filter_upwards [eventually_scalePieces_connect] with N h
  intro α hα N' hN' havoid M M' hM hM' small large
  subst N'
  subst M'
  exact h α hα havoid M hM small large

/-- Actual finite safe walks at all sufficiently large dyadic scales.
Each walk remembers its two possible containing direction corridors. -/
structure CorridorDyadicChain (α : ℝ) where
  base : ℕ
  endpoint : ℕ → LatticePoint
  segment : ∀ n, CorridorSafeWalk (endpoint n) (endpoint (n + 1))
  segment_corridor : ∀ n p, p ∈ (segment n).walk.support →
    directionCorridor (dyadicScale (base + n)) α p ∨
    directionCorridor (dyadicScale (base + (n + 1))) α p
  endpoint_lower : ∀ n, dyadicScale (base + n) ≤ ((endpoint n).x : ℝ)

theorem exists_corridorDyadicChain {α : ℝ}
    (hα : α ∈ algebraicCorridorSlopeInterval)
    (havoid : ∀ᶠ j : ℕ in atTop, DirectionAvoidance (dyadicScale j) α) :
    Nonempty (CorridorDyadicChain α) := by
  have hdyadic : Tendsto dyadicScale atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp
    ((hdyadic.eventually eventually_scalePiece_exists).and
      ((hdyadic.eventually eventually_scalePieces_connect_next).and havoid))
  have hcast (n : ℕ) : ((2 ^ (J + n) : ℕ) : ℝ) = dyadicScale (J + n) := by
    simp [dyadicScale]
  let piece (n : ℕ) : CorridorScalePiece (dyadicScale (J + n)) α (2 ^ (J + n)) :=
    Classical.choice ((hJ (J + n) (by omega)).1 α hα
      (hJ (J + n) (by omega)).2.2 (2 ^ (J + n)) (hcast n))
  have hnextR (n : ℕ) : dyadicScale (J + (n + 1)) = 2 * dyadicScale (J + n) := by
    simp only [dyadicScale, ← Nat.add_assoc, pow_succ]
    ring
  have hnextN (n : ℕ) : (2 : ℕ) ^ (J + (n + 1)) = 2 * 2 ^ (J + n) := by
    simp only [← Nat.add_assoc, pow_succ]
    omega
  have hsegments (n : ℕ) :
      ∃ v : CorridorSafeWalk (piece n).firstRight (piece (n + 1)).firstRight,
      ∀ p ∈ v.walk.support,
        directionCorridor (dyadicScale (J + n)) α p ∨
        directionCorridor (dyadicScale (J + (n + 1))) α p := by
    exact (hJ (J + n) (by omega)).2.1 α hα _ (hnextR n)
      (hJ (J + (n + 1)) (by omega)).2.2 _ _ (hcast n) (hnextN n)
      (piece n) (piece (n + 1))
  choose segment hsegment using hsegments
  refine ⟨⟨J, fun n => (piece n).firstRight, segment, hsegment, ?_⟩⟩
  intro n
  have hαone : (1 : ℝ) ≤ α := by
    have h : (4 / 3 : ℝ) < α := hα.1
    linarith
  have hc : 2 ^ (J + n) ≤ squareCenter α (2 ^ (J + n)) := Nat.le_floor (by
    have h := mul_le_mul_of_nonneg_right hαone
      (show (0 : ℝ) ≤ ((2 ^ (J + n) : ℕ) : ℝ) by positivity)
    simpa using h)
  rw [(piece n).first_right]
  change dyadicScale (J + n) ≤
    ((squareCenter α (2 ^ (J + n)) + squareHalfSide (dyadicScale (J + n)) : ℕ) : ℝ)
  rw [← hcast n]
  exact_mod_cast hc.trans (Nat.le_add_right _ _)

end
end Erdos1212Kernel.CorridorScale
