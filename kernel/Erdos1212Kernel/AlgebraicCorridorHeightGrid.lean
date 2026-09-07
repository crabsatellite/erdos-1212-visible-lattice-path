import Erdos1212Kernel.AlgebraicCorridorSquareScale

namespace Erdos1212Kernel.CorridorScale

/-- Index of the final selected height; add the endpoint only if needed. -/
def heightGridLast (N s : ℕ) : ℕ := N / s + if N % s = 0 then 0 else 1

/-- The paper's heights N, N+s, ... together with the final height 2N.
Only indices up to heightGridLast are selected. -/
def heightGrid (N s i : ℕ) : ℕ := min (N + i * s) (2 * N)

theorem heightGrid_bounds (N s i : ℕ) :
    N ≤ heightGrid N s i ∧ heightGrid N s i ≤ 2 * N := by
  dsimp [heightGrid]
  omega

@[simp] theorem heightGrid_zero (N s : ℕ) : heightGrid N s 0 = N := by
  simp [heightGrid]
  omega

theorem heightGrid_step (N s i : ℕ) :
    heightGrid N s i ≤ heightGrid N s (i + 1) ∧
      heightGrid N s (i + 1) - heightGrid N s i ≤ s := by
  simp only [heightGrid, Nat.add_mul, Nat.one_mul]
  omega

theorem heightGrid_last (N s : ℕ) (hs : 0 < s) :
    heightGrid N s (heightGridLast N s) = 2 * N := by
  have hmod := Nat.mod_lt N hs
  have hdiv := Nat.mod_add_div N s
  have hprod : N ≤ heightGridLast N s * s := by
    unfold heightGridLast
    split_ifs with h
    · simp only [Nat.add_zero]
      nlinarith
    · simp only [Nat.add_mul, Nat.one_mul]
      nlinarith
  dsimp [heightGrid]
  omega

/-- Every entry before the last is precisely the untruncated arithmetic grid. -/
theorem heightGrid_before_last (N s i : ℕ) (hi : i < heightGridLast N s) :
    heightGrid N s i = N + i * s ∧ N + i * s < 2 * N := by
  have hdiv := Nat.mod_add_div N s
  have hprod : i * s < N := by
    unfold heightGridLast at hi
    split_ifs at hi with h
    · have hi' : i + 1 ≤ N / s := by omega
      have hmul := Nat.mul_le_mul_right s hi'
      have hs : 0 < s := by
        by_contra hn
        have hz : s = 0 := by omega
        simp [hz] at hi
      simp only [Nat.add_mul, Nat.one_mul] at hmul
      nlinarith
    · have hi' : i ≤ N / s := by omega
      have hmul := Nat.mul_le_mul_right s hi'
      have hmod : 0 < N % s := by omega
      nlinarith
  constructor
  · exact min_eq_left (by omega)
  · omega

end Erdos1212Kernel.CorridorScale
