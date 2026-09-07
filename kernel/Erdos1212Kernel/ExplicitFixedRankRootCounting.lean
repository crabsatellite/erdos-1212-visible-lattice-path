import Erdos1212Kernel.PrimeRankGeometryBounds
import Erdos1212Kernel.FixedRankRootCounting

namespace Erdos1212Kernel

/-!
# Explicit fixed-rank root envelope

This is the quantitative form needed by a growing-cutoff close.  The
prime--prime anchor still supplies the extra prime-counting factor, while the
entire fibre is now bounded by a fixed exponential in the exact boundary
rank.
-/

theorem componentRankAnchorDiameter_le (K : Nat) :
    2 * componentRankAnchorRadius K + 1 ≤
      5 * 16 ^ (K + 6) := by
  have hgap := componentRankGap_le_sixteen_pow K
  have hone : 1 ≤ 16 ^ (K + 6) := by
    exact Nat.one_le_pow' (K + 6) 15
  dsimp [componentRankAnchorRadius]
  omega

/-- The geometric threshold at which the prime--prime anchor count is
available is itself only exponential in the exact boundary rank.  This
explicit form is what permits a growing-rank split without hiding a
rank-dependent eventuality. -/
theorem fixedRankCorridorThreshold_le_exponential (K : Nat) :
    fixedRankCorridorThreshold K ≤ 14 * 16 ^ (K + 6) := by
  have hbase : 2 ^ (K + 6) ≤ 16 ^ (K + 6) :=
    Nat.pow_le_pow_left (by omega) _
  have hnthTwo : Nat.nth Nat.Prime (K + 5) ≤ 2 ^ (K + 6) := by
    simpa only [show K + 5 + 1 = K + 6 by omega] using
      nthPrime_le_two_pow_succ (K + 5)
  have hnth := hnthTwo.trans hbase
  have hgap := componentRankGap_le_sixteen_pow K
  have hone : 1 ≤ 16 ^ (K + 6) :=
    Nat.one_le_pow' (K + 6) 15
  dsimp [fixedRankCorridorThreshold, componentRankThreshold,
    componentRankAnchorRadius]
  omega

theorem boundedHighCorridorRootsOfRank_card_le_exponential
    {N K : Nat} (hN : fixedRankCorridorThreshold K ≤ N) :
    (boundedHighCorridorRootsOfRank N K).card ≤
      (Nat.primeCounting (8 * N)) ^ 2 *
        (5 * 16 ^ (K + 6)) ^ 2 := by
  refine (boundedHighCorridorRootsOfRank_card_le hN).trans ?_
  exact Nat.mul_le_mul_left _ <| by
    rw [pow_two, pow_two]
    exact Nat.mul_le_mul
      (componentRankAnchorDiameter_le K)
      (componentRankAnchorDiameter_le K)

end Erdos1212Kernel
