import Erdos1212Kernel.AlgebraicCorridorOffsets

namespace Erdos1212Kernel.CorridorScale

noncomputable section

open Filter

def AlgebraicPointAtScale (N : Real) : Prop :=
  ∀ (root : Fin 2 → Int) (point : Fin (rows N) → Fin 2 → Int)
    (q : Fin (rows N) → Nat),
    (∀ i k, |(point i k : Real)| ≤ radius N) →
    (∀ k, |(root k : Real)| ≤ 4 * N) →
    (∀ i, (q i).Prime) → Function.Injective q →
    (∀ i, z N < (q i : Real)) →
    (∀ i k, (q i : Int) ∣ root k + point i k) →
    ∃ F : MvPolynomial (Fin 2) Int,
      F ≠ 0 ∧ F.totalDegree ≤ degree N ∧ MvPolynomial.eval root F = 0 ∧
      corridorPolynomialHeight F ≤ height N

theorem eventually_AlgebraicPointAtScale :
    ∀ᶠ N : Real in atTop, AlgebraicPointAtScale N := by
  simpa only [AlgebraicPointAtScale] using eventually_algebraic_point

theorem exists_AlgebraicPointAtScale_threshold :
    ∃ N₀ : Real, ∀ N ≥ N₀, AlgebraicPointAtScale N :=
  eventually_atTop.mp eventually_AlgebraicPointAtScale

theorem localized_rows_algebraic_point_at_large_scale
    {N N₀ : Real} (hNpos : 0 < N) (hN : N₀ ≤ N)
    (hscale : ∀ N ≥ N₀, AlgebraicPointAtScale N)
    {base : LatticePoint}
    (pointNat : Fin (rows N) → LatticePoint)
    (hspan : ∀ i, Nat.dist (pointNat i).x base.x ≤ radius N ∧
      Nat.dist (pointNat i).y base.y ≤ radius N)
    (q : Fin (rows N) → Nat)
    (hqprime : ∀ i, (q i).Prime) (hqinj : Function.Injective q)
    (hqlarge : ∀ i, z N < (q i : Real))
    (hqdiv : ∀ i, (q i) ∣ (pointNat i).x ∧ (q i) ∣ (pointNat i).y)
    (hbase : base.x ≤ Nat.floor (4 * N) ∧ base.y ≤ Nat.floor (4 * N)) :
    ∃ F : MvPolynomial (Fin 2) Int,
      F ≠ 0 ∧ F.totalDegree ≤ degree N ∧
      MvPolynomial.eval (corridorRoot base) F = 0 ∧
      corridorPolynomialHeight F ≤ height N := by
  apply corridor_localized_rows_algebraic_point hNpos (hscale N hN)
    pointNat hspan q hqprime hqinj hqlarge hqdiv hbase

end

end Erdos1212Kernel.CorridorScale
