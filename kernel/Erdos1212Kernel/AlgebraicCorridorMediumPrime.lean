import Erdos1212Kernel.AlgebraicCorridorAhBonferroni

namespace Erdos1212Kernel.CorridorScale

noncomputable section

open scoped BigOperators

/-- The paper's literal medium-prime interval `z < q ≤ 2z`.  The strict
prime pool supplies only a finite enumeration envelope; the filter retains
both displayed real endpoints exactly. -/
def mediumPrimePool (N : ℝ) : Finset ℕ :=
  (iwaniecStrictPrimePool (2 * z N + 1)).filter fun q =>
    z N < (q : ℝ) ∧ (q : ℝ) ≤ 2 * z N

@[simp]
theorem mem_mediumPrimePool {N : ℝ} {q : ℕ} :
    q ∈ mediumPrimePool N ↔
      q.Prime ∧ z N < (q : ℝ) ∧ (q : ℝ) ≤ 2 * z N := by
  simp only [mediumPrimePool, Finset.mem_filter, mem_iwaniecStrictPrimePool]
  constructor
  · rintro ⟨⟨hq, _⟩, hlow, hupp⟩
    exact ⟨hq, hlow, hupp⟩
  · rintro ⟨hq, hlow, hupp⟩
    exact ⟨⟨hq, lt_of_le_of_lt hupp (lt_add_one _)⟩, hlow, hupp⟩

theorem prime_of_mem_mediumPrimePool {N : ℝ} {q : ℕ}
    (hq : q ∈ mediumPrimePool N) : q.Prime :=
  (mem_mediumPrimePool.mp hq).1

theorem mediumPrimePool_disjoint_smallPrimePool (N : ℝ) :
    Disjoint (mediumPrimePool N) (smallPrimePool N) := by
  rw [Finset.disjoint_left]
  intro q hqMedium hqSmall
  have hlow := (mem_mediumPrimePool.mp hqMedium).2.1
  have hupp := (mem_smallPrimePool.mp hqSmall).2
  linarith

theorem mediumPrime_coprime_smallPrime
    {N : ℝ} {q p : ℕ} (hq : q ∈ mediumPrimePool N)
    (hp : p ∈ smallPrimePool N) : Nat.Coprime q p := by
  apply (Nat.coprime_primes (prime_of_mem_mediumPrimePool hq)
    (mem_smallPrimePool.mp hp).1).mpr
  intro heq
  have hlow := (mem_mediumPrimePool.mp hq).2.1
  have hupp := (mem_smallPrimePool.mp hp).2
  subst p
  linarith

theorem mediumPrime_coprime_smallPool
    {N : ℝ} {q : ℕ} (hq : q ∈ mediumPrimePool N) :
    ∀ p ∈ smallPrimePool N, Nat.Coprime q p := by
  intro p hp
  exact mediumPrime_coprime_smallPrime hq hp

theorem mediumPrimeProduct_coprime_smallPool
    {N : ℝ} {q q' : ℕ} (hq : q ∈ mediumPrimePool N)
    (hq' : q' ∈ mediumPrimePool N) :
    ∀ p ∈ smallPrimePool N, Nat.Coprime (q * q') p := by
  intro p hp
  exact (mediumPrime_coprime_smallPrime hq hp).mul_left
    (mediumPrime_coprime_smallPrime hq' hp)

theorem mediumPrimeSubsetProduct_coprime_smallPool
    {N : ℝ} {subset : Finset ℕ} (hsubset : subset ⊆ mediumPrimePool N) :
    ∀ p ∈ smallPrimePool N,
      Nat.Coprime (∏ q ∈ subset, q) p := by
  intro p hp
  exact (corridor_h_coprime_subsetProduct hsubset
    (fun q hq => (mediumPrime_coprime_smallPrime hq hp).symm)).symm

theorem mediumPrimePool_pair_product_pos
    {N : ℝ} {q q' : ℕ} (hq : q ∈ mediumPrimePool N)
    (hq' : q' ∈ mediumPrimePool N) : 0 < q * q' :=
  Nat.mul_pos (prime_of_mem_mediumPrimePool hq).pos
    (prime_of_mem_mediumPrimePool hq').pos

end

end Erdos1212Kernel.CorridorScale
