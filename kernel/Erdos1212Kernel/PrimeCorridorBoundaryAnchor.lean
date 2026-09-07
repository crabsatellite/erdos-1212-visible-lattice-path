import Mathlib.NumberTheory.Bertrand
import Erdos1212Kernel.ConcreteComponentBoundary
import Erdos1212Kernel.PrimeCorridorHighBaseline

namespace Erdos1212Kernel

/-!
# An actual prime--prime boundary anchor for every corridor root

The prime-corridor root `(p, 2 * k)` lies on a prime column with
`2 * k < p`.  Bertrand's postulate supplies a prime height below `2 * k`.
Descend the column and stop at the first prime height.  Every earlier height
is composite, hence every earlier column point is safe; the stopped point is
prime--prime and is therefore outside the safe component.  It is consequently
an actual exterior-boundary vertex of that component.

This argument is finite and pointwise.  In particular it does not use a
positive-density full-visible component, a contour surrogate, or a moved
prime cut.
-/

def primeColumnDownPoint (p height step : Nat) : LatticePoint :=
  ⟨p, height - step⟩

theorem adjacent_primeColumnDownPoint_succ
    {p height step : Nat} (hstep : step < height) :
    Adjacent (primeColumnDownPoint p height step)
      (primeColumnDownPoint p height (step + 1)) := by
  right
  right
  right
  simp only [primeColumnDownPoint]
  constructor
  · omega
  · trivial

theorem safeReachableFrom_primeColumnDownPoint
    {p height steps : Nat} (hsteps : steps ≤ height)
    (hsafe : ∀ step ≤ steps,
      SafePoint (primeColumnDownPoint p height step)) :
    SafeReachableFrom (primeColumnDownPoint p height 0)
      (primeColumnDownPoint p height steps) := by
  induction steps with
  | zero =>
      refine ⟨SimpleGraph.Walk.nil, ?_⟩
      intro point hpoint
      have hpointEq : point = primeColumnDownPoint p height 0 := by
        simpa using hpoint
      rw [hpointEq]
      exact hsafe 0 (Nat.zero_le 0)
  | succ steps ih =>
      have hstepsPrevious : steps ≤ height := by omega
      obtain ⟨walk, hwalkSafe⟩ := ih hstepsPrevious (fun step hstep ↦
        hsafe step (by omega))
      have hadjacent :
          Adjacent (primeColumnDownPoint p height steps)
            (primeColumnDownPoint p height (steps + 1)) :=
        adjacent_primeColumnDownPoint_succ (by omega)
      refine ⟨walk.concat hadjacent, ?_⟩
      intro point hpoint
      rw [SimpleGraph.Walk.support_concat] at hpoint
      rcases List.mem_append.mp hpoint with hpoint | hpoint
      · exact hwalkSafe point hpoint
      · have hpointLast :
            point = primeColumnDownPoint p height (steps + 1) := by
          simpa using hpoint
        rw [hpointLast]
        exact hsafe (steps + 1) (Nat.le_refl _)

theorem exists_primeHeightBelow_double {k : Nat} (hk : 2 ≤ k) :
    ∃ q, Nat.Prime q ∧ k < q ∧ q < 2 * k := by
  obtain ⟨q, hqPrime, hkq, hqUpper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul k (by omega)
  refine ⟨q, hqPrime, hkq, ?_⟩
  by_contra hnot
  have hqEq : q = 2 * k := by omega
  rw [hqEq] at hqPrime
  exact (Nat.not_prime_mul (by norm_num : 2 ≠ 1) (by omega : k ≠ 1)) hqPrime

abbrev PrimeColumnDescentWitness (k step : Nat) : Prop :=
  0 < step ∧ step < 2 * k ∧ Nat.Prime (2 * k - step)

theorem primeColumnDescentWitness_exists {k : Nat} (hk : 2 ≤ k) :
    ∃ step, PrimeColumnDescentWitness k step := by
  obtain ⟨q, hqPrime, _hkq, hqUpper⟩ :=
    exists_primeHeightBelow_double hk
  have hsub : 2 * k - (2 * k - q) = q := by omega
  exact ⟨2 * k - q, by omega, by omega, hsub.symm ▸ hqPrime⟩

noncomputable def firstPrimeColumnDescent (k : Nat) : Nat :=
  by
    exact if hk : 2 ≤ k then Nat.find (primeColumnDescentWitness_exists hk) else 0

theorem firstPrimeColumnDescent_spec {k : Nat} (hk : 2 ≤ k) :
    0 < firstPrimeColumnDescent k ∧
    firstPrimeColumnDescent k < 2 * k ∧
    Nat.Prime (2 * k - firstPrimeColumnDescent k) := by
  rw [firstPrimeColumnDescent, dif_pos hk]
  exact Nat.find_spec (primeColumnDescentWitness_exists hk)

theorem not_prime_before_firstPrimeColumnDescent
    {k step : Nat} (hk : 2 ≤ k)
    (hstep : step < firstPrimeColumnDescent k) :
    ¬ Nat.Prime (2 * k - step) := by
  intro hprime
  by_cases hstepZero : step = 0
  · subst step
    have htwoNeOne : (2 : Nat) ≠ 1 := by decide
    have hkNeOne : k ≠ 1 := by
      intro hkOne
      omega
    exact (Nat.not_prime_mul htwoNeOne hkNeOne) (by simpa using hprime)
  · rw [firstPrimeColumnDescent, dif_pos hk] at hstep
    exact (Nat.find_min (primeColumnDescentWitness_exists hk) hstep)
      ⟨Nat.pos_of_ne_zero hstepZero,
        hstep.trans (Nat.find_spec (primeColumnDescentWitness_exists hk)).2.1,
        hprime⟩

theorem primeColumnDownPoint_safe_before_firstPrime
    {p k step : Nat} (hp : Nat.Prime p) (hk : 2 ≤ k)
    (hkp : 2 * k < p)
    (hstep : step < firstPrimeColumnDescent k) :
    SafePoint (primeColumnDownPoint p (2 * k) step) := by
  have hheightLower : 2 ≤ 2 * k - step := by
    have hfirstPrime := (firstPrimeColumnDescent_spec hk).2.2.two_le
    have hfirstHeightLe :
        2 * k - firstPrimeColumnDescent k ≤ 2 * k - step := by omega
    exact hfirstPrime.trans hfirstHeightLe
  have hheightUpper : 2 * k - step < p := by omega
  by_contra hbad
  have hprime := primeColumn_bad_height_is_prime hp hheightLower hheightUpper hbad
  exact not_prime_before_firstPrimeColumnDescent hk hstep hprime

noncomputable def primeCorridorBoundaryAnchor (root : Nat × Nat) :
    LatticePoint :=
  primeColumnDownPoint root.1 (2 * root.2)
    (firstPrimeColumnDescent root.2)

theorem primeCorridorBoundaryAnchor_spec
    {N : Nat} {root : Nat × Nat}
    (hroot : root ∈ primeCorridorRoots N) :
    primeCorridorBoundaryAnchor root ∈
        safeComponentFrontier (primeCorridorPoint root) ∧
      PrimePair (primeCorridorBoundaryAnchor root) := by
  rcases root with ⟨p, k⟩
  rcases Finset.mem_product.mp hroot with ⟨hpMem, hkMem⟩
  have hpData := Finset.mem_filter.mp hpMem
  have hp : Nat.Prime p := (Nat.mem_primesLE.mp hpData.1).2
  have hpLower : N < p := hpData.2
  have hk : 2 ≤ k := (Finset.mem_Icc.mp hkMem).1
  have hkUpper : k ≤ N / 2 := (Finset.mem_Icc.mp hkMem).2
  have hkp : 2 * k < p := by omega
  let first := firstPrimeColumnDescent k
  let predecessor := primeColumnDownPoint p (2 * k) (first - 1)
  let anchor := primeCorridorBoundaryAnchor (p, k)
  have hfirst := firstPrimeColumnDescent_spec hk
  have hpredecessorStep : first - 1 < first := by omega
  have hpredecessorReachable :
      predecessor ∈ safeComponent (primeCorridorPoint (p, k)) := by
    change SafeReachableFrom (primeCorridorPoint (p, k)) predecessor
    have hstartEq :
        primeCorridorPoint (p, k) = primeColumnDownPoint p (2 * k) 0 := by
      rfl
    rw [hstartEq]
    apply safeReachableFrom_primeColumnDownPoint (by omega)
    intro step hstep
    exact primeColumnDownPoint_safe_before_firstPrime hp hk hkp
      (hstep.trans_lt hpredecessorStep)
  have hadjacent : Adjacent predecessor anchor := by
    change Adjacent
      (primeColumnDownPoint p (2 * k) (first - 1))
      (primeColumnDownPoint p (2 * k) first)
    have hfirstEq : first - 1 + 1 = first := by omega
    simpa [hfirstEq] using
      (adjacent_primeColumnDownPoint_succ
        (p := p) (height := 2 * k) (step := first - 1) (by omega))
  have hanchorPrime : Nat.Prime anchor.y := by
    simpa [anchor, primeCorridorBoundaryAnchor, first,
      primeColumnDownPoint] using hfirst.2.2
  have hanchorPair : PrimePair anchor := by
    exact ⟨by simpa [anchor, primeCorridorBoundaryAnchor,
      primeColumnDownPoint] using hp, hanchorPrime⟩
  refine ⟨⟨?_, predecessor, hpredecessorReachable, hadjacent⟩,
    hanchorPair⟩
  exact primePair_not_mem_safeComponent hanchorPair

theorem exists_primePair_on_primeCorridorFrontier
    {N : Nat} {root : Nat × Nat}
    (hroot : root ∈ primeCorridorRoots N) :
    ∃ anchor,
      anchor ∈ safeComponentFrontier (primeCorridorPoint root) ∧
      PrimePair anchor :=
  ⟨primeCorridorBoundaryAnchor root,
    (primeCorridorBoundaryAnchor_spec hroot).1,
    (primeCorridorBoundaryAnchor_spec hroot).2⟩

theorem exists_primePair_on_highPrimeCorridorFrontier
    {N : Nat} {root : Nat × Nat}
    (hroot : root ∈ highPrimeCorridorRoots N) :
    ∃ anchor,
      anchor ∈ safeComponentFrontier (primeCorridorPoint root) ∧
      PrimePair anchor :=
  exists_primePair_on_primeCorridorFrontier
    (highPrimeCorridorRoots_subset N hroot)

end Erdos1212Kernel
