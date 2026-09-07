import Erdos1212Kernel.AlgebraicCorridorSupport

namespace Erdos1212Kernel

noncomputable section

/-! The canonical finite prime state for one literal band.  It is the union
of the actual prime-factor sets of the `B` band values; consequently the
support consumer receives its factor-containment hypothesis by construction,
not from a named or conditional axiom. -/

def corridorBandPrimeFactors (lower B : ℕ) : Finset ℕ :=
  (Finset.range B).biUnion (fun i => (lower + i).primeFactors)

theorem mem_corridorBandPrimeFactors_of_dvd
    {lower B y p : ℕ} (hlower : 0 < lower)
    (hyLower : lower ≤ y) (hyUpper : y < lower + B)
    (hp : p.Prime) (hpy : p ∣ y) :
    p ∈ corridorBandPrimeFactors lower B := by
  obtain ⟨i, hi⟩ := Nat.exists_eq_add_of_le hyLower
  have hiB : i < B := by omega
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_range.mpr hiB, ?_⟩
  apply Nat.mem_primeFactors.mpr
  refine ⟨hp, ?_, ?_⟩
  · simpa [hi] using hpy
  · subst y
    omega

theorem corridorBandPrimeFactors_state
    {lower B : ℕ} (hlower : 0 < lower) :
    ∀ y, lower ≤ y → y < lower + B →
      ∀ p, p.Prime → p ∣ y → p ∈ corridorBandPrimeFactors lower B := by
  intro y hyLower hyUpper p hp hpy
  exact mem_corridorBandPrimeFactors_of_dvd hlower hyLower hyUpper hp hpy

theorem prime_of_mem_corridorBandPrimeFactors
    {lower B p : ℕ} (hp : p ∈ corridorBandPrimeFactors lower B) :
    p.Prime := by
  rcases Finset.mem_biUnion.mp hp with ⟨i, hi, hpi⟩
  exact Nat.prime_of_mem_primeFactors hpi

theorem dvd_of_mem_corridorBandPrimeFactors
    {lower B p : ℕ} (hp : p ∈ corridorBandPrimeFactors lower B) :
    ∃ i, i < B ∧ p ∣ lower + i := by
  rcases Finset.mem_biUnion.mp hp with ⟨i, hi, hpi⟩
  exact ⟨i, Finset.mem_range.mp hi, Nat.dvd_of_mem_primeFactors hpi⟩

end

end Erdos1212Kernel
