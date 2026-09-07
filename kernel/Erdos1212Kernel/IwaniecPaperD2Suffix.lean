import Erdos1212Kernel.IwaniecThresholdFirstPair

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 650000

/-- The literal first even stopped mass: p₂<p₁<z, y/p₁≤p₂³,
with the full omitted Euler product R(p₂). -/
def iwaniecPaperD2At (level z : Real) : Real :=
  ∑ p ∈ iwaniecStrictPrimePool z,
    ∑ q ∈ iwaniecStrictPrimePool (p : Real),
      if level / p ≤ (q : Real) ^ 3 then
        iwaniecPaperR (q : Real) / ((p : Real) * q)
      else 0

def iwaniecPaperD2 (level s : Real) : Real :=
  iwaniecPaperD2At level (Real.exp (Real.log level / s))

theorem iwaniecSum_descendingFactors_real (pool : Finset Nat) (weight : Nat → Real) :
    (∑ i : Fin (iwaniecDescendingFactors pool).length,
      weight (iwaniecDescendingFactors pool)[i]) = ∑ p ∈ pool, weight p := by
  classical
  apply Finset.sum_bij (fun i _hi => (iwaniecDescendingFactors pool)[i])
  · intro i hi
    exact (Finset.mem_sort _).1 (List.getElem_mem i.isLt)
  · intro i hi j hj heq
    apply Fin.ext
    exact (List.getElem_inj (Finset.sort_nodup _ _)).1 heq
  · intro p hp
    have hmem : p ∈ iwaniecDescendingFactors pool := by
      simpa [iwaniecDescendingFactors] using hp
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
    exact ⟨⟨i, hi⟩, Finset.mem_univ _, heq⟩
  · intro i hi
    rfl

theorem iwaniecCubicThresholdMass_singleton_paperR (y p : Nat) (z : Real) :
    iwaniecCubicThresholdMass 2 (iwaniecCubicEvenRestriction y)
      iwaniecReciprocalFactorWeight [p]
      (iwaniecDescendingFactors (iwaniecStrictPrimePool z)) =
      ∑ q ∈ iwaniecStrictPrimePool z,
        if y ≤ q ^ 3 * p then iwaniecPaperR (q : Real) / q else 0 := by
  classical
  rw [iwaniecCubicThresholdMass_firstPair_singleton]
  calc
    _ = ∑ i : Fin (iwaniecDescendingFactors (iwaniecStrictPrimePool z)).length,
        if y ≤ (iwaniecDescendingFactors (iwaniecStrictPrimePool z))[i] ^ 3 * p then
          iwaniecPaperR ((iwaniecDescendingFactors (iwaniecStrictPrimePool z))[i] : Real) /
            (iwaniecDescendingFactors (iwaniecStrictPrimePool z))[i]
        else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [iwaniecPaperR_suffix z i]
      rw [abs_of_pos (iwaniecPaperR_pos _)]
      unfold iwaniecReciprocalFactorWeight
      rw [abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
      split <;> simp only [div_eq_mul_inv] <;> ring
    _ = _ := iwaniecSum_descendingFactors_real _
      (fun q => if y ≤ q ^ 3 * p then iwaniecPaperR (q : Real) / q else 0)

theorem iwaniecPaperD2At_nonneg (level z : Real) : 0 ≤ iwaniecPaperD2At level z := by
  classical
  apply Finset.sum_nonneg
  intro p hp
  apply Finset.sum_nonneg
  intro q hq
  split
  · exact div_nonneg (iwaniecPaperR_pos _).le (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · exact le_rfl

end

end Erdos1212Kernel
