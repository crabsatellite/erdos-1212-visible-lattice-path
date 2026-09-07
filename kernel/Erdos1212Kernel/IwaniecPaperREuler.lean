import Erdos1212Kernel.IwaniecEulerProductError
import Erdos1212Kernel.IwaniecStrictPrimeSuffix

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 600000

/-- The paper's literal R(z): all primes strictly below the real cutoff. -/
def iwaniecPaperR (z : Real) : Real :=
  ∏ p ∈ iwaniecStrictPrimePool z, (1 - (p : Real)⁻¹)

theorem iwaniecPaperR_pos (z : Real) : 0 < iwaniecPaperR z := by
  unfold iwaniecPaperR
  apply Finset.prod_pos
  intro p hp
  simpa only [one_div] using Erdos696.Mertens.one_sub_inv_prime_pos p (mem_iwaniecStrictPrimePool.mp hp).1

theorem iwaniecPaperR_le_one (z : Real) : iwaniecPaperR z ≤ 1 := by
  unfold iwaniecPaperR
  have hh : (∏ p ∈ iwaniecStrictPrimePool z, (1 - (p : Real)⁻¹)) ≤
      ∏ _p ∈ iwaniecStrictPrimePool z, (1 : Real) := by
    apply Finset.prod_le_prod
    · intro p hp
      have hpos : 0 < 1 - (p : Real)⁻¹ := by
        simpa only [one_div] using Erdos696.Mertens.one_sub_inv_prime_pos p (mem_iwaniecStrictPrimePool.mp hp).1
      exact hpos.le
    · intro p _hp
      have hp0 : 0 ≤ (p : Real)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
      linarith
  simpa using hh

theorem iwaniecStrictPrimePool_eq_ceil_pred (z : Real) :
    iwaniecStrictPrimePool z = Nat.primesLE (Nat.ceil z - 1) := by
  ext p
  rw [mem_iwaniecStrictPrimePool, Nat.mem_primesLE]
  constructor
  · rintro ⟨hp, hpz⟩
    have hh : p < Nat.ceil z := Nat.lt_ceil.mpr hpz
    exact ⟨by omega, hp⟩
  · rintro ⟨hbound, hp⟩
    have hceil : p < Nat.ceil z := by have hp2 := hp.two_le; omega
    exact ⟨hp, Nat.lt_ceil.mp hceil⟩

theorem iwaniecPaperR_eq_mertensProd (z : Real) :
    iwaniecPaperR z = Erdos696.Mertens.mertensProd (Nat.ceil z - 1) := by
  rw [iwaniecPaperR, iwaniecStrictPrimePool_eq_ceil_pred, Nat.primesLE_eq_filter_range]
  simp only [Erdos696.Mertens.mertensProd, one_div]

theorem iwaniecPaperR_eq_listEuler (z : Real) :
    iwaniecPaperR z = iwaniecListEulerProduct iwaniecReciprocalFactorWeight
      (iwaniecDescendingFactors (iwaniecStrictPrimePool z)) := by
  rw [iwaniecListEulerProduct_descendingFactors]
  rfl

theorem iwaniecPaperR_suffix (z : Real)
    (i : Fin (iwaniecDescendingFactors (iwaniecStrictPrimePool z)).length) :
    iwaniecListEulerProduct iwaniecReciprocalFactorWeight
      ((iwaniecDescendingFactors (iwaniecStrictPrimePool z)).drop (i.val + 1)) =
      iwaniecPaperR ((iwaniecDescendingFactors (iwaniecStrictPrimePool z))[i] : Real) := by
  rw [iwaniecStrictPrimeSuffix z i, ← iwaniecPaperR_eq_listEuler]

end

end Erdos1212Kernel
