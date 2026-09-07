import Erdos1212Kernel.IwaniecPaperSupportCount
import Erdos1212Kernel.IwaniecReferencePrimeCutoff

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

/-- Integer strict cutoff containing exactly the first `K` primes. -/
def iwaniecStrictReferenceCutoff (K : Nat) : Nat :=
  if K = 0 then 2 else iwaniecReferencePrimeCutoff K + 1

theorem iwaniecStrictPrimePool_referenceCutoff (K : Nat) :
    iwaniecStrictPrimePool (iwaniecStrictReferenceCutoff K) =
      iwaniecReferencePrimePool K := by
  by_cases hK : K = 0
  · subst K
    have hpool : iwaniecReferencePrimePool 0 = ∅ := by
      apply Finset.card_eq_zero.mp
      exact iwaniecReferencePrimePool_card 0
    simp [iwaniecStrictReferenceCutoff, iwaniecStrictPrimePool_eq_empty (le_refl 2), hpool]
  · have hKPos : 0 < K := Nat.pos_of_ne_zero hK
    rw [iwaniecStrictReferenceCutoff, if_neg hK,
      Nat.cast_add, Nat.cast_one, iwaniecStrictPrimePool_nat_add_one]
    exact (iwaniecReferencePrimePool_eq_vaughanPrimePool hKPos).symm

theorem two_le_iwaniecStrictReferenceCutoff (K : Nat) :
    2 ≤ iwaniecStrictReferenceCutoff K := by
  by_cases hK : K = 0
  · simp [iwaniecStrictReferenceCutoff, hK]
  · rw [iwaniecStrictReferenceCutoff, if_neg hK]
    have hp : 2 ≤ iwaniecReferencePrimeCutoff K :=
      (Nat.prime_nth_prime (K - 1)).two_le
    omega

/-- The quantitative support estimate will be applied to exactly this
`A`-carrier.  Neither an upper bound nor a changed prime pool is used. -/
theorem iwaniecCubicShiftedErrorMass_eq_paperSupportCount
    {r y : Nat} (hr : 0 < r) (Q : Finset Nat)
    (hy : iwaniecStrictReferenceCutoff Q.card ≤ y) :
    iwaniecCubicShiftedErrorMass r y Q =
      (iwaniecPaperSupportCount (2 * r - 1) y
        (iwaniecStrictReferenceCutoff Q.card) : Real) := by
  have hyOne : (1 : Real) < y := by
    exact_mod_cast (show 1 < y by
      have := two_le_iwaniecStrictReferenceCutoff Q.card
      omega)
  have hodd : Odd (2 * r - 1) := ⟨r - 1, by omega⟩
  have hnotEven : ¬Even (2 * r - 1) := Nat.not_even_iff_odd.mpr hodd
  rw [iwaniecPaperSupportCount_eq_realTotalCount _ hyOne (by exact_mod_cast hy),
    if_neg hnotEven, iwaniecStrictPrimePool_referenceCutoff,
    iwaniecCubicShiftedErrorMass_eq_realTotalCount hr]

theorem iwaniecPaperA_logRatio
    (rank : Nat) {level z : Real} (hlevel : 1 < level) (hz : 0 < z) :
    iwaniecPaperA rank level (Real.log level / Real.log z) =
      iwaniecPaperSupportCount rank level z := by
  unfold iwaniecPaperA
  have hL : Real.log level ≠ 0 := (Real.log_pos hlevel).ne'
  have hquot : Real.log level / (Real.log level / Real.log z) = Real.log z := by
    by_cases hlogz : Real.log z = 0
    · simp [hlogz]
    · field_simp [hL, hlogz]
  rw [hquot, Real.exp_log hz]

/-- The exact local error mass is the displayed paper `A_(2r-1,y)(s)` at
`s=log y/log z`, with the strict cutoff `z` already matched to the reference
prime state. -/
theorem iwaniecCubicShiftedErrorMass_eq_paperA
    {r y : Nat} (hr : 0 < r) (Q : Finset Nat)
    (hy : iwaniecStrictReferenceCutoff Q.card ≤ y) :
    iwaniecCubicShiftedErrorMass r y Q =
      (iwaniecPaperA (2 * r - 1) y
        (Real.log y / Real.log (iwaniecStrictReferenceCutoff Q.card)) : Real) := by
  have hz : (0 : Real) < iwaniecStrictReferenceCutoff Q.card := by
    exact_mod_cast (show 0 < iwaniecStrictReferenceCutoff Q.card by
      have := two_le_iwaniecStrictReferenceCutoff Q.card
      omega)
  have hyOne : (1 : Real) < y := by
    exact_mod_cast (show 1 < y by
      have := two_le_iwaniecStrictReferenceCutoff Q.card
      omega)
  rw [iwaniecPaperA_logRatio _ hyOne hz]
  exact iwaniecCubicShiftedErrorMass_eq_paperSupportCount hr Q hy

end

end Erdos1212Kernel
