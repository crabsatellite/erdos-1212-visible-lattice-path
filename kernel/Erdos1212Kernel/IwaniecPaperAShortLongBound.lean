import Erdos1212Kernel.IwaniecPaperAFactorialTail
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

def iwaniecStrictPrimeReciprocalSum (z : Real) : Real :=
  ∑ p ∈ iwaniecStrictPrimePool z, (p : Real)⁻¹

theorem iwaniecStrictPrimePool_card_le {z : Real} (hz : 0 ≤ z) :
    ((iwaniecStrictPrimePool z).card : Real) ≤ z := by
  have hsub : iwaniecStrictPrimePool z ⊆ Finset.Icc 1 ⌊z⌋₊ := by
    intro p hp
    obtain ⟨hprime, hlt⟩ := mem_iwaniecStrictPrimePool.mp hp
    exact Finset.mem_Icc.mpr ⟨hprime.pos, Nat.le_floor hlt.le⟩
  have hcard : (iwaniecStrictPrimePool z).card ≤ ⌊z⌋₊ := by
    simpa using Finset.card_le_card hsub
  exact (show ((iwaniecStrictPrimePool z).card : Real) ≤ (⌊z⌋₊ : Real) by
    exact_mod_cast hcard).trans (Nat.floor_le hz)

theorem iwaniecStrictPrimeReciprocalSum_eq_list (z : Real) :
    ((iwaniecDescendingFactors (iwaniecStrictPrimePool z)).map
        (fun p : Nat => (p : Real)⁻¹)).sum =
      iwaniecStrictPrimeReciprocalSum z := by
  let pool := iwaniecStrictPrimePool z
  let weight := fun p : Nat => (p : Real)⁻¹
  have hperm := Finset.sort_perm_toList pool (fun p q : Nat => q ≤ p)
  calc
    _ = (pool.toList.map weight).sum := (hperm.map weight).sum_eq
    _ = ∑ p ∈ pool, weight p := Finset.sum_map_toList pool weight

theorem iwaniecCubicRealProductCount_sum_short_le
    (offset : Nat) (level : Real) (factors : List Nat) (upper K : Nat)
    {z : Real} (hz : 1 ≤ z) (hsize : (factors.length : Real) ≤ z)
    (hupper : upper ≤ K) :
    (∑ k ∈ Finset.range upper,
      (iwaniecCubicRealProductCount offset level factors k : Real)) ≤ 3 * z ^ K := by
  have hterm : ∀ k ∈ Finset.range upper,
      (iwaniecCubicRealProductCount offset level factors k : Real) ≤
        z ^ K * (1 / (k.factorial : Real)) := by
    intro k hk
    have hcount : (iwaniecCubicRealProductCount offset level factors k : Real) ≤
        factors.length.choose k := by
      exact_mod_cast iwaniecCubicRealProductCount_le_choose offset level factors k
    have hchoose := Nat.choose_le_pow_div (α := Real) k factors.length
    have hpower : (factors.length : Real) ^ k ≤ z ^ K := by
      exact (pow_le_pow_left₀ (by positivity) hsize k).trans
        (pow_le_pow_right₀ hz (by have := Finset.mem_range.mp hk; omega))
    have hdiv := div_le_div_of_nonneg_right hpower
      (by positivity : (0 : Real) ≤ k.factorial)
    exact (hcount.trans hchoose).trans (by simpa [div_eq_mul_inv] using hdiv)
  have hexp : (∑ k ∈ Finset.range upper, (1 : Real) / k.factorial) ≤ Real.exp 1 := by
    simpa using Real.sum_le_exp_of_nonneg (x := (1 : Real)) (by norm_num) upper
  calc
    (∑ k ∈ Finset.range upper,
        (iwaniecCubicRealProductCount offset level factors k : Real)) ≤
        ∑ k ∈ Finset.range upper, z ^ K * (1 / (k.factorial : Real)) :=
      Finset.sum_le_sum hterm
    _ = z ^ K * ∑ k ∈ Finset.range upper, (1 : Real) / k.factorial := by
      rw [Finset.mul_sum]
    _ ≤ z ^ K * Real.exp 1 := mul_le_mul_of_nonneg_left hexp (pow_nonneg (by linarith) _)
    _ ≤ z ^ K * 3 := mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le
      (pow_nonneg (by linarith) _)
    _ = 3 * z ^ K := by ring

/-- Quantitative short/long support estimate at the paper's literal prime
cutoff.  Both terms retain their genuine counting/reciprocal origin. -/
theorem iwaniecPaperSupportCount_short_long_bound
    (rank K : Nat) {level z : Real} (hlevel : 0 ≤ level) (hz : 1 ≤ z)
    (hthreshold : 2 * iwaniecStrictPrimeReciprocalSum z ≤ (K + 1 : Nat)) :
    (iwaniecPaperSupportCount rank level z : Real) ≤
      3 * z ^ K + 2 * level * (iwaniecStrictPrimeReciprocalSum z) ^ K / K.factorial := by
  let factors := iwaniecDescendingFactors (iwaniecStrictPrimePool z)
  let offset := if Even rank then 1 else 0
  have hsize : (factors.length : Real) ≤ z := by
    simpa [factors, iwaniecDescendingFactors] using
      iwaniecStrictPrimePool_card_le (by linarith : 0 ≤ z)
  have hpos : ∀ p ∈ factors, 0 < p := by
    apply iwaniecDescendingFactors_positive
    intro p hp
    exact (mem_iwaniecStrictPrimePool.mp hp).1
  have hrecip : (factors.map (fun p : Nat => (p : Real)⁻¹)).sum =
      iwaniecStrictPrimeReciprocalSum z := iwaniecStrictPrimeReciprocalSum_eq_list z
  have hnonneg : 0 ≤ iwaniecStrictPrimeReciprocalSum z := by
    unfold iwaniecStrictPrimeReciprocalSum
    exact Finset.sum_nonneg (fun p _hp => inv_nonneg.mpr (Nat.cast_nonneg p))
  unfold iwaniecPaperSupportCount
  rw [Nat.cast_sum]
  change (∑ k ∈ Finset.range (rank + 1),
    (iwaniecCubicRealProductCount offset level factors k : Real)) ≤ _
  by_cases hK : K ≤ rank + 1
  · have hshort := iwaniecCubicRealProductCount_sum_short_le
      offset level factors K K hz hsize le_rfl
    have hlong := iwaniecCubicRealProductCount_sum_tail_le
      offset level factors K (rank + 1) hlevel hpos (by rwa [hrecip])
    rw [hrecip] at hlong
    have hsplit := Finset.sum_range_add_sum_Ico
      (fun k => (iwaniecCubicRealProductCount offset level factors k : Real)) hK
    rw [← hsplit]
    exact add_le_add hshort hlong
  · have hshort := iwaniecCubicRealProductCount_sum_short_le
      offset level factors (rank + 1) K hz hsize (by omega)
    have htailNonneg : 0 ≤
        2 * level * (iwaniecStrictPrimeReciprocalSum z) ^ K / K.factorial := by positivity
    exact hshort.trans (le_add_of_nonneg_right htailNonneg)

end

end Erdos1212Kernel
