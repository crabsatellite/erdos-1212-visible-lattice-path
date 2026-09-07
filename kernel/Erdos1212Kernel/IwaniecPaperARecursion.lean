import Erdos1212Kernel.IwaniecPaperSupportRecursion
import Erdos1212Kernel.IwaniecPaperSupportReferenceTransport

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

theorem iwaniecPaperCutoff_le_level
    {level s : Real} (hlevel : 1 < level) (hs : 1 ≤ s) :
    Real.exp (Real.log level / s) ≤ level := by
  calc
    Real.exp (Real.log level / s) ≤ Real.exp (Real.log level) := by
      apply Real.exp_le_exp.mpr
      exact div_le_self (Real.log_pos hlevel).le hs
    _ = level := Real.exp_log (zero_lt_one.trans hlevel)

theorem iwaniecPaperCutoff_prime_cube_lt
    {level s : Real} (hlevel : 1 < level) (hs : 3 ≤ s)
    {p : Nat} (hp : p ∈ iwaniecStrictPrimePool (Real.exp (Real.log level / s))) :
    (p : Real) ^ 3 < level := by
  have hpData := mem_iwaniecStrictPrimePool.mp hp
  have hpow : (p : Real) ^ 3 < Real.exp (Real.log level / s) ^ 3 :=
    pow_lt_pow_left₀ hpData.2 (by positivity) (by norm_num)
  apply hpow.trans_le
  calc
    Real.exp (Real.log level / s) ^ 3 =
        Real.exp (3 * (Real.log level / s)) := (Real.exp_nat_mul _ 3).symm
    _ ≤ Real.exp (Real.log level) := by
      apply Real.exp_le_exp.mpr
      rw [← mul_div_assoc, div_le_iff₀ (by linarith : 0 < s)]
      nlinarith [Real.log_pos hlevel]
    _ = level := Real.exp_log (zero_lt_one.trans hlevel)

theorem iwaniecPaperChild_logParameter
    {level : Real} (hlevel : 0 < level) {p : Nat} (hp : p.Prime) :
    Real.log (level / p) / Real.log p = Real.log level / Real.log p - 1 := by
  rw [Real.log_div hlevel.ne' (by exact_mod_cast hp.ne_zero), sub_div,
    div_self hp.log_ne_zero]

/-- The first displayed Lemma 17 recursion with all levels, strict prime
cutoffs and the child parameter `log y/log p - 1` retained literally. -/
theorem iwaniecPaperA_odd_recursion
    (r : Nat) {level s : Real} (hlevel : 1 < level) (hs : 2 ≤ s) :
    iwaniecPaperA (2 * r + 1) level s =
      1 + ∑ p ∈ iwaniecStrictPrimePool (Real.exp (Real.log level / s)),
        iwaniecPaperA (2 * r) (level / p) (Real.log level / Real.log p - 1) := by
  classical
  change iwaniecPaperSupportCount (2 * r + 1) level
    (Real.exp (Real.log level / s)) = _
  have hz := iwaniecPaperCutoff_le_level hlevel (by linarith : 1 ≤ s)
  rw [iwaniecPaperSupportCount_odd_recursion r hlevel hz]
  apply congrArg (fun n : Nat => 1 + n)
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpPrime, hpLt⟩ := mem_iwaniecStrictPrimePool.mp hp
  have hpPos : (0 : Real) < p := by exact_mod_cast hpPrime.pos
  have hchild : 1 < level / p := by
    rw [lt_div_iff₀ hpPos, one_mul]
    exact hpLt.trans_le hz
  rw [← iwaniecPaperChild_logParameter (zero_lt_one.trans hlevel) hpPrime]
  exact (iwaniecPaperA_logRatio (2 * r) hchild hpPos).symm

/-- Definition-derived correction to the second Lemma 17 display.  The
empty-tuple term `1` has been proved necessary, not silently omitted. -/
theorem iwaniecPaperA_even_recursion_with_unit
    (r : Nat) {level s : Real} (hlevel : 1 < level) (hs : 3 ≤ s) :
    iwaniecPaperA (2 * r + 2) level s =
      1 + ∑ p ∈ iwaniecStrictPrimePool (Real.exp (Real.log level / s)),
        iwaniecPaperA (2 * r + 1) (level / p) (Real.log level / Real.log p - 1) := by
  classical
  change iwaniecPaperSupportCount (2 * r + 2) level
    (Real.exp (Real.log level / s)) = _
  have hz := iwaniecPaperCutoff_le_level hlevel (by linarith : 1 ≤ s)
  rw [iwaniecPaperSupportCount_even_recursion_with_unit r hlevel
    (fun _ hp => iwaniecPaperCutoff_prime_cube_lt hlevel hs hp)]
  apply congrArg (fun n : Nat => 1 + n)
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpPrime, hpLt⟩ := mem_iwaniecStrictPrimePool.mp hp
  have hpPos : (0 : Real) < p := by exact_mod_cast hpPrime.pos
  have hchild : 1 < level / p := by
    rw [lt_div_iff₀ hpPos, one_mul]
    exact hpLt.trans_le hz
  rw [← iwaniecPaperChild_logParameter (zero_lt_one.trans hlevel) hpPrime]
  exact (iwaniecPaperA_logRatio (2 * r + 1) hchild hpPos).symm

end

end Erdos1212Kernel
