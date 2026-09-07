import Erdos1212Kernel.IwaniecPaperAChildDomain
import Erdos1212Kernel.IwaniecPaperABoundedLevel

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 650000

def iwaniecPaperChildMajorantTerm (rank : Nat) (level : Real) (p : Nat) : Real :=
  (iwaniecAuxWeightPower (level / (p : Real)) (Real.log (level / (p : Real)) / Real.log (p : Real)) *
    iwaniecAuxG rank (Real.log (level / (p : Real)) / Real.log (p : Real)) /
      Real.log (level / (p : Real)) ^ 2) * (level / (p : Real))

/-- This consumes the actual rank-n induction hypothesis on every child;
the y/p and xi(y/p) conditions are proved by the domain transport. -/
theorem iwaniecPaperA_child_count_sum_le (n : Nat) {C level s : Real}
    (hy : 1 < level) (hξ : iwaniecAuxSZero ≤ iwaniecPaperXi level)
    (hs : iwaniecCorollaryThreeDomainStart (n + 1) ≤ s)
    (hIH : ∀ y t : Real, 1 < y → iwaniecAuxGStart (n + 1) ≤ t → t ≤ iwaniecPaperXi y →
      (iwaniecPaperA n y t : Real) ≤ iwaniecPaperAMajorant C n y t) :
    ((∑ p ∈ iwaniecStrictPrimeBand
      (Real.exp (Real.log level / (iwaniecPaperXi level - 1))) (Real.exp (Real.log level / s)),
      iwaniecPaperA n (level / (p : Real)) (Real.log level / Real.log (p : Real) - 1) : Nat) : Real) ≤
      (C * ((n : Real) / ((n : Real) + 1))) *
      ∑ p ∈ iwaniecStrictPrimeBand
        (Real.exp (Real.log level / (iwaniecPaperXi level - 1))) (Real.exp (Real.log level / s)),
        iwaniecPaperChildMajorantTerm (n + 1) level p := by
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hprime := (mem_iwaniecStrictPrimePool.mp (Finset.mem_filter.mp hp).1).1
  obtain ⟨hchild, hstart, hxi⟩ := iwaniecPaperBand_child_domain (n + 1) hy hξ hs hp
  have hh := hIH (level / (p : Real)) (Real.log (level / (p : Real)) / Real.log (p : Real)) hchild hstart hxi
  rw [← iwaniecPaperChild_logParameter (show 0 < level by linarith) hprime]
  convert hh using 1 <;> unfold iwaniecPaperAMajorant iwaniecPaperChildMajorantTerm <;> ring

theorem iwaniec_rank_ratio_ge_half {n : Nat} (hn : 1 ≤ n) :
    (1 / 2 : Real) ≤ (n : Real) / ((n : Real) + 1) := by
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  apply (le_div_iff₀ (show 0 < (n : Real) + 1 by positivity)).mpr
  linarith only [hnR]

theorem iwaniec_middle_step_budget {B q C f W : Real}
    (hB : 0 ≤ B) (hq : 0 ≤ q) (hC : 2 ≤ C) (hf : (1 / 2 : Real) ≤ f) (hW : 1 ≤ W) :
    B * q + C * f * (B * W * (1 + q)) ≤ C * B * (f * (1 + 4 * q) * W) := by
  have hC0 : 0 ≤ C := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hW0 : 0 ≤ W := by linarith
  have hCf : 1 ≤ C * f := by
    have hh := mul_le_mul hC hf (by norm_num : (0 : Real) ≤ 1 / 2) hC0
    nlinarith only [hh]
  have hCfW : 1 ≤ C * f * W := by
    have hh := mul_le_mul hCf hW (by norm_num : (0 : Real) ≤ 1) (mul_nonneg hC0 hf0)
    simpa only [one_mul] using hh
  have hpaid := mul_le_mul_of_nonneg_right hCfW (mul_nonneg hB hq)
  have hpositive : 0 ≤ C * f * B * W * q := by positivity
  nlinarith only [hpaid, hpositive]

end

end Erdos1212Kernel
