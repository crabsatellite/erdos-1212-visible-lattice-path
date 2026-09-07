import Erdos1212Kernel.TaoPerronRieszKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory Set Complex
open scoped ArithmeticFunction BigOperators

set_option maxHeartbeats 1900000

def taoVonMangoldtRieszSum (x : Real) : Complex :=
  ∑ n ∈ Finset.range (Nat.ceil x + 1),
    (ArithmeticFunction.vonMangoldt n : Complex) * taoRieszCutoff (n / x)

theorem taoRieszCutoff_eq_zero_of_one_le {y : Real} (hy : 1 ≤ y) :
    taoRieszCutoff y = 0 := by
  unfold taoRieszCutoff
  rcases eq_or_lt_of_le hy with rfl | hy
  · simp
  · rw [Set.indicator_of_notMem]
    intro h
    exact (not_le_of_gt hy) h.2

theorem taoVonMangoldtRiesz_tsum_eq (x : Real) (hx : 0 < x) :
    (∑' n : Nat,
      (ArithmeticFunction.vonMangoldt n : Complex) * taoRieszCutoff (n / x)) =
      taoVonMangoldtRieszSum x := by
  unfold taoVonMangoldtRieszSum
  apply tsum_eq_sum
  intro n hn
  rw [Finset.mem_range, not_lt] at hn
  have hxceil : x ≤ (Nat.ceil x : Real) := Nat.le_ceil x
  have hceiln : (Nat.ceil x : Real) + 1 ≤ (n : Real) := by exact_mod_cast hn
  have hxn : x < (n : Real) := by linarith
  have hy : 1 ≤ (n : Real) / x := by
    exact (le_div_iff₀ hx).2 (by simpa only [one_mul] using hxn.le)
  rw [taoRieszCutoff_eq_zero_of_one_le hy, mul_zero]

theorem taoVonMangoldtRiesz_term_mellinInv
    {σ x : Real} (hσ : 0 < σ) (hx : 0 < x) (n : Nat) :
    (ArithmeticFunction.vonMangoldt n : Complex) * taoRieszCutoff (n / x) =
      (ArithmeticFunction.vonMangoldt n : Complex) *
        mellinInv σ taoRieszMellinKernel (n / x) := by
  by_cases hn : n = 0
  · subst n
    simp [ArithmeticFunction.vonMangoldt_apply]
  · have hnx : 0 < (n : Real) / x := div_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) hx
    rw [taoRiesz_mellin_inversion hσ hnx]

end

end Erdos1212Kernel
