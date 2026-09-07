import Erdos1212Kernel.TaoCorputFiniteSums

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1400000

/-- The H-fold averaged shift sum equals exactly H times the original
sum; the enlarged integer interval contains only proved zero padding. -/
theorem taoCorput_shift_average (z : Int → Complex) (a : Int) (N H : Nat)
    (hz : ∀ n, n ∉ taoCorputInterval a N → z n = 0) :
    (∑ n ∈ taoCorputPadding a N H, ∑ h ∈ Finset.Icc 1 H, z (n + h)) = (H : Complex) * taoCorputSum z a N := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ h ∈ Finset.Icc 1 H, taoCorputSum z a N := by
      apply Finset.sum_congr rfl
      intro h hh
      exact taoCorput_shift_sum z a N H (Nat.cast_nonneg h) (by exact_mod_cast (Finset.mem_Icc.mp hh).2) hz
    _ = _ := by simp [nsmul_eq_mul]

theorem taoCorput_shift_diagonal (z : Int → Complex) (a : Int) (N H : Nat)
    (hz : ∀ n, n ∉ taoCorputInterval a N → z n = 0) :
    (∑ h ∈ Finset.Icc 1 H, ∑ n ∈ taoCorputPadding a N H, ‖z (n + h)‖ ^ 2) =
      (H : Real) * ∑ n ∈ taoCorputInterval a N, ‖z n‖ ^ 2 := by
  calc
    _ = ∑ h ∈ Finset.Icc 1 H, ∑ n ∈ taoCorputInterval a N, ‖z n‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro h hh
      apply taoCorput_shift_sum (fun n => ‖z n‖ ^ 2) a N H (Nat.cast_nonneg h)
        (by exact_mod_cast (Finset.mem_Icc.mp hh).2)
      intro n hn
      rw [hz n hn, norm_zero, zero_pow (by decide : (2 : Nat) ≠ 0)]
    _ = _ := by simp [nsmul_eq_mul]

theorem taoCorput_shift_cauchy (z : Int → Complex) (a : Int) (N H : Nat)
    (hz : ∀ n, n ∉ taoCorputInterval a N → z n = 0) :
    (H : Real) ^ 2 * ‖taoCorputSum z a N‖ ^ 2 ≤
      ((N : Real) + H) * ∑ n ∈ taoCorputPadding a N H, ‖∑ h ∈ Finset.Icc 1 H, z (n + h)‖ ^ 2 := by
  have h := taoCorput_complex_cauchy (taoCorputPadding a N H) (fun n => ∑ h ∈ Finset.Icc 1 H, z (n + h))
  rw [taoCorput_shift_average z a N H hz, taoCorputPadding_card] at h
  simpa only [Complex.norm_mul, Complex.norm_natCast, mul_pow, Nat.cast_add] using h

/-- Reindex an off-diagonal term into its actual difference correlation.
Neither member of the shifted overlap is discarded. -/
theorem taoCorput_shift_correlation (z : Int → Complex) (a : Int) (N H : Nat)
    (hz : ∀ n, n ∉ taoCorputInterval a N → z n = 0)
    {i j : Nat} (hi : i ∈ Finset.Icc 1 H) (hij : i ≤ j) :
    (∑ n ∈ taoCorputPadding a N H, z (n + j) * star (z (n + i))) =
      taoCorputCorrelation z a N (j - i) := by
  let g : Int → Complex := fun m => z (m + (j - i : Nat)) * star (z m)
  have hg : ∀ n, n ∉ taoCorputInterval a N → g n = 0 := by
    intro n hn
    dsimp [g]
    simp only [hz n hn, map_zero, mul_zero]
  have h := taoCorput_shift_sum g a N H (h := (i : Int)) (Nat.cast_nonneg i)
    (by exact_mod_cast (Finset.mem_Icc.mp hi).2) hg
  change (∑ n ∈ taoCorputPadding a N H, z (n + j) * star (z (n + i))) = ∑ n ∈ taoCorputInterval a N, g n
  rw [← h]
  apply Finset.sum_congr rfl
  intro n _hn
  dsimp [g]
  rw [Nat.cast_sub hij]
  congr 2
  ring

end

end Erdos1212Kernel
