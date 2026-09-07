import Erdos1212Kernel.TaoCorputGram
import Erdos1212Kernel.TaoCorputAveraging
import Erdos1212Kernel.TaoCorputDifferenceCount

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1500000

theorem taoCorput_energy_identity (z : Int → Complex) (a : Int) (N H : Nat)
    (hz : ∀ n, n ∉ taoCorputInterval a N → z n = 0) :
    (∑ n ∈ taoCorputPadding a N H, ‖∑ h ∈ Finset.Icc 1 H, z (n + h)‖ ^ 2) =
      (H : Real) * (∑ n ∈ taoCorputInterval a N, ‖z n‖ ^ 2) +
      2 * ∑ j ∈ Finset.Icc 1 H, ∑ i ∈ Finset.Ico 1 j, (taoCorputCorrelation z a N (j - i)).re := by
  have h := taoCorput_row_energy (taoCorputPadding a N H) H (fun n h => z (n + h))
  rw [taoCorput_shift_diagonal z a N H hz] at h
  rw [h]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_Ico.mp hi
  have hj' := Finset.mem_Icc.mp hj
  have hiH : i ∈ Finset.Icc 1 H := Finset.mem_Icc.mpr ⟨hi'.1, by omega⟩
  rw [taoCorput_shift_correlation z a N H hz hiH hi'.2.le]

theorem taoCorput_energy_bound (z : Int → Complex) (a : Int) (N H : Nat)
    (hz : ∀ n, n ∉ taoCorputInterval a N → z n = 0) :
    (∑ n ∈ taoCorputPadding a N H, ‖∑ h ∈ Finset.Icc 1 H, z (n + h)‖ ^ 2) ≤
      (H : Real) * ((∑ n ∈ taoCorputInterval a N, ‖z n‖ ^ 2) +
        2 * ∑ h ∈ Finset.Icc 1 H, ‖taoCorputCorrelation z a N h‖) := by
  have hre : (∑ j ∈ Finset.Icc 1 H, ∑ i ∈ Finset.Ico 1 j, (taoCorputCorrelation z a N (j - i)).re) ≤
      ∑ j ∈ Finset.Icc 1 H, ∑ i ∈ Finset.Ico 1 j, ‖taoCorputCorrelation z a N (j - i)‖ := by
    apply Finset.sum_le_sum
    intro j _hj
    apply Finset.sum_le_sum
    intro i _hi
    exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have hcount := taoCorput_difference_count_bound (fun h => ‖taoCorputCorrelation z a N h‖) H (fun h => norm_nonneg _)
  rw [taoCorput_energy_identity z a N H hz]
  linarith

/-- Exact finite van der Corput energy inequality with the padding cost
N+H shown explicitly. No boundedness or phase assumption is hidden. -/
theorem taoCorput_vdc_scaled (z : Int → Complex) (a : Int) (N H : Nat) (hH : 0 < H)
    (hz : ∀ n, n ∉ taoCorputInterval a N → z n = 0) :
    (H : Real) * ‖taoCorputSum z a N‖ ^ 2 ≤
      ((N : Real) + H) * ((∑ n ∈ taoCorputInterval a N, ‖z n‖ ^ 2) +
        2 * ∑ h ∈ Finset.Icc 1 H, ‖taoCorputCorrelation z a N h‖) := by
  have hHreal : (0 : Real) < H := by exact_mod_cast hH
  have h := (taoCorput_shift_cauchy z a N H hz).trans
    (mul_le_mul_of_nonneg_left (taoCorput_energy_bound z a N H hz) (by positivity))
  apply le_of_mul_le_mul_left (a := (H : Real)) _ hHreal
  convert h using 1 <;> ring

theorem taoCorput_vdc_unit_scaled (z : Int → Complex) (a : Int) (N H : Nat) (hH : 0 < H) (hHN : H ≤ N)
    (hz : ∀ n, n ∉ taoCorputInterval a N → z n = 0)
    (hunit : ∀ n ∈ taoCorputInterval a N, ‖z n‖ ≤ 1) :
    (H : Real) * ‖taoCorputSum z a N‖ ^ 2 ≤
      2 * (N : Real) * ((N : Real) + 2 * ∑ h ∈ Finset.Icc 1 H, ‖taoCorputCorrelation z a N h‖) := by
  have hdiag : (∑ n ∈ taoCorputInterval a N, ‖z n‖ ^ 2) ≤ (N : Real) := by
    calc
      _ ≤ ∑ _n ∈ taoCorputInterval a N, (1 : Real) := by
        apply Finset.sum_le_sum
        intro n hn
        simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (hunit n hn) 2
      _ = _ := by simp [taoCorputInterval_card]
  have hcount : ((N : Real) + H) ≤ 2 * N := by exact_mod_cast (show N + H ≤ 2 * N by omega)
  have hsum : 0 ≤ ∑ h ∈ Finset.Icc 1 H, ‖taoCorputCorrelation z a N h‖ := Finset.sum_nonneg (fun h _ => norm_nonneg _)
  calc
    _ ≤ ((N : Real) + H) * ((∑ n ∈ taoCorputInterval a N, ‖z n‖ ^ 2) +
        2 * ∑ h ∈ Finset.Icc 1 H, ‖taoCorputCorrelation z a N h‖) := taoCorput_vdc_scaled z a N H hH hz
    _ ≤ ((N : Real) + H) * ((N : Real) + 2 * ∑ h ∈ Finset.Icc 1 H, ‖taoCorputCorrelation z a N h‖) := by
      apply mul_le_mul_of_nonneg_left (add_le_add hdiag le_rfl) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount (by positivity)

end

end Erdos1212Kernel
