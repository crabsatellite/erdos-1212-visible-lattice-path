import Erdos1212Kernel.TaoCorputFiniteSums
import Mathlib.Data.Complex.BigOperators

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1500000

theorem taoCorput_norm_add_sq (z w : Complex) :
    ‖z + w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * (w * star z).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem taoCorput_cross_sum (z : Complex) {ι : Type*} (s : Finset ι) (v : ι → Complex) :
    (z * star (∑ i ∈ s, v i)).re = ∑ i ∈ s, (z * star (v i)).re := by
  have hs : star (∑ i ∈ s, v i) = ∑ i ∈ s, star (v i) := map_sum (starRingEnd Complex) v s
  rw [hs, Finset.mul_sum, Complex.re_sum]

/-- The source diagonal/off-diagonal decomposition, before applying a
triangle inequality to any correlation sum. -/
theorem taoCorput_norm_sum_sq (H : Nat) (v : Nat → Complex) :
    ‖∑ h ∈ Finset.Icc 1 H, v h‖ ^ 2 =
      (∑ h ∈ Finset.Icc 1 H, ‖v h‖ ^ 2) +
      2 * ∑ j ∈ Finset.Icc 1 H, ∑ i ∈ Finset.Ico 1 j, (v j * star (v i)).re := by
  induction H with
  | zero => simp
  | succ H ih =>
      have hset : Finset.Ico 1 (H + 1) = Finset.Icc 1 H := by
        ext i
        simp only [Finset.mem_Ico, Finset.mem_Icc]
        omega
      rw [Finset.sum_Icc_succ_top (by omega), taoCorput_norm_add_sq, ih,
        Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
        hset, taoCorput_cross_sum]
      ring

theorem taoCorput_row_energy (R : Finset Int) (H : Nat) (z : Int → Nat → Complex) :
    (∑ n ∈ R, ‖∑ h ∈ Finset.Icc 1 H, z n h‖ ^ 2) =
      (∑ h ∈ Finset.Icc 1 H, ∑ n ∈ R, ‖z n h‖ ^ 2) +
      2 * ∑ j ∈ Finset.Icc 1 H, ∑ i ∈ Finset.Ico 1 j,
        (∑ n ∈ R, z n j * star (z n i)).re := by
  simp_rw [taoCorput_norm_sum_sq]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  · exact Finset.sum_comm
  · congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    exact (Complex.re_sum R _).symm

end

end Erdos1212Kernel
