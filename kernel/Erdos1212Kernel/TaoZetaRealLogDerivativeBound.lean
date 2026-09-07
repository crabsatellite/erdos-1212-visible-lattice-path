import Erdos1212Kernel.TaoZetaAdjustedZeroRepulsion
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators ArithmeticFunction

set_option maxHeartbeats 1900000

theorem taoRealWeightedPrefix_abel_identity
    (z w : Nat → Real) (m : Nat) :
    (∑ n ∈ Finset.range (m + 1), w n * z n) =
      w m * (∑ n ∈ Finset.range (m + 1), z n) +
        ∑ n ∈ Finset.range m,
          (w n - w (n + 1)) * (∑ j ∈ Finset.range (n + 1), z j) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ (f := fun n => w n * z n) (n := m + 1)]
      rw [ih]
      rw [Finset.sum_range_succ (f := z) (n := m + 1)]
      rw [Finset.sum_range_succ
        (f := fun n => (w n - w (n + 1)) * (∑ j ∈ Finset.range (n + 1), z j))
        (n := m)]
      ring

theorem taoRealWeightedPrefix_linear_bound
    (z w : Nat → Real) (M : Nat) {C : Real}
    (hC : 0 ≤ C) (hz : ∀ n < M, 0 ≤ z n)
    (hw : ∀ n < M, 0 ≤ w n)
    (hmono : ∀ n, n + 1 < M → w (n + 1) ≤ w n)
    (hprefix : ∀ m ≤ M,
      (∑ n ∈ Finset.range m, z n) ≤ C * m) :
    (∑ n ∈ Finset.range M, w n * z n) ≤
      C * ∑ n ∈ Finset.range M, w n := by
  cases M with
  | zero => simp
  | succ m =>
      rw [taoRealWeightedPrefix_abel_identity]
      have hwm : 0 ≤ w m := hw m (by omega)
      have hterminal :
          w m * (∑ n ∈ Finset.range (m + 1), z n) ≤
            w m * (C * (m + 1)) :=
        mul_le_mul_of_nonneg_left (by
          simpa only [Nat.cast_add, Nat.cast_one] using hprefix (m + 1) le_rfl) hwm
      have hdiff (n : Nat) (hn : n ∈ Finset.range m) :
          0 ≤ w n - w (n + 1) := by
        exact sub_nonneg.mpr (hmono n (by
          have := Finset.mem_range.mp hn
          omega))
      have hsum :
          (∑ n ∈ Finset.range m,
            (w n - w (n + 1)) * (∑ j ∈ Finset.range (n + 1), z j)) ≤
          ∑ n ∈ Finset.range m,
            (w n - w (n + 1)) * (C * (n + 1)) := by
        apply Finset.sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_left (by
          simpa only [Nat.cast_add, Nat.cast_one] using hprefix (n + 1) (by
            have := Finset.mem_range.mp hn
            omega)) (hdiff n hn)
      have hone := taoRealWeightedPrefix_abel_identity (fun _ => (1 : Real)) w m
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hone
      calc
        w m * (∑ n ∈ Finset.range (m + 1), z n) +
            ∑ n ∈ Finset.range m,
              (w n - w (n + 1)) * (∑ j ∈ Finset.range (n + 1), z j) ≤
            w m * (C * (m + 1)) +
              ∑ n ∈ Finset.range m,
                (w n - w (n + 1)) * (C * (n + 1)) :=
          add_le_add hterminal hsum
        _ = C * (w m * (m + 1) +
              ∑ n ∈ Finset.range m, (w n - w (n + 1)) * (n + 1)) := by
          have hsumfactor :
              (∑ n ∈ Finset.range m,
                (w n - w (n + 1)) * (C * (n + 1))) =
              C * ∑ n ∈ Finset.range m,
                (w n - w (n + 1)) * (n + 1) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n _hn
            ring
          rw [hsumfactor]
          ring
        _ = C * ∑ n ∈ Finset.range (m + 1), w n := by
          have hone' :
              (∑ x ∈ Finset.range (m + 1), w x) =
                w m * ((m : Real) + 1) +
                  ∑ x ∈ Finset.range m, (w x - w (x + 1)) * ((x : Real) + 1) := by
            simpa only [Nat.cast_add, Nat.cast_one] using hone
          rw [hone']

theorem taoVonMangoldt_shifted_prefix_le (m : Nat) :
    (∑ n ∈ Finset.range m, ArithmeticFunction.vonMangoldt (n + 1)) ≤
      (Real.log 4 + 4) * m := by
  have hpsi := Chebyshev.psi_le_const_mul_self
    (show (0 : Real) ≤ m by positivity)
  have heq :
      (∑ n ∈ Finset.range m, ArithmeticFunction.vonMangoldt (n + 1)) =
        Chebyshev.psi m := by
    rw [Chebyshev.psi]
    norm_num
    rw [show Finset.Ioc 0 m = Finset.Ico 1 (m + 1) by ext n; simp; omega]
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro n _hn
    congr 1
    omega
  rw [heq]
  simpa using hpsi

theorem taoVonMangoldt_dirichlet_tsum_le
    {σ : Real} (hσ : 1 < σ) :
    (∑' n : Nat, ArithmeticFunction.vonMangoldt (n + 1) *
      ((n + 1 : Nat) : Real) ^ (-σ)) ≤
      (Real.log 4 + 4) * (1 + 1 / (σ - 1)) := by
  apply Real.tsum_le_of_sum_range_le
  · intro n
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (by positivity) _)
  · intro M
    let z : Nat → Real := fun n => ArithmeticFunction.vonMangoldt (n + 1)
    let w : Nat → Real := fun n => ((n + 1 : Nat) : Real) ^ (-σ)
    have hC : 0 ≤ Real.log 4 + 4 := by
      have := Real.log_nonneg (by norm_num : (1 : Real) ≤ 4)
      linarith
    have hweighted := taoRealWeightedPrefix_linear_bound z w M hC
      (fun n _hn => ArithmeticFunction.vonMangoldt_nonneg)
      (fun n _hn => Real.rpow_nonneg (by positivity) _)
      (fun n _hn => Real.rpow_le_rpow_of_nonpos (by positivity)
        (by exact_mod_cast (show n + 1 ≤ n + 2 by omega)) (by linarith))
      (fun m hm => by simpa only [z, Nat.cast_ofNat] using taoVonMangoldt_shifted_prefix_le m)
    have hweights :
        (∑ n ∈ Finset.range M, w n) ≤ 1 + 1 / (σ - 1) := by
      have hsum : Summable w := by
        simpa only [w, Nat.cast_add, Nat.cast_one] using
          (_root_.summable_nat_add_iff 1).2
            (Real.summable_nat_rpow.mpr (by linarith : -σ < -1))
      exact (hsum.sum_le_tsum (Finset.range M)
        (fun n _hn => Real.rpow_nonneg (by positivity) _)).trans
          (by simpa only [w] using taoRealPSeries_bound hσ)
    calc
      (∑ n ∈ Finset.range M, ArithmeticFunction.vonMangoldt (n + 1) *
          ((n + 1 : Nat) : Real) ^ (-σ)) =
          ∑ n ∈ Finset.range M, w n * z n := by
        apply Finset.sum_congr rfl
        intro n _hn
        ring
      _ ≤ (Real.log 4 + 4) * ∑ n ∈ Finset.range M, w n := hweighted
      _ ≤ (Real.log 4 + 4) * (1 + 1 / (σ - 1)) :=
        mul_le_mul_of_nonneg_left hweights hC

theorem norm_taoZetaLogDerivative_real_le
    {σ : Real} (hσ : 1 < σ) :
    ‖taoZetaLogDerivative (σ : Complex)‖ ≤
      (Real.log 4 + 4) * (1 + 1 / (σ - 1)) := by
  have hσc : 1 < ((σ : Real) : Complex).re := by simpa using hσ
  rw [taoZetaLogDerivative_eq_vonMangoldtLSeries hσc]
  have hsum := ArithmeticFunction.LSeriesSummable_vonMangoldt hσc
  unfold LSeries
  have hnorm := norm_tsum_le_tsum_norm hsum.norm
  apply hnorm.trans
  have hshift := hsum.norm.tsum_eq_zero_add
  rw [hshift]
  simp only [LSeries.term_zero, norm_zero, zero_add]
  have heq :
      (∑' n : Nat,
        ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : Complex))
          (σ : Complex) (n + 1)‖) =
      ∑' n : Nat, ArithmeticFunction.vonMangoldt (n + 1) *
        ((n + 1 : Nat) : Real) ^ (-σ) := by
    apply tsum_congr
    intro n
    rw [LSeries.norm_term_eq, if_neg (Nat.succ_ne_zero n)]
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity)]
    rfl
  rw [heq]
  exact taoVonMangoldt_dirichlet_tsum_le hσ

end

end Erdos1212Kernel
