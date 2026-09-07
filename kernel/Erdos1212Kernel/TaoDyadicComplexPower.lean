import Erdos1212Kernel.TaoDyadicWeightedDirichlet

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1800000

theorem taoDyadicWeight_scale_identity {N n : Real} (hN : 0 < N) (hn : 0 < n) (σ : Real) :
    N ^ (-σ) * (N / n) ^ σ = n ^ (-σ) := by
  rw [Real.div_rpow hN.le hn.le, Real.rpow_neg hN.le, Real.rpow_neg hn.le]
  field_simp [Real.rpow_pos_of_pos hN σ, Real.rpow_pos_of_pos hn σ]

theorem taoDyadicWeight_complex_term (N n : Nat) (hN : 0 < N) (hn : 0 < n) (hNn : N ≤ n) (σ t : Real) :
    (((N : Real) ^ (-σ) : Real) : Complex) *
        ((taoDyadicWeight N σ (n - N) : Real) : Complex) *
        ((n : Complex) ^ (-(t : Complex) * Complex.I)) =
      (n : Complex) ^ (-((σ : Complex) + (t : Complex) * Complex.I)) := by
  have hNR : 0 < (N : Real) := by exact_mod_cast hN
  have hnR : 0 < (n : Real) := by exact_mod_cast hn
  have hnC : (n : Complex) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hw : taoDyadicWeight N σ (n - N) = ((N : Real) / n) ^ σ := by
    unfold taoDyadicWeight
    rw [Nat.add_sub_of_le hNn]
  have hreal := taoDyadicWeight_scale_identity hNR hnR σ
  rw [hw]
  have hcast : (((N : Real) ^ (-σ) : Real) : Complex) *
      ((((N : Real) / n) ^ σ : Real) : Complex) =
      (((n : Real) ^ (-σ) : Real) : Complex) := by exact_mod_cast hreal
  rw [hcast, Complex.ofReal_cpow hnR.le]
  change (n : Complex) ^ ((-σ : Real) : Complex) *
      (n : Complex) ^ (-(t : Complex) * Complex.I) = _
  rw [show -((σ : Complex) + (t : Complex) * Complex.I) =
    ((-σ : Real) : Complex) + (-(t : Complex) * Complex.I) by push_cast; ring,
    Complex.cpow_add _ _ hnC]

theorem taoDyadicComplexPower_sum_identity (N M : Nat) (hN : 0 < N) (σ t : Real) :
    (((N : Real) ^ (-σ) : Real) : Complex) *
        (∑ m ∈ Finset.range M, (taoDyadicWeight N σ m : Complex) *
          (((N + m : Nat) : Complex) ^ (-(t : Complex) * Complex.I))) =
      ∑ m ∈ Finset.range M,
        (((N + m : Nat) : Complex) ^ (-((σ : Complex) + (t : Complex) * Complex.I))) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [← mul_assoc]
  have hn : 0 < N + m := by omega
  simpa only [Nat.add_sub_cancel_left] using
    taoDyadicWeight_complex_term N (N + m) hN hn (by omega) σ t

theorem taoDyadicComplexPower_band_bound (t σ : Real) (k N M : Nat)
    (hk : 2 ≤ k) (hN : 0 < N) (hMN : M ≤ N) (ht : t ≠ 0) (hσ : 0 ≤ σ)
    (hlow : (N : Real) ^ (k - 1) ≤ taoLogFrequency t) :
    ‖∑ m ∈ Finset.range M,
        (((N + m : Nat) : Complex) ^ (-((σ : Complex) + (t : Complex) * Complex.I)))‖ ≤
      (N : Real) ^ (1 - σ) * ((2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t) *
        (taoLogFrequency t / (N : Real) ^ k) ^ (taoVdcBeta k)) := by
  have hNR : 0 < (N : Real) := by exact_mod_cast hN
  have hweighted := taoDyadicWeightedDirichlet_band_bound t σ k N M hk hN hMN ht hσ hlow
  have hscale : 0 ≤ (N : Real) ^ (-σ) := Real.rpow_nonneg hNR.le _
  have hmul := mul_le_mul_of_nonneg_left hweighted hscale
  have hid := taoDyadicComplexPower_sum_identity N M hN σ t
  have hscaleN : (N : Real) ^ (-σ) * (N : Real) = (N : Real) ^ (1 - σ) := by
    calc
      _ = (N : Real) ^ (-σ) * (N : Real) ^ (1 : Real) := by rw [Real.rpow_one]
      _ = (N : Real) ^ (-σ + 1) := by rw [Real.rpow_add hNR]
      _ = _ := by congr 1; ring
  have heq : (N : Real) ^ (-σ) * ((N : Real) *
      ((2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t) *
        (taoLogFrequency t / (N : Real) ^ k) ^ (taoVdcBeta k))) =
      (N : Real) ^ (1 - σ) * ((2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t) *
        (taoLogFrequency t / (N : Real) ^ k) ^ (taoVdcBeta k)) := by
    rw [← mul_assoc, hscaleN]
  rw [← hid, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hscale]
  exact hmul.trans_eq heq

end

end Erdos1212Kernel
