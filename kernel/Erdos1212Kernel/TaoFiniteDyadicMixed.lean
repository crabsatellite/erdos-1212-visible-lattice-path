import Erdos1212Kernel.TaoFiniteDyadicZetaBlocks

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1800000

/-- Mixed finite dyadic aggregation: scales below R use the weighted
trivial estimate, while scales from R onward use oscillatory absorption. -/
theorem taoFiniteDyadic_zeta_mixed_scales (t σ : Real) (R J : Nat)
    (ht : t ≠ 0) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hR : 1 ≤ R) (hRJ : R ≤ J)
    (hfrequency : ∀ r, R ≤ r → r < J → ((2 ^ r : Nat) : Real) ≤ taoLogFrequency t)
    (hwidth : ∀ r, R ≤ r → r < J →
      1 - σ ≤ taoExplicitDecayExponent (taoLogFrequency t) ((2 ^ r : Nat) : Real)) :
    ‖∑ n ∈ Finset.Ico 1 (2 ^ J), taoZetaTerm σ t n‖ ≤
      (J : Real) * (((2 ^ R : Nat) : Real) ^ (1 - σ) +
        (2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t)) := by
  let S : Real := (((2 ^ R : Nat) : Real) ^ (1 - σ))
  let L : Real := (2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t)
  have hT := taoLogFrequency_pos ht
  have hS : 0 ≤ S := by unfold S; positivity
  have hL : 0 ≤ L := by
    unfold L
    have hlog := Real.log_nonneg (by linarith : 1 ≤ 2 + taoLogFrequency t)
    positivity
  apply taoFiniteDyadic_partial_sum_bound (taoZetaTerm σ t) J (add_nonneg hS hL)
  intro r hrJ
  by_cases hrR : r < R
  · have hNpos : 0 < 2 ^ r := by positivity
    have htriv := taoDyadicComplexPower_trivial_scale_bound t σ (2 ^ r) (2 ^ r)
      hNpos le_rfl hσ0
    have hpowNat : 2 ^ r ≤ 2 ^ R := pow_le_pow_right₀ (by norm_num) (by omega)
    have hpow : (((2 ^ r : Nat) : Real)) ≤ ((2 ^ R : Nat) : Real) := by exact_mod_cast hpowNat
    have hscale : (((2 ^ r : Nat) : Real)) ^ (1 - σ) ≤
        (((2 ^ R : Nat) : Real)) ^ (1 - σ) :=
      Real.rpow_le_rpow (by positivity) hpow (by linarith)
    rw [taoDyadicBlock_zeta_eq]
    exact htriv.trans (hscale.trans (le_add_of_nonneg_right hL))
  · have hRr : R ≤ r := by omega
    have hr1 : 1 ≤ r := hR.trans hRr
    have hNr : 2 ≤ 2 ^ r :=
      (pow_le_pow_right₀ (by norm_num) hr1 : 2 ^ 1 ≤ 2 ^ r)
    have hgood := taoDyadicComplexPower_log_bound_of_width t σ (2 ^ r) (2 ^ r)
      hNr le_rfl ht hσ0 (hfrequency r hRr hrJ) (hwidth r hRr hrJ)
    rw [taoDyadicBlock_zeta_eq]
    exact hgood.trans (le_add_of_nonneg_left hS)

end

end Erdos1212Kernel
