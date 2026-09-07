import Erdos1212Kernel.TaoPsiRootLogError

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

theorem tao_prime_power_error_absorption {a x : Real} (ha : 0 < a)
    (hx : Real.exp ((4 * a) ^ 2) ≤ x) :
    2 * Real.sqrt x * Real.log x ≤
      8 * x * Real.exp (-a * Real.sqrt (Real.log x)) := by
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have hl := Real.log_le_log (Real.exp_pos _) hx
  rw [Real.log_exp] at hl
  have hl0 : 0 ≤ Real.log x := (sq_nonneg (4 * a)).trans hl
  let q : Real := Real.sqrt (Real.log x)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqs : q ^ 2 = Real.log x := Real.sq_sqrt hl0
  have hq : 4 * a ≤ q := by
    have ht := Real.sqrt_le_sqrt hl
    simpa only [Real.sqrt_sq (show 0 ≤ 4 * a by positivity)] using ht
  have hgap : a * q ≤ q ^ 2 / 4 := by nlinarith
  have hpoly : 2 * q ^ 2 ≤ 8 * Real.exp (q ^ 2 / 4) := by
    have ht := Real.add_one_le_exp (q ^ 2 / 4)
    linarith
  have hex : Real.exp (q ^ 2) = x := by rw [hqs, Real.exp_log hx0]
  have hsqx : Real.sqrt x = Real.exp (q ^ 2 / 2) := by
    rw [Real.exp_half, hex]
  calc
    _ = (2 * q ^ 2) * Real.exp (q ^ 2 / 2) := by rw [← hqs, hsqx]; ring
    _ ≤ (8 * Real.exp (q ^ 2 / 4)) * Real.exp (q ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ = 8 * Real.exp (q ^ 2 / 4 + q ^ 2 / 2) := by rw [mul_assoc, ← Real.exp_add]
    _ ≤ 8 * Real.exp (q ^ 2 - a * q) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.exp_le_exp.mpr (by linarith)
    _ = 8 * x * Real.exp (-a * Real.sqrt (Real.log x)) := by
      rw [show q ^ 2 - a * q = q ^ 2 + -a * q by ring, Real.exp_add, hex]
      ring

theorem exists_taoTheta_root_log_error :
    ∃ a A X₀ : Real, 0 < a ∧ 0 < A ∧ 1 ≤ X₀ ∧
      ∀ x : Real, X₀ ≤ x →
        |Chebyshev.theta x - x| ≤ A * x * Real.exp (-a * Real.sqrt (Real.log x)) := by
  obtain ⟨a, A, X₀, ha, hA, hX, herr⟩ := exists_taoPsi_root_log_error
  let X₁ : Real := max X₀ (Real.exp ((4 * a) ^ 2))
  refine ⟨a, A + 8, X₁, ha, by positivity, hX.trans (le_max_left _ _), ?_⟩
  intro x hx
  have hxX : X₀ ≤ x := (le_max_left _ _).trans hx
  have hxexp : Real.exp ((4 * a) ^ 2) ≤ x := (le_max_right _ _).trans hx
  have hpsi := herr x hxX
  have hpp := (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (hX.trans hxX)).trans
    (tao_prime_power_error_absorption ha hxexp)
  have htri := abs_add_le (Chebyshev.psi x - x) (-(Chebyshev.psi x - Chebyshev.theta x))
  rw [abs_neg, show Chebyshev.psi x - x + -(Chebyshev.psi x - Chebyshev.theta x) =
    Chebyshev.theta x - x by ring] at htri
  calc
    _ ≤ |Chebyshev.psi x - x| + |Chebyshev.psi x - Chebyshev.theta x| := htri
    _ ≤ A * x * Real.exp (-a * Real.sqrt (Real.log x)) +
        8 * x * Real.exp (-a * Real.sqrt (Real.log x)) := add_le_add hpsi hpp
    _ = _ := by ring

end

end Erdos1212Kernel
