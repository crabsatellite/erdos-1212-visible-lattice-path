import Erdos1212Kernel.TaoPsiUnitError
import Erdos1212Kernel.TaoThetaRootLogError
import Erdos1212Kernel.IwaniecMertensRateTransfer

namespace Erdos1212Kernel

noncomputable section

theorem exists_taoTheta_unit_root_log_error :
    ∃ A X₀ : Real, 0 < A ∧ 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x →
      |Chebyshev.theta x - x| ≤ A * x * Real.exp (-Real.sqrt (Real.log x)) := by
  obtain ⟨A, X₀, hA, hX, herr⟩ := exists_taoPsi_unit_root_log_error
  let X₁ := max X₀ (Real.exp 16)
  refine ⟨A + 8, X₁, by positivity, hX.trans (le_max_left _ _), ?_⟩
  intro x hx
  have hxX : X₀ ≤ x := (le_max_left _ _).trans hx
  have hxexp : Real.exp 16 ≤ x := (le_max_right _ _).trans hx
  have hpsi := herr x hxX
  have hpower : 2 * Real.sqrt x * Real.log x ≤ 8 * x * Real.exp (-Real.sqrt (Real.log x)) := by
    have hxexp' : Real.exp (((4 : Real) * 1) ^ 2) ≤ x := by
      simpa only [mul_one, show (4 : Real) ^ 2 = 16 by norm_num] using hxexp
    simpa only [neg_one_mul] using tao_prime_power_error_absorption (a := 1) (by norm_num) hxexp'
  have hpp := (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (hX.trans hxX)).trans hpower
  have htri := abs_add_le (Chebyshev.psi x - x) (-(Chebyshev.psi x - Chebyshev.theta x))
  rw [abs_neg, show Chebyshev.psi x - x + -(Chebyshev.psi x - Chebyshev.theta x) =
    Chebyshev.theta x - x by ring] at htri
  calc
    _ ≤ |Chebyshev.psi x - x| + |Chebyshev.psi x - Chebyshev.theta x| := htri
    _ ≤ A * x * Real.exp (-Real.sqrt (Real.log x)) + 8 * x * Real.exp (-Real.sqrt (Real.log x)) :=
      add_le_add hpsi hpp
    _ = _ := by ring

theorem exists_iwaniecMertensRealRemainder_unit_root_log_error :
    ∃ A X₀ : Real, 0 < A ∧ Real.exp 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x →
      |iwaniecMertensRealRemainder x| ≤ A * Real.exp (-Real.sqrt (Real.log x)) := by
  obtain ⟨A, X₀, hA, _hX, htheta⟩ := exists_taoTheta_unit_root_log_error
  let X₁ := max X₀ (Real.exp 1)
  refine ⟨5 * A, X₁, by positivity, le_max_right _ _, ?_⟩
  intro x hx
  have hxexp : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  have hxX : X₀ ≤ x := (le_max_left _ _).trans hx
  have ht : ∀ t ≥ x, |Chebyshev.theta t - t| ≤ A * t * iwaniecRootLogDecay 1 t := by
    intro t ht
    simpa only [iwaniecRootLogDecay, neg_one_mul] using htheta t (hxX.trans ht)
  have herr := iwaniecMertensRealRemainder_bound_of_theta_envelope (a := 1) (by norm_num) hA.le hxexp ht
  simpa only [iwaniecRootLogDecay, div_one, show (1 : Real) + 4 = 5 by norm_num, neg_one_mul] using herr

theorem exists_iwaniecPrimeReciprocalRemainder_unit_root_log_error :
    ∃ A : Real, ∃ N₀ : Nat, 0 < A ∧ 3 ≤ N₀ ∧ ∀ N : Nat, N₀ ≤ N →
      |iwaniecPrimeReciprocalRemainder N| ≤ A * Real.exp (-Real.sqrt (Real.log (N : Real))) := by
  obtain ⟨A, X₀, hA, _hX, herr⟩ := exists_iwaniecMertensRealRemainder_unit_root_log_error
  let N₀ := max 3 (Nat.ceil X₀)
  refine ⟨A, N₀, hA, le_max_left _ _, ?_⟩
  intro N hN
  have hXN : X₀ ≤ (N : Real) :=
    (Nat.le_ceil X₀).trans (by exact_mod_cast (le_max_right 3 (Nat.ceil X₀)).trans hN)
  simpa only [iwaniecMertensRealRemainder_nat] using herr (N : Real) hXN

end

end Erdos1212Kernel
