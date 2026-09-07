import Erdos1212Kernel.TaoZetaRealCenterRepulsion
import Mathlib.NumberTheory.Harmonic.Bounds

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1900000

theorem norm_taoZetaTerm_eq {σ t : Real} {n : Nat} (hn : 0 < n) :
    ‖taoZetaTerm σ t n‖ = (n : Real) ^ (-σ) := by
  unfold taoZetaTerm
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  change ‖(((n : Real) : Complex) ^
    (-((σ : Complex) + (t : Complex) * Complex.I)))‖ = (n : Real) ^ (-σ)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hnR]
  simp

theorem norm_taoZetaDirichletPrefix_le_one_add_log
    (σ t : Real) (hσ : 1 ≤ σ) (N : Nat) (hN : 2 ≤ N) :
    ‖∑ n ∈ Finset.Ico 1 N, taoZetaTerm σ t n‖ ≤
      1 + Real.log N := by
  have hterm (n : Nat) (hn : n ∈ Finset.Ico 1 N) :
      ‖taoZetaTerm σ t n‖ ≤ 1 / (n : Real) := by
    have hnpos : 0 < n := (Finset.mem_Ico.mp hn).1
    rw [norm_taoZetaTerm_eq hnpos]
    have hn1 : (1 : Real) ≤ n := by exact_mod_cast hnpos
    calc
      (n : Real) ^ (-σ) ≤ (n : Real) ^ (-1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      _ = 1 / (n : Real) := by rw [Real.rpow_neg_one, one_div]
  calc
    ‖∑ n ∈ Finset.Ico 1 N, taoZetaTerm σ t n‖ ≤
        ∑ n ∈ Finset.Ico 1 N, ‖taoZetaTerm σ t n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ico 1 N, 1 / (n : Real) := by
      exact Finset.sum_le_sum hterm
    _ = (harmonic (N - 1) : Real) := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      apply Finset.sum_congr rfl
      intro n _hn
      simp only [one_div, Nat.cast_add, Nat.cast_one, add_comm]
    _ ≤ 1 + Real.log ((N - 1 : Nat) : Real) := by
      exact harmonic_le_one_add_log (N - 1)
    _ ≤ 1 + Real.log N := by
      gcongr
      · exact_mod_cast (show 0 < N - 1 by omega)
      · exact_mod_cast (show N - 1 ≤ N by omega)

/-- A uniform elementary zeta bound immediately to the right of the
critical line, retaining the exact Euler correction and remainder. -/
theorem riemannZeta_norm_le_right_strip_harmonic
    (σ t : Real) (hσ : 1 ≤ σ) (ht : t ≠ 0)
    (N : Nat) (hN : 2 ≤ N) :
    ‖riemannZeta ((σ : Complex) + (t : Complex) * Complex.I)‖ ≤
      1 + Real.log N +
        (N : Real) ^ (1 - σ) /
          ‖((σ : Complex) + (t : Complex) * Complex.I) - 1‖ +
        ‖(σ : Complex) + (t : Complex) * Complex.I‖ *
          (N : Real) ^ (-σ) * (1 + 1 / σ) := by
  have hbase := riemannZeta_norm_le_partial_add_correction_add_error
    σ t (by linarith) ht N (by omega)
  exact hbase.trans (add_le_add (add_le_add
    (norm_taoZetaDirichletPrefix_le_one_add_log σ t hσ N hN) le_rfl) le_rfl)

end

end Erdos1212Kernel
