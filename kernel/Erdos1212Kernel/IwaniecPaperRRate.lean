import Erdos1212Kernel.IwaniecPaperREuler
import Erdos1212Kernel.IwaniecLogReciprocalRounding

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 650000

theorem iwaniec_ceil_pred_rounding {x : Real} (hx : 3 ≤ x) :
    2 ≤ Nat.ceil x - 1 ∧ x - 1 ≤ ((Nat.ceil x - 1 : Nat) : Real) ∧
      ((Nat.ceil x - 1 : Nat) : Real) < x := by
  have hceil : 3 ≤ Nat.ceil x := by exact_mod_cast hx.trans (Nat.le_ceil x)
  have hcast : ((Nat.ceil x - 1 : Nat) : Real) = (Nat.ceil x : Real) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ Nat.ceil x), Nat.cast_one]
  refine ⟨by omega, ?_, ?_⟩
  · rw [hcast]
    linarith [Nat.le_ceil x]
  · rw [hcast]
    have hh := Nat.ceil_lt_add_one (show 0 ≤ x by linarith)
    linarith

theorem exists_iwaniecPaperR_unit_error_high :
    ∃ C : Real, 0 < C ∧ ∀ x : Real, 3 ≤ x →
      |iwaniecPaperR x - Real.exp (-Real.eulerMascheroniConstant) / Real.log x| ≤
        C * Real.exp (-Real.sqrt (Real.log x)) := by
  obtain ⟨A, hA, hprod⟩ := exists_iwaniecMertensProd_unit_error_all
  refine ⟨Real.exp 1 * (A + 8), by positivity, ?_⟩
  intro x hx
  let N := Nat.ceil x - 1
  let c := Real.exp (-Real.eulerMascheroniConstant)
  let E := Real.exp (-Real.sqrt (Real.log x))
  obtain ⟨hN2, hNlow, hNhigh⟩ := iwaniec_ceil_pred_rounding hx
  have hNerror : |iwaniecPaperR x - c / Real.log (N : Real)| ≤
      A * Real.exp (-Real.sqrt (Real.log (N : Real))) := by
    rw [iwaniecPaperR_eq_mertensProd]
    exact hprod N
  have hdecay := iwaniec_unit_decay_le_pred_envelope hx hNlow
  have hNrate : |iwaniecPaperR x - c / Real.log (N : Real)| ≤ A * (Real.exp 1 * E) :=
    hNerror.trans (mul_le_mul_of_nonneg_left hdecay hA.le)
  have hround := iwaniec_log_reciprocal_nearby_bound hx hNlow hNhigh.le
    iwaniecEulerConstant_pos_le_one.1.le iwaniecEulerConstant_pos_le_one.2
  have hinverse := iwaniec_inverse_le_sqrt_log_exponential (show 1 ≤ x by linarith)
  have hdrift : |c / Real.log (N : Real) - c / Real.log x| ≤ 8 * Real.exp 1 * E := by
    have hh := mul_le_mul_of_nonneg_left hinverse (show (0 : Real) ≤ 8 by norm_num)
    have hh' : 8 / x ≤ 8 * Real.exp 1 * E := by convert hh using 1 <;> ring
    exact hround.trans hh'
  have htri := abs_add_le (iwaniecPaperR x - c / Real.log (N : Real))
    (c / Real.log (N : Real) - c / Real.log x)
  rw [show iwaniecPaperR x - c / Real.log (N : Real) + (c / Real.log (N : Real) - c / Real.log x) =
    iwaniecPaperR x - c / Real.log x by ring] at htri
  have hh := htri.trans (add_le_add hNrate hdrift)
  convert hh using 1 <;> ring

/-- The actual strict real Euler product, with the coefficient-one
exponential rate used in the paper and with x=2 included. -/
theorem exists_iwaniecPaperR_unit_error :
    ∃ C : Real, 0 < C ∧ ∀ x : Real, 2 ≤ x →
      |iwaniecPaperR x - Real.exp (-Real.eulerMascheroniConstant) / Real.log x| ≤
        C * Real.exp (-Real.sqrt (Real.log x)) := by
  obtain ⟨A, hA, hlarge⟩ := exists_iwaniecPaperR_unit_error_high
  let E₃ := Real.exp (-Real.sqrt (Real.log (3 : Real)))
  let C := max A (3 / E₃)
  have hC : 0 < C := hA.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro x hx
  by_cases hx3 : 3 ≤ x
  · exact (hlarge x hx3).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have hx0 : 0 < x := by linarith
    have hlog : 0 < Real.log x := Real.log_pos (by linarith)
    have hhalf : (1 / 2 : Real) ≤ Real.log x := iwaniec_half_le_log_two.trans (Real.log_le_log (by norm_num) hx)
    have hmain : Real.exp (-Real.eulerMascheroniConstant) / Real.log x ≤ 2 := by
      apply (div_le_iff₀ hlog).mpr
      have hh := iwaniecEulerConstant_pos_le_one.2
      linarith only [hh, hhalf]
    have hsmall : |iwaniecPaperR x - Real.exp (-Real.eulerMascheroniConstant) / Real.log x| ≤ 3 := by
      have hh := abs_sub (iwaniecPaperR x) (Real.exp (-Real.eulerMascheroniConstant) / Real.log x)
      rw [abs_of_pos (iwaniecPaperR_pos x), abs_of_nonneg (div_nonneg (Real.exp_pos _).le hlog.le)] at hh
      have hR := iwaniecPaperR_le_one x
      linarith
    have hE : E₃ ≤ Real.exp (-Real.sqrt (Real.log x)) := by
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (Real.sqrt_le_sqrt (Real.log_le_log hx0 (le_of_not_ge hx3)))
    have hCsmall : 3 ≤ C * E₃ := (div_le_iff₀ (Real.exp_pos _)).mp (le_max_right A (3 / E₃))
    exact hsmall.trans (hCsmall.trans (mul_le_mul_of_nonneg_left hE hC.le))

end

end Erdos1212Kernel
