import Erdos1212Kernel.TaoPerronUnitHeight

namespace Erdos1212Kernel

noncomputable section

theorem exists_taoVonMangoldtRieszSum_four_root_log_error :
    ∃ A X₀ : Real, 0 < A ∧ 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x →
      ‖taoVonMangoldtRieszSum x - (x : Complex) / 2‖ ≤
        A * x * Real.exp (-4 * Real.sqrt (Real.log x)) := by
  obtain ⟨A, Q₀, hA, hQ, herr⟩ := exists_taoVonMangoldtRieszSum_four_exp_sq_error
  let X₀ := Real.exp (Q₀ ^ 2)
  refine ⟨A, X₀, hA, Real.one_le_exp (sq_nonneg Q₀), ?_⟩
  intro x hx
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have hlog : Q₀ ^ 2 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (Q₀ ^ 2)) hx
  have hlog0 : 0 ≤ Real.log x := (sq_nonneg Q₀).trans hlog
  have hq : Q₀ ≤ Real.sqrt (Real.log x) := by
    have hh := Real.sqrt_le_sqrt hlog
    simpa only [Real.sqrt_sq (show 0 ≤ Q₀ by linarith)] using hh
  have hex : Real.exp ((Real.sqrt (Real.log x)) ^ 2) = x := by
    rw [Real.sq_sqrt hlog0, Real.exp_log hx0]
  simpa only [hex] using herr (Real.sqrt (Real.log x)) hq

end

end Erdos1212Kernel
