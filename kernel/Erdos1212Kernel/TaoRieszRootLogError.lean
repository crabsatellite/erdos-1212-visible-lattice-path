import Erdos1212Kernel.TaoPerronHeightChoice

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

theorem exists_taoVonMangoldtRieszSum_exp_sq_error :
    ∃ a A Q₀ : Real, 0 < a ∧ 0 < A ∧ 1 ≤ Q₀ ∧
      ∀ q : Real, Q₀ ≤ q →
        ‖taoVonMangoldtRieszSum (Real.exp (q ^ 2)) - (Real.exp (q ^ 2) : Complex) / 2‖ ≤
          A * Real.exp (q ^ 2) * Real.exp (-a * q) := by
  obtain ⟨d, D, H₀, hd, hD, hH₀, herr⟩ := exists_taoVonMangoldtRieszSum_two_term_error
  let b : Real := d / (d + 4)
  let A : Real := 16 * D * (d + 4) ^ 2 / b ^ 2
  let Q₀ : Real := max 1 (Real.log H₀)
  have hb : 0 < b := div_pos hd (by linarith)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨b / 2, A, Q₀, by positivity, hA, le_max_left _ _, ?_⟩
  intro q hq
  have hq1 : 1 ≤ q := (le_max_left 1 (Real.log H₀)).trans hq
  have hq0 : 0 ≤ q := by linarith
  let H : Real := Real.exp ((d + 1) * q)
  let L : Real := Real.log (3 + H)
  have hH : H₀ ≤ H := by
    have hlogH : Real.log H₀ ≤ (d + 1) * q := by
      have hh := (le_max_right 1 (Real.log H₀)).trans hq
      nlinarith
    have he := Real.exp_le_exp.mpr hlogH
    simpa only [Real.exp_log (show 0 < H₀ by linarith), H] using he
  have hx : 1 ≤ Real.exp (q ^ 2) := Real.one_le_exp (sq_nonneg q)
  have hraw := herr H (Real.exp (q ^ 2)) hH hx
  obtain ⟨hLlow, hLup⟩ := taoPerron_height_log_bounds hd hq1
  have hLpos : 0 ≤ L := by
    change 0 ≤ Real.log (3 + Real.exp ((d + 1) * q))
    exact (show 0 ≤ (d + 1) * q by positivity).trans hLlow
  have hLs : L ^ 2 ≤ (d + 4) ^ 2 * q ^ 2 := by
    have hmul := mul_self_le_mul_self hLpos hLup
    nlinarith
  obtain ⟨hp1, hp2⟩ := taoPerron_height_power_bounds hd hq1
  have hpsum : (Real.exp (q ^ 2)) ^ (1 - d / L) +
      (Real.exp (q ^ 2)) ^ (1 + d / L) / H ≤
        2 * Real.exp (q ^ 2) * Real.exp (-b * q) := by
    have hs := add_le_add hp1 hp2
    simpa only [H, L, b, two_mul, add_mul] using hs
  have habsorb := tao_sq_mul_exp_decay_le hb hq0
  calc
    _ ≤ D * L ^ 2 * ((Real.exp (q ^ 2)) ^ (1 - d / L) +
        (Real.exp (q ^ 2)) ^ (1 + d / L) / H) := hraw
    _ ≤ D * ((d + 4) ^ 2 * q ^ 2) *
        (2 * Real.exp (q ^ 2) * Real.exp (-b * q)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hLs hD.le) hpsum (by positivity) (by positivity)
    _ = (2 * D * (d + 4) ^ 2) * Real.exp (q ^ 2) *
        (q ^ 2 * Real.exp (-b * q)) := by ring
    _ ≤ (2 * D * (d + 4) ^ 2) * Real.exp (q ^ 2) *
        ((8 / b ^ 2) * Real.exp (-(b / 2) * q)) :=
      mul_le_mul_of_nonneg_left habsorb (by positivity)
    _ = A * Real.exp (q ^ 2) * Real.exp (-(b / 2) * q) := by dsimp [A]; ring

theorem exists_taoVonMangoldtRieszSum_root_log_error :
    ∃ a A X₀ : Real, 0 < a ∧ 0 < A ∧ 1 ≤ X₀ ∧
      ∀ x : Real, X₀ ≤ x →
        ‖taoVonMangoldtRieszSum x - (x : Complex) / 2‖ ≤
          A * x * Real.exp (-a * Real.sqrt (Real.log x)) := by
  obtain ⟨a, A, Q₀, ha, hA, hQ, herr⟩ := exists_taoVonMangoldtRieszSum_exp_sq_error
  let X₀ : Real := Real.exp (Q₀ ^ 2)
  refine ⟨a, A, X₀, ha, hA, Real.one_le_exp (sq_nonneg Q₀), ?_⟩
  intro x hx
  have hx0 : 0 < x := (Real.exp_pos (Q₀ ^ 2)).trans_le hx
  have hlog : Q₀ ^ 2 ≤ Real.log x := by
    have hmono := Real.log_le_log (Real.exp_pos (Q₀ ^ 2)) hx
    simpa only [X₀, Real.log_exp] using hmono
  have hlog0 : 0 ≤ Real.log x := (sq_nonneg Q₀).trans hlog
  have hq : Q₀ ≤ Real.sqrt (Real.log x) := by
    have hmono := Real.sqrt_le_sqrt hlog
    simpa only [Real.sqrt_sq (show 0 ≤ Q₀ by linarith)] using hmono
  have hex : Real.exp ((Real.sqrt (Real.log x)) ^ 2) = x := by
    rw [Real.sq_sqrt hlog0, Real.exp_log hx0]
  simpa only [hex] using herr (Real.sqrt (Real.log x)) hq

end

end Erdos1212Kernel
