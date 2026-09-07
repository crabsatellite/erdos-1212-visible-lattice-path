import Erdos1212Kernel.IwaniecInductionExponentialError
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 650000

theorem eventually_iwaniec_loglog_le_eighth_log :
    ∀ᶠ x : Real in atTop, 2 ≤ Real.log x ∧ Real.log (Real.log x) ≤ Real.log x / 8 := by
  have hlim := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 2,
    hlim.eventually (Iio_mem_nhds (show (0 : Real) < 1 / 8 by norm_num))] with x hx hh
  have hlog : 0 < Real.log x := by linarith
  have hscaled := (div_lt_iff₀ hlog).mp (show Real.log (Real.log x) / Real.log x < 1 / 8 from hh)
  exact ⟨hx, by linarith⟩

/-- The source's two far-exponent comparisons (4.4)--(4.5), before
substituting its actual xi(y). -/
theorem eventually_iwaniec_far_exponent_comparisons (C : Real) :
    ∀ᶠ x : Real in atTop, 3 ≤ x ∧
      Real.exp (-x * Real.log x + x * Real.log (Real.log x) + 2 * x) <
        Real.exp (-(x / 2) * Real.log x - x * Real.log (Real.log x) - 2 * C * x) ∧
      Real.exp (-x * Real.log x + x * Real.log (Real.log x) + 2 * x) <
        Real.exp (-x * Real.log x + 2 * x * Real.log (Real.log x) - 3 * C * x) := by
  filter_upwards [eventually_ge_atTop (3 : Real), eventually_iwaniec_loglog_le_eighth_log,
    Real.tendsto_log_atTop.eventually_gt_atTop (16 * C + 16),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop (3 * C + 2)]
    with x hx hlog hC hll
  have hx0 : 0 < x := by linarith
  change 3 * C + 2 < Real.log (Real.log x) at hll
  have hfirst : 4 * Real.log (Real.log x) + 4 * C + 4 < Real.log x := by linarith [hlog.1, hlog.2]
  refine ⟨hx, Real.exp_lt_exp.mpr ?_, Real.exp_lt_exp.mpr ?_⟩
  · have hh := mul_lt_mul_of_pos_left hfirst hx0
    nlinarith only [hh]
  · have hh := mul_lt_mul_of_pos_left hll hx0
    nlinarith only [hh]

def iwaniecFarHighExponent (C s : Real) : Real :=
  -s * Real.log s + 2 * s * Real.log (Real.log s) - 3 * C * s

theorem iwaniecFarHighExponent_hasDerivAt (C : Real) {s : Real} (hs : 1 < s) :
    HasDerivAt (iwaniecFarHighExponent C)
      (-Real.log s - 1 + 2 * Real.log (Real.log s) + 2 / Real.log s - 3 * C) s := by
  have hs0 : s ≠ 0 := by linarith
  have hlog : Real.log s ≠ 0 := (Real.log_pos hs).ne'
  have hd := (hasDerivAt_id s).log hs0
  have hdd := hd.log hlog
  have hh := (((hasDerivAt_id s).mul hd).neg.add
    (((hasDerivAt_id s).mul hdd).const_mul 2)).sub ((hasDerivAt_id s).const_mul (3 * C))
  unfold iwaniecFarHighExponent
  convert hh using 1
  · funext t
    simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.mul_apply, id_eq]
    ring
  · simp only [id_eq]
    field_simp [hs0, hlog]
    <;> ring

theorem exists_iwaniecFarHighExponent_antitone {C : Real} (hC : 0 ≤ C) :
    ∃ S : Real, 3 ≤ S ∧ AntitoneOn (iwaniecFarHighExponent C) (Set.Ici S) := by
  obtain ⟨S₀, hS₀⟩ := Filter.eventually_atTop.1 eventually_iwaniec_loglog_le_eighth_log
  let S := max S₀ 3
  refine ⟨S, le_max_right _ _, ?_⟩
  apply antitoneOn_of_deriv_nonpos (convex_Ici S)
  · intro s hs
    have hs3 : 3 ≤ s := (le_max_right _ _).trans hs
    exact (iwaniecFarHighExponent_hasDerivAt C (by linarith)).continuousAt.continuousWithinAt
  · intro s hs
    have hsi : s ∈ Set.Ici S := interior_subset hs
    have hs3 : 3 ≤ s := (le_max_right _ _).trans hsi
    exact (iwaniecFarHighExponent_hasDerivAt C (by linarith)).differentiableAt.differentiableWithinAt
  · intro s hs
    have hsi : s ∈ Set.Ici S := interior_subset hs
    have hs3 : 3 ≤ s := (le_max_right _ _).trans hsi
    obtain ⟨hlog, hll⟩ := hS₀ s ((le_max_left _ _).trans hsi)
    have hinv : 2 / Real.log s ≤ 1 := (div_le_one₀ (by linarith)).mpr hlog
    rw [(iwaniecFarHighExponent_hasDerivAt C (by linarith)).deriv]
    linarith

end

end Erdos1212Kernel
