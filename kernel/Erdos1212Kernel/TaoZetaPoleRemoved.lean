import Erdos1212Kernel.TaoZetaRightStripBound
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

namespace Erdos1212Kernel

noncomputable section

open Filter Metric Topology

set_option maxHeartbeats 1900000

def taoZetaPoleRemoved : Complex → Complex :=
  Function.update (fun s => (s - 1) * riemannZeta s) 1 1

@[simp] theorem taoZetaPoleRemoved_one : taoZetaPoleRemoved 1 = 1 := by
  simp [taoZetaPoleRemoved]

theorem taoZetaPoleRemoved_of_ne_one {s : Complex} (hs : s ≠ 1) :
    taoZetaPoleRemoved s = (s - 1) * riemannZeta s := by
  simp [taoZetaPoleRemoved, hs]

theorem continuousAt_taoZetaPoleRemoved_one :
    ContinuousAt taoZetaPoleRemoved 1 := by
  apply continuousAt_update_same.mpr
  simpa only using riemannZeta_residue_one

theorem analyticAt_taoZetaPoleRemoved_one :
    AnalyticAt Complex taoZetaPoleRemoved 1 := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : s ≠ 1 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hs
    have hEq : taoZetaPoleRemoved =ᶠ[nhds s]
        (fun z => (z - 1) * riemannZeta z) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz
      exact taoZetaPoleRemoved_of_ne_one hz
    exact ((differentiableAt_id.sub_const 1).mul
      (differentiableAt_riemannZeta hs1)).congr_of_eventuallyEq hEq
  · exact continuousAt_taoZetaPoleRemoved_one

theorem taoZetaLogDerivative_eq_inv_sub_logDeriv_poleRemoved
    {s : Complex} (hsre : 1 < s.re) :
    taoZetaLogDerivative s = 1 / (s - 1) - logDeriv taoZetaPoleRemoved s := by
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hsre
  have hzeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hsre
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hEq : taoZetaPoleRemoved =ᶠ[nhds s]
      (fun z => (z - 1) * riemannZeta z) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz
    exact taoZetaPoleRemoved_of_ne_one hz
  have hval := hEq.self_of_nhds
  have hderiv := hEq.deriv_eq
  have hmul := logDeriv_mul s hsub hzeta
    (differentiableAt_id.sub_const 1) (differentiableAt_riemannZeta hs1)
  have hlinear : logDeriv (fun z : Complex => z - 1) s = 1 / (s - 1) := by
    unfold logDeriv
    simp only [Pi.div_apply]
    rw [deriv_sub_const, show deriv (fun z : Complex => z) s = 1 by
      simpa using (deriv_id (x := s))]
  have hmul' : logDeriv (fun z => (z - 1) * riemannZeta z) s =
      1 / (s - 1) + logDeriv riemannZeta s := by
    simpa only [id_eq, hlinear] using hmul
  have hlogEq : logDeriv taoZetaPoleRemoved s =
      logDeriv (fun z => (z - 1) * riemannZeta z) s := by
    unfold logDeriv
    simp only [Pi.div_apply]
    rw [hderiv, hval]
  rw [hlogEq, hmul']
  unfold taoZetaLogDerivative logDeriv
  simp only [Pi.div_apply]
  ring

theorem continuousAt_logDeriv_taoZetaPoleRemoved_one :
    ContinuousAt (logDeriv taoZetaPoleRemoved) 1 := by
  have hAn := analyticAt_taoZetaPoleRemoved_one
  unfold logDeriv
  exact hAn.deriv.continuousAt.div hAn.continuousAt (by simp)

theorem exists_local_norm_logDeriv_taoZetaPoleRemoved_bound :
    ∃ δ B : Real, 0 < δ ∧ 0 ≤ B ∧
      ∀ s : Complex, dist s 1 < δ → ‖logDeriv taoZetaPoleRemoved s‖ ≤ B := by
  have hevent : ∀ᶠ s : Complex in nhds 1,
      dist (logDeriv taoZetaPoleRemoved s)
        (logDeriv taoZetaPoleRemoved 1) < 1 :=
    continuousAt_logDeriv_taoZetaPoleRemoved_one
      (ball_mem_nhds _ (by norm_num : (0 : Real) < 1))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  let B : Real := ‖logDeriv taoZetaPoleRemoved 1‖ + 1
  refine ⟨δ, B, hδ, by unfold B; positivity, fun s hs => ?_⟩
  have hdist := hball hs
  unfold B
  have htri := norm_le_norm_add_norm_sub' (logDeriv taoZetaPoleRemoved s)
    (logDeriv taoZetaPoleRemoved 1)
  rw [dist_eq_norm] at hdist
  linarith

/-- Sharp pole coefficient: sufficiently close to one from the right,
the real logarithmic derivative is at most `9/8` times the pole term. -/
theorem exists_norm_taoZetaLogDerivative_real_le_nine_eighth :
    ∃ δ : Real, 0 < δ ∧ ∀ σ : Real, 1 < σ → σ - 1 < δ →
      ‖taoZetaLogDerivative (σ : Complex)‖ ≤ 9 / (8 * (σ - 1)) := by
  obtain ⟨δ₀, B, hδ₀, hB, hlocal⟩ :=
    exists_local_norm_logDeriv_taoZetaPoleRemoved_bound
  let δ : Real := min δ₀ (1 / (8 * (B + 1)))
  have hB1 : 0 < B + 1 := by linarith
  have hδ : 0 < δ := lt_min hδ₀ (by positivity)
  refine ⟨δ, hδ, fun σ hσ hσδ => ?_⟩
  have hgap : 0 < σ - 1 := by linarith
  have hdist : dist ((σ : Complex)) 1 < δ₀ := by
    rw [Complex.dist_eq, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hgap]
    exact hσδ.trans_le (min_le_left _ _)
  have hres := hlocal (σ : Complex) hdist
  have hδsmall : σ - 1 < 1 / (8 * (B + 1)) :=
    hσδ.trans_le (min_le_right _ _)
  have hBsmall : B * (σ - 1) ≤ 1 / 8 := by
    have hmul := mul_lt_mul_of_pos_right hδsmall hB1
    have hBfac : B ≤ B + 1 := by linarith
    have hgap0 := hgap.le
    have := mul_le_mul_of_nonneg_right hBfac hgap0
    have hcalc : (B + 1) * (1 / (8 * (B + 1))) = 1 / 8 := by
      field_simp [hB1.ne']
    rw [mul_comm (1 / (8 * (B + 1))) (B + 1), hcalc] at hmul
    linarith
  have hexact := taoZetaLogDerivative_eq_inv_sub_logDeriv_poleRemoved
    (s := (σ : Complex)) (by simpa using hσ)
  have hinvnorm : ‖(1 : Complex) / ((σ : Complex) - 1)‖ = 1 / (σ - 1) := by
    rw [Complex.norm_div, norm_one, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hgap]
  have hnorm := norm_sub_le ((1 : Complex) / ((σ : Complex) - 1))
    (logDeriv taoZetaPoleRemoved (σ : Complex))
  rw [← hexact, hinvnorm] at hnorm
  have hupper : ‖taoZetaLogDerivative (σ : Complex)‖ ≤ 1 / (σ - 1) + B :=
    hnorm.trans (add_le_add_right hres _)
  have htarget : 1 / (σ - 1) + B ≤ 9 / (8 * (σ - 1)) := by
    apply (le_div_iff₀ (by positivity : 0 < 8 * (σ - 1))).2
    have hgapInv : (σ - 1) * (1 / (σ - 1)) = 1 := by field_simp
    nlinarith
  exact hupper.trans htarget

end

end Erdos1212Kernel
