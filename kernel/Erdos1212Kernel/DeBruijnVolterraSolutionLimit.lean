import Erdos1212Kernel.DeBruijnVolterraOscillationLimit
import Mathlib.Topology.Order.MonotoneConvergence

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

/-- The source's convergence conclusion for the actual rho kernel.
The two effective window envelopes converge to the same constant, and
their proved future bounds squeeze f on the full real axis. -/
theorem deBruijnRhoVolterra_solution_has_limit {f : Real → Real}
    (hf : ContinuousOn f (Set.Ici (0 : Real))) (heq : DeBruijnRhoVolterraEquation f) :
    ∃ C : Real, Tendsto f atTop (nhds C) := by
  let lower : Nat → Real := fun n => deBruijnVolterraWindowMin f (2 * (n : Real) + 1)
  let upper : Nat → Real := fun n => deBruijnVolterraWindowMax f (2 * (n : Real) + 1)
  have hidx (n : Nat) : 1 ≤ 2 * (n : Real) + 1 := by
    have hn : 0 ≤ (n : Real) := Nat.cast_nonneg n
    linarith
  have horder (n : Nat) : lower n ≤ upper n :=
    sub_nonneg.mp (deBruijnVolterraOscillation_nonneg hf (hidx n))
  have hlMono : Monotone lower := by
    intro i j hij
    apply deBruijnVolterraWindowMin_monotoneOn hf heq (hidx i) (hidx j)
    have hc : (i : Real) ≤ (j : Real) := by exact_mod_cast hij
    linarith
  have huAnti : Antitone upper := by
    intro i j hij
    apply deBruijnVolterraWindowMax_antitoneOn hf heq (hidx i) (hidx j)
    have hc : (i : Real) ≤ (j : Real) := by exact_mod_cast hij
    linarith
  have hlBdd : BddAbove (Set.range lower) := by
    refine ⟨upper 0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (horder n).trans (huAnti (Nat.zero_le n))
  have huBdd : BddBelow (Set.range upper) := by
    refine ⟨lower 0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (hlMono (Nat.zero_le n)).trans (horder n)
  let C := iSup lower
  let D := iInf upper
  have hLower : Tendsto lower atTop (nhds C) := tendsto_atTop_ciSup hlMono hlBdd
  have hUpper : Tendsto upper atTop (nhds D) := tendsto_atTop_ciInf huAnti huBdd
  have hOsc : Tendsto (fun n : Nat => upper n - lower n) atTop (nhds 0) :=
    tendsto_deBruijnVolterraOscillation_odd hf heq
  have hDC : D = C := sub_eq_zero.mp (tendsto_nhds_unique (hUpper.sub hLower) hOsc)
  rw [hDC] at hUpper
  refine ⟨C, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨Nl, hl⟩ := Metric.tendsto_atTop.mp hLower ε hε
  obtain ⟨Nu, hu⟩ := Metric.tendsto_atTop.mp hUpper ε hε
  let N := max Nl Nu
  have hNl : Nl ≤ N := le_max_left _ _
  have hNu : Nu ≤ N := le_max_right _ _
  have hlow : |lower N - C| < ε := by simpa only [Real.dist_eq] using hl N hNl
  have hupp : |upper N - C| < ε := by simpa only [Real.dist_eq] using hu N hNu
  refine ⟨2 * (N : Real) + 1, ?_⟩
  intro x hx
  have hb := deBruijnVolterraWindow_future_bounds hf heq (hidx N) x (by linarith)
  change lower N ≤ f x ∧ f x ≤ upper N at hb
  rw [Real.dist_eq, abs_lt]
  have hl' := (abs_lt.mp hlow).1
  have hu' := (abs_lt.mp hupp).2
  constructor <;> linarith [hb.1, hb.2]

/-- Qualitative comparison for the original convolution equation, after
the exact (4.3) transport. This does not assert the later O(u^(-1/2)) rate. -/
theorem deBruijnRhoSolutionRatio_has_limit {F : Real → Real}
    (hc : ContinuousOn F (Set.Ici (0 : Real)))
    (heq : ∀ x : Real, 1 ≤ x → x * F x = ∫ t in (0 : Real)..1, F (x - t)) :
    ∃ C : Real, Tendsto (fun x : Real => F x / deBruijnRho x) atTop (nhds C) :=
  deBruijnRhoVolterra_solution_has_limit (deBruijnRhoSolutionRatio_continuousOn hc)
    (deBruijnRhoSolutionRatio_equation heq)

end

end Erdos1212Kernel
