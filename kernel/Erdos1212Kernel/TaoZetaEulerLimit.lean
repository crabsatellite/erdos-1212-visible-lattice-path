import Erdos1212Kernel.TaoZetaEulerApproximation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 1900000

theorem taoZetaEulerApprox_cauchy {s : Complex} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    CauchySeq (taoZetaEulerApprox s) := by
  apply Metric.cauchySeq_iff'.2
  intro ε hε
  let C : Real := ‖s‖ * (1 + 1 / s.re)
  have hC : 0 ≤ C := by
    unfold C
    have : 0 ≤ 1 + 1 / s.re := by positivity
    positivity
  have hpow : Tendsto (fun n : Nat => (n : Real) ^ (-s.re)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop
  have htend : Tendsto (fun n : Nat => C * (n : Real) ^ (-s.re)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hpow
  have hsmall : ∀ᶠ n : Nat in atTop, C * (n : Real) ^ (-s.re) < ε :=
    (tendsto_order.1 htend).2 ε hε
  have hone : ∀ᶠ n : Nat in atTop, 1 ≤ n := eventually_ge_atTop 1
  obtain ⟨N, hNsmall, hNone⟩ := (hsmall.and hone).exists
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have hbound := taoZetaEulerApprox_sub hs hs1 hNone hn
  have hconst : ‖s‖ * (N : Real) ^ (-s.re) * (1 + 1 / s.re) =
      C * (N : Real) ^ (-s.re) := by unfold C; ring
  rw [hconst] at hbound
  exact hbound.trans_lt hNsmall

def taoZetaEulerLimit (s : Complex) : Complex :=
  limUnder atTop (taoZetaEulerApprox s)

theorem taoZetaEulerApprox_tendsto {s : Complex} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Tendsto (taoZetaEulerApprox s) atTop (𝓝 (taoZetaEulerLimit s)) :=
  (taoZetaEulerApprox_cauchy hs hs1).tendsto_limUnder

theorem taoZetaEulerLimit_truncation_error {s : Complex}
    (hs : 0 < s.re) (hs1 : s ≠ 1) (N : Nat) (hN : 1 ≤ N) :
    ‖taoZetaEulerLimit s - taoZetaEulerApprox s N‖ ≤
      ‖s‖ * (N : Real) ^ (-s.re) * (1 + 1 / s.re) := by
  have hconst : Tendsto (fun _ : Nat => taoZetaEulerApprox s N) atTop
      (𝓝 (taoZetaEulerApprox s N)) := tendsto_const_nhds
  have htend := (taoZetaEulerApprox_tendsto hs hs1).sub hconst
  have hnorm : Tendsto (fun M => ‖taoZetaEulerApprox s M - taoZetaEulerApprox s N‖)
      atTop (𝓝 ‖taoZetaEulerLimit s - taoZetaEulerApprox s N‖) := htend.norm
  have hevent : ∀ᶠ M : Nat in atTop,
      ‖taoZetaEulerApprox s M - taoZetaEulerApprox s N‖ ≤
        ‖s‖ * (N : Real) ^ (-s.re) * (1 + 1 / s.re) := by
    filter_upwards [eventually_ge_atTop N] with M hNM
    exact taoZetaEulerApprox_sub hs hs1 hN hNM
  have hle := le_of_tendsto hnorm hevent
  simpa only [norm_sub_rev] using hle

end

end Erdos1212Kernel
