import Erdos1212Kernel.TaoBorelDerivativeBound
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.NumberTheory.LSeries.ZetaZeros

namespace Erdos1212Kernel

noncomputable section

open Metric

set_option maxHeartbeats 1900000

theorem taoRiemannZeta_analyticOrderAt_ne_top {z : Complex} (hz : z ≠ 1) :
    analyticOrderAt riemannZeta z ≠ ⊤ := by
  have hconn : IsPreconnected ({1}ᶜ : Set Complex) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : Complex)).isPreconnected
  have htwoMem : (2 : Complex) ∈ ({1}ᶜ : Set Complex) := by norm_num
  have htwoOrder : analyticOrderAt riemannZeta (2 : Complex) ≠ ⊤ := by
    have hzero : analyticOrderAt riemannZeta (2 : Complex) = 0 :=
      (analyticOn_riemannZeta (2 : Complex) htwoMem).analyticOrderAt_eq_zero.mpr
        (riemannZeta_ne_zero_of_one_le_re (s := (2 : Complex)) (by norm_num))
    rw [hzero]
    exact ENat.zero_ne_top
  exact analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected hconn
    htwoMem (by simpa) htwoOrder

theorem taoRiemannZeta_meromorphicOrderAt_ne_top {z : Complex} (hz : z ≠ 1) :
    meromorphicOrderAt riemannZeta z ≠ ⊤ := by
  rw [(analyticOn_riemannZeta z (by simpa)).meromorphicOrderAt_eq]
  have horder := taoRiemannZeta_analyticOrderAt_ne_top hz
  rw [← ENat.coe_toNat horder]
  simp

def taoZetaLocalDivisor (c : Complex) (R : Real) :
    Function.locallyFinsuppWithin (closedBall c R) Int :=
  MeromorphicOn.divisor riemannZeta (closedBall c R)

theorem taoZetaLocalDivisor_support_finite (c : Complex) (R : Real) :
    (taoZetaLocalDivisor c R).support.Finite := by
  exact (taoZetaLocalDivisor c R).finiteSupport (isCompact_closedBall c R)

theorem taoZetaLocalDivisor_nonneg {c : Complex} {R : Real}
    (hAvoid : ∀ z ∈ closedBall c R, z ≠ 1) :
    0 ≤ taoZetaLocalDivisor c R := by
  have hzetaAn : AnalyticOnNhd Complex riemannZeta (closedBall c R) :=
    analyticOn_riemannZeta.mono hAvoid
  have hzetaNF := hzetaAn.meromorphicNFOn
  simpa only [taoZetaLocalDivisor] using
    hzetaNF.divisor_nonneg_iff_analyticOnNhd.mpr hzetaAn

def taoZetaLocalFactorProduct (c : Complex) (R : Real) : Complex → Complex :=
  ∏ᶠ u, (· - u) ^ (taoZetaLocalDivisor c R) u

/-- Actual multiplicity-preserving factor extraction for canonical zeta
on a compact disk avoiding the pole. -/
theorem exists_taoZetaLocalZeroFreeFactor {c : Complex} {R : Real}
    (hAvoid : ∀ z ∈ closedBall c R, z ≠ 1) :
    ∃ g : Complex → Complex,
      AnalyticOnNhd Complex g (closedBall c R) ∧
      (∀ u : (closedBall c R : Set Complex), g u ≠ 0) ∧
      riemannZeta =ᶠ[Filter.codiscreteWithin (closedBall c R)]
        taoZetaLocalFactorProduct c R • g := by
  have hzeta : MeromorphicOn riemannZeta (closedBall c R) :=
    (analyticOn_riemannZeta.mono hAvoid).meromorphicOn
  have hextract := hzeta.extract_zeros_poles
    (fun u => taoRiemannZeta_meromorphicOrderAt_ne_top (hAvoid u u.property))
    (taoZetaLocalDivisor_support_finite c R)
  simpa only [taoZetaLocalFactorProduct, taoZetaLocalDivisor] using hextract

end

end Erdos1212Kernel
