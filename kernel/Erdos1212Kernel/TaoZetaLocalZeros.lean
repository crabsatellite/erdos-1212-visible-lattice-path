import Erdos1212Kernel.TaoZetaEulerTermPositivity
import Mathlib.NumberTheory.LSeries.ZetaZeros

namespace Erdos1212Kernel

noncomputable section

open Metric

set_option maxHeartbeats 1900000

def taoZetaZerosInClosedBall (c : Complex) (R : Real) : Finset Complex :=
  ((isCompact_closedBall c R).inter_riemannZetaZeros_finite).toFinset

theorem mem_taoZetaZerosInClosedBall {c z : Complex} {R : Real} :
    z ∈ taoZetaZerosInClosedBall c R ↔ dist z c ≤ R ∧ riemannZeta z = 0 := by
  rw [taoZetaZerosInClosedBall, Set.Finite.mem_toFinset, Set.mem_inter_iff,
    mem_closedBall, mem_riemannZetaZeros]

theorem taoZetaZerosInClosedBall_subset {c : Complex} {R₁ R₂ : Real}
    (hR : R₁ ≤ R₂) :
    taoZetaZerosInClosedBall c R₁ ⊆ taoZetaZerosInClosedBall c R₂ := by
  intro z hz
  rw [mem_taoZetaZerosInClosedBall] at hz ⊢
  exact ⟨hz.1.trans hR, hz.2⟩

theorem taoZetaZerosInClosedBall_erase_center {c : Complex} {R : Real}
    (hc : riemannZeta c ≠ 0) :
    (taoZetaZerosInClosedBall c R).erase c = taoZetaZerosInClosedBall c R := by
  rw [Finset.erase_eq_self]
  intro hcmem
  exact hc (mem_taoZetaZerosInClosedBall.mp hcmem).2

/-- The nearby-zero reciprocal sum uses the actual canonical zeta zero
set, with no caller-supplied list or finite certificate. -/
def taoZetaNearbyReciprocalSum (s : Complex) (R : Real) : Complex :=
  ∑ ρ ∈ taoZetaZerosInClosedBall s R, 1 / (s - ρ)

end

end Erdos1212Kernel
