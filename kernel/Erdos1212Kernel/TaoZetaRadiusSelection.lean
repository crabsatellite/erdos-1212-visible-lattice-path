import Erdos1212Kernel.TaoZetaCanonicalAdjustment
import Mathlib.Order.Interval.Set.Infinite

namespace Erdos1212Kernel

noncomputable section

open Metric

set_option maxHeartbeats 1900000

def taoZetaForbiddenRadii (c : Complex) (B : Real) : Finset Real :=
  (taoZetaZerosInClosedBall c B).image (fun ρ => dist ρ c)

/-- In every nonempty radius interval one can choose a circle containing
no canonical zeta zero. The proof excludes the finite image of the
actual compact zero set. -/
theorem exists_zetaZeroFreeSphereRadius (c : Complex) {A B : Real}
    (hAB : A < B) :
    ∃ R ∈ Set.Ioo A B,
      ∀ ρ : Complex, riemannZeta ρ = 0 → dist ρ c ≠ R := by
  obtain ⟨R, hRmem, hRforbid⟩ :=
    Set.Infinite.exists_notMem_finset (Set.Ioo_infinite hAB)
      (taoZetaForbiddenRadii c B)
  refine ⟨R, hRmem, fun ρ hρzero hdist => ?_⟩
  apply hRforbid
  unfold taoZetaForbiddenRadii
  rw [Finset.mem_image]
  refine ⟨ρ, ?_, hdist⟩
  rw [mem_taoZetaZerosInClosedBall]
  exact ⟨by rw [hdist]; exact hRmem.2.le, hρzero⟩

theorem zetaZero_closedBall_mem_ball_of_sphere_free
    {c ρ : Complex} {R : Real}
    (hSphere : ∀ z : Complex, riemannZeta z = 0 → dist z c ≠ R)
    (hρ : ρ ∈ taoZetaZerosInClosedBall c R) :
    ρ ∈ ball c R := by
  rw [mem_ball]
  have hz := mem_taoZetaZerosInClosedBall.mp hρ
  exact lt_of_le_of_ne hz.1 (hSphere ρ hz.2)

theorem taoZetaLocalDivisor_support_riemannZeta_eq_zero
    {c ρ : Complex} {R : Real}
    (hAvoid : ∀ z ∈ closedBall c R, z ≠ 1)
    (hρ : ρ ∈ (taoZetaLocalDivisor c R).support) :
    riemannZeta ρ = 0 := by
  have hρU := (taoZetaLocalDivisor c R).supportWithinDomain hρ
  by_contra hne
  have hDzero : taoZetaLocalDivisor c R ρ = 0 := by
    unfold taoZetaLocalDivisor
    rw [MeromorphicOn.divisor_apply
      (analyticOn_riemannZeta.mono hAvoid).meromorphicOn hρU,
      (analyticOn_riemannZeta ρ (hAvoid ρ hρU)).meromorphicOrderAt_eq,
      (analyticOn_riemannZeta ρ (hAvoid ρ hρU)).analyticOrderAt_eq_zero.mpr hne]
    simp
  exact hρ hDzero

theorem taoZetaZero_mem_localDivisor_support
    {c ρ : Complex} {R : Real}
    (hAvoid : ∀ z ∈ closedBall c R, z ≠ 1)
    (hρU : ρ ∈ closedBall c R) (hρzero : riemannZeta ρ = 0) :
    ρ ∈ (taoZetaLocalDivisor c R).support := by
  have hzetaAn : AnalyticOnNhd Complex riemannZeta (closedBall c R) :=
    analyticOn_riemannZeta.mono hAvoid
  have hzeroSet := hzetaAn.meromorphicNFOn.zero_set_eq_divisor_support
    (fun u => taoRiemannZeta_meromorphicOrderAt_ne_top (hAvoid u u.property))
  unfold taoZetaLocalDivisor
  have hmem : ρ ∈ Function.support
      (MeromorphicOn.divisor riemannZeta (closedBall c R)) := by
    rw [← hzeroSet]
    exact ⟨hρU, hρzero⟩
  exact hmem

theorem taoZetaLocalDivisor_support_mem_ball_of_sphere_free
    {c ρ : Complex} {R : Real}
    (hAvoid : ∀ z ∈ closedBall c R, z ≠ 1)
    (hSphere : ∀ z : Complex, riemannZeta z = 0 → dist z c ≠ R)
    (hρ : ρ ∈ (taoZetaLocalDivisor c R).support) :
    ρ ∈ ball c R := by
  have hρU := (taoZetaLocalDivisor c R).supportWithinDomain hρ
  have hρzero := taoZetaLocalDivisor_support_riemannZeta_eq_zero hAvoid hρ
  exact zetaZero_closedBall_mem_ball_of_sphere_free hSphere
    (mem_taoZetaZerosInClosedBall.mpr ⟨mem_closedBall.mp hρU, hρzero⟩)

end

end Erdos1212Kernel
