import Erdos1212Kernel.TaoRieszUnsmoothingFinite

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

def taoVonMangoldtIntegrated (x : Real) : Real :=
  x * (taoVonMangoldtRieszSum x).re

theorem taoVonMangoldtIntegrated_error {x E : Real} (hx : 0 < x)
    (hE : ‖taoVonMangoldtRieszSum x - (x : Complex) / 2‖ ≤ E) :
    |taoVonMangoldtIntegrated x - x ^ 2 / 2| ≤ x * E := by
  have hre : (taoVonMangoldtRieszSum x - (x : Complex) / 2).re =
      (taoVonMangoldtRieszSum x).re - x / 2 := by simp
  have hreal := (Complex.abs_re_le_norm
    (taoVonMangoldtRieszSum x - (x : Complex) / 2)).trans hE
  rw [hre] at hreal
  have hid : taoVonMangoldtIntegrated x - x ^ 2 / 2 =
      x * ((taoVonMangoldtRieszSum x).re - x / 2) := by
    unfold taoVonMangoldtIntegrated
    ring
  rw [hid, abs_mul, abs_of_pos hx]
  exact mul_le_mul_of_nonneg_left hreal hx.le

theorem taoVonMangoldtIntegrated_secant_sandwich
    {x y : Real} (hx : 0 < x) (hxy : x ≤ y) :
    (y - x) * Chebyshev.psi x ≤ taoVonMangoldtIntegrated y - taoVonMangoldtIntegrated x ∧
      taoVonMangoldtIntegrated y - taoVonMangoldtIntegrated x ≤ (y - x) * Chebyshev.psi y := by
  let N := max (Nat.ceil x + 1) (Nat.ceil y + 1)
  have hNx : Nat.ceil x + 1 ≤ N := le_max_left _ _
  have hNy : Nat.ceil y + 1 ≤ N := le_max_right _ _
  have h := taoVonMangoldtRampSum_secant_sandwich hx.le hxy hNx hNy
  rw [taoVonMangoldtRampSum_eq_scaled_Riesz (hx.trans_le hxy) hNy,
    taoVonMangoldtRampSum_eq_scaled_Riesz hx hNx] at h
  exact h

theorem taoPsi_error_of_three_integrated_errors
    {x h E : Real} (hh : 0 < h) (hxh : 0 < x - h)
    (hminus : |taoVonMangoldtIntegrated (x - h) - (x - h) ^ 2 / 2| ≤ E)
    (hcenter : |taoVonMangoldtIntegrated x - x ^ 2 / 2| ≤ E)
    (hplus : |taoVonMangoldtIntegrated (x + h) - (x + h) ^ 2 / 2| ≤ E) :
    |Chebyshev.psi x - x| ≤ (h ^ 2 / 2 + 2 * E) / h := by
  have hx : 0 < x := by linarith
  have hleft := (taoVonMangoldtIntegrated_secant_sandwich hxh
    (show x - h ≤ x by linarith)).2
  have hright := (taoVonMangoldtIntegrated_secant_sandwich hx
    (show x ≤ x + h by linarith)).1
  obtain ⟨hmlo, hmhi⟩ := abs_le.mp hminus
  obtain ⟨hclo, hchi⟩ := abs_le.mp hcenter
  obtain ⟨hplo, hphi⟩ := abs_le.mp hplus
  apply abs_le.mpr
  constructor
  · have hlow : x - Chebyshev.psi x ≤ (h ^ 2 / 2 + 2 * E) / h := by
      apply (le_div_iff₀ hh).mpr
      nlinarith only [hleft, hmhi, hclo]
    linarith
  · apply (le_div_iff₀ hh).mpr
    nlinarith only [hright, hchi, hplo, hclo, hphi]

end

end Erdos1212Kernel
