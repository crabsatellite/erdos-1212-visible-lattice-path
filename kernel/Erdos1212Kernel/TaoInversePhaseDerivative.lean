import Erdos1212Kernel.TaoPhaseChordBounds
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1400000

def taoCorputPhaseDerivative (u : Real) : Complex :=
  taoCorputPhase u * (((2 * Real.pi : Real) : Complex) * Complex.I)

theorem taoCorputPhase_hasDerivAt (u : Real) : HasDerivAt taoCorputPhase (taoCorputPhaseDerivative u) u := by
  have h := ((((hasDerivAt_id u).const_mul (2 * Real.pi)).ofReal_comp).mul_const Complex.I).cexp
  apply h.congr_deriv
  simp only [taoCorputPhaseDerivative, taoCorputPhase, mul_one, id_eq]

theorem taoCorputPhaseDerivative_norm (u : Real) : ‖taoCorputPhaseDerivative u‖ = 2 * Real.pi := by
  unfold taoCorputPhaseDerivative
  rw [Complex.norm_mul, taoCorputPhase_norm, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (show 0 < 2 * Real.pi by positivity), Complex.norm_I]
  ring

def taoCorputInversePhaseDerivative (u : Real) : Complex :=
  -taoCorputPhaseDerivative u / (taoCorputPhase u - 1) ^ 2

theorem taoCorputInversePhase_hasDerivAt {u : Real} (hu : taoCorputPhase u - 1 ≠ 0) :
    HasDerivAt taoCorputInversePhase (taoCorputInversePhaseDerivative u) u := by
  have h := (hasDerivAt_inv (𝕜 := Complex) hu).comp u ((taoCorputPhase_hasDerivAt u).sub_const 1)
  apply h.congr_deriv
  unfold taoCorputInversePhaseDerivative
  ring

theorem taoCorputInversePhaseDerivative_norm (u : Real) :
    ‖taoCorputInversePhaseDerivative u‖ = (2 * Real.pi) / ‖taoCorputPhase u - 1‖ ^ 2 := by
  unfold taoCorputInversePhaseDerivative
  rw [Complex.norm_div, norm_neg, Complex.norm_pow, taoCorputPhaseDerivative_norm]

theorem taoCorputInversePhaseDerivative_bound {δ u : Real} (hδ : 0 < δ) (hlow : δ ≤ |u|) (hhigh : |u| ≤ 1 / 2) :
    ‖taoCorputInversePhaseDerivative u‖ ≤ (2 * Real.pi) / δ ^ 2 := by
  rw [taoCorputInversePhaseDerivative_norm]
  exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hδ)
    (pow_le_pow_left₀ hδ.le (taoCorputPhase_denominator_bound hδ hlow hhigh) 2)

theorem taoCorputInversePhase_comp_hasDerivAt {g : Real → Real} {d x : Real}
    (hg : HasDerivAt g d x) (hne : taoCorputPhase (g x) - 1 ≠ 0) :
    HasDerivAt (fun t : Real => taoCorputInversePhase (g t)) (d • taoCorputInversePhaseDerivative (g x)) x :=
  (taoCorputInversePhase_hasDerivAt hne).scomp x hg

theorem taoCorputInversePhase_comp_derivative_bound {δ u d D : Real}
    (hδ : 0 < δ) (hlow : δ ≤ |u|) (hhigh : |u| ≤ 1 / 2) (hD : 0 ≤ D) (hd : |d| ≤ D) :
    ‖d • taoCorputInversePhaseDerivative u‖ ≤ D * ((2 * Real.pi) / δ ^ 2) := by
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul hd (taoCorputInversePhaseDerivative_bound hδ hlow hhigh) (norm_nonneg _) hD

end

end Erdos1212Kernel
