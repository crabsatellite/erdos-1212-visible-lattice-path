import Erdos1212Kernel.TaoPhaseIncrementCalculus

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1400000

def taoFirstDerivativeWeight (f : Real → Real) (x : Real) : Complex :=
  taoCorputInversePhase (taoPhaseIncrement f x)

def taoFirstDerivativeWeightDerivative (f f' : Real → Real) (x : Real) : Complex :=
  taoPhaseIncrementDerivative f' x • taoCorputInversePhaseDerivative (taoPhaseIncrement f x)

theorem taoFirstDerivativeWeight_norm_bound (f f' : Real → Real) {L U x δ : Real}
    (hδ : 0 < δ) (hf : ∀ t ∈ Set.Icc L U, HasDerivAt f (f' t) t)
    (hlow : ∀ t ∈ Set.Icc L U, δ ≤ |f' t|)
    (hhigh : ∀ t ∈ Set.Icc L U, |f' t| ≤ 1 / 2) (hx : x ∈ Set.Icc L (U - 1)) :
    ‖taoFirstDerivativeWeight f x‖ ≤ 1 / δ := by
  obtain ⟨hlo, hhi⟩ := taoPhaseIncrement_bounds f f' hf hlow hhigh hx
  exact taoCorputInversePhase_norm_bound hδ hlo hhi

theorem taoFirstDerivativeWeight_hasDerivAt (f f' : Real → Real) {L U x δ : Real}
    (hδ : 0 < δ) (hf : ∀ t ∈ Set.Icc L U, HasDerivAt f (f' t) t)
    (hlow : ∀ t ∈ Set.Icc L U, δ ≤ |f' t|)
    (hhigh : ∀ t ∈ Set.Icc L U, |f' t| ≤ 1 / 2) (hx : x ∈ Set.Icc L (U - 1)) :
    HasDerivAt (taoFirstDerivativeWeight f) (taoFirstDerivativeWeightDerivative f f' x) x := by
  obtain ⟨hlo, hhi⟩ := taoPhaseIncrement_bounds f f' hf hlow hhigh hx
  exact taoCorputInversePhase_comp_hasDerivAt (taoPhaseIncrement_hasDerivAt f f' hf hx)
    (taoCorputPhase_denominator_ne_zero hδ hlo hhi)

theorem taoFirstDerivativeWeight_derivative_bound (f f' f'' : Real → Real) {L U x δ D : Real}
    (hδ : 0 < δ) (hD : 0 ≤ D)
    (hf : ∀ t ∈ Set.Icc L U, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc L U, HasDerivAt f' (f'' t) t)
    (hlow : ∀ t ∈ Set.Icc L U, δ ≤ |f' t|)
    (hhigh : ∀ t ∈ Set.Icc L U, |f' t| ≤ 1 / 2)
    (hsecond : ∀ t ∈ Set.Icc L U, |f'' t| ≤ D) (hx : x ∈ Set.Icc L (U - 1)) :
    ‖taoFirstDerivativeWeightDerivative f f' x‖ ≤ D * ((2 * Real.pi) / δ ^ 2) := by
  obtain ⟨hlo, hhi⟩ := taoPhaseIncrement_bounds f f' hf hlow hhigh hx
  exact taoCorputInversePhase_comp_derivative_bound hδ hlo hhi hD
    (taoPhaseIncrement_derivative_bound f' f'' hf' hsecond hx)

/-- The original inverse denominator varies by at most the integral of its
derivative bound on the literal common increment domain. -/
theorem taoFirstDerivativeWeight_variation (f f' f'' : Real → Real) {L U x y δ D : Real}
    (hδ : 0 < δ) (hD : 0 ≤ D)
    (hf : ∀ t ∈ Set.Icc L U, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc L U, HasDerivAt f' (f'' t) t)
    (hlow : ∀ t ∈ Set.Icc L U, δ ≤ |f' t|)
    (hhigh : ∀ t ∈ Set.Icc L U, |f' t| ≤ 1 / 2)
    (hsecond : ∀ t ∈ Set.Icc L U, |f'' t| ≤ D)
    (hx : x ∈ Set.Icc L (U - 1)) (hy : y ∈ Set.Icc L (U - 1)) :
    ‖taoFirstDerivativeWeight f y - taoFirstDerivativeWeight f x‖ ≤
      (D * ((2 * Real.pi) / δ ^ 2)) * |y - x| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (taoFirstDerivativeWeight_hasDerivAt f f' hδ hf hlow hhigh ht).hasDerivWithinAt)
    (fun t ht => taoFirstDerivativeWeight_derivative_bound f f' f'' hδ hD hf hf' hlow hhigh hsecond ht)
    (convex_Icc L (U - 1)) hx hy
  simpa only [Real.norm_eq_abs] using h

end

end Erdos1212Kernel
