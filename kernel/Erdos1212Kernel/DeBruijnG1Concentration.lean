import Erdos1212Kernel.DeBruijnG1RealPhase

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1600000

theorem deBruijnG1_tilted_average_hasDerivAt (u x : Real) :
    HasDerivAt (fun t : Real => deBruijnSaddleAverage t - deBruijnG1CurvatureFloor u * t)
      (deBruijnSaddleMoment x - deBruijnG1CurvatureFloor u) x := by
  simpa only [mul_one] using (deBruijnSaddleAverage_hasDerivAt x).sub ((hasDerivAt_id x).const_mul (deBruijnG1CurvatureFloor u))

theorem deBruijnG1_tilted_average_monotone (u : Real) :
    MonotoneOn (fun x : Real => deBruijnSaddleAverage x - deBruijnG1CurvatureFloor u * x)
      (Set.Ici (deBruijnSaddle u - 1)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici (deBruijnSaddle u - 1))
    (deBruijnSaddleAverage_continuous.sub (continuous_const.mul continuous_id)).continuousOn
  · intro x _hx
    exact (deBruijnG1_tilted_average_hasDerivAt u x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    change 0 ≤ deriv (fun t : Real => deBruijnSaddleAverage t - deBruijnG1CurvatureFloor u * t) x
    rw [(deBruijnG1_tilted_average_hasDerivAt u x).deriv]
    exact sub_nonneg.mpr (deBruijnSaddleMoment_lower_near hx.le)

def deBruijnG1QuadraticPhase (u x : Real) : Real :=
  deBruijnRealSaddlePhase u x - (deBruijnG1CurvatureFloor u / 2) * (x - deBruijnSaddle u) ^ 2

theorem deBruijnG1QuadraticPhase_hasDerivAt (u x : Real) :
    HasDerivAt (deBruijnG1QuadraticPhase u)
      (deBruijnSaddleAverage x - u - deBruijnG1CurvatureFloor u * (x - deBruijnSaddle u)) x := by
  have h := (deBruijnRealSaddlePhase_hasDerivAt u x).sub
    ((((hasDerivAt_id x).sub_const (deBruijnSaddle u)).pow 2).const_mul (deBruijnG1CurvatureFloor u / 2))
  apply h.congr_deriv
  simp only [id_eq, pow_one, mul_one]
  ring

theorem deBruijnG1QuadraticPhase_continuous (u : Real) : Continuous (deBruijnG1QuadraticPhase u) :=
  continuous_iff_continuousAt.mpr (fun x => (deBruijnG1QuadraticPhase_hasDerivAt u x).continuousAt)

theorem deBruijnG1QuadraticPhase_monotone {u : Real} (hu : 1 < u) :
    MonotoneOn (deBruijnG1QuadraticPhase u) (Set.Ici (deBruijnSaddle u)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici (deBruijnSaddle u)) (deBruijnG1QuadraticPhase_continuous u).continuousOn
  · intro x _hx
    exact (deBruijnG1QuadraticPhase_hasDerivAt u x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(deBruijnG1QuadraticPhase_hasDerivAt u x).deriv]
    have h := deBruijnG1_tilted_average_monotone u
      (show deBruijnSaddle u - 1 ≤ deBruijnSaddle u by linarith)
      (show deBruijnSaddle u - 1 ≤ x by linarith [hx.out]) hx.le
    dsimp only at h
    rw [deBruijnSaddle_average hu] at h
    nlinarith

theorem deBruijnG1QuadraticPhase_antitone {u : Real} (hu : 1 < u) :
    AntitoneOn (deBruijnG1QuadraticPhase u) (Set.Icc (deBruijnSaddle u - 1) (deBruijnSaddle u)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) (deBruijnG1QuadraticPhase_continuous u).continuousOn
  · intro x _hx
    exact (deBruijnG1QuadraticPhase_hasDerivAt u x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(deBruijnG1QuadraticPhase_hasDerivAt u x).deriv]
    have h := deBruijnG1_tilted_average_monotone u hx.1.le
      (show deBruijnSaddle u - 1 ≤ deBruijnSaddle u by linarith) hx.2.le
    dsimp only at h
    rw [deBruijnSaddle_average hu] at h
    nlinarith

/-- The actual phase has a uniform quadratic lower bound on the whole
half-line starting one unit before the source saddle. -/
theorem deBruijnRealSaddlePhase_quadratic_lower {u x : Real} (hu : 1 < u) (hx : deBruijnSaddle u - 1 ≤ x) :
    (deBruijnG1CurvatureFloor u / 2) * (x - deBruijnSaddle u) ^ 2 ≤
      deBruijnRealSaddlePhase u x - deBruijnRealSaddlePhase u (deBruijnSaddle u) := by
  have hQ : deBruijnG1QuadraticPhase u (deBruijnSaddle u) ≤ deBruijnG1QuadraticPhase u x := by
    by_cases hxx : x ≤ deBruijnSaddle u
    · exact deBruijnG1QuadraticPhase_antitone hu ⟨hx, hxx⟩ ⟨by linarith, le_rfl⟩ hxx
    · exact deBruijnG1QuadraticPhase_monotone hu (show deBruijnSaddle u ∈ Set.Ici (deBruijnSaddle u) by simp)
        (le_of_lt (lt_of_not_ge hxx)) (le_of_lt (lt_of_not_ge hxx))
  simp only [deBruijnG1QuadraticPhase, sub_self, zero_pow (by decide : (2 : Nat) ≠ 0), mul_zero, sub_zero] at hQ
  linarith

theorem deBruijnRealSaddlePhase_left_slope {u : Real} (hu : 1 < u) :
    deBruijnSaddleAverage (deBruijnSaddle u - 1) - u ≤ -deBruijnG1CurvatureFloor u := by
  have h := deBruijnG1_tilted_average_monotone u
    (show deBruijnSaddle u - 1 ∈ Set.Ici (deBruijnSaddle u - 1) by simp)
    (show deBruijnSaddle u - 1 ≤ deBruijnSaddle u by linarith)
    (show deBruijnSaddle u - 1 ≤ deBruijnSaddle u by linarith)
  dsimp only at h
  rw [deBruijnSaddle_average hu] at h
  nlinarith

theorem deBruijnRealSaddlePhase_left_linear_lower {u x : Real} (hu : 1 < u) (hx : x ≤ deBruijnSaddle u - 1) :
    deBruijnG1CurvatureFloor u / 2 + deBruijnG1CurvatureFloor u * (deBruijnSaddle u - 1 - x) ≤
      deBruijnRealSaddlePhase u x - deBruijnRealSaddlePhase u (deBruijnSaddle u) := by
  have hd (t : Real) : HasDerivAt (fun y : Real => deBruijnRealSaddlePhase u y + deBruijnG1CurvatureFloor u * y)
      (deBruijnSaddleAverage t - u + deBruijnG1CurvatureFloor u) t := by
    simpa only [mul_one] using (deBruijnRealSaddlePhase_hasDerivAt u t).add ((hasDerivAt_id t).const_mul (deBruijnG1CurvatureFloor u))
  have hanti : AntitoneOn (fun y : Real => deBruijnRealSaddlePhase u y + deBruijnG1CurvatureFloor u * y)
      (Set.Iic (deBruijnSaddle u - 1)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iic _) ((deBruijnRealSaddlePhase_continuous u).add (continuous_const.mul continuous_id)).continuousOn
    · intro t _ht
      exact (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Iic] at ht
      change deriv (fun y : Real => deBruijnRealSaddlePhase u y + deBruijnG1CurvatureFloor u * y) t ≤ 0
      rw [(hd t).deriv]
      have hA := deBruijnSaddleAverage_strictMono.monotone ht.le
      linarith [deBruijnRealSaddlePhase_left_slope hu]
  have hl := hanti hx (show deBruijnSaddle u - 1 ∈ Set.Iic (deBruijnSaddle u - 1) by simp) hx
  dsimp only at hl
  have hb := deBruijnRealSaddlePhase_quadratic_lower hu (x := deBruijnSaddle u - 1) le_rfl
  rw [show (deBruijnSaddle u - 1 - deBruijnSaddle u) ^ 2 = 1 by ring, mul_one] at hb
  nlinarith

end

end Erdos1212Kernel
