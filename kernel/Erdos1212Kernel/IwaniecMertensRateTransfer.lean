import Erdos1212Kernel.IwaniecThetaDecayMajorant
import Erdos1212Kernel.IwaniecMertensThetaTail

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem iwaniecMertensThetaErrorDensity_envelope {a A x t : Real}
    (hx : Real.exp 1 ≤ x) (ht : x ≤ t)
    (hθ : |Chebyshev.theta t - t| ≤ A * t * iwaniecRootLogDecay a t) :
    |iwaniecMertensThetaErrorDensity t| ≤ A * iwaniecThetaDecayMajorant a t := by
  have ht1 := (iwaniec_exp_one_range (hx.trans ht)).1
  unfold iwaniecMertensThetaErrorDensity
  rw [abs_mul, abs_of_pos (iwaniecMertensThetaKernel_pos ht1)]
  calc
    _ ≤ (A * t * iwaniecRootLogDecay a t) * iwaniecMertensThetaKernel t :=
      mul_le_mul_of_nonneg_right hθ (iwaniecMertensThetaKernel_pos ht1).le
    _ = _ := by unfold iwaniecThetaDecayMajorant; ring

theorem iwaniecMertensTheta_finite_tail_envelope {a A x y : Real} (ha : 0 < a) (hA : 0 ≤ A)
    (hx : Real.exp 1 ≤ x) (hxy : x ≤ y)
    (hθ : ∀ t ≥ x, |Chebyshev.theta t - t| ≤ A * t * iwaniecRootLogDecay a t) :
    |∫ t in x..y, iwaniecMertensThetaErrorDensity t| ≤ (4 / a) * A * iwaniecRootLogDecay a x := by
  have hi := (iwaniecThetaDecayMajorant_intervalIntegrable ha hx hxy).const_mul A
  have h := intervalIntegral.norm_integral_le_of_norm_le
    (f := iwaniecMertensThetaErrorDensity) (g := fun t => A * iwaniecThetaDecayMajorant a t) hxy (by
      filter_upwards with t ht
      simpa only [Real.norm_eq_abs] using iwaniecMertensThetaErrorDensity_envelope hx ht.1.le (hθ t ht.1.le)) hi
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul] at h
  calc
    _ ≤ A * ∫ t in x..y, iwaniecThetaDecayMajorant a t := h
    _ ≤ A * ((4 / a) * iwaniecRootLogDecay a x) :=
      mul_le_mul_of_nonneg_left (iwaniecThetaDecayMajorant_finite_bound ha hx hxy) hA
    _ = _ := by ring

theorem iwaniecMertensThetaBoundary_envelope {a A x : Real} (hA : 0 ≤ A) (hx : Real.exp 1 ≤ x)
    (hθ : |Chebyshev.theta x - x| ≤ A * x * iwaniecRootLogDecay a x) :
    |iwaniecMertensThetaBoundary x| ≤ A * iwaniecRootLogDecay a x := by
  obtain ⟨hx1, hlog1⟩ := iwaniec_exp_one_range hx
  have hx0 : 0 < x := by linarith
  have hlog := Real.log_pos hx1
  unfold iwaniecMertensThetaBoundary
  rw [abs_div, abs_of_pos (mul_pos hx0 hlog)]
  calc
    _ ≤ (A * x * iwaniecRootLogDecay a x) / (x * Real.log x) :=
      div_le_div_of_nonneg_right hθ (mul_pos hx0 hlog).le
    _ = (A * iwaniecRootLogDecay a x) / Real.log x := by field_simp
    _ ≤ _ := div_le_self (mul_nonneg hA (iwaniecRootLogDecay_pos a x).le) hlog1

/-- Rate-preserving transfer for the actual theta function and the
actual Mertens remainder. The theta envelope is an explicit hypothesis;
this theorem is not a producer of that still-unproved envelope. -/
theorem iwaniecMertensRealRemainder_bound_of_theta_envelope {a A x : Real} (ha : 0 < a) (hA : 0 ≤ A)
    (hx : Real.exp 1 ≤ x)
    (hθ : ∀ t ≥ x, |Chebyshev.theta t - t| ≤ A * t * iwaniecRootLogDecay a t) :
    |iwaniecMertensRealRemainder x| ≤ (1 + 4 / a) * A * iwaniecRootLogDecay a x := by
  have hx2 : 2 ≤ x := Real.exp_one_gt_two.le.trans hx
  have htail : |iwaniecMertensThetaBoundary x - iwaniecMertensRealRemainder x| ≤
      (4 / a) * A * iwaniecRootLogDecay a x := by
    apply le_of_tendsto (by simpa only [Real.norm_eq_abs] using (iwaniecMertensTheta_tail_limit hx2).norm)
    filter_upwards [eventually_ge_atTop x] with y hy
    exact iwaniecMertensTheta_finite_tail_envelope ha hA hx hy hθ
  have hb := iwaniecMertensThetaBoundary_envelope hA hx (hθ x le_rfl)
  have htri := abs_add_le (iwaniecMertensThetaBoundary x)
    (-(iwaniecMertensThetaBoundary x - iwaniecMertensRealRemainder x))
  rw [abs_neg, show iwaniecMertensThetaBoundary x + -(iwaniecMertensThetaBoundary x - iwaniecMertensRealRemainder x) =
    iwaniecMertensRealRemainder x by ring] at htri
  calc
    _ ≤ |iwaniecMertensThetaBoundary x| + |iwaniecMertensThetaBoundary x - iwaniecMertensRealRemainder x| := htri
    _ ≤ A * iwaniecRootLogDecay a x + (4 / a) * A * iwaniecRootLogDecay a x := add_le_add hb htail
    _ = _ := by ring

theorem iwaniecPrimeReciprocalRemainder_bound_of_theta_envelope {a A : Real} {N : Nat}
    (ha : 0 < a) (hA : 0 ≤ A) (hN : Real.exp 1 ≤ (N : Real))
    (hθ : ∀ t ≥ (N : Real), |Chebyshev.theta t - t| ≤ A * t * Real.exp (-a * Real.sqrt (Real.log t))) :
    |iwaniecPrimeReciprocalRemainder N| ≤ (1 + 4 / a) * A * Real.exp (-a * Real.sqrt (Real.log (N : Real))) := by
  have h := iwaniecMertensRealRemainder_bound_of_theta_envelope ha hA hN hθ
  simpa only [iwaniecMertensRealRemainder_nat, iwaniecRootLogDecay] using h

theorem iwaniecPrimeReciprocalRemainder_unit_bound_of_theta_envelope {A : Real} {N : Nat}
    (hA : 0 ≤ A) (hN : Real.exp 1 ≤ (N : Real))
    (hθ : ∀ t ≥ (N : Real), |Chebyshev.theta t - t| ≤ A * t * Real.exp (-Real.sqrt (Real.log t))) :
    |iwaniecPrimeReciprocalRemainder N| ≤ 5 * A * Real.exp (-Real.sqrt (Real.log (N : Real))) := by
  have h := iwaniecPrimeReciprocalRemainder_bound_of_theta_envelope (a := 1) (by norm_num) hA hN (by simpa only [neg_one_mul] using hθ)
  simpa only [div_one, show (1 : Real) + 4 = 5 by norm_num, neg_one_mul] using h

end

end Erdos1212Kernel
