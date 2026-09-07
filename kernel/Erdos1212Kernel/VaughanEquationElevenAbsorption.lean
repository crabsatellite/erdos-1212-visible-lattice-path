import Erdos1212Kernel.VaughanIntervalScale

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 800000

theorem vaughanSieveCutoff_rank_ratio {A : Real} (hA : 192 ≤ A) {rank : Nat}
    (hr : vaughanRankThreshold A ≤ rank) :
    (rank : Real) / vaughanSieveCutoff A (vaughanIntervalLength A rank : Real) ≤
      2 / Real.log (2 * (rank : Real)) ^ 2 := by
  obtain ⟨hr0, hu2, _hlogr, hscale⟩ := vaughanRankThreshold_data hA hr
  let H := vaughanIntervalScale A rank
  let h := vaughanIntervalLength A rank
  let u := Real.log (2 * (rank : Real))
  let X := vaughanSieveCutoff A (h : Real)
  have hrR : (0 : Real) < rank := by exact_mod_cast hr0
  have hu : 0 < u := by dsimp [u]; linarith only [hu2]
  have hh : (0 : Real) < h := by exact_mod_cast vaughanIntervalLength_pos hscale
  have hX : 0 < X := vaughanSieveCutoff_pos A hh
  have hhalf : H / 2 ≤ (h : Real) := vaughanIntervalLength_half_lower hscale
  have hcancel : Real.exp (2 * A) * Real.exp (-2 * A) = 1 := by
    rw [← Real.exp_add]
    simp
  have hscaleCancel : H / 2 * Real.exp (-2 * A) = (rank : Real) ^ 2 * u ^ 4 / 2 := by
    dsimp [H, u, vaughanIntervalScale]
    calc
      _ = (Real.exp (2 * A) * Real.exp (-2 * A)) *
          ((rank : Real) ^ 2 * Real.log (2 * (rank : Real)) ^ 4 / 2) := by ring
      _ = _ := by rw [hcancel, one_mul]
  have hcutSq : X ^ 2 = (h : Real) * Real.exp (-2 * A) := by
    dsimp [X, vaughanSieveCutoff]
    rw [mul_pow, Real.sq_sqrt hh.le]
    have he : Real.exp (-A) ^ 2 = Real.exp (-2 * A) := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
    rw [he]
  have hscaled := mul_le_mul_of_nonneg_right hhalf (Real.exp_pos (-2 * A)).le
  have hxLower : (rank : Real) ^ 2 * u ^ 4 / 2 ≤ X ^ 2 := by
    rw [← hscaleCancel, hcutSq]
    exact hscaled
  change (rank : Real) / X ≤ 2 / u ^ 2
  apply le_of_sq_le_sq _ (by positivity)
  field_simp [hX.ne', hu.ne']
  nlinarith only [hxLower, sq_nonneg X]

theorem vaughanEquationEleven_raw_loss {A : Real} (hA : 192 ≤ A) {rank : Nat}
    (hr : vaughanRankThreshold A ≤ rank) :
    (rank : Real) *
        ((vaughanIntervalLength A rank : Real) /
          vaughanSieveCutoff A (vaughanIntervalLength A rank : Real) + 1) ≤
      3 * (vaughanIntervalLength A rank : Real) /
        Real.log (2 * (rank : Real)) ^ 2 := by
  obtain ⟨hr0, hu2, _hlogr, hscale⟩ := vaughanRankThreshold_data hA hr
  let H := vaughanIntervalScale A rank
  let h := vaughanIntervalLength A rank
  let u := Real.log (2 * (rank : Real))
  have hrR : (1 : Real) ≤ rank := by exact_mod_cast (show 1 ≤ rank by omega)
  have hu : 0 < u := by dsimp [u]; linarith only [hu2]
  have hh : (0 : Real) < h := by exact_mod_cast vaughanIntervalLength_pos hscale
  have hhalf : H / 2 ≤ (h : Real) := vaughanIntervalLength_half_lower hscale
  have hratio := vaughanSieveCutoff_rank_ratio hA hr
  have hfirst0 := mul_le_mul_of_nonneg_right hratio hh.le
  have hfirst : (rank : Real) * ((h : Real) / vaughanSieveCutoff A (h : Real)) ≤
      2 * (h : Real) / u ^ 2 := by
    convert hfirst0 using 1 <;> dsimp [u] <;> ring
  have he : (2 : Real) ≤ Real.exp (2 * A) := by
    have he0 := Real.add_one_le_exp (2 * A)
    linarith only [hA, he0]
  have huSq : (1 : Real) ≤ u ^ 2 := one_le_pow₀ (by linarith only [hu2])
  have hrU : (1 : Real) ≤ (rank : Real) * u ^ 2 := by
    simpa only [one_mul] using mul_le_mul hrR huSq (by norm_num : (0 : Real) ≤ 1) (Nat.cast_nonneg rank)
  have hcoeff : (2 : Real) ≤ Real.exp (2 * A) * (rank : Real) * u ^ 2 := by
    have hh' := mul_le_mul_of_nonneg_left hrU (Real.exp_pos (2 * A)).le
    exact he.trans (by simpa only [mul_assoc, mul_one] using hh')
  have hprod := mul_le_mul_of_nonneg_right hcoeff
    (mul_nonneg (Nat.cast_nonneg rank) (sq_nonneg u))
  have hsmall : (rank : Real) * u ^ 2 ≤ H / 2 := by
    dsimp [H, u, vaughanIntervalScale]
    nlinarith only [hprod]
  have hsecond : (rank : Real) ≤ (h : Real) / u ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hu)).mpr
    exact hsmall.trans hhalf
  calc
    _ = (rank : Real) * ((h : Real) / vaughanSieveCutoff A (h : Real)) + (rank : Real) := by ring
    _ ≤ 2 * (h : Real) / u ^ 2 + (h : Real) / u ^ 2 := add_le_add hfirst hsecond
    _ = _ := by dsimp [h, u]; ring

/-- Vaughan's equation-(11) loss is absorbed by one unit of the A
coefficient in the proved small-pool lower bound. -/
theorem vaughanEquationEleven_loss_absorbed {A : Real} (hA : 192 ≤ A) {rank : Nat}
    (hr : vaughanRankThreshold A ≤ rank) :
    (rank : Real) *
        ((vaughanIntervalLength A rank : Real) /
          vaughanSieveCutoff A (vaughanIntervalLength A rank : Real) + 1) ≤
      A * (vaughanIntervalLength A rank : Real) /
        Real.log (vaughanIntervalLength A rank : Real) ^ 2 := by
  have hraw := vaughanEquationEleven_raw_loss hA hr
  obtain ⟨hloglow, hlogup⟩ := vaughanIntervalLength_log_bounds hA hr
  obtain ⟨_hr0, hu2, _hlogr, hscale⟩ := vaughanRankThreshold_data hA hr
  let h := vaughanIntervalLength A rank
  let u := Real.log (2 * (rank : Real))
  let L := Real.log (h : Real)
  have hh : (0 : Real) < h := by exact_mod_cast vaughanIntervalLength_pos hscale
  have hu : 0 < u := by dsimp [u]; linarith only [hu2]
  have hL : 0 < L := by dsimp [L]; linarith only [hA, hloglow]
  have hsq := pow_le_pow_left₀ hL.le hlogup 2
  have hsq' : L ^ 2 ≤ 64 * u ^ 2 := by
    convert hsq using 1 <;> dsimp [L, u] <;> ring
  have hfirst := mul_le_mul_of_nonneg_left hsq' (show 0 ≤ 3 * (h : Real) by positivity)
  have hcoef := mul_le_mul_of_nonneg_right hA
    (mul_nonneg (show (0 : Real) ≤ h by positivity) (sq_nonneg u))
  have hcross : (3 * (h : Real)) * L ^ 2 ≤ (A * (h : Real)) * u ^ 2 := by
    calc
      _ ≤ (3 * (h : Real)) * (64 * u ^ 2) := hfirst
      _ = 192 * ((h : Real) * u ^ 2) := by ring
      _ ≤ _ := by simpa only [mul_assoc] using hcoef
  have hnormal : 3 * (h : Real) / u ^ 2 ≤ A * (h : Real) / L ^ 2 := by
    exact (div_le_div_iff₀ (sq_pos_of_pos hu) (sq_pos_of_pos hL)).mpr hcross
  exact hraw.trans (by simpa only [h, u, L] using hnormal)

end

end Erdos1212Kernel
