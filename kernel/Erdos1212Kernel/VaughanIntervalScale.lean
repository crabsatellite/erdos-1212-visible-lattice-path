import Erdos1212Kernel.VaughanRealCutoffComparison

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 700000

/-- Vaughan (1977), equation (6), before taking the integer part. -/
def vaughanIntervalScale (A : Real) (rank : Nat) : Real :=
  Real.exp (2 * A) * (rank : Real) ^ 2 * Real.log (2 * (rank : Real)) ^ 4

def vaughanIntervalLength (A : Real) (rank : Nat) : Nat :=
  Nat.floor (vaughanIntervalScale A rank)

def vaughanRankThreshold (A : Real) : Nat := Nat.ceil (Real.exp (3 * A + 2))

theorem vaughanIntervalScale_nonneg (A : Real) (rank : Nat) :
    0 ≤ vaughanIntervalScale A rank := by unfold vaughanIntervalScale; positivity

theorem vaughanIntervalLength_upper (A : Real) (rank : Nat) :
    (vaughanIntervalLength A rank : Real) ≤ vaughanIntervalScale A rank :=
  Nat.floor_le (vaughanIntervalScale_nonneg A rank)

theorem vaughanIntervalLength_half_lower {A : Real} {rank : Nat}
    (hscale : 2 ≤ vaughanIntervalScale A rank) :
    vaughanIntervalScale A rank / 2 ≤ (vaughanIntervalLength A rank : Real) := by
  have hfloor := (Nat.sub_one_lt_floor (vaughanIntervalScale A rank)).le
  exact (show vaughanIntervalScale A rank / 2 ≤ vaughanIntervalScale A rank - 1 by
    linarith only [hscale]).trans hfloor

theorem vaughanIntervalLength_pos {A : Real} {rank : Nat}
    (hscale : 2 ≤ vaughanIntervalScale A rank) : 0 < vaughanIntervalLength A rank := by
  have hh := vaughanIntervalLength_half_lower hscale
  have hreal : (1 : Real) ≤ vaughanIntervalLength A rank := by linarith only [hh, hscale]
  exact_mod_cast (show (0 : Nat) < vaughanIntervalLength A rank by exact_mod_cast hreal)

theorem vaughanIntervalScale_log {A : Real} {rank : Nat} (hr : 0 < rank)
    (hu : 0 < Real.log (2 * (rank : Real))) :
    Real.log (vaughanIntervalScale A rank) =
      2 * A + 2 * Real.log (rank : Real) + 4 * Real.log (Real.log (2 * (rank : Real))) := by
  have hrR : (0 : Real) < rank := by exact_mod_cast hr
  unfold vaughanIntervalScale
  rw [Real.log_mul (mul_ne_zero (Real.exp_ne_zero _) (pow_ne_zero 2 hrR.ne')) (pow_ne_zero 4 hu.ne'),
    Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero 2 hrR.ne'),
    Real.log_exp, Real.log_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]

theorem vaughanRankThreshold_data {A : Real} (hA : 192 ≤ A) {rank : Nat}
    (hr : vaughanRankThreshold A ≤ rank) :
    0 < rank ∧ 2 ≤ Real.log (2 * (rank : Real)) ∧
      3 * A + 1 ≤ Real.log (rank : Real) ∧ 2 ≤ vaughanIntervalScale A rank := by
  have hx := Nat.le_ceil (Real.exp (3 * A + 2))
  have hcast : ((vaughanRankThreshold A : Nat) : Real) ≤ rank := by exact_mod_cast hr
  have hxr : Real.exp (3 * A + 2) ≤ (rank : Real) := hx.trans hcast
  have hrR : (0 : Real) < rank := (Real.exp_pos _).trans_le hxr
  have hrNat : 0 < rank := by exact_mod_cast hrR
  have hlogr := Real.log_le_log (Real.exp_pos _) hxr
  rw [Real.log_exp] at hlogr
  have huEq : Real.log (2 * (rank : Real)) = Real.log 2 + Real.log (rank : Real) := by
    rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0) hrR.ne']
  have hu : 2 ≤ Real.log (2 * (rank : Real)) := by
    rw [huEq]
    linarith [iwaniec_half_le_log_two]
  have he : (2 : Real) ≤ Real.exp (2 * A) := by
    have hh := Real.add_one_le_exp (2 * A)
    linarith only [hA, hh]
  have hrSq : (1 : Real) ≤ (rank : Real) ^ 2 := one_le_pow₀ (by exact_mod_cast hrNat)
  have huPow : (1 : Real) ≤ Real.log (2 * (rank : Real)) ^ 4 := one_le_pow₀ (by linarith [hu])
  have hp := mul_le_mul he hrSq (by norm_num : (0 : Real) ≤ 1) (Real.exp_pos _).le
  have hscale := mul_le_mul hp huPow (by norm_num : (0 : Real) ≤ 1)
    (mul_nonneg (Real.exp_pos _).le (sq_nonneg (rank : Real)))
  refine ⟨hrNat, hu, ?_, ?_⟩
  · linarith only [hlogr]
  · norm_num only [mul_one] at hscale
    simpa only [vaughanIntervalScale] using hscale

theorem vaughanIntervalLength_log_bounds {A : Real} (hA : 192 ≤ A) {rank : Nat}
    (hr : vaughanRankThreshold A ≤ rank) :
    6 * A ≤ Real.log (vaughanIntervalLength A rank : Real) ∧
      Real.log (vaughanIntervalLength A rank : Real) ≤ 8 * Real.log (2 * (rank : Real)) := by
  obtain ⟨hr0, hu2, hlogr, hscale⟩ := vaughanRankThreshold_data hA hr
  let H := vaughanIntervalScale A rank
  let h := vaughanIntervalLength A rank
  let u := Real.log (2 * (rank : Real))
  have hH : 0 < H := by dsimp [H, vaughanIntervalScale]; positivity
  have hh : 0 < (h : Real) := by exact_mod_cast vaughanIntervalLength_pos hscale
  have hhalf : H / 2 ≤ (h : Real) := vaughanIntervalLength_half_lower hscale
  have hupper : (h : Real) ≤ H := vaughanIntervalLength_upper A rank
  have hloglow := Real.log_le_log (by positivity : 0 < H / 2) hhalf
  have hlogup := Real.log_le_log hh hupper
  have hu0 : 0 < u := by dsimp [u]; linarith only [hu2]
  have hlogH := vaughanIntervalScale_log (A := A) (rank := rank) hr0 hu0
  have hlogrU : Real.log (rank : Real) ≤ u := by
    dsimp [u]
    exact Real.log_le_log (by exact_mod_cast hr0) (by exact_mod_cast (show rank ≤ 2 * rank by omega))
  have hlogu : Real.log u ≤ u := by
    have hh' := Real.log_le_sub_one_of_pos (by linarith only [hu2] : 0 < u)
    linarith only [hh']
  have hlogtwo : Real.log 2 ≤ 1 := by
    have hh' := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    linarith only [hh']
  rw [Real.log_div hH.ne' (by norm_num : (2 : Real) ≠ 0), hlogH] at hloglow
  rw [hlogH] at hlogup
  dsimp only [h, u] at hloglow hlogup ⊢
  constructor
  · have hlogu0 : 0 ≤ Real.log u := Real.log_nonneg (by dsimp [u]; linarith)
    linarith only [hA, hloglow, hlogr, hlogu0, hlogtwo]
  · linarith only [hA, hlogup, hlogr, hlogrU, hlogu]

end

end Erdos1212Kernel
