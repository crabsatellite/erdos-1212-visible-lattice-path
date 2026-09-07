import Erdos1212Kernel.TaoZetaDyadicCanonicalBound

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1900000

/-- Strip width attached to the first oscillatory dyadic scale.  This
normalization makes the small-scale loss exactly `log T`. -/
def taoLittlewoodWidth (T : Real) (R : Nat) : Real :=
  Real.log (Real.log T) / ((R : Real) * Real.log 2)

theorem taoLittlewoodWidth_pos {T : Real} {R : Nat}
    (hL : 1 < Real.log T) (hR : 1 ≤ R) :
    0 < taoLittlewoodWidth T R := by
  unfold taoLittlewoodWidth
  exact div_pos (Real.log_pos hL)
    (mul_pos (by exact_mod_cast hR) (Real.log_pos (by norm_num)))

theorem taoLittlewood_scale_rpow {T : Real} {R : Nat}
    (hL : 1 < Real.log T) (hR : 1 ≤ R) :
    (((2 ^ R : Nat) : Real)) ^ (taoLittlewoodWidth T R) = Real.log T := by
  have hbase : (0 : Real) < ((2 ^ R : Nat) : Real) := by positivity
  have hr : (0 : Real) < R := by exact_mod_cast hR
  have hlog2 : (0 : Real) < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.rpow_def_of_pos hbase]
  have hlogbase : Real.log (((2 ^ R : Nat) : Real)) = (R : Real) * Real.log 2 := by
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    rw [Real.log_pow]
  rw [hlogbase]
  unfold taoLittlewoodWidth
  have hcancel : (R : Real) * Real.log 2 *
      (Real.log (Real.log T) / ((R : Real) * Real.log 2)) =
        Real.log (Real.log T) := by
    field_simp
  rw [hcancel]
  exact Real.exp_log (by linarith)

theorem taoExplicitDecayExponent_two_pow {T : Real} {R : Nat}
    (hR : 1 ≤ R) :
    taoExplicitDecayExponent T (((2 ^ R : Nat) : Real)) =
      1 / (4 * T ^ (1 / (R : Real))) := by
  have hr : (0 : Real) < R := by exact_mod_cast hR
  have hlog2 : (0 : Real) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogbase : Real.log (((2 ^ R : Nat) : Real)) = (R : Real) * Real.log 2 := by
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    rw [Real.log_pow]
  unfold taoExplicitDecayExponent
  rw [hlogbase]
  congr 3
  field_simp

/-- A lower bound `R >= 8 log T / log log T` makes the van der Corput
decay threshold dominate the attached Littlewood strip width.  The last
hypothesis is a single real-variable large-`T` inequality, separated from
the dyadic and exponential-sum consumers. -/
theorem taoLittlewoodWidth_le_explicitDecay {T : Real} {R : Nat}
    (hT : 1 < T) (hL : 1 < Real.log T) (hR : 1 ≤ R)
    (hRlow : 8 * Real.log T / Real.log (Real.log T) ≤ (R : Real))
    (hlarge :
      Real.log (Real.log T) ^ 2 /
          (8 * Real.log 2 * Real.log T) ≤
        1 / (4 * (Real.log T) ^ (1 / 8 : Real))) :
    taoLittlewoodWidth T R ≤
      taoExplicitDecayExponent T (((2 ^ R : Nat) : Real)) := by
  let L : Real := Real.log T
  let l : Real := Real.log L
  let r : Real := R
  have hLp : 0 < L := by unfold L; linarith
  have hlp : 0 < l := by unfold l; exact Real.log_pos hL
  have hrp : 0 < r := by unfold r; exact_mod_cast hR
  have hlog2 : (0 : Real) < Real.log 2 := Real.log_pos (by norm_num)
  have hdenOrder : 8 * L * Real.log 2 / l ≤ r * Real.log 2 := by
    have h := mul_le_mul_of_nonneg_right hRlow hlog2.le
    dsimp only [L, l, r] at h ⊢
    convert h using 1 <;> ring
  have hdenLow : 0 < 8 * L * Real.log 2 / l := by positivity
  have hwidthFirst : l / (r * Real.log 2) ≤ l / (8 * L * Real.log 2 / l) :=
    div_le_div_of_nonneg_left hlp.le hdenLow hdenOrder
  have hquotient : l / (8 * L * Real.log 2 / l) =
      l ^ 2 / (8 * Real.log 2 * L) := by
    field_simp
  have hwidthUpper : taoLittlewoodWidth T R ≤
      1 / (4 * L ^ (1 / 8 : Real)) := by
    unfold taoLittlewoodWidth
    dsimp only [L, l, r] at hwidthFirst hlarge ⊢
    rw [hquotient] at hwidthFirst
    exact hwidthFirst.trans hlarge
  have hlogRatio : L / r ≤ l / 8 := by
    have hcross : 8 * L ≤ r * l := by
      have := (div_le_iff₀ hlp).mp (show 8 * L / l ≤ r by
        simpa only [L, l, r] using hRlow)
      nlinarith
    exact (div_le_iff₀ hrp).2 (by nlinarith)
  have hpow : T ^ (1 / r) ≤ L ^ (1 / 8 : Real) := by
    have hexp : (1 / r) * L ≤ (1 / 8 : Real) * l := by
      calc
        (1 / r) * L = L / r := by ring
        _ ≤ l / 8 := hlogRatio
        _ = (1 / 8 : Real) * l := by ring
    rw [Real.rpow_def_of_pos (by linarith : 0 < T), Real.rpow_def_of_pos hLp]
    apply Real.exp_le_exp.mpr
    have hlogT : Real.log T = L := rfl
    have hlogL : Real.log L = l := rfl
    rw [hlogT, hlogL]
    simpa only [mul_comm] using hexp
  have hrecip : 1 / (4 * L ^ (1 / 8 : Real)) ≤
      1 / (4 * T ^ (1 / r)) := by
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left hpow (by norm_num))
  rw [taoExplicitDecayExponent_two_pow hR]
  dsimp only [r] at hrecip
  exact hwidthUpper.trans hrecip

end

end Erdos1212Kernel
