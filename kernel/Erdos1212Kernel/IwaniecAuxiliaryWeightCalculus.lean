import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1400000

/-- Literal base in the source's Lemmas 11 and 12; the first parameter
is y itself, so the denominator is exactly `(log y)^2`. -/
def iwaniecAuxWeightBase (level s : Real) : Real :=
  1 + s ^ 2 * Real.log s ^ 5 / Real.log level ^ 2

def iwaniecAuxWeightPower (level s : Real) : Real :=
  iwaniecAuxWeightBase level s ^ (5 * s)

def iwaniecAuxWeightLowerPower (level s : Real) : Real :=
  iwaniecAuxWeightBase level s ^ (5 * (s - 1))

def iwaniecAuxWeightLogDerivative (level s : Real) : Real :=
  5 * Real.log (iwaniecAuxWeightBase level s) +
    5 * s * (2 * s * Real.log s ^ 5 + 5 * s * Real.log s ^ 4) /
      (s ^ 2 * Real.log s ^ 5 + Real.log level ^ 2)

theorem iwaniecAuxWeightBase_one_le (level : Real) {s : Real} (hs : 1 ≤ s) :
    1 ≤ iwaniecAuxWeightBase level s := by
  have hl := Real.log_nonneg hs
  unfold iwaniecAuxWeightBase
  have hnn := div_nonneg (mul_nonneg (sq_nonneg s) (pow_nonneg hl 5)) (sq_nonneg (Real.log level))
  linarith

theorem iwaniecAuxWeightBase_pos (level : Real) {s : Real} (hs : 1 ≤ s) :
    0 < iwaniecAuxWeightBase level s := lt_of_lt_of_le zero_lt_one (iwaniecAuxWeightBase_one_le level hs)

theorem iwaniecAuxWeightPower_pos (level : Real) {s : Real} (hs : 1 ≤ s) :
    0 < iwaniecAuxWeightPower level s := Real.rpow_pos_of_pos (iwaniecAuxWeightBase_pos level hs) _

theorem iwaniecAuxWeightLowerPower_pos (level : Real) {s : Real} (hs : 1 ≤ s) :
    0 < iwaniecAuxWeightLowerPower level s := Real.rpow_pos_of_pos (iwaniecAuxWeightBase_pos level hs) _

theorem iwaniecAuxWeightBase_hasDerivAt (level : Real) {s : Real} (hs : 0 < s) :
    HasDerivAt (iwaniecAuxWeightBase level)
      ((2 * s * Real.log s ^ 5 + 5 * s * Real.log s ^ 4) / Real.log level ^ 2) s := by
  have hlog := (hasDerivAt_id s).log hs.ne'
  have hraw := ((((hasDerivAt_id s).pow 2).mul (hlog.pow 5)).div_const (Real.log level ^ 2)).const_add 1
  refine hraw.congr_deriv ?_
  simp only [Pi.pow_apply, id_eq]
  field_simp [hs.ne'] <;> ring

theorem iwaniecAuxWeightBase_logDerivative_identity
    {level s : Real} (hy : 1 < level) (hs : 1 ≤ s) :
    ((2 * s * Real.log s ^ 5 + 5 * s * Real.log s ^ 4) / Real.log level ^ 2) /
      iwaniecAuxWeightBase level s =
        (2 * s * Real.log s ^ 5 + 5 * s * Real.log s ^ 4) /
          (s ^ 2 * Real.log s ^ 5 + Real.log level ^ 2) := by
  have hlog := Real.log_nonneg hs
  have hL := Real.log_pos hy
  have hden : 0 < s ^ 2 * Real.log s ^ 5 + Real.log level ^ 2 :=
    add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg s) (pow_nonneg hlog 5)) (sq_pos_of_pos hL)
  unfold iwaniecAuxWeightBase
  field_simp [hL.ne', hden.ne'] <;> ring

theorem iwaniecAuxWeightPower_hasDerivAt
    {level s : Real} (hy : 1 < level) (hs : 1 ≤ s) :
    HasDerivAt (iwaniecAuxWeightPower level)
      (iwaniecAuxWeightPower level s * iwaniecAuxWeightLogDerivative level s) s := by
  have hbase := iwaniecAuxWeightBase_hasDerivAt level (show 0 < s by linarith)
  have hexp : HasDerivAt (fun t : Real => 5 * t) 5 s := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul 5
  have hraw := hbase.rpow hexp (iwaniecAuxWeightBase_pos level hs)
  refine hraw.congr_deriv ?_
  rw [Real.rpow_sub_one (iwaniecAuxWeightBase_pos level hs).ne']
  have hf := iwaniecAuxWeightBase_logDerivative_identity hy hs
  unfold iwaniecAuxWeightPower iwaniecAuxWeightLogDerivative
  calc
    _ = (iwaniecAuxWeightBase level s ^ (5 * s)) *
        (5 * Real.log (iwaniecAuxWeightBase level s) + 5 * s *
          (((2 * s * Real.log s ^ 5 + 5 * s * Real.log s ^ 4) / Real.log level ^ 2) /
            iwaniecAuxWeightBase level s)) := by ring
    _ = _ := by rw [hf]; ring

theorem iwaniecAuxWeightPower_split (level : Real) {s : Real} (hs : 1 ≤ s) :
    iwaniecAuxWeightPower level s =
      iwaniecAuxWeightLowerPower level s * iwaniecAuxWeightBase level s ^ 5 := by
  unfold iwaniecAuxWeightPower iwaniecAuxWeightLowerPower
  rw [show (5 : Real) * s = 5 * (s - 1) + 5 by ring,
    Real.rpow_add (iwaniecAuxWeightBase_pos level hs)]
  norm_num

end

end Erdos1212Kernel
