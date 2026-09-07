import Erdos1212Kernel.IwaniecEulerLogError

namespace Erdos1212Kernel

noncomputable section

open Filter Topology
open scoped BigOperators

set_option maxHeartbeats 650000

theorem iwaniecEulerConstant_pos_le_one :
    0 < Real.exp (-Real.eulerMascheroniConstant) ∧ Real.exp (-Real.eulerMascheroniConstant) ≤ 1 := by
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr ?_⟩
  linarith [Real.one_half_lt_eulerMascheroniConstant]

theorem exists_iwaniecMertensProd_unit_error_eventual :
    ∃ C : Real, ∃ N₀ : Nat, 0 < C ∧ 4 ≤ N₀ ∧ ∀ N : Nat, N₀ ≤ N →
      |Erdos696.Mertens.mertensProd N - Real.exp (-Real.eulerMascheroniConstant) / Real.log (N : Real)| ≤
        C * Real.exp (-Real.sqrt (Real.log (N : Real))) := by
  obtain ⟨A, hA, hlogerr⟩ := exists_iwaniecEulerLogRemainder_unit_error
  have hlim : Tendsto (fun N : Nat => A * Real.exp (-Real.sqrt (Real.log (N : Real)))) atTop (nhds 0) := by
    have hh := (tendsto_iwaniecRootLogDecay (a := 1) (by norm_num)).comp tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, iwaniecRootLogDecay, neg_one_mul, mul_zero] using hh.const_mul A
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 (hlim.eventually (Iio_mem_nhds (show (0 : Real) < 1 by norm_num)))
  refine ⟨2 * A, max 4 N₁, by positivity, le_max_left _ _, ?_⟩
  intro N hN
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN1 : N₁ ≤ N := (le_max_right _ _).trans hN
  have he := hlogerr N (by omega)
  have hsmall : |iwaniecEulerLogRemainder N| ≤ 1 := he.trans (hN₁ N hN1).le
  have hlog : 1 ≤ Real.log (N : Real) := by
    have hNReal : (4 : Real) ≤ N := by exact_mod_cast hN4
    have harg : Real.exp 1 ≤ (N : Real) := Real.exp_one_lt_three.le.trans (by linarith)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) harg
  let c := Real.exp (-Real.eulerMascheroniConstant) / Real.log (N : Real)
  have hc : 0 < c := div_pos (Real.exp_pos _) (by linarith)
  have hc1 : c ≤ 1 := (div_le_self (Real.exp_pos _).le hlog).trans iwaniecEulerConstant_pos_le_one.2
  have hexp := Real.abs_exp_sub_one_le hsmall
  have hidentity : Erdos696.Mertens.mertensProd N - c = c * (Real.exp (iwaniecEulerLogRemainder N) - 1) := by
    rw [iwaniecEulerLogRemainder_exp_identity (by omega : 2 ≤ N)]
    ring
  change |Erdos696.Mertens.mertensProd N - c| ≤ _
  rw [hidentity, abs_mul, abs_of_pos hc]
  calc
    _ ≤ c * (2 * |iwaniecEulerLogRemainder N|) := mul_le_mul_of_nonneg_left hexp hc.le
    _ ≤ 1 * (2 * (A * Real.exp (-Real.sqrt (Real.log (N : Real))))) :=
      mul_le_mul hc1 (mul_le_mul_of_nonneg_left he (by norm_num)) (by positivity) (by norm_num)
    _ = _ := by ring

theorem iwaniec_unit_error_extend_finite (f : Nat → Real) {A : Real} {N₀ : Nat}
    (hA : 0 < A) (hbound : ∀ N : Nat, N₀ ≤ N → |f N| ≤ A * Real.exp (-Real.sqrt (Real.log (N : Real)))) :
    ∃ C : Real, 0 < C ∧ ∀ N : Nat, |f N| ≤ C * Real.exp (-Real.sqrt (Real.log (N : Real))) := by
  let E := fun n : Nat => |f n| / Real.exp (-Real.sqrt (Real.log (n : Real)))
  let S := ∑ n ∈ Finset.range N₀, E n
  let C := A + 1 + S
  have hE : ∀ n, 0 ≤ E n := fun n => div_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have hS : 0 ≤ S := Finset.sum_nonneg (fun n _ => hE n)
  have hC : 0 < C := by dsimp [C]; linarith
  have hAC : A ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro N
  by_cases hn : N₀ ≤ N
  · exact (hbound N hn).trans (mul_le_mul_of_nonneg_right hAC (Real.exp_pos _).le)
  · have hterm : E N ≤ S := Finset.single_le_sum (fun n _ => hE n) (Finset.mem_range.mpr (Nat.lt_of_not_ge hn))
    have hEC : E N ≤ C := by dsimp [C]; linarith
    exact (div_le_iff₀ (Real.exp_pos _)).mp hEC

theorem exists_iwaniecMertensProd_unit_error_all :
    ∃ C : Real, 0 < C ∧ ∀ N : Nat,
      |Erdos696.Mertens.mertensProd N - Real.exp (-Real.eulerMascheroniConstant) / Real.log (N : Real)| ≤
        C * Real.exp (-Real.sqrt (Real.log (N : Real))) := by
  obtain ⟨A, N₀, hA, _hN₀, hbound⟩ := exists_iwaniecMertensProd_unit_error_eventual
  exact iwaniec_unit_error_extend_finite _ hA hbound

end

end Erdos1212Kernel
