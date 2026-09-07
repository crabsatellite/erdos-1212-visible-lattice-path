import Erdos1212Kernel.RosserLowerSieveBasics
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Tactic.FieldSimp

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1200000

/-!
# Iwaniec's shifted-sieve divisor-lattice transport

This is the finite subset form of the normalization used in Iwaniec (1978),
Lemma 1.  The same lower coefficient is evaluated at two coordinatewise
ordered denominator systems.  Its normalized main sum improves when the
denominators increase.
-/

def iwaniecShiftedSubsetMain
    {α : Type*} [DecidableEq α] (U : Finset α)
    (denominator : α → Real) (coefficient : Finset α → Real) : Real :=
  ∑ S ∈ U.powerset,
    coefficient S * ∏ i ∈ S, (denominator i)⁻¹

def iwaniecShiftedSubsetCumulative
    {α : Type*} [DecidableEq α]
    (coefficient : Finset α → Real) (T : Finset α) : Real :=
  ∑ S ∈ T.powerset, coefficient S

def iwaniecShiftedSubsetEuler
    {α : Type*} [DecidableEq α] (U : Finset α)
    (denominator : α → Real) : Real :=
  ∏ i ∈ U, (1 - (denominator i)⁻¹)

def iwaniecShiftedSubsetOdds
    {α : Type*} [DecidableEq α] (T : Finset α)
    (denominator : α → Real) : Real :=
  ∏ i ∈ T, (denominator i - 1)⁻¹

theorem iwaniecShiftedSubsetMain_insert
    {α : Type*} [DecidableEq α]
    {a : α} {U : Finset α} (ha : a ∉ U)
    (denominator : α → Real) (coefficient : Finset α → Real) :
    iwaniecShiftedSubsetMain (insert a U) denominator coefficient =
      iwaniecShiftedSubsetMain U denominator coefficient +
        (denominator a)⁻¹ *
          iwaniecShiftedSubsetMain U denominator
            (fun S => coefficient (insert a S)) := by
  classical
  unfold iwaniecShiftedSubsetMain
  rw [Finset.sum_powerset_insert ha]
  congr 1
  calc
    (∑ S ∈ U.powerset,
        coefficient (insert a S) *
          ∏ i ∈ insert a S, (denominator i)⁻¹) =
      ∑ S ∈ U.powerset,
        coefficient (insert a S) *
          ((denominator a)⁻¹ * ∏ i ∈ S, (denominator i)⁻¹) := by
            apply Finset.sum_congr rfl
            intro S hS
            rw [Finset.prod_insert]
            exact fun hmem => ha (Finset.mem_powerset.mp hS hmem)
    _ = (denominator a)⁻¹ *
        ∑ S ∈ U.powerset,
          coefficient (insert a S) *
            ∏ i ∈ S, (denominator i)⁻¹ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S _hS
          ring

theorem iwaniecShiftedSubsetCumulative_insert
    {α : Type*} [DecidableEq α]
    {a : α} {U : Finset α} (ha : a ∉ U)
    (coefficient : Finset α → Real) :
    iwaniecShiftedSubsetCumulative coefficient (insert a U) =
      iwaniecShiftedSubsetCumulative coefficient U +
        iwaniecShiftedSubsetCumulative
          (fun S => coefficient (insert a S)) U := by
  classical
  unfold iwaniecShiftedSubsetCumulative
  exact Finset.sum_powerset_insert ha coefficient

theorem iwaniecShiftedSubsetEuler_insert
    {α : Type*} [DecidableEq α]
    {a : α} {U : Finset α} (ha : a ∉ U)
    (denominator : α → Real) :
    iwaniecShiftedSubsetEuler (insert a U) denominator =
      (1 - (denominator a)⁻¹) *
        iwaniecShiftedSubsetEuler U denominator := by
  simp [iwaniecShiftedSubsetEuler, Finset.prod_insert ha]

theorem iwaniecShiftedSubsetOdds_insert
    {α : Type*} [DecidableEq α]
    {a : α} {U : Finset α} (ha : a ∉ U)
    (denominator : α → Real) :
    iwaniecShiftedSubsetOdds (insert a U) denominator =
      (denominator a - 1)⁻¹ *
        iwaniecShiftedSubsetOdds U denominator := by
  simp [iwaniecShiftedSubsetOdds, Finset.prod_insert ha]

/-- Exact divisor-lattice normalization identity behind the shifted sieve. -/
theorem iwaniecShiftedSubsetMain_eq_euler_mul_cumulative
    {α : Type*} [DecidableEq α]
    (U : Finset α) (denominator : α → Real)
    (coefficient : Finset α → Real)
    (hzero : ∀ i ∈ U, denominator i ≠ 0)
    (hone : ∀ i ∈ U, denominator i ≠ 1) :
    iwaniecShiftedSubsetMain U denominator coefficient =
      iwaniecShiftedSubsetEuler U denominator *
        ∑ T ∈ U.powerset,
          iwaniecShiftedSubsetCumulative coefficient T *
            iwaniecShiftedSubsetOdds T denominator := by
  classical
  induction U using Finset.induction_on generalizing coefficient with
  | empty =>
      simp [iwaniecShiftedSubsetMain, iwaniecShiftedSubsetEuler,
        iwaniecShiftedSubsetCumulative, iwaniecShiftedSubsetOdds]
  | @insert a U ha ih =>
      have haZero : denominator a ≠ 0 := hzero a (by simp)
      have haOne : denominator a ≠ 1 := hone a (by simp)
      have hUZero : ∀ i ∈ U, denominator i ≠ 0 := by
        intro i hi
        exact hzero i (by simp [hi])
      have hUOne : ∀ i ∈ U, denominator i ≠ 1 := by
        intro i hi
        exact hone i (by simp [hi])
      rw [iwaniecShiftedSubsetMain_insert ha,
        ih coefficient hUZero hUOne,
        ih (fun S => coefficient (insert a S)) hUZero hUOne,
        iwaniecShiftedSubsetEuler_insert ha,
        Finset.sum_powerset_insert ha]
      have hcumulative (T : Finset α) (hT : T ∈ U.powerset) :
          iwaniecShiftedSubsetCumulative coefficient (insert a T) =
            iwaniecShiftedSubsetCumulative coefficient T +
              iwaniecShiftedSubsetCumulative
                (fun S => coefficient (insert a S)) T := by
        apply iwaniecShiftedSubsetCumulative_insert
        exact fun hmem => ha (Finset.mem_powerset.mp hT hmem)
      have hodds (T : Finset α) (hT : T ∈ U.powerset) :
          iwaniecShiftedSubsetOdds (insert a T) denominator =
            (denominator a - 1)⁻¹ *
              iwaniecShiftedSubsetOdds T denominator := by
        apply iwaniecShiftedSubsetOdds_insert
        exact fun hmem => ha (Finset.mem_powerset.mp hT hmem)
      have hsumInsert :
          (∑ T ∈ U.powerset,
              iwaniecShiftedSubsetCumulative coefficient (insert a T) *
                iwaniecShiftedSubsetOdds (insert a T) denominator) =
            (denominator a - 1)⁻¹ *
              ((∑ T ∈ U.powerset,
                  iwaniecShiftedSubsetCumulative coefficient T *
                    iwaniecShiftedSubsetOdds T denominator) +
                ∑ T ∈ U.powerset,
                  iwaniecShiftedSubsetCumulative
                      (fun S => coefficient (insert a S)) T *
                    iwaniecShiftedSubsetOdds T denominator) := by
        calc
          (∑ T ∈ U.powerset,
              iwaniecShiftedSubsetCumulative coefficient (insert a T) *
                iwaniecShiftedSubsetOdds (insert a T) denominator) =
              ∑ T ∈ U.powerset,
                ((denominator a - 1)⁻¹ *
                    (iwaniecShiftedSubsetCumulative coefficient T *
                      iwaniecShiftedSubsetOdds T denominator) +
                  (denominator a - 1)⁻¹ *
                    (iwaniecShiftedSubsetCumulative
                        (fun S => coefficient (insert a S)) T *
                      iwaniecShiftedSubsetOdds T denominator)) := by
            apply Finset.sum_congr rfl
            intro T hT
            rw [hcumulative T hT, hodds T hT]
            ring
          _ = (denominator a - 1)⁻¹ *
                (∑ T ∈ U.powerset,
                  iwaniecShiftedSubsetCumulative coefficient T *
                    iwaniecShiftedSubsetOdds T denominator) +
              (denominator a - 1)⁻¹ *
                ∑ T ∈ U.powerset,
                  iwaniecShiftedSubsetCumulative
                      (fun S => coefficient (insert a S)) T *
                    iwaniecShiftedSubsetOdds T denominator := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          _ = _ := by ring
      rw [hsumInsert]
      field_simp [haZero, haOne]
      ring

theorem iwaniecShiftedSubsetEuler_pos
    {α : Type*} [DecidableEq α]
    (U : Finset α) (denominator : α → Real)
    (hone : ∀ i ∈ U, 1 < denominator i) :
    0 < iwaniecShiftedSubsetEuler U denominator := by
  unfold iwaniecShiftedSubsetEuler
  apply Finset.prod_pos
  intro i hi
  have h := hone i hi
  exact sub_pos.mpr (inv_lt_one_of_one_lt₀ h)

theorem iwaniecShiftedSubsetOdds_nonneg
    {α : Type*} [DecidableEq α]
    (T : Finset α) (denominator : α → Real)
    (hone : ∀ i ∈ T, 1 < denominator i) :
    0 ≤ iwaniecShiftedSubsetOdds T denominator := by
  unfold iwaniecShiftedSubsetOdds
  apply Finset.prod_nonneg
  intro i hi
  exact le_of_lt (inv_pos.mpr (sub_pos.mpr (hone i hi)))

theorem iwaniecShiftedSubsetOdds_mono
    {α : Type*} [DecidableEq α]
    (T : Finset α) (small large : α → Real)
    (hsmall : ∀ i ∈ T, 1 < small i)
    (hlarge : ∀ i ∈ T, small i ≤ large i) :
    iwaniecShiftedSubsetOdds T large ≤
      iwaniecShiftedSubsetOdds T small := by
  unfold iwaniecShiftedSubsetOdds
  apply Finset.prod_le_prod
  · intro i hi
    have hsmallPos : 0 < small i - 1 := sub_pos.mpr (hsmall i hi)
    have hlargePos : 0 < large i - 1 :=
      hsmallPos.trans_le (sub_le_sub_right (hlarge i hi) 1)
    exact le_of_lt (inv_pos.mpr hlargePos)
  · intro i hi
    have hsmallPos : 0 < small i - 1 := sub_pos.mpr (hsmall i hi)
    have hden : small i - 1 ≤ large i - 1 := sub_le_sub_right (hlarge i hi) 1
    have hlargePos : 0 < large i - 1 := hsmallPos.trans_le hden
    exact (inv_le_inv₀ hlargePos hsmallPos).2 hden

/-- Iwaniec's shifted normalized lower main sum is monotone under a
coordinatewise increase of the paired prime denominators. -/
theorem iwaniec_shifted_normalized_main_mono
    {α : Type*} [DecidableEq α]
    (U : Finset α) (reference actual : α → Real)
    (coefficient : Finset α → Real)
    (href : ∀ i ∈ U, 1 < reference i)
    (hordered : ∀ i ∈ U, reference i ≤ actual i)
    (hempty : coefficient ∅ = 1)
    (hlower : ∀ T ∈ U.powerset, T.Nonempty →
      iwaniecShiftedSubsetCumulative coefficient T ≤ 0) :
    iwaniecShiftedSubsetEuler U actual *
        iwaniecShiftedSubsetMain U reference coefficient ≤
      iwaniecShiftedSubsetEuler U reference *
        iwaniecShiftedSubsetMain U actual coefficient := by
  have hactual : ∀ i ∈ U, 1 < actual i := by
    intro i hi
    exact (href i hi).trans_le (hordered i hi)
  have hrefZero : ∀ i ∈ U, reference i ≠ 0 := by
    intro i hi
    exact ne_of_gt (zero_lt_one.trans (href i hi))
  have hrefOne : ∀ i ∈ U, reference i ≠ 1 := by
    intro i hi
    exact ne_of_gt (href i hi)
  have hactualZero : ∀ i ∈ U, actual i ≠ 0 := by
    intro i hi
    exact ne_of_gt (zero_lt_one.trans (hactual i hi))
  have hactualOne : ∀ i ∈ U, actual i ≠ 1 := by
    intro i hi
    exact ne_of_gt (hactual i hi)
  rw [iwaniecShiftedSubsetMain_eq_euler_mul_cumulative
      U reference coefficient hrefZero hrefOne,
    iwaniecShiftedSubsetMain_eq_euler_mul_cumulative
      U actual coefficient hactualZero hactualOne]
  have hnormalized :
      (∑ T ∈ U.powerset,
          iwaniecShiftedSubsetCumulative coefficient T *
            iwaniecShiftedSubsetOdds T reference) ≤
        ∑ T ∈ U.powerset,
          iwaniecShiftedSubsetCumulative coefficient T *
            iwaniecShiftedSubsetOdds T actual := by
    apply Finset.sum_le_sum
    intro T hT
    by_cases hTEmpty : T = ∅
    · subst T
      simp [iwaniecShiftedSubsetCumulative,
        iwaniecShiftedSubsetOdds, hempty]
    · have hTSubset := Finset.mem_powerset.mp hT
      have hcum := hlower T hT (Finset.nonempty_iff_ne_empty.mpr hTEmpty)
      have hodds := iwaniecShiftedSubsetOdds_mono T reference actual
        (fun i hi => href i (hTSubset hi))
        (fun i hi => hordered i (hTSubset hi))
      exact mul_le_mul_of_nonpos_left hodds hcum
  have hrefEuler := iwaniecShiftedSubsetEuler_pos U reference href
  have hactualEuler := iwaniecShiftedSubsetEuler_pos U actual hactual
  nlinarith [mul_le_mul_of_nonneg_left hnormalized
    (le_of_lt (mul_pos hactualEuler hrefEuler))]

end

end Erdos1212Kernel
