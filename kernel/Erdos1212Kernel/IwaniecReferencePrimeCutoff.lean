import Erdos1212Kernel.IwaniecSieveMainMargin
import Erdos1212Kernel.IwaniecPrimePoolEuler

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

def iwaniecReferencePrimeCutoff (K : Nat) : Nat :=
  Nat.nth Nat.Prime (K - 1)

theorem iwaniecReferencePrimePool_subset_cutoff
    {K : Nat} (hK : 0 < K) :
    iwaniecReferencePrimePool K ⊆
      vaughanPrimePool (iwaniecReferencePrimeCutoff K) := by
  intro p hp
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hp
  apply Nat.mem_primesLE.mpr
  constructor
  · unfold iwaniecReferencePrimeCutoff
    apply Nat.nth_monotone Nat.infinite_setOf_prime
    omega
  · exact Nat.prime_nth_prime i

theorem vaughanPrimePool_referenceCutoff_card
    {K : Nat} (hK : 0 < K) :
    (vaughanPrimePool (iwaniecReferencePrimeCutoff K)).card = K := by
  unfold vaughanPrimePool iwaniecReferencePrimeCutoff
  rw [Nat.primesLE_eq_filter_range]
  rw [← Nat.count_eq_card_filter_range]
  convert Nat.count_nth_succ_of_infinite Nat.infinite_setOf_prime (K - 1) using 1
  omega

theorem iwaniecReferencePrimePool_eq_vaughanPrimePool
    {K : Nat} (hK : 0 < K) :
    iwaniecReferencePrimePool K =
      vaughanPrimePool (iwaniecReferencePrimeCutoff K) := by
  apply Finset.eq_of_subset_of_card_le
    (iwaniecReferencePrimePool_subset_cutoff hK)
  rw [vaughanPrimePool_referenceCutoff_card hK,
    iwaniecReferencePrimePool_card]

theorem iwaniecReferencePrimePoolEuler_eq_mertensProd
    {K : Nat} (hK : 0 < K) :
    iwaniecReferencePrimePoolEuler K =
      Erdos696.Mertens.mertensProd (iwaniecReferencePrimeCutoff K) := by
  unfold iwaniecReferencePrimePoolEuler iwaniecShiftedSubsetEuler
  rw [iwaniecReferencePrimePool_eq_vaughanPrimePool hK]
  rw [← iwaniecListEulerProduct_descendingFactors]
  rw [vaughanPrimePool_euler_eq_mertensProd]

theorem tendsto_iwaniecReferencePrimeCutoff_atTop :
    Filter.Tendsto iwaniecReferencePrimeCutoff Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro B
  filter_upwards [Filter.eventually_ge_atTop (B + 1)] with K hK
  unfold iwaniecReferencePrimeCutoff
  have hlower := Nat.add_two_le_nth_prime (K - 1)
  omega

theorem iwaniecReferencePrimePoolEuler_log_tendsto :
    Filter.Tendsto
      (fun K : Nat => iwaniecReferencePrimePoolEuler K *
        Real.log (iwaniecReferencePrimeCutoff K))
      Filter.atTop
      (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
  have h := Erdos696.Mertens.mertens_equation_15.comp
    tendsto_iwaniecReferencePrimeCutoff_atTop
  apply h.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with K hK
  rw [iwaniecReferencePrimePoolEuler_eq_mertensProd (by omega : 0 < K)]
  rfl

theorem eventually_iwaniecReferencePrimePoolEuler_log_lower :
    ∀ᶠ K : Nat in Filter.atTop,
      Real.exp (-Real.eulerMascheroniConstant) / 2 <
        iwaniecReferencePrimePoolEuler K *
          Real.log (iwaniecReferencePrimeCutoff K) := by
  let c := Real.exp (-Real.eulerMascheroniConstant)
  have hc : 0 < c := by dsimp [c]; positivity
  have hmetric := Metric.tendsto_atTop.mp
    iwaniecReferencePrimePoolEuler_log_tendsto (c / 2) (half_pos hc)
  obtain ⟨K₀, hK₀⟩ := hmetric
  filter_upwards [Filter.eventually_ge_atTop K₀] with K hK
  have hdist := hK₀ K hK
  rw [Real.dist_eq] at hdist
  dsimp [c] at hdist ⊢
  by_contra hnot
  push_neg at hnot
  have hlower : Real.exp (-Real.eulerMascheroniConstant) / 2 ≤
      |iwaniecReferencePrimePoolEuler K *
          Real.log (iwaniecReferencePrimeCutoff K) -
        Real.exp (-Real.eulerMascheroniConstant)| := by
    calc
      Real.exp (-Real.eulerMascheroniConstant) / 2 ≤
          Real.exp (-Real.eulerMascheroniConstant) -
            iwaniecReferencePrimePoolEuler K *
              Real.log (iwaniecReferencePrimeCutoff K) := by linarith
      _ = -(iwaniecReferencePrimePoolEuler K *
          Real.log (iwaniecReferencePrimeCutoff K) -
        Real.exp (-Real.eulerMascheroniConstant)) := by ring
      _ ≤ _ := neg_le_abs _
  linarith

end

end Erdos1212Kernel
