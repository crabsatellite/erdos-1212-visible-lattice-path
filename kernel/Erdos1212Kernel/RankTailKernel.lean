import Mathlib.Order.Filter.AtTopBot.Basic
import Erdos1212Kernel.RenewalKernel

namespace Erdos1212Kernel

open Filter Topology

/-!
The terminal positive rank argument used by the canonical-contour route.

The rank coefficient is indexed first by the translation scale and then by
its exact number of nonpermanent labels.  This file isolates the two analytic
facts needed at the endpoint: a summable coefficientwise majorant gives a
uniformly tight rank tail, and fixed-rank vanishing then forces the complete
positive coefficient to vanish.  No contour geometry is assumed here.
-/

/-- The mass above the exact-rank cutoff `K`. -/
noncomputable def rankTail
    (rankMass : Nat → Nat → NNReal) (T K : Nat) : NNReal :=
  tailMass (rankMass T) (K + 1)

/--
The exact order-of-limits form used in the manuscript: after choosing a rank
cutoff, the tail is eventually small in the translation scale.
-/
def AsymptoticRankTight (rankMass : Nat → Nat → NNReal) : Prop :=
  ∀ ε > 0, ∃ K,
    Filter.Eventually (fun T : Nat ↦ rankTail rankMass T K < ε) atTop

/-- The total exact-rank coefficient at translation scale `T`. -/
noncomputable def totalRankMass
    (rankMass : Nat → Nat → NNReal) (T : Nat) : NNReal :=
  ∑' K, rankMass T K

/-- The coefficient carried by exact ranks at most `K`. -/
def finiteRankMass
    (rankMass : Nat → Nat → NNReal) (K T : Nat) : NNReal :=
  ∑ k ∈ Finset.range (K + 1), rankMass T k

theorem finiteRankMass_tendsto_zero
    (rankMass : Nat → Nat → NNReal)
    (hfixed : ∀ K, Tendsto (fun T ↦ rankMass T K) atTop (nhds 0))
    (K : Nat) :
    Tendsto (finiteRankMass rankMass K) atTop (nhds 0) := by
  simpa only [finiteRankMass, Finset.sum_const_zero] using
    (tendsto_finsetSum (Finset.range (K + 1)) (fun k _ ↦ hfixed k))

theorem totalRankMass_eq_finiteRankMass_add_rankTail
    (rankMass : Nat → Nat → NNReal)
    (hsummable : ∀ T, Summable (rankMass T))
    (T K : Nat) :
    totalRankMass rankMass T =
      finiteRankMass rankMass K T + rankTail rankMass T K := by
  apply NNReal.eq
  change
    ((∑' k, rankMass T k : NNReal) : Real) =
      ((∑ k ∈ Finset.range (K + 1), rankMass T k : NNReal) : Real) +
        ((∑' n : {n : Nat // n ∉ Finset.range (K + 1)}, rankMass T n : NNReal) : Real)
  simp_rw [NNReal.coe_tsum]
  push_cast
  exact
    ((NNReal.summable_coe.mpr (hsummable T)).sum_add_tsum_compl
      (s := Finset.range (K + 1))).symm

private theorem nnreal_add_lt_of_lt_half
    {a b ε : NNReal} (ha : a < ε / 2) (hb : b < ε / 2) :
    a + b < ε :=
  (add_lt_add ha hb).trans_eq (add_halves ε)

/-
The paper's endpoint implication with its stated order of limits.  At every
finite translation scale the exact-rank coefficient is summable (in the
concrete application it has finite support); fixed ranks vanish, while the
escaping-rank tail is asymptotically tight.  Positivity then forces the full
coefficient to vanish.
-/
set_option maxHeartbeats 1000000 in
theorem totalRankMass_tendsto_zero_of_asymptotic_rank_tight
    (rankMass : Nat → Nat → NNReal)
    (hsummable : ∀ T, Summable (rankMass T))
    (hfixed : ∀ K, Tendsto (fun T ↦ rankMass T K) atTop (nhds 0))
    (htight : AsymptoticRankTight rankMass) :
    Tendsto (totalRankMass rankMass) atTop (nhds 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact (not_lt_of_ge bot_le ha).elim
  · intro ε hε
    have hhalf : 0 < ε / 2 := by positivity
    obtain ⟨K, htail⟩ := htight (ε / 2) hhalf
    have hfinite : Tendsto (finiteRankMass rankMass K) atTop (nhds 0) :=
      finiteRankMass_tendsto_zero rankMass hfixed K
    have hfiniteEventually :
        Filter.Eventually
          (fun T : Nat ↦ finiteRankMass rankMass K T < ε / 2)
          atTop :=
      (tendsto_order.1 hfinite).2 (ε / 2) hhalf
    refine (htail.and hfiniteEventually).mono ?_
    intro T hT
    rcases hT with ⟨htailT, hfiniteT⟩
    have hsum : finiteRankMass rankMass K T + rankTail rankMass T K < ε :=
      nnreal_add_lt_of_lt_half hfiniteT htailT
    exact (totalRankMass_eq_finiteRankMass_add_rankTail rankMass hsummable T K).symm ▸ hsum

end Erdos1212Kernel
