import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Topology.Instances.NNReal.Lemmas

namespace Erdos1212Kernel

open Filter Topology

/-!
The abstract positive-renewal layer of the contour route.

This file deliberately does not postulate that the concrete Erdős 1212
contours satisfy these hypotheses.  That semantic binding is a separate open
obligation.  What is closed here is the analytic implication: once the
contour masses have the stated positive geometric domination and the escape
event is dominated by their tails, escape mass tends to zero.
-/

/-- Total repeat ratio from the finite and large-prime pieces. -/
def repeatRatio (smallRepeat largeRepeat : NNReal) : NNReal :=
  smallRepeat + largeRepeat

/-- The strict certificate margins combine to a genuinely subcritical ratio. -/
theorem repeatRatio_lt_one
    {smallRepeat largeRepeat : NNReal}
    (hsmall : smallRepeat < (933 : NNReal) / 1000)
    (hlarge : largeRepeat < (67 : NNReal) / 1000) :
    repeatRatio smallRepeat largeRepeat < 1 := by
  calc
    repeatRatio smallRepeat largeRepeat = smallRepeat + largeRepeat := rfl
    _ < (933 : NNReal) / 1000 + (67 : NNReal) / 1000 := add_lt_add hsmall hlarge
    _ = 1 := by norm_num

/-- Scalar majorant for `n` successive first-repeat renewals. -/
def renewalMajorant (freshBound ratio : NNReal) (n : Nat) : NNReal :=
  freshBound * ratio ^ n

theorem renewalMajorant_summable
    (freshBound ratio : NNReal) (hratio : ratio < 1) :
    Summable (renewalMajorant freshBound ratio) := by
  simpa [renewalMajorant] using (NNReal.summable_geometric hratio).mul_left freshBound

/-- Mass outside the finite set of contour sizes `< M`. -/
noncomputable def tailMass (mass : Nat → NNReal) (M : Nat) : NNReal :=
  ∑' n : {n : Nat // n ∉ Finset.range M}, mass n

theorem tailMass_tendsto_zero (mass : Nat → NNReal) (_hmass : Summable mass) :
    Tendsto (tailMass mass) atTop (𝓝 0) := by
  simpa [tailMass] using
    (NNReal.tendsto_tsum_compl_atTop_zero mass).comp tendsto_finset_range

/-- All hypotheses supplied by the concrete contour/necklace encoding. -/
structure RenewalDomination where
  freshBound : NNReal
  smallRepeat : NNReal
  largeRepeat : NNReal
  renewalLayerMass : Nat → NNReal
  contourMass : Nat → NNReal
  smallRepeat_lt : smallRepeat < (933 : NNReal) / 1000
  largeRepeat_lt : largeRepeat < (67 : NNReal) / 1000
  renewalLayer_le : ∀ n,
    renewalLayerMass n ≤
      renewalMajorant freshBound (repeatRatio smallRepeat largeRepeat) n
  contour_partial_le : ∀ M,
    (∑ n ∈ Finset.range M, contourMass n) ≤ ∑' n, renewalLayerMass n

theorem RenewalDomination.repeat_lt_one (D : RenewalDomination) :
    repeatRatio D.smallRepeat D.largeRepeat < 1 :=
  repeatRatio_lt_one D.smallRepeat_lt D.largeRepeat_lt

theorem renewalLayerMass_summable (D : RenewalDomination) :
    Summable D.renewalLayerMass := by
  rw [← NNReal.summable_coe]
  apply Summable.of_nonneg_of_le
  · intro n
    exact (D.renewalLayerMass n).coe_nonneg
  · intro n
    exact_mod_cast D.renewalLayer_le n
  · exact NNReal.summable_coe.mpr <|
      renewalMajorant_summable D.freshBound
        (repeatRatio D.smallRepeat D.largeRepeat) D.repeat_lt_one

theorem contourMass_summable (D : RenewalDomination) :
    Summable D.contourMass :=
  NNReal.summable_of_sum_range_le D.contour_partial_le

/-- The exact tail-tightness conclusion needed by the no-escape route. -/
def NoEscape (escapeMass : Nat → NNReal) : Prop :=
  Tendsto escapeMass atTop (𝓝 0)

theorem noEscape_of_tail_domination
    (mass escapeMass : Nat → NNReal)
    (_hmass : Summable mass)
    (hdom : ∀ M, escapeMass M ≤ tailMass mass M) :
    NoEscape escapeMass := by
  change Tendsto escapeMass atTop (𝓝 0)
  have htail : Tendsto (tailMass mass) atTop (𝓝 0) :=
    tailMass_tendsto_zero mass _hmass
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact (not_lt_of_ge bot_le ha).elim
  · intro b hb
    have hev : ∀ᶠ M in atTop, tailMass mass M < b :=
      (tendsto_order.1 htail).2 b hb
    filter_upwards [hev] with M hM
    exact lt_of_le_of_lt (hdom M) hM

theorem noEscape_of_renewal
    (D : RenewalDomination)
    (escapeMass : Nat → NNReal)
    (hdom : ∀ M, escapeMass M ≤ tailMass D.contourMass M) :
    NoEscape escapeMass :=
  noEscape_of_tail_domination D.contourMass escapeMass
    (contourMass_summable D) hdom

end Erdos1212Kernel
