import Erdos1212Kernel.TranslationPhaseCharge
import Erdos1212Kernel.ReciprocalSquareTail

namespace Erdos1212Kernel

open scoped BigOperators
open Filter Topology

/-!
# Joint finite-box phase lift

The finite-box boundary atom may not be multiplied conditionally along one
incoming row.  Here a fixed finite source pool is summed first.  The complete
joint density is then bounded by its elementary-symmetric Euler term plus one
boundary error proportional to `box⁻²`.  Consequently the boundary disappears
only after the source pool and the stopped rank have been fixed.
-/

section DistinctNNActivity

variable {α : Type*} [DecidableEq α]

/-- The unordered, without-replacement `marked`-identity activity in `NNReal`.
This is the Haar--CRT main term after a fixed source pool has been summed. -/
def finiteDistinctNNActivity (weight : α → NNReal) (pool : Finset α)
    (marked : Nat) : NNReal :=
  ∑ labels ∈ pool.powersetCard marked, ∏ label ∈ labels, weight label

theorem finiteDistinctNNActivity_zero (weight : α → NNReal)
    (pool : Finset α) :
    finiteDistinctNNActivity weight pool 0 = 1 := by
  simp [finiteDistinctNNActivity]

theorem finiteDistinctNNActivity_insert_succ
    (weight : α → NNReal) {label : α} {pool : Finset α}
    (hfresh : label ∉ pool) (marked : Nat) :
    finiteDistinctNNActivity weight (insert label pool) (marked + 1) =
      finiteDistinctNNActivity weight pool (marked + 1) +
        weight label * finiteDistinctNNActivity weight pool marked := by
  classical
  let old := pool.powersetCard (marked + 1)
  let new := (pool.powersetCard marked).image (insert label)
  have hdecomposition :
      (insert label pool).powersetCard (marked + 1) = old ∪ new := by
    simpa [old, new, Nat.succ_eq_add_one] using
      (Finset.powersetCard_succ_insert hfresh marked)
  have hdisjoint : Disjoint old new := by
    refine Finset.disjoint_left.mpr ?_
    intro labels hOld hNew
    obtain ⟨tail, hTail, rfl⟩ := Finset.mem_image.mp hNew
    have hsubset : insert label tail ⊆ pool :=
      (Finset.mem_powersetCard.mp hOld).1
    exact hfresh (hsubset (Finset.mem_insert_self label tail))
  have hinjective : Set.InjOn (insert label)
      (↑(pool.powersetCard marked) : Set (Finset α)) := by
    intro left hLeft right hRight heq
    have hleftFresh : label ∉ left := by
      intro hmem
      exact hfresh ((Finset.mem_powersetCard.mp hLeft).1 hmem)
    have hrightFresh : label ∉ right := by
      intro hmem
      exact hfresh ((Finset.mem_powersetCard.mp hRight).1 hmem)
    have herase := congrArg (fun labels : Finset α => labels.erase label) heq
    simpa [Finset.erase_insert hleftFresh,
      Finset.erase_insert hrightFresh] using herase
  rw [finiteDistinctNNActivity, hdecomposition,
    Finset.sum_union hdisjoint]
  change (∑ labels ∈ old, ∏ prime ∈ labels, weight prime) +
      (∑ labels ∈ new, ∏ prime ∈ labels, weight prime) = _
  have hnew :
      (∑ labels ∈ new, ∏ prime ∈ labels, weight prime) =
        weight label *
          ∑ tail ∈ pool.powersetCard marked,
            ∏ prime ∈ tail, weight prime := by
    dsimp [new]
    rw [Finset.sum_image hinjective]
    calc
      (∑ tail ∈ pool.powersetCard marked,
          ∏ prime ∈ insert label tail, weight prime) =
          ∑ tail ∈ pool.powersetCard marked,
            weight label * ∏ prime ∈ tail, weight prime := by
        apply Finset.sum_congr rfl
        intro tail hTail
        rw [Finset.prod_insert]
        intro hmem
        exact hfresh ((Finset.mem_powersetCard.mp hTail).1 hmem)
      _ = weight label *
          ∑ tail ∈ pool.powersetCard marked,
            ∏ prime ∈ tail, weight prime := by
        rw [Finset.mul_sum]
  rw [hnew]
  rfl

/-- The unordered distinct-identity sum is bounded by the ordered sum. -/
theorem finiteDistinctNNActivity_le_pow_sum
    (weight : α → NNReal) :
    ∀ pool marked,
      finiteDistinctNNActivity weight pool marked ≤
        (∑ label ∈ pool, weight label) ^ marked := by
  intro pool
  induction pool using Finset.induction_on with
  | empty =>
      intro marked
      cases marked with
      | zero => simp [finiteDistinctNNActivity]
      | succ marked =>
          have hempty :
              (∅ : Finset α).powersetCard (marked + 1) = ∅ :=
            Finset.powersetCard_eq_empty.mpr (by simp)
          rw [finiteDistinctNNActivity, hempty]
          simp
  | @insert label pool hfresh ih =>
      intro marked
      cases marked with
      | zero => simp [finiteDistinctNNActivity]
      | succ marked =>
          let total : NNReal := ∑ other ∈ pool, weight other
          have htotal : 0 ≤ total := bot_le
          have hsame := ih (marked + 1)
          have hprevious := ih marked
          have hscaled :
              weight label * finiteDistinctNNActivity weight pool marked ≤
                weight label * total ^ marked :=
            mul_le_mul_left' hprevious (weight label)
          have hlinear :
              total ^ (marked + 1) + weight label * total ^ marked ≤
                total ^ (marked + 1) +
                  (((marked + 1 : Nat) : NNReal) * total ^ marked) *
                    weight label := by
            have hterm :
                weight label * total ^ marked ≤
                  ((marked + 1 : Nat) : NNReal) * total ^ marked *
                    weight label := by
              calc
              weight label * total ^ marked =
                  1 * (total ^ marked * weight label) := by ring
              _ ≤ ((marked + 1 : Nat) : NNReal) *
                    (total ^ marked * weight label) := by
                apply mul_le_mul_of_nonneg_right
                · exact_mod_cast (Nat.succ_le_succ (Nat.zero_le marked))
                · exact bot_le
              _ = ((marked + 1 : Nat) : NNReal) *
                    total ^ marked * weight label := by ring
            simpa [add_comm] using
              add_le_add_left hterm (total ^ (marked + 1))
          have hbernoulli :
              total ^ (marked + 1) +
                  (((marked + 1 : Nat) : NNReal) * total ^ marked) *
                    weight label ≤
                (total + weight label) ^ (marked + 1) := by
            simpa using pow_add_mul_le_add_pow htotal
              (by positivity : 0 ≤ 2 * total + weight label) (marked + 1)
          calc
            finiteDistinctNNActivity weight (insert label pool)
                (marked + 1) =
              finiteDistinctNNActivity weight pool (marked + 1) +
                weight label *
                  finiteDistinctNNActivity weight pool marked := by
              rw [finiteDistinctNNActivity_insert_succ weight hfresh marked]
            _ ≤ total ^ (marked + 1) +
                weight label * total ^ marked := add_le_add hsame hscaled
            _ ≤ total ^ (marked + 1) +
                (((marked + 1 : Nat) : NNReal) * total ^ marked) *
                  weight label := hlinear
            _ ≤ (total + weight label) ^ (marked + 1) := hbernoulli
            _ = (∑ other ∈ insert label pool, weight other) ^
                (marked + 1) := by
              rw [Finset.sum_insert hfresh]
              dsimp [total]
              rw [add_comm]

/-- Sharp elementary-symmetric inequality in `NNReal`:
`m! * e_m <= (sum weight)^m`. -/
theorem factorial_mul_finiteDistinctNNActivity_le_pow_sum
    (weight : α → NNReal) :
    ∀ pool marked,
      (marked.factorial : NNReal) *
          finiteDistinctNNActivity weight pool marked ≤
        (∑ label ∈ pool, weight label) ^ marked := by
  intro pool
  induction pool using Finset.induction_on with
  | empty =>
      intro marked
      cases marked with
      | zero => simp [finiteDistinctNNActivity]
      | succ marked =>
          have hempty :
              (∅ : Finset α).powersetCard (marked + 1) = ∅ :=
            Finset.powersetCard_eq_empty.mpr (by simp)
          rw [finiteDistinctNNActivity, hempty]
          simp
  | @insert label pool hfresh inductionHypothesis =>
      intro marked
      cases marked with
      | zero => simp [finiteDistinctNNActivity]
      | succ marked =>
          let total : NNReal := ∑ other ∈ pool, weight other
          have hsame := inductionHypothesis (marked + 1)
          have hprevious := inductionHypothesis marked
          have hscaled :
              (((marked + 1 : Nat) : NNReal) * weight label) *
                    ((marked.factorial : NNReal) *
                      finiteDistinctNNActivity weight pool marked) ≤
                (((marked + 1 : Nat) : NNReal) * weight label) *
                    total ^ marked :=
            mul_le_mul_left' hprevious _
          have hbernoulli :
              total ^ (marked + 1) +
                  (((marked + 1 : Nat) : NNReal) * total ^ marked) *
                    weight label ≤
                (total + weight label) ^ (marked + 1) := by
            simpa using pow_add_mul_le_add_pow (show 0 ≤ total from bot_le)
              (show 0 ≤ 2 * total + weight label from bot_le) (marked + 1)
          calc
            (((marked + 1).factorial : Nat) : NNReal) *
                finiteDistinctNNActivity weight (insert label pool)
                  (marked + 1) =
              (((marked + 1).factorial : Nat) : NNReal) *
                (finiteDistinctNNActivity weight pool (marked + 1) +
                  weight label *
                    finiteDistinctNNActivity weight pool marked) := by
              rw [finiteDistinctNNActivity_insert_succ weight hfresh marked]
            _ = (((marked + 1).factorial : Nat) : NNReal) *
                    finiteDistinctNNActivity weight pool (marked + 1) +
                (((marked + 1 : Nat) : NNReal) * weight label) *
                  ((marked.factorial : NNReal) *
                    finiteDistinctNNActivity weight pool marked) := by
              rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
                Nat.cast_one]
              ring
            _ ≤ total ^ (marked + 1) +
                (((marked + 1 : Nat) : NNReal) * weight label) *
                  total ^ marked := add_le_add hsame hscaled
            _ = total ^ (marked + 1) +
                (((marked + 1 : Nat) : NNReal) * total ^ marked) *
                  weight label := by ring
            _ ≤ (total + weight label) ^ (marked + 1) := hbernoulli
            _ = (∑ other ∈ insert label pool, weight other) ^
                (marked + 1) := by
              rw [Finset.sum_insert hfresh]
              dsimp [total]
              rw [add_comm]

theorem finiteDistinctNNActivity_le_pow_div_factorial
    (weight : α → NNReal) (pool : Finset α) (marked : Nat) :
    finiteDistinctNNActivity weight pool marked ≤
      (∑ label ∈ pool, weight label) ^ marked /
        (marked.factorial : NNReal) := by
  apply (le_div_iff₀ (by positivity : (0 : NNReal) < marked.factorial)).2
  simpa [mul_comm] using
    factorial_mul_finiteDistinctNNActivity_le_pow_sum
      weight pool marked

end DistinctNNActivity

/-- The two-coordinate activity of one prime identity. -/
noncomputable def squarePrimeActivityNN (prime : Nat) : NNReal :=
  ((prime : NNReal) ^ 2)⁻¹

/-- Joint density of all `marked`-element phase sets in one fixed finite
source pool.  Residues may depend on the complete identity set, but the pool
itself is fixed before the box limit. -/
noncomputable def jointTranslationPhaseDensity
    (box marked : Nat) (pool : Finset Nat)
    (residueX residueY : Finset Nat → Nat → Nat) : NNReal :=
  ∑ labels ∈ pool.powersetCard marked,
    ((translationPhaseCell box labels
      (residueX labels) (residueY labels)).card : NNReal) /
        (box : NNReal) ^ 2

/-- After the fixed pool is summed, the honest finite-box density is the
Euler main term plus one vanishing boundary error. -/
theorem jointTranslationPhaseDensity_le_euler_add_boundary
    (box marked : Nat) (pool : Finset Nat)
    (residueX residueY : Finset Nat → Nat → Nat)
    (hbox : 0 < box) (hprime : ∀ q ∈ pool, Nat.Prime q) :
    jointTranslationPhaseDensity box marked pool residueX residueY ≤
      2 * finiteDistinctNNActivity squarePrimeActivityNN pool marked +
        2 * (pool.powersetCard marked).card *
          ((box : NNReal)⁻¹) ^ 2 := by
  classical
  unfold jointTranslationPhaseDensity
  calc
    (∑ labels ∈ pool.powersetCard marked,
        ((translationPhaseCell box labels
          (residueX labels) (residueY labels)).card : NNReal) /
            (box : NNReal) ^ 2) ≤
      ∑ labels ∈ pool.powersetCard marked,
        ((((∏ q ∈ labels, q : Nat) : NNReal)⁻¹ +
          (box : NNReal)⁻¹) ^ 2) := by
      apply Finset.sum_le_sum
      intro labels hlabels
      simpa [Nat.cast_prod] using
        translationPhaseCell_density_le_inverse_prod_add_boundary_sq
          box labels (residueX labels) (residueY labels) hbox
          (fun q hq =>
            hprime q ((Finset.mem_powersetCard.mp hlabels).1 hq))
    _ ≤ ∑ labels ∈ pool.powersetCard marked,
        (2 * ∏ q ∈ labels, squarePrimeActivityNN q +
          2 * ((box : NNReal)⁻¹) ^ 2) := by
      apply Finset.sum_le_sum
      intro labels _hlabels
      have hsquare (a b : NNReal) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
        apply NNReal.coe_le_coe.mp
        push_cast
        nlinarith [sq_nonneg ((a : Real) - (b : Real))]
      simpa [squarePrimeActivityNN, Finset.prod_inv_distrib,
        ← Finset.prod_pow] using
        hsquare (((∏ q ∈ labels, q : Nat) : NNReal)⁻¹)
          ((box : NNReal)⁻¹)
    _ = 2 * finiteDistinctNNActivity squarePrimeActivityNN pool marked +
        2 * (pool.powersetCard marked).card *
          ((box : NNReal)⁻¹) ^ 2 := by
      rw [Finset.sum_add_distrib]
      simp only [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      unfold finiteDistinctNNActivity
      ring

/-- With the stopped rank and source pool fixed, the total finite-box boundary
atom vanishes.  This limit is taken after the joint source sum, not per row. -/
theorem jointTranslationPhaseBoundary_tendsto_zero
    (pool : Finset Nat) (marked : Nat) :
    Tendsto
      (fun box : Nat =>
        2 * (pool.powersetCard marked).card *
          ((box : NNReal)⁻¹) ^ 2)
      atTop (nhds 0) := by
  have hbox : Tendsto (fun box : Nat => (box : NNReal)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun box : Nat => ((box : NNReal)⁻¹))
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hbox
  simpa using
    (tendsto_const_nhds.mul (hinv.pow 2) :
      Tendsto
        (fun box : Nat =>
          (2 * (pool.powersetCard marked).card : NNReal) *
            ((box : NNReal)⁻¹) ^ 2)
        atTop (nhds (2 * (pool.powersetCard marked).card * 0 ^ 2)))

/-- The exact fixed-pool order of limits: after the complete joint phase sum,
the finite-box density is eventually within `δ` of twice its Euler term. -/
theorem jointTranslationPhaseDensity_eventually_lt_euler_add
    (marked : Nat) (pool : Finset Nat)
    (residueX residueY : Finset Nat → Nat → Nat)
    (hprime : ∀ q ∈ pool, Nat.Prime q)
    (δ : NNReal) (hδ : 0 < δ) :
    ∀ᶠ box : Nat in atTop,
      jointTranslationPhaseDensity box marked pool residueX residueY <
        2 * finiteDistinctNNActivity squarePrimeActivityNN pool marked + δ := by
  have hboundary := jointTranslationPhaseBoundary_tendsto_zero pool marked
  have hboundaryEventually :
      ∀ᶠ box : Nat in atTop,
        2 * (pool.powersetCard marked).card *
            ((box : NNReal)⁻¹) ^ 2 < δ :=
    (tendsto_order.1 hboundary).2 δ hδ
  filter_upwards [hboundaryEventually, eventually_ge_atTop 1]
      with box hsmall hbox
  calc
    jointTranslationPhaseDensity box marked pool residueX residueY ≤
        2 * finiteDistinctNNActivity squarePrimeActivityNN pool marked +
          2 * (pool.powersetCard marked).card *
            ((box : NNReal)⁻¹) ^ 2 :=
      jointTranslationPhaseDensity_le_euler_add_boundary
        box marked pool residueX residueY hbox hprime
    _ < 2 * finiteDistinctNNActivity squarePrimeActivityNN pool marked + δ :=
      by
        simpa [add_comm] using
          add_lt_add_left hsmall
            (2 * finiteDistinctNNActivity squarePrimeActivityNN pool marked)

/-- The joint Euler term is controlled by the complete reciprocal-square
mass of the fixed pool; no identity is recharged. -/
theorem finiteDistinctSquarePrimeActivity_le_tail_pow
    (pool : Finset Nat) (marked : Nat) :
    finiteDistinctNNActivity squarePrimeActivityNN pool marked ≤
      (∑ q ∈ pool, squarePrimeActivityNN q) ^ marked :=
  finiteDistinctNNActivity_le_pow_sum squarePrimeActivityNN pool marked

/-- A fixed finite pool above `start` is uniformly bounded by the complete
integer reciprocal-square tail. -/
theorem sum_squarePrimeActivityNN_le_integer_tail
    {pool : Finset Nat} {start : Nat}
    (hstart : 2 ≤ start) (hpool : ∀ q ∈ pool, start ≤ q) :
    (∑ q ∈ pool, squarePrimeActivityNN q) ≤
      (((start : NNReal) - 1)⁻¹) := by
  have hrat := finite_integer_reciprocal_square_tail hstart hpool
  have hsub : (start : Rat) - 1 = ((start - 1 : Nat) : Rat) := by
    rw [Nat.cast_sub (by omega : 1 ≤ start)]
    norm_num
  rw [hsub] at hrat
  simp only [one_div, ← Nat.cast_pow] at hrat
  have hstartNN : (1 : NNReal) ≤ (start : NNReal) := by
    exact_mod_cast (show 1 ≤ start by omega)
  apply NNReal.coe_le_coe.mp
  rw [NNReal.coe_sum, NNReal.coe_inv, NNReal.coe_sub hstartNN]
  simp_rw [squarePrimeActivityNN, NNReal.coe_inv, NNReal.coe_pow,
    NNReal.coe_natCast]
  norm_num
  rw [show (start : Real) - 1 = ((start - 1 : Nat) : Real) by
    rw [Nat.cast_sub (by omega : 1 ≤ start)]
    norm_num]
  have hreal :
      ((((∑ x ∈ pool, (((x ^ 2 : Nat) : Rat))⁻¹) : Rat)) : Real) ≤
        (((((start - 1 : Nat) : Rat))⁻¹ : Rat) : Real) :=
    (Rat.cast_le).2 hrat
  push_cast at hreal
  simpa [Nat.cast_pow] using hreal

/-- The complete joint Euler contribution of `marked` distinct identities
above `start` is bounded independently of the finite truncation pool. -/
theorem finiteDistinctSquarePrimeActivity_le_integer_tail_pow
    {pool : Finset Nat} {start marked : Nat}
    (hstart : 2 ≤ start) (hpool : ∀ q ∈ pool, start ≤ q) :
    finiteDistinctNNActivity squarePrimeActivityNN pool marked ≤
      (((start : NNReal) - 1)⁻¹) ^ marked := by
  calc
    finiteDistinctNNActivity squarePrimeActivityNN pool marked ≤
        (∑ q ∈ pool, squarePrimeActivityNN q) ^ marked :=
      finiteDistinctSquarePrimeActivity_le_tail_pow pool marked
    _ ≤ (((start : NNReal) - 1)⁻¹) ^ marked := by
      gcongr
      exact sum_squarePrimeActivityNN_le_integer_tail hstart hpool

theorem finiteDistinctSquarePrimeActivity_le_integer_tail_pow_div_factorial
    {pool : Finset Nat} {start marked : Nat}
    (hstart : 2 ≤ start) (hpool : ∀ q ∈ pool, start ≤ q) :
    finiteDistinctNNActivity squarePrimeActivityNN pool marked ≤
      (((start : NNReal) - 1)⁻¹) ^ marked /
        (marked.factorial : NNReal) := by
  calc
    finiteDistinctNNActivity squarePrimeActivityNN pool marked ≤
        (∑ q ∈ pool, squarePrimeActivityNN q) ^ marked /
          (marked.factorial : NNReal) :=
      finiteDistinctNNActivity_le_pow_div_factorial
        squarePrimeActivityNN pool marked
    _ ≤ (((start : NNReal) - 1)⁻¹) ^ marked /
          (marked.factorial : NNReal) := by
      exact div_le_div_of_nonneg_right
        (pow_le_pow_left'
          (sum_squarePrimeActivityNN_le_integer_tail hstart hpool) marked)
        (by positivity)

theorem jointTranslationPhaseDensity_le_integer_tail_factorial_add_boundary
    (box marked : Nat) (pool : Finset Nat)
    (residueX residueY : Finset Nat → Nat → Nat)
    {start : Nat} (hbox : 0 < box) (hstart : 2 ≤ start)
    (hpool : ∀ q ∈ pool, start ≤ q)
    (hprime : ∀ q ∈ pool, Nat.Prime q) :
    jointTranslationPhaseDensity box marked pool residueX residueY ≤
      2 * ((((start : NNReal) - 1)⁻¹) ^ marked /
        (marked.factorial : NNReal)) +
      2 * (pool.powersetCard marked).card *
        ((box : NNReal)⁻¹) ^ 2 := by
  calc
    jointTranslationPhaseDensity box marked pool residueX residueY ≤
        2 * finiteDistinctNNActivity squarePrimeActivityNN pool marked +
          2 * (pool.powersetCard marked).card *
            ((box : NNReal)⁻¹) ^ 2 :=
      jointTranslationPhaseDensity_le_euler_add_boundary
        box marked pool residueX residueY hbox hprime
    _ ≤ 2 * ((((start : NNReal) - 1)⁻¹) ^ marked /
          (marked.factorial : NNReal)) +
        2 * (pool.powersetCard marked).card *
          ((box : NNReal)⁻¹) ^ 2 := by
      gcongr
      exact finiteDistinctSquarePrimeActivity_le_integer_tail_pow_div_factorial
        hstart hpool

/-- Fixed stopped-prefix phase lift with a truncation-independent Euler tail.
The source pool is finite while the box tends to infinity, but the right-hand
side depends only on the common lower cutoff `start`. -/
theorem jointTranslationPhaseDensity_eventually_lt_integer_tail
    (marked : Nat) (pool : Finset Nat)
    (residueX residueY : Finset Nat → Nat → Nat)
    {start : Nat} (hstart : 2 ≤ start)
    (hpool : ∀ q ∈ pool, start ≤ q)
    (hprime : ∀ q ∈ pool, Nat.Prime q)
    (δ : NNReal) (hδ : 0 < δ) :
    ∀ᶠ box : Nat in atTop,
      jointTranslationPhaseDensity box marked pool residueX residueY <
        2 * (((start : NNReal) - 1)⁻¹) ^ marked + δ := by
  filter_upwards [jointTranslationPhaseDensity_eventually_lt_euler_add
      marked pool residueX residueY hprime δ hδ]
      with box hdensity
  exact hdensity.trans_le <| by
    gcongr
    exact finiteDistinctSquarePrimeActivity_le_integer_tail_pow
      hstart hpool

section StoppedSourceSum

variable {σ : Type*} [DecidableEq σ]

/-- The complete positive density after all fixed stopped source records have
been summed.  The phase sum is never conditioned on one incoming row. -/
noncomputable def jointStoppedSourceDensity
    (box marked : Nat) (sources : Finset σ)
    (sourceWeight : σ → NNReal) (pool : σ → Finset Nat)
    (residueX residueY : σ → Finset Nat → Nat → Nat) : NNReal :=
  ∑ source ∈ sources,
    sourceWeight source *
      jointTranslationPhaseDensity box marked (pool source)
        (residueX source) (residueY source)

/-- The summed boundary term of the fixed stopped source family. -/
noncomputable def jointStoppedSourceBoundary
    (box marked : Nat) (sources : Finset σ)
    (sourceWeight : σ → NNReal) (pool : σ → Finset Nat) : NNReal :=
  ∑ source ∈ sources,
    sourceWeight source *
      (2 * ((pool source).powersetCard marked).card *
        ((box : NNReal)⁻¹) ^ 2)

/-- Coefficient-level finite-box bound after every stopped source has already
been summed. -/
theorem jointStoppedSourceDensity_le_integer_tail_add_boundary
    (box marked : Nat) (sources : Finset σ)
    (sourceWeight : σ → NNReal) (pool : σ → Finset Nat)
    (residueX residueY : σ → Finset Nat → Nat → Nat)
    {start : Nat} (hbox : 0 < box) (hstart : 2 ≤ start)
    (hpool : ∀ source ∈ sources, ∀ q ∈ pool source, start ≤ q)
    (hprime : ∀ source ∈ sources, ∀ q ∈ pool source, Nat.Prime q) :
    jointStoppedSourceDensity box marked sources sourceWeight pool
        residueX residueY ≤
      2 * (∑ source ∈ sources, sourceWeight source) *
          (((start : NNReal) - 1)⁻¹) ^ marked +
        jointStoppedSourceBoundary box marked sources sourceWeight pool := by
  classical
  unfold jointStoppedSourceDensity jointStoppedSourceBoundary
  calc
    (∑ source ∈ sources,
        sourceWeight source *
          jointTranslationPhaseDensity box marked (pool source)
            (residueX source) (residueY source)) ≤
      ∑ source ∈ sources,
        sourceWeight source *
          (2 * (((start : NNReal) - 1)⁻¹) ^ marked +
            2 * ((pool source).powersetCard marked).card *
              ((box : NNReal)⁻¹) ^ 2) := by
      apply Finset.sum_le_sum
      intro source hsource
      apply mul_le_mul_left'
      calc
        jointTranslationPhaseDensity box marked (pool source)
            (residueX source) (residueY source) ≤
          2 * finiteDistinctNNActivity squarePrimeActivityNN
                (pool source) marked +
            2 * ((pool source).powersetCard marked).card *
              ((box : NNReal)⁻¹) ^ 2 :=
          jointTranslationPhaseDensity_le_euler_add_boundary
            box marked (pool source) (residueX source) (residueY source)
            hbox (hprime source hsource)
        _ ≤ 2 * (((start : NNReal) - 1)⁻¹) ^ marked +
            2 * ((pool source).powersetCard marked).card *
              ((box : NNReal)⁻¹) ^ 2 := by
          gcongr
          exact finiteDistinctSquarePrimeActivity_le_integer_tail_pow
            hstart (hpool source hsource)
    _ = 2 * (∑ source ∈ sources, sourceWeight source) *
          (((start : NNReal) - 1)⁻¹) ^ marked +
        ∑ source ∈ sources,
          sourceWeight source *
            (2 * ((pool source).powersetCard marked).card *
              ((box : NNReal)⁻¹) ^ 2) := by
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_mul]
      ring

theorem jointStoppedSourceDensity_le_integer_tail_factorial_add_boundary
    (box marked : Nat) (sources : Finset σ)
    (sourceWeight : σ → NNReal) (pool : σ → Finset Nat)
    (residueX residueY : σ → Finset Nat → Nat → Nat)
    {start : Nat} (hbox : 0 < box) (hstart : 2 ≤ start)
    (hpool : ∀ source ∈ sources, ∀ q ∈ pool source, start ≤ q)
    (hprime : ∀ source ∈ sources, ∀ q ∈ pool source, Nat.Prime q) :
    jointStoppedSourceDensity box marked sources sourceWeight pool
        residueX residueY ≤
      2 * (∑ source ∈ sources, sourceWeight source) *
          ((((start : NNReal) - 1)⁻¹) ^ marked /
            (marked.factorial : NNReal)) +
        jointStoppedSourceBoundary box marked sources sourceWeight pool := by
  classical
  unfold jointStoppedSourceDensity jointStoppedSourceBoundary
  calc
    (∑ source ∈ sources,
        sourceWeight source *
          jointTranslationPhaseDensity box marked (pool source)
            (residueX source) (residueY source)) ≤
      ∑ source ∈ sources,
        sourceWeight source *
          (2 * ((((start : NNReal) - 1)⁻¹) ^ marked /
              (marked.factorial : NNReal)) +
            2 * ((pool source).powersetCard marked).card *
              ((box : NNReal)⁻¹) ^ 2) := by
      apply Finset.sum_le_sum
      intro source hsource
      apply mul_le_mul_left'
      exact jointTranslationPhaseDensity_le_integer_tail_factorial_add_boundary
        box marked (pool source) (residueX source) (residueY source)
        hbox hstart (hpool source hsource) (hprime source hsource)
    _ = 2 * (∑ source ∈ sources, sourceWeight source) *
          ((((start : NNReal) - 1)⁻¹) ^ marked /
            (marked.factorial : NNReal)) +
        ∑ source ∈ sources,
          sourceWeight source *
            (2 * ((pool source).powersetCard marked).card *
              ((box : NNReal)⁻¹) ^ 2) := by
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_mul]
      ring

/-- After the finite stopped source family has been fixed and summed, its
complete boundary error tends to zero. -/
theorem jointStoppedSourceBoundary_tendsto_zero
    (marked : Nat) (sources : Finset σ)
    (sourceWeight : σ → NNReal) (pool : σ → Finset Nat) :
    Tendsto
      (fun box : Nat =>
        jointStoppedSourceBoundary box marked sources sourceWeight pool)
      atTop (nhds 0) := by
  unfold jointStoppedSourceBoundary
  simpa only [mul_zero, Finset.sum_const_zero] using
    tendsto_finsetSum sources (fun source _ =>
      (tendsto_const_nhds :
        Tendsto (fun _ : Nat => sourceWeight source) atTop
          (nhds (sourceWeight source))).mul
        (jointTranslationPhaseBoundary_tendsto_zero
          (pool source) marked))

/-- The fixed stopped-prefix lift in its final coefficient form.  Its source
mass is the sum of the positive source weights and is independent of the box. -/
theorem jointStoppedSourceDensity_eventually_lt_integer_tail
    (marked : Nat) (sources : Finset σ)
    (sourceWeight : σ → NNReal) (pool : σ → Finset Nat)
    (residueX residueY : σ → Finset Nat → Nat → Nat)
    {start : Nat} (hstart : 2 ≤ start)
    (hpool : ∀ source ∈ sources, ∀ q ∈ pool source, start ≤ q)
    (hprime : ∀ source ∈ sources, ∀ q ∈ pool source, Nat.Prime q)
    (δ : NNReal) (hδ : 0 < δ) :
    ∀ᶠ box : Nat in atTop,
      jointStoppedSourceDensity box marked sources sourceWeight pool
          residueX residueY <
        2 * (∑ source ∈ sources, sourceWeight source) *
            (((start : NNReal) - 1)⁻¹) ^ marked + δ := by
  have hboundary := jointStoppedSourceBoundary_tendsto_zero
    marked sources sourceWeight pool
  have hboundaryEventually :
      ∀ᶠ box : Nat in atTop,
        jointStoppedSourceBoundary box marked sources sourceWeight pool < δ :=
    (tendsto_order.1 hboundary).2 δ hδ
  filter_upwards [hboundaryEventually, eventually_ge_atTop 1]
      with box hsmall hbox
  exact (jointStoppedSourceDensity_le_integer_tail_add_boundary
    box marked sources sourceWeight pool residueX residueY hbox hstart
      hpool hprime).trans_lt <| by
        simpa [add_comm] using
          add_lt_add_left hsmall
            (2 * (∑ source ∈ sources, sourceWeight source) *
              (((start : NNReal) - 1)⁻¹) ^ marked)

end StoppedSourceSum

end Erdos1212Kernel
