import Erdos1212Kernel.IwaniecCubicSupport
import Erdos1212Kernel.VaughanJacobsthalLargePrimeComparison
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Real.Archimedean

namespace Erdos1212Kernel

noncomputable section

open scoped ArithmeticFunction BigOperators
open Finset Nat

set_option maxHeartbeats 1400000

theorem primeFinsetProduct_squarefree
    (Q : Finset Nat) (hprime : ∀ q ∈ Q, Nat.Prime q) :
    Squarefree (∏ q ∈ Q, q) := by
  refine Nat.squarefree_iff_prime_squarefree.mpr ?_
  intro p hp
  by_contra hsq
  by_cases hpQ : p ∈ Q
  · rw [← Finset.mul_prod_erase (a := p) (h := hpQ),
      mul_dvd_mul_iff_left hp.ne_zero] at hsq
    obtain ⟨q, hqMem, hpDvdQ⟩ :=
      Prime.exists_mem_finset_dvd hp.prime hsq
    rw [Finset.mem_erase] at hqMem
    exact hqMem.1 ((Nat.prime_dvd_prime_iff_eq hp
      (hprime q hqMem.2)).mp hpDvdQ).symm
  · have hpDvdProduct : p ∣ ∏ q ∈ Q, q :=
      (dvd_mul_right p p).trans hsq
    obtain ⟨q, hqMem, hpDvdQ⟩ :=
      Prime.exists_mem_finset_dvd hp.prime hpDvdProduct
    have hpEqQ := (Nat.prime_dvd_prime_iff_eq hp
      (hprime q hqMem)).mp hpDvdQ
    exact hpQ (hpEqQ ▸ hqMem)

def vaughanIntervalNu : ArithmeticFunction Real :=
  (ArithmeticFunction.zeta : ArithmeticFunction Real).pdiv
    ArithmeticFunction.id

theorem vaughanIntervalNu_apply_of_ne_zero {n : Nat} (hn : n ≠ 0) :
    vaughanIntervalNu n = (n : Real)⁻¹ := by
  simp [vaughanIntervalNu, ArithmeticFunction.pdiv_apply,
    ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
    ArithmeticFunction.id_apply, hn]

/-- The exact consecutive interval used in Vaughan's small-state sieve. -/
def vaughanIntervalSieve
    (Q : Finset Nat) (lower length : Nat)
    (hprime : ∀ q ∈ Q, Nat.Prime q) : BoundingSieve where
  support := Finset.Ioc lower (lower + length)
  prodPrimes := ∏ q ∈ Q, q
  prodPrimes_squarefree := primeFinsetProduct_squarefree Q hprime
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := length
  nu := vaughanIntervalNu
  nu_mult := by
    unfold vaughanIntervalNu
    arith_mult
  nu_pos_of_prime := by
    intro p hp _hpDvd
    rw [vaughanIntervalNu_apply_of_ne_zero hp.ne_zero]
    exact inv_pos.mpr (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := by
    intro p hp _hpDvd
    rw [vaughanIntervalNu_apply_of_ne_zero hp.ne_zero]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

theorem card_Ioc_filter_dvd_eq_div_sub
    (d lower upper : Nat) (hlower : lower ≤ upper) :
    ((Finset.Ioc lower upper).filter fun value => d ∣ value).card =
      upper / d - lower / d := by
  have hsets :
      ((Finset.Ioc lower upper).filter fun value => d ∣ value) =
        ((Finset.Ioc 0 upper).filter fun value => d ∣ value) \ 
          ((Finset.Ioc 0 lower).filter fun value => d ∣ value) := by
    ext value
    simp
    omega
  have hsubset :
      ((Finset.Ioc 0 lower).filter fun value => d ∣ value) ⊆
        ((Finset.Ioc 0 upper).filter fun value => d ∣ value) := by
    intro value hvalue
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hvalue ⊢
    exact ⟨⟨hvalue.1.1, hvalue.1.2.trans hlower⟩, hvalue.2⟩
  rw [hsets, Finset.card_sdiff_of_subset hsubset,
    Nat.Ioc_filter_dvd_card_eq_div,
    Nat.Ioc_filter_dvd_card_eq_div]

theorem vaughanIntervalSieve_multSum_eq
    (Q : Finset Nat) (lower length d : Nat)
    (hprime : ∀ q ∈ Q, Nat.Prime q) :
    (vaughanIntervalSieve Q lower length hprime).multSum d =
      (((Finset.Ioc lower (lower + length)).filter fun value =>
        d ∣ value).card : Real) := by
  change (∑ value ∈ Finset.Ioc lower (lower + length),
    if d ∣ value then (1 : Real) else 0) = _
  rw [← Finset.sum_filter, Finset.card_eq_sum_ones]
  norm_cast

theorem vaughanIntervalSieve_rem_eq
    (Q : Finset Nat) (lower length d : Nat)
    (hprime : ∀ q ∈ Q, Nat.Prime q) (hd : d ≠ 0) :
    (vaughanIntervalSieve Q lower length hprime).rem d =
      (((lower + length) / d - lower / d : Nat) : Real) -
        (d : Real)⁻¹ * length := by
  rw [BoundingSieve.rem, vaughanIntervalSieve_multSum_eq,
    card_Ioc_filter_dvd_eq_div_sub d lower (lower + length) (by omega)]
  simp [vaughanIntervalSieve, vaughanIntervalNu_apply_of_ne_zero hd]

theorem vaughanIntervalSieve_abs_rem_le_one
    (Q : Finset Nat) (lower length d : Nat)
    (hprime : ∀ q ∈ Q, Nat.Prime q) (hd : d ≠ 0) :
    |(vaughanIntervalSieve Q lower length hprime).rem d| ≤ 1 := by
  rw [vaughanIntervalSieve_rem_eq Q lower length d hprime hd]
  have hquot : lower / d ≤ (lower + length) / d :=
    Nat.div_le_div_right (by omega)
  rw [Nat.cast_sub hquot]
  have hlowerFloor :
      ((lower / d : Nat) : Real) ≤ (lower : Real) / d :=
    Nat.cast_div_le
  have hlowerCeil :
      (lower : Real) / d < ((lower / d : Nat) : Real) + 1 := by
    have h := Nat.lt_floor_add_one ((lower : Real) / d)
    rw [Nat.floor_div_eq_div] at h
    exact h
  have hupperFloor :
      ((((lower + length) / d : Nat) : Real)) ≤
        ((lower + length : Nat) : Real) / d :=
    Nat.cast_div_le
  have hupperCeil :
      ((lower + length : Nat) : Real) / d <
        (((lower + length) / d : Nat) : Real) + 1 := by
    have h := Nat.lt_floor_add_one (((lower + length : Nat) : Real) / d)
    rw [Nat.floor_div_eq_div] at h
    exact h
  have hsplit :
      ((lower + length : Nat) : Real) / d =
        (lower : Real) / d + (length : Real) / d := by
    push_cast
    ring
  have hinvLength :
      (d : Real)⁻¹ * length = (length : Real) / d := by
    ring
  rw [hinvLength]
  rw [abs_le]
  constructor <;> rw [hsplit] at hupperFloor hupperCeil <;>
    norm_num at * <;> linarith

theorem coprime_primeFinsetProduct_iff
    {Q : Finset Nat} {value : Nat}
    (hprime : ∀ q ∈ Q, Nat.Prime q) :
    Nat.Coprime (∏ q ∈ Q, q) value ↔
      ∀ q ∈ Q, ¬q ∣ value := by
  rw [Nat.coprime_prod_left_iff]
  apply forall_congr'
  intro q
  apply imp_congr_right
  intro hq
  exact (hprime q hq).coprime_iff_not_dvd

theorem vaughanIntervalSieve_siftedSum_eq_avoidingNumbers
    (Q : Finset Nat) (lower length : Nat)
    (hprime : ∀ q ∈ Q, Nat.Prime q) :
    (vaughanIntervalSieve Q lower length hprime).siftedSum =
      (((Finset.Ioc lower (lower + length)).filter fun value =>
        ∀ q ∈ Q, ¬q ∣ value).card : Real) := by
  unfold BoundingSieve.siftedSum
  change (∑ value ∈ Finset.Ioc lower (lower + length),
    if Nat.Coprime (∏ q ∈ Q, q) value then (1 : Real) else 0) = _
  rw [← Finset.sum_filter]
  calc
    (∑ _value ∈
        (Finset.Ioc lower (lower + length)).filter fun value =>
          Nat.Coprime (∏ q ∈ Q, q) value, (1 : Real)) =
        (((Finset.Ioc lower (lower + length)).filter fun value =>
          Nat.Coprime (∏ q ∈ Q, q) value).card : Real) := by simp
    _ = _ := by
      have hsets :
          (Finset.Ioc lower (lower + length)).filter (fun value =>
            Nat.Coprime (∏ q ∈ Q, q) value) =
          (Finset.Ioc lower (lower + length)).filter (fun value =>
            ∀ q ∈ Q, ¬q ∣ value) := by
        ext value
        simp [coprime_primeFinsetProduct_iff hprime]
      rw [hsets]

theorem primeStateAvoidingIndices_card_eq_avoidingNumbers
    (Q : Finset Nat) (lower length : Nat) :
    (primeStateAvoidingIndices Q lower length).card =
      ((Finset.Ioc lower (lower + length)).filter fun value =>
        ∀ q ∈ Q, ¬q ∣ value).card := by
  let candidate := fun index : Nat => lower + 1 + index
  have hinjective : Function.Injective candidate := by
    intro left right heq
    dsimp [candidate] at heq
    omega
  have himage :
      (primeStateAvoidingIndices Q lower length).image candidate =
        (Finset.Ioc lower (lower + length)).filter fun value =>
          ∀ q ∈ Q, ¬q ∣ value := by
    ext value
    constructor
    · intro hvalue
      obtain ⟨index, hindex, rfl⟩ := Finset.mem_image.mp hvalue
      have hindexData := Finset.mem_filter.mp hindex
      have hindexLt : index < length :=
        Finset.mem_range.mp hindexData.1
      apply Finset.mem_filter.mpr
      exact ⟨by
        rw [Finset.mem_Ioc]
        dsimp [candidate]
        omega, hindexData.2⟩
    · intro hvalue
      have hvalueData := Finset.mem_filter.mp hvalue
      have hlowerValue : lower + 1 ≤ value := by
        rw [Finset.mem_Ioc] at hvalueData
        omega
      let index := value - (lower + 1)
      have hcandidate : candidate index = value := by
        dsimp [candidate, index]
        omega
      apply Finset.mem_image.mpr
      refine ⟨index, ?_, hcandidate⟩
      apply Finset.mem_filter.mpr
      constructor
      · rw [Finset.mem_range]
        rw [Finset.mem_Ioc] at hvalueData
        dsimp [index]
        omega
      · intro q hq hdvd
        apply hvalueData.2 q hq
        have hcandEq : lower + 1 + index = value := by
          simpa [candidate] using hcandidate
        rwa [← hcandEq]
  calc
    (primeStateAvoidingIndices Q lower length).card =
        ((primeStateAvoidingIndices Q lower length).image candidate).card :=
      (Finset.card_image_of_injective _ hinjective).symm
    _ = _ := congrArg Finset.card himage

theorem vaughanIntervalSieve_siftedSum_eq_primeStateAvoiding_card
    (Q : Finset Nat) (lower length : Nat)
    (hprime : ∀ q ∈ Q, Nat.Prime q) :
    (vaughanIntervalSieve Q lower length hprime).siftedSum =
      (primeStateAvoidingIndices Q lower length).card := by
  rw [vaughanIntervalSieve_siftedSum_eq_avoidingNumbers,
    primeStateAvoidingIndices_card_eq_avoidingNumbers]

theorem BoundingSieve.iwaniecCubic_errSum_le_divisors_card
    (Q : Finset Nat) (lower length r y : Nat)
    (hprime : ∀ q ∈ Q, Nat.Prime q) :
    (vaughanIntervalSieve Q lower length hprime).errSum
        (iwaniecCubicLowerMoebius r y) ≤
      ((∏ q ∈ Q, q).divisors.card : Real) := by
  unfold BoundingSieve.errSum
  calc
    (∑ d ∈ (∏ q ∈ Q, q).divisors,
        |iwaniecCubicLowerMoebius r y d| *
          |(vaughanIntervalSieve Q lower length hprime).rem d|) ≤
      ∑ _d ∈ (∏ q ∈ Q, q).divisors, (1 : Real) := by
        apply Finset.sum_le_sum
        intro d hdDiv
        have hd : d ≠ 0 := by
          have hproduct : (∏ q ∈ Q, q) ≠ 0 :=
            (primeFinsetProduct_squarefree Q hprime).ne_zero
          intro hd0
          subst d
          apply hproduct
          simpa using (Nat.mem_divisors.mp hdDiv).1
        exact mul_le_one₀
          (abs_iwaniecCubicLowerMoebius_le_one r y d)
          (abs_nonneg _)
          (vaughanIntervalSieve_abs_rem_le_one Q lower length d hprime hd)
    _ = _ := by simp

theorem primeFactor_lt_of_dvd_primeFinsetProduct
    {Q : Finset Nat} {d y : Nat}
    (hprime : ∀ q ∈ Q, Nat.Prime q) (hQlt : ∀ q ∈ Q, q < y)
    (hd : d ∣ ∏ q ∈ Q, q) :
    ∀ p ∈ d.primeFactors, p < y := by
  intro p hpFactor
  have hp := Nat.prime_of_mem_primeFactors hpFactor
  have hpDvdProduct := (Nat.dvd_of_mem_primeFactors hpFactor).trans hd
  obtain ⟨q, hqMem, hpDvdQ⟩ :=
    Prime.exists_mem_finset_dvd hp.prime hpDvdProduct
  have hpEqQ := (Nat.prime_dvd_prime_iff_eq hp
    (hprime q hqMem)).mp hpDvdQ
  simpa [hpEqQ] using hQlt q hqMem

/-- Iwaniec's cubic support cuts the interval-sieve remainder sum down from
all divisors of the state product to fewer than `y` possible moduli. -/
theorem BoundingSieve.iwaniecCubic_errSum_le_level
    (Q : Finset Nat) (lower length r y : Nat)
    (hprime : ∀ q ∈ Q, Nat.Prime q) (hy : 1 < y)
    (hQlt : ∀ q ∈ Q, q < y) :
    (vaughanIntervalSieve Q lower length hprime).errSum
        (iwaniecCubicLowerMoebius r y) ≤ y := by
  unfold BoundingSieve.errSum
  calc
    (∑ d ∈ (∏ q ∈ Q, q).divisors,
        |iwaniecCubicLowerMoebius r y d| *
          |(vaughanIntervalSieve Q lower length hprime).rem d|) ≤
      ∑ d ∈ (∏ q ∈ Q, q).divisors,
        if d < y then (1 : Real) else 0 := by
          apply Finset.sum_le_sum
          intro d hdDiv
          have hdProduct := (Nat.mem_divisors.mp hdDiv).1
          have hd : d ≠ 0 := by
            have hproduct : (∏ q ∈ Q, q) ≠ 0 :=
              (primeFinsetProduct_squarefree Q hprime).ne_zero
            intro hd0
            subst d
            apply hproduct
            simpa using hdProduct
          by_cases hcoeff : iwaniecCubicLowerMoebius r y d = 0
          · simp [hcoeff]
            split <;> norm_num
          · have hdLt : d < y :=
              iwaniecCubicLowerMoebius_ne_zero_imp_lt hy
                (primeFactor_lt_of_dvd_primeFinsetProduct
                  hprime hQlt hdProduct) hcoeff
            rw [if_pos hdLt]
            exact mul_le_one₀
              (abs_iwaniecCubicLowerMoebius_le_one r y d)
              (abs_nonneg _)
              (vaughanIntervalSieve_abs_rem_le_one
                Q lower length d hprime hd)
    _ = (((∏ q ∈ Q, q).divisors.filter fun d => d < y).card : Real) := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ y := by
      have hcard := Finset.card_le_card (by
        intro d hd
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hd).2 :
          ((∏ q ∈ Q, q).divisors.filter fun d => d < y) ⊆ Finset.range y)
      have hcard' :
          ((∏ q ∈ Q, q).divisors.filter fun d => d < y).card ≤ y := by
        simpa using hcard
      exact_mod_cast hcard'

/-- First unconditional quantitative consumer of the literal Iwaniec
coefficients on Vaughan's actual finite prime state. -/
theorem iwaniecCubic_main_sub_divisors_le_primeStateAvoiding_card
    (Q : Finset Nat) (lower length r y : Nat)
    (hprime : ∀ q ∈ Q, Nat.Prime q) (hr : 0 < r) :
    (length : Real) *
          (vaughanIntervalSieve Q lower length hprime).mainSum
            (iwaniecCubicLowerMoebius r y) -
        ((∏ q ∈ Q, q).divisors.card : Real) ≤
      (primeStateAvoidingIndices Q lower length).card := by
  have hlower := BoundingSieve.lowerMoebius_main_sub_error_le_siftedSum
    (s := vaughanIntervalSieve Q lower length hprime)
    (iwaniecCubicLowerMoebius r y)
    (iwaniecCubicLowerMoebius_isLower r y hr)
  have herr := BoundingSieve.iwaniecCubic_errSum_le_divisors_card
    Q lower length r y hprime
  rw [vaughanIntervalSieve_siftedSum_eq_primeStateAvoiding_card] at hlower
  dsimp [vaughanIntervalSieve] at hlower
  calc
    (length : Real) *
          (vaughanIntervalSieve Q lower length hprime).mainSum
            (iwaniecCubicLowerMoebius r y) -
        ((∏ q ∈ Q, q).divisors.card : Real) ≤
      (length : Real) *
          (vaughanIntervalSieve Q lower length hprime).mainSum
            (iwaniecCubicLowerMoebius r y) -
        (vaughanIntervalSieve Q lower length hprime).errSum
          (iwaniecCubicLowerMoebius r y) := sub_le_sub_left herr _
    _ ≤ _ := hlower

/-- Vaughan-scale form: the entire interval remainder is charged by `y`,
not by the exponentially large number of divisors of the state product. -/
theorem iwaniecCubic_main_sub_level_le_primeStateAvoiding_card
    (Q : Finset Nat) (lower length r y : Nat)
    (hprime : ∀ q ∈ Q, Nat.Prime q) (hr : 0 < r)
    (hy : 1 < y) (hQlt : ∀ q ∈ Q, q < y) :
    (length : Real) *
          (vaughanIntervalSieve Q lower length hprime).mainSum
            (iwaniecCubicLowerMoebius r y) - y ≤
      (primeStateAvoidingIndices Q lower length).card := by
  have hlower := BoundingSieve.lowerMoebius_main_sub_error_le_siftedSum
    (s := vaughanIntervalSieve Q lower length hprime)
    (iwaniecCubicLowerMoebius r y)
    (iwaniecCubicLowerMoebius_isLower r y hr)
  have herr := BoundingSieve.iwaniecCubic_errSum_le_level
    Q lower length r y hprime hy hQlt
  rw [vaughanIntervalSieve_siftedSum_eq_primeStateAvoiding_card] at hlower
  dsimp [vaughanIntervalSieve] at hlower
  calc
    (length : Real) *
          (vaughanIntervalSieve Q lower length hprime).mainSum
            (iwaniecCubicLowerMoebius r y) - y ≤
      (length : Real) *
          (vaughanIntervalSieve Q lower length hprime).mainSum
            (iwaniecCubicLowerMoebius r y) -
        (vaughanIntervalSieve Q lower length hprime).errSum
          (iwaniecCubicLowerMoebius r y) := sub_le_sub_left herr _
    _ ≤ _ := hlower

end

end Erdos1212Kernel
