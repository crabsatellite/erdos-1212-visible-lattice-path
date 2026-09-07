import Mathlib

/-!
This file vendors the axiom-free Brun--Titchmarsh kernel from
`Jayyhk/erdos-lean`, commit `32434b3a0859bb1e485fa7e530f38eee73a3debf`,
`problems/696/Erdos696.lean`, lines 1--5818.  The upstream source is
Apache-2.0 licensed and preserves its individual copyright notices below.

Only the self-contained Selberg-sieve/Mertens/AP segment is retained; the
later Erdos 696 development and its unrelated analytic axiom are not present.
-/

set_option autoImplicit true

namespace Erdos696

-- === Inlined from SelbergSieve4.Tactic.AesopDiv ===
/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

/-!
# LeanPool.SelbergSieve4.Tactic.AesopDiv
-/

namespace LPSieve
open Finset

/-- Wrapper predicate for divisibility. -/
protected def MyDvd (a b : ℕ) : Prop := a ∣ b
open LPSieve (MyDvd)

@[simp]
theorem myDvd_iff (a b : ℕ) : MyDvd a b ↔ a ∣ b := by
  exact Iff.rfl

theorem dvd_of_myDvd (a b : ℕ) : MyDvd a b → a ∣ b := (myDvd_iff a b).mp

theorem myDvd_of_dvd (a b : ℕ) : a ∣ b → MyDvd a b := (myDvd_iff a b).mpr

theorem myDvd_trans {a b c : ℕ} : MyDvd a b → MyDvd b c → MyDvd a c := by
  intro hab hbc
  exact (myDvd_iff a c).mpr (Nat.dvd_trans ((myDvd_iff a b).mp hab) ((myDvd_iff b c).mp hbc))

theorem myDvd_of_mem_divisors {a b : ℕ} : a ∈ b.divisors → MyDvd a b := by
  rw [myDvd_iff]; exact Nat.dvd_of_mem_divisors

theorem myDvd_of_mem_primeFactors {a b : ℕ} : a ∈ b.primeFactors → MyDvd a b := by
  rw [myDvd_iff]; exact Nat.dvd_of_mem_primeFactors

theorem eq_zero_of_zero_myDvd (a : ℕ) : MyDvd 0 a → a = 0 := by
  intro h
  exact eq_zero_of_zero_dvd ((myDvd_iff 0 a).mp h)

theorem zero_mem_divisors (a : ℕ) (h : 0 ∈ a.divisors) : False := by simp at h

theorem mem_zero_divisors (a : ℕ) (h : a ∈ Nat.divisors 0) : False := by simp at h

theorem zero_lt_zero (h : 0 < 0) : False := by linarith

theorem test {n m : ℕ} : n ∣ m ∧ m ≠ 0 → n ∈ m.divisors := Nat.mem_divisors.mpr

theorem dvd_of_gcd_dvd_left (a b c : ℕ) (h : MyDvd c (a.gcd b)) : MyDvd c a :=
  myDvd_trans h (myDvd_of_dvd _ _ <| Nat.gcd_dvd_left a b)

theorem dvd_of_gcd_dvd_right (a b c : ℕ) (h : MyDvd c (a.gcd b)) : MyDvd c b :=
  myDvd_trans h (myDvd_of_dvd _ _ <| Nat.gcd_dvd_right a b)

theorem gcd_dvd_of_dvd_left (a b c : ℕ) (h : MyDvd a c) : MyDvd (a.gcd b) c :=
  myDvd_trans (myDvd_of_dvd _ _ <| Nat.gcd_dvd_left a b) h

theorem gcd_dvd_of_dvd_right (a b c : ℕ) (h : MyDvd b c) : MyDvd (a.gcd b) c :=
  myDvd_trans (myDvd_of_dvd _ _ <| Nat.gcd_dvd_right a b) h

theorem gcd_myDvd_left (a b : ℕ) : MyDvd (a.gcd b) a :=
  myDvd_of_dvd _ _ (gcd_dvd_left a b)

theorem gcd_myDvd_right (a b : ℕ) : MyDvd (a.gcd b) b :=
  myDvd_of_dvd _ _ (gcd_dvd_right a b)

theorem gcd_eq_zero_left (a b : ℕ) (h : a.gcd b = 0) : a = 0 := by
  rw [Nat.gcd_eq_zero_iff] at h; exact h.1
theorem gcd_eq_zero_right (a b : ℕ) (h : a.gcd b = 0) : b = 0 := by
  rw [Nat.gcd_eq_zero_iff] at h; exact h.2

theorem dvd_of_lcm_dvd_left (a b c : ℕ) (h : MyDvd (a.lcm b) c) : MyDvd a c :=
  myDvd_trans (myDvd_of_dvd _ _ <| Nat.dvd_lcm_left a b) h

theorem dvd_of_lcm_dvd_right (a b c : ℕ) (h : MyDvd (a.lcm b) c) : MyDvd b c :=
  myDvd_trans (myDvd_of_dvd _ _ <| Nat.dvd_lcm_right a b) h

theorem dvd_lcm_of_dvd_left (a b c : ℕ) (h : MyDvd c a) : MyDvd c (a.lcm b) :=
  myDvd_trans h (myDvd_of_dvd _ _ <| Nat.dvd_lcm_left a b)

theorem dvd_lcm_of_dvd_right (a b c : ℕ) (h : MyDvd c b) : MyDvd c (a.lcm b) :=
  myDvd_trans h (myDvd_of_dvd _ _ <| Nat.dvd_lcm_right a b)

theorem myDvd_lcm_left (a b : ℕ) : MyDvd a (a.lcm b) :=
  myDvd_of_dvd _ _ (dvd_lcm_left a b)

theorem myDvd_lcm_right (a b : ℕ) : MyDvd b (a.lcm b) :=
  myDvd_of_dvd _ _ (dvd_lcm_right a b)

theorem lcm_eq_zero_left (a b : ℕ) (h : a.lcm b = 0) : a = 0 ∨ b = 0 := by
  rw [←lcm_eq_nat_lcm, _root_.lcm_eq_zero_iff] at h; exact h

theorem squarefree_of_myDvd (a b : ℕ) (hb : Squarefree b) (h : MyDvd a b) :
    Squarefree a := by
  rw[myDvd_iff] at h
  exact Squarefree.squarefree_of_dvd h hb

/-- Run `aesop` with the divisibility lemma pack inlined and simp disabled. -/
macro (name := aesopDiv) "aesopDiv" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop $c*
    (config := { enableSimp := false })
    (add safe [LPSieve.dvd_of_myDvd, LPSieve.test, LPSieve.gcd_dvd_of_dvd_left,
               LPSieve.gcd_dvd_of_dvd_right, LPSieve.gcd_myDvd_left, LPSieve.gcd_myDvd_right,
               LPSieve.dvd_lcm_of_dvd_left, LPSieve.dvd_lcm_of_dvd_right,
               LPSieve.myDvd_lcm_left, LPSieve.myDvd_lcm_right, Nat.pos_of_ne_zero])
    (add safe destruct [LPSieve.myDvd_of_dvd])
    (add safe forward [LPSieve.myDvd_trans, LPSieve.myDvd_of_mem_divisors,
                       LPSieve.myDvd_of_mem_primeFactors, not_squarefree_zero,
                       LPSieve.eq_zero_of_zero_myDvd, LPSieve.zero_mem_divisors,
                       LPSieve.mem_zero_divisors, LPSieve.zero_lt_zero,
                       LPSieve.dvd_of_gcd_dvd_left, LPSieve.dvd_of_gcd_dvd_right,
                       LPSieve.gcd_eq_zero_left, LPSieve.gcd_eq_zero_right,
                       LPSieve.dvd_of_lcm_dvd_left, LPSieve.dvd_of_lcm_dvd_right,
                       LPSieve.lcm_eq_zero_left, Squarefree.squarefree_of_dvd,
                       LPSieve.squarefree_of_myDvd,
                       $(Lean.mkIdent `LPSieve.prodPrimes_ne_zero):ident,
                       $(Lean.mkIdent `LPSieve.prodPrimes_squarefree):ident]))

/-- `aesop?` companion variant of `aesopDiv`. -/
macro (name := aesopDiv?) "aesopDiv?" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop? $c*
    (config := { enableSimp := false })
    (add safe [LPSieve.dvd_of_myDvd, LPSieve.test, LPSieve.gcd_dvd_of_dvd_left,
               LPSieve.gcd_dvd_of_dvd_right, LPSieve.gcd_myDvd_left, LPSieve.gcd_myDvd_right,
               LPSieve.dvd_lcm_of_dvd_left, LPSieve.dvd_lcm_of_dvd_right,
               LPSieve.myDvd_lcm_left, LPSieve.myDvd_lcm_right, Nat.pos_of_ne_zero])
    (add safe destruct [LPSieve.myDvd_of_dvd])
    (add safe forward [LPSieve.myDvd_trans, LPSieve.myDvd_of_mem_divisors,
                       LPSieve.myDvd_of_mem_primeFactors, not_squarefree_zero,
                       LPSieve.eq_zero_of_zero_myDvd, LPSieve.zero_mem_divisors,
                       LPSieve.mem_zero_divisors, LPSieve.zero_lt_zero,
                       LPSieve.dvd_of_gcd_dvd_left, LPSieve.dvd_of_gcd_dvd_right,
                       LPSieve.gcd_eq_zero_left, LPSieve.gcd_eq_zero_right,
                       LPSieve.dvd_of_lcm_dvd_left, LPSieve.dvd_of_lcm_dvd_right,
                       LPSieve.lcm_eq_zero_left, Squarefree.squarefree_of_dvd,
                       LPSieve.squarefree_of_myDvd,
                       $(Lean.mkIdent `LPSieve.prodPrimes_ne_zero):ident,
                       $(Lean.mkIdent `LPSieve.prodPrimes_squarefree):ident]))

end LPSieve



-- === Inlined from SelbergSieve4.ForMathlib.Basic ===
/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
/-!
# LeanPool.SelbergSieve4.ForMathlib.Basic
-/

namespace Aux

open BigOperators ArithmeticFunction
/- Lemmas in this file are singled out as suitable for addition to Mathlib with minor
modifications. -/

variable {R : Type*}

theorem mult_lcm_eq_of_ne_zero [CommGroupWithZero R] (f : ArithmeticFunction R)
    (h_mult : f.IsMultiplicative) (x y : ℕ)
    (hf : f (x.gcd y) ≠ 0) :
    f (x.lcm y) = f x * f y / f (x.gcd y) := by
  rw [←h_mult.lcm_apply_mul_gcd_apply]
  field_simp

theorem prod_factors_of_mult (f : ArithmeticFunction ℝ)
    (h_mult : ArithmeticFunction.IsMultiplicative f) {l : ℕ} (hl : Squarefree l) :
    ∏ a ∈ l.primeFactors, f a = f l := by
  rw [←IsMultiplicative.map_prod_of_subset_primeFactors h_mult l _ Finset.Subset.rfl,
    Nat.prod_primeFactors_of_squarefree hl]

end Aux



-- === Inlined from SelbergSieve4.ForMathlib.ProdsAntidiagonal ===
/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/


/-!
# LeanPool.SelbergSieve4.ForMathlib.ProdsAntidiagonal
-/

section LPSieveProdsAntidiagonal
open scoped ArithmeticFunction.omega

/-- Alias for the multiplicative antidiagonal indexed by `Fin d`. -/
abbrev _root_.Nat.finMulAntidiagonal (d n : ℕ) : Finset (Fin d → ℕ) :=
  Nat.finMulAntidiag d n

/-- Membership in the multiplicative antidiagonal. -/
theorem _root_.Nat.mem_finMulAntidiagonal {d n : ℕ} {f : Fin d → ℕ} :
    f ∈ Nat.finMulAntidiagonal d n ↔ ∏ i, f i = n ∧ n ≠ 0 :=
  Nat.mem_finMulAntidiag

theorem _root_.Nat.finMulAntidiagonal_univ_eq {d m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    Nat.finMulAntidiagonal d m =
      (Fintype.piFinset fun _ : Fin d => n.divisors).filter (fun f => ∏ i, f i = m) :=
  Nat.finMulAntidiag_eq_piFinset_divisors_filter hmn hn

theorem _root_.Nat.card_finMulAntidiagonal {d n : ℕ} (hn : Squarefree n) :
    (Nat.finMulAntidiagonal d n).card = d ^ ω n := by
  simpa [Nat.finMulAntidiagonal] using Nat.card_finMulAntidiag_of_squarefree (d := d) hn

end LPSieveProdsAntidiagonal



-- === Inlined from SelbergSieve4.AuxResults ===
/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

/-!
# LeanPool.SelbergSieve4.AuxResults
-/

--import LPSelbergSieve.AesopDiv
noncomputable section

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)
open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius ArithmeticFunction.omega

open Nat ArithmeticFunction Finset Tactic.Interactive

namespace Aux

theorem sum_over_dvd_ite {α : Type _} [Ring α] {P : ℕ} (hP : P ≠ 0) {n : ℕ} (hn : n ∣ P)
    {f : ℕ → α} : ∑ d ∈ n.divisors, f d = ∑ d ∈ P.divisors, if d ∣ n then f d else 0 :=
  by
  rw [←Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hP hn]

theorem sum_intro {α M : Type _} [AddCommMonoid M] [DecidableEq α] (s : Finset α)
    {f : α → M} (d : α)
     (hd : d ∈ s) :
    f d = ∑ k ∈ s, if k = d then f k else 0 := by
  trans (∑ k ∈ s, if k = d then f d else 0)
  · rw [sum_eq_single_of_mem d hd]
    · rw [if_pos rfl]
    · intro _ _ h
      rw [if_neg h]
  apply sum_congr rfl; intro k _; apply if_ctx_congr Iff.rfl _ (fun _ => rfl)
  intro h; rw [h]

theorem ite_sum_zero {p : Prop} [Decidable p] (s : Finset ℕ) (f : ℕ → ℝ) :
    (if p then (∑ x ∈ s, f x) else 0) = ∑ x ∈ s, if p then f x else 0 := by
  split_ifs <;> simp

theorem conv_lambda_sq_larger_sum (f : ℕ → ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ d ∈ n.divisors,
        ∑ d1 ∈ d.divisors,
          ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0) =
      ∑ d ∈ n.divisors,
        ∑ d1 ∈ n.divisors,
          ∑ d2 ∈ n.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0 := by
  apply sum_congr rfl; intro d hd
  rw [mem_divisors] at hd
  simp_rw [←Nat.divisors_filter_dvd_of_dvd hd.2 hd.1, sum_filter, ←ite_and, ite_sum_zero, ←ite_and]
  congr with d1
  congr with d2
  congr
  rw [eq_iff_iff]
  refine ⟨fun ⟨_, _, h⟩ ↦ h, ?_⟩
  rintro rfl
  exact ⟨Nat.dvd_lcm_left d1 d2, Nat.dvd_lcm_right d1 d2, rfl⟩

-- theorem dvd_iff_mul_of_dvds {P : ℕ} (k d l m : ℕ) (hd : d ∈ P.divisors) :
--     k = d / l ∧ l ∣ d ∧ d ∣ m ↔ d = k * l ∧ d ∣ m := by
--   constructor
--   · intro ⟨hk_eq, hld, hdm⟩
--     exact ⟨Nat.eq_mul_of_div_eq_left hld hk_eq.symm, hdm⟩
--   · intro ⟨hd_eq, hdm⟩
--     refine ⟨?_, ?_, hdm⟩
--     · apply (Nat.div_eq_of_eq_mul_left _ hd_eq).symm
--       apply Nat.pos_of_ne_zero
--       apply right_ne_zero_of_mul (a:=k)
--       rw [←hd_eq]
--       apply _root_.ne_of_gt
--       apply Nat.pos_of_mem_divisors hd
--     · use k; rw [hd_eq, mul_comm]

theorem moebius_inv_dvd_lower_bound (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then (μ d:ℤ) else 0) = if l = m then (μ l:ℤ) else 0 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero <| Squarefree.ne_zero hm
  revert hm
  revert m
  apply (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on {n | Squarefree n}
    (fun _ _ => Squarefree.squarefree_of_dvd)).mpr
  intro m hm_pos hm
  rw [sum_divisorsAntidiagonal' (f:= fun x y => μ x • if l=y then μ l else 0)]--
  by_cases hl : l ∣ m
  · rw [if_pos hl, sum_eq_single l]
    · have hmul : m / l * l = m := Nat.div_mul_cancel hl
      rw [if_pos rfl, smul_eq_mul, ←isMultiplicative_moebius.map_mul_of_coprime, hmul]
      apply coprime_of_squarefree_mul; rw [hmul]; exact hm
    · intro d _ hdl; rw[if_neg <| hdl.symm, smul_zero]
    · intro h; rw[mem_divisors] at h; exfalso; exact h ⟨hl, (Nat.ne_of_lt hm_pos).symm⟩
  · rw [if_neg hl, sum_eq_zero]; intro d hd
    rw [if_neg, smul_zero]
    by_contra h; rw [←h] at hd; exact hl (dvd_of_mem_divisors hd)

theorem moebius_inv_dvd_lower_bound' {P : ℕ} (hP : Squarefree P) (l m : ℕ)
    (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then μ d else 0) = if l = m then μ l else 0 := by
  rw [←moebius_inv_dvd_lower_bound _ _ (Squarefree.squarefree_of_dvd hm hP),
    sum_over_dvd_ite hP.ne_zero hm]
  simp_rw[ite_and, ←sum_filter, filter_comm]

theorem moebius_inv_dvd_lower_bound_real {P : ℕ} (hP : Squarefree P) (l m : ℕ)
    (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) =
      if l = m then (μ l : ℝ) else 0 := by
  norm_cast
  apply moebius_inv_dvd_lower_bound' hP l m hm

theorem gcd_dvd_mul (m n : ℕ) : m.gcd n ∣ m * n := by
  calc
    m.gcd n ∣ m := Nat.gcd_dvd_left m n
    _ ∣ m * n := ⟨n, rfl⟩

theorem multiplicative_zero_of_zero_dvd (f : ArithmeticFunction ℝ)
    (h_mult : IsMultiplicative f) {m n : ℕ}
    (h_sq : Squarefree n) (hmn : m ∣ n) (h_zero : f m = 0) : f n = 0 := by
  rcases hmn with ⟨k, rfl⟩
  simp only [MulZeroClass.zero_mul, h_mult.map_mul_of_coprime
    (coprime_of_squarefree_mul h_sq), h_zero]

theorem primeDivisors_nonempty (n : ℕ) (hn : 2 ≤ n) : n.primeFactors.Nonempty := by
  unfold Finset.Nonempty
  simp_rw[Nat.mem_primeFactors_of_ne_zero (by positivity)]
  apply Nat.exists_prime_and_dvd (by linarith)

theorem div_mult_of_dvd_squarefree (f : ArithmeticFunction ℝ) (h_mult : IsMultiplicative f)
    (l d : ℕ) (hdl : d ∣ l)
    (hl : Squarefree l) (hd : f d ≠ 0) : f l / f d = f (l / d) := by
  apply div_eq_of_eq_mul hd
  rw [← h_mult.right, Nat.div_mul_cancel hdl]
  apply coprime_of_squarefree_mul
  convert hl
  exact Nat.div_mul_cancel hdl

theorem inv_sub_antitoneOn_gt {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (c : R) :
    AntitoneOn (fun x : R ↦ (x-c)⁻¹) (Set.Ioi c) := by
  refine antitoneOn_iff_forall_lt.mpr ?_
  intro a ha b hb hab
  rw [Set.mem_Ioi] at ha hb
  gcongr

theorem inv_sub_antitoneOn_Icc {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b c : R) (ha : c < a) :
    AntitoneOn (fun x ↦ (x-c)⁻¹) (Set.Icc a b) := by
  by_cases hab : a ≤ b
  · exact inv_sub_antitoneOn_gt c |>.mono <| (Set.Icc_subset_Ioi_iff hab).mpr ha
  · simp [hab, Set.Subsingleton.antitoneOn]

theorem inv_antitoneOn_pos {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    AntitoneOn (fun x:R ↦ x⁻¹) (Set.Ioi 0) := by
  convert inv_sub_antitoneOn_gt (R:=R) 0; ring

theorem inv_antitoneOn_Icc {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b : R) (ha : 0 < a) :
    AntitoneOn (fun x ↦ x⁻¹) (Set.Icc a b) := by
  convert inv_sub_antitoneOn_Icc a b 0 ha; ring

theorem log_add_one_le_sum_inv (n : ℕ) :
    Real.log ↑(n+1) ≤ ∑ d ∈ Finset.Icc 1 n, (d:ℝ)⁻¹ := by
  calc _ = ∫ x in (1)..↑(n+1), x⁻¹ := ?_
       _ = ∫ x in (1:ℕ)..↑(n+1), x⁻¹ := ?_
       _ ≤ _ := ?_
  · rw[integral_inv (by simp[(show ¬ (1:ℝ) ≤ 0 by norm_num)] )]; congr; ring
  · congr; norm_num
  · apply AntitoneOn.integral_le_sum_Ico (by norm_num)
    apply inv_antitoneOn_Icc
    norm_num

theorem log_le_sum_inv (y : ℝ) (hy : 1 ≤ y) :
    Real.log y ≤ ∑ d ∈ Finset.Icc 1 (⌊y⌋₊), (d:ℝ)⁻¹ := by
  calc _ ≤ Real.log ↑(Nat.floor y + 1) := ?_
       _ ≤ _ := ?_
  · gcongr
    apply (le_ceil y).trans
    norm_cast
    exact ceil_le_floor_add_one y
  · apply log_add_one_le_sum_inv

theorem sum_inv_le_log (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ Finset.Icc 1 n, (d : ℝ)⁻¹ ≤ 1 + Real.log ↑n :=
  by
  rw [← Finset.sum_erase_add (Icc 1 n) _ (by simp [hn] : 1 ∈ Icc 1 n), add_comm]
  gcongr
  · norm_num
  simp only [Icc_erase_left]
  calc
    ∑ d ∈ Ico 2 (n + 1), (d : ℝ)⁻¹ = ∑ d ∈ Ico 2 (n + 1), (↑(d + 1) - 1)⁻¹ := ?_
    _ ≤ ∫ x in (2).. ↑(n + 1), (x - 1)⁻¹  := ?_
    _ = Real.log ↑n := ?_
  · congr; norm_num;
  · apply @AntitoneOn.sum_le_integral_Ico 2 (n + 1) fun x : ℝ => (x - 1)⁻¹
    · linarith [hn]
    apply inv_sub_antitoneOn_Icc; norm_num
  rw [intervalIntegral.integral_comp_sub_right _ 1, integral_inv]
  · norm_num
  norm_num; simp[hn, show (0:ℝ) < 1 by norm_num]

theorem sum_inv_le_log_real (y : ℝ) (hy : 1 ≤ y) :
    ∑ d ∈ Finset.Icc 1 (⌊y⌋₊), (d:ℝ)⁻¹ ≤ 1 + Real.log y := by
  trans (1 + Real.log (⌊y⌋₊))
  · apply sum_inv_le_log (⌊y⌋₊)
    apply le_floor; norm_cast
  gcongr
  · norm_cast; apply Nat.lt_of_succ_le; apply le_floor; norm_cast
  · apply floor_le; linarith

theorem natLe_prod {f : ι → ℕ} {s : Finset ι} {i : ι} (hi : i ∈ s)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    f i ≤ ∏ j ∈ s, f j := by
  classical
  rw [←prod_erase_mul (a:=i) (h:= hi)]
  exact Nat.le_mul_of_pos_left _ <|
    prod_pos fun j hj => Nat.pos_of_ne_zero (hf j (mem_of_mem_erase hj))


-- Lemma 3.1 in Heath-Brown's notes
theorem sum_pow_cardDistinctFactors_div_self_le_log_pow {P k : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d ∈ P.divisors, if d ≤ x then (k:ℝ) ^ (ω d) / (d : ℝ) else (0 : ℝ))
    ≤ (1 + Real.log x) ^ k := by
  have hx_pos : 0 < x := by
    linarith
  calc
    _ = ∑ d ∈ P.divisors,
          ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
            if ∏ i, a i = d ∧ d ∣ P then if ↑d ≤ x then (d : ℝ)⁻¹ else 0 else 0 := ?_
    _ = ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          if ∏ i, a i ∣ P then if ↑(∏ i, a i) ≤ x then ∏ i, (a i : ℝ)⁻¹ else 0 else 0 := ?_
    _ ≤ ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          if ↑(∏ i, a i) ≤ x then ∏ i, (a i : ℝ)⁻¹ else 0 := ?_ -- do we need this one?
    _ ≤ ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          ∏ i, if ↑(a i) ≤ x then (a i : ℝ)⁻¹ else 0 := ?_
    _ = ∏ _i : Fin k, ∑ d ∈ P.divisors, if ↑d ≤ x then (d : ℝ)⁻¹ else 0 := by rw [prod_univ_sum]
    _ = (∑ d ∈ P.divisors, if ↑d ≤ x then (d : ℝ)⁻¹ else 0) ^ k := by
      rw [prod_const, Finset.card_fin]
    _ ≤ (1 + Real.log x) ^ k := ?_
  · apply sum_congr rfl; intro d hd
    rw [mem_divisors] at hd
    simp_rw [ite_and];
    rw [←sum_filter, Finset.sum_const, ←finMulAntidiagonal_univ_eq hd.1 hd.2,
      card_finMulAntidiagonal <| hP.squarefree_of_dvd hd.1, if_pos hd.1]
    simp only [div_eq_mul_inv, nsmul_eq_mul, cast_pow, mul_ite, mul_zero]
  · rw [sum_comm]; apply sum_congr rfl; intro a _; rw [sum_eq_single (∏ i, a i)]
    · apply if_ctx_congr _ _ (fun _ => rfl)
      · rw [Iff.comm, iff_and_self]
        exact fun _ => rfl
      intro; rw [cast_prod, ← prod_inv_distrib]
    · exact fun d _ hd_ne ↦ if_neg fun h => hd_ne.symm h.1
    · exact fun h ↦ if_neg fun h' => h (mem_divisors.mpr ⟨h'.2, hP.ne_zero⟩)
  · apply sum_le_sum; intro a _
    by_cases h : (∏ i, a i ∣ P)
    · rw [if_pos h]
    rw [if_neg h]
    split_ifs with h'
    · apply prod_nonneg; intro i _; norm_num
    · rfl
  · apply sum_le_sum; intro a ha
    split_ifs with h
    · apply le_of_eq
      apply prod_congr rfl
      intro i hi
      have hai_le_x : ↑(a i) ≤ x := by
        refine le_trans ?_ h
        norm_cast
        rw [←prod_erase_mul (a:=i) (h:= hi)]
        apply Nat.le_mul_of_pos_left
        rw [Fintype.mem_piFinset] at ha
        apply prod_pos
        intro j hj
        apply pos_of_mem_divisors (ha j)
      rw [if_pos hai_le_x]
    · apply prod_nonneg; intro j _
      split_ifs
      · norm_num
      · rfl
  · rw [←sum_filter]
    gcongr
    trans (∑ d ∈ Icc 1 (floor x), (d:ℝ)⁻¹)
    · apply sum_le_sum_of_subset_of_nonneg
      · intro d
        rw[mem_filter, mem_Icc]
        intro hd
        constructor
        · rw [Nat.succ_le_iff]
          exact pos_of_mem_divisors hd.1
        · rw [le_floor_iff]
          · exact hd.2
          · exact le_of_lt hx_pos
      · norm_num
    apply sum_inv_le_log_real
    linarith

theorem sum_pow_cardDistinctFactors_le_self_mul_log_pow {P h : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d ∈ P.divisors, if ↑d ≤ x then (h : ℝ) ^ ω d else (0 : ℝ)) ≤ x * (1 + Real.log x) ^ h := by
  trans (∑ d ∈ P.divisors, x * if ↑d ≤ x then (h : ℝ) ^ ω d / d else (0 : ℝ))
  · simp_rw [mul_ite, mul_zero, ←sum_filter]
    gcongr with i hi
    rw [div_eq_mul_inv, mul_comm _ (i:ℝ)⁻¹, ←mul_assoc]
    trans (1*(h:ℝ)^ω i)
    · rw [one_mul]
    gcongr
    rw [mem_filter] at hi
    rw [←div_eq_mul_inv]
    apply one_le_div (by norm_cast; apply Nat.pos_of_mem_divisors hi.1) |>.mpr hi.2
  rw [←mul_sum];
  gcongr
  apply sum_pow_cardDistinctFactors_div_self_le_log_pow x hx hP


end Aux

end -- close `noncomputable section` opened in AuxResults



-- === Inlined from SelbergSieve4.UpperBoundSieve ===
/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

/-!
# LeanPool.SelbergSieve4.UpperBoundSieve
-/

section LPSieveUpperBound
open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius ArithmeticFunction.omega

namespace LPSieve

/-- A real-valued divisor weight majorizing the delta function at `1`. -/
def UpperMoebius (μ_plus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, (if n=1 then 1 else 0) ≤ ∑ d ∈ n.divisors, μ_plus d

/-- Upper-bound sieve weights with their majorization property. -/
structure UpperBoundSieve where mk ::
  /-- Upper-bound Moebius weight. -/
  μPlus : ℕ → ℝ
  hμPlus : UpperMoebius μPlus

instance ubToμPlus : CoeFun UpperBoundSieve fun _ => ℕ → ℝ where coe ub := ub.μPlus

/-- A real-valued divisor weight minorizing the delta function at `1`. -/
def LowerMoebius (μMinus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, ∑ d ∈ n.divisors, μMinus d ≤ (if n=1 then 1 else 0)

/-- Lower-bound sieve weights with their minorization property. -/
structure LowerBoundSieve where mk ::
  /-- Lower-bound Moebius weight. -/
  μMinus : ℕ → ℝ
  hμMinus : LowerMoebius μMinus

instance lbToμMinus : CoeFun LowerBoundSieve fun _ => ℕ → ℝ where coe lb := lb.μMinus

end LPSieve

end LPSieveUpperBound



-- === Inlined from SelbergSieve4.SieveLemmas ===
/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

/-!
# LeanPool.SelbergSieve4.SieveLemmas
-/

noncomputable section

open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius ArithmeticFunction.omega

open Finset Real Nat Aux

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-- Data for a finite weighted sieve problem. -/
structure LPSieve where mk ::
  /-- Finite support of integers being sifted. -/
  support : Finset ℕ
  /-- Product of the primes used by the sieve. -/
  prodPrimes : ℕ
  prodPrimes_squarefree : Squarefree prodPrimes
  /-- Nonnegative weights on the support. -/
  weights : ℕ → ℝ
  weights_nonneg : ∀ n : ℕ, 0 ≤ weights n
  /-- Main term for the weighted support. -/
  totalMass : ℝ
  /-- Local density arithmetic function. -/
  nu : ArithmeticFunction ℝ
  nu_mult : nu.IsMultiplicative
  nu_pos_of_prime : ∀ p : ℕ, p.Prime → p ∣ prodPrimes → 0 < nu p
  nu_lt_one_of_prime : ∀ p : ℕ, p.Prime → p ∣ prodPrimes → nu p < 1

attribute [arith_mult] LPSieve.nu_mult

namespace LPSieve

variable (s : LPSieve)
local notation3 "ν" => LPSieve.nu s
local notation3 "P" => LPSieve.prodPrimes s
local notation3 "a" => LPSieve.weights s
local notation3 "X" => LPSieve.totalMass s
local notation3 "A" => LPSieve.support s

/-- Weighted count of support elements divisible by `d`. -/
@[simp]
def multSum (d : ℕ) : ℝ :=
  ∑ n ∈ A, if d ∣ n then a n else 0

local notation3 "𝒜" => LPSieve.multSum s

-- A_d = ν (d)/d X + R_d
/-- Remainder term after subtracting the expected main term from `multSum`. -/
@[simp]
def rem (d : ℕ) : ℝ :=
  𝒜 d - ν d * X

local notation3 "R" => LPSieve.rem s

/-- Weighted count of support elements coprime to the sieve modulus. -/
def siftedSum : ℝ :=
  ∑ d ∈ A, if Coprime P d then a d else 0

open scoped ArithmeticFunction
/-- Selberg local factor product used in the simple upper-bound sieve. -/
def selbergTerms : ArithmeticFunction ℝ :=
  s.nu.pmul (.prodPrimeFactors fun p =>  1 / (1 - ν p))

local notation3 "g" => LPSieve.selbergTerms s

/-- Expands `selbergTerms` as a product over the prime factors of `d`. -/
theorem selbergTerms_apply (d : ℕ) :
    g d = ν d * ∏ p ∈ d.primeFactors, 1/(1 - ν p) := by
  unfold selbergTerms
  by_cases h : d=0
  · rw [h]; simp
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.prodPrimeFactors_apply h]


/-- Main contribution of an upper-bound sieve weight. -/
def mainSum (μPlus : ℕ → ℝ) : ℝ :=
  ∑ d ∈ divisors P, μPlus d * ν d

/-- Error contribution of an upper-bound sieve weight. -/
def errSum (μPlus : ℕ → ℝ) : ℝ :=
  ∑ d ∈ divisors P, |μPlus d| * |R d|

section SieveLemmas

theorem prodPrimes_ne_zero : P ≠ 0 :=
  Squarefree.ne_zero s.prodPrimes_squarefree

theorem squarefree_of_dvd_prodPrimes {d : ℕ} (hd : d ∣ P) : Squarefree d :=
  Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree

theorem squarefree_of_mem_divisors_prodPrimes {d : ℕ} (hd : d ∈ divisors P) : Squarefree d := by
  simp only [Nat.mem_divisors] at hd
  exact Squarefree.squarefree_of_dvd hd.left s.prodPrimes_squarefree

theorem nu_pos_of_dvd_prodPrimes {d : ℕ} (hd : d ∣ P) : 0 < ν d := by
  calc
    0 < ∏ p ∈ d.primeFactors, ν p := by
      apply prod_pos
      intro p hpd
      have hp_prime : p.Prime := by exact prime_of_mem_primeFactors hpd
      have hp_dvd : p ∣ P := (dvd_of_mem_primeFactors hpd).trans hd
      exact s.nu_pos_of_prime p hp_prime hp_dvd
    _ = ν d := prod_factors_of_mult ν s.nu_mult
      (Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree)

theorem nu_ne_zero {d : ℕ} (hd : d ∣ P) : ν d ≠ 0 := by
  apply _root_.ne_of_gt
  exact nu_pos_of_dvd_prodPrimes s hd

theorem nu_ne_zero_of_mem_divisors_prodPrimes {d : ℕ} (hd : d ∈ divisors P) : ν d ≠ 0 := by
  apply _root_.ne_of_gt
  rw [mem_divisors] at hd
  apply s.nu_pos_of_dvd_prodPrimes hd.left

theorem multSum_eq_main_err (d : ℕ) : s.multSum d = ν d * X + R d := by
  dsimp [rem]
  ring

/-- Kronecker delta at `1`, valued in the reals. -/
def delta (n : ℕ) : ℝ := if n=1 then 1 else 0

local notation "δ" => delta

theorem siftedSum_as_delta : s.siftedSum = ∑ d ∈ s.support, a d * δ (Nat.gcd P d) :=
  by
  dsimp only [siftedSum]
  apply sum_congr rfl
  intro d _
  dsimp only [Nat.Coprime, delta] at *
  rw [mul_ite_zero]
  exact if_congr Iff.rfl (symm <| mul_one _) rfl

-- Unused ?
theorem nu_lt_self_of_dvd_prodPrimes : ∀ d : ℕ, d ∣ P → d ≠ 1 → ν d < 1 := by
  intro d hdP hd_ne_one
  have hd_sq : Squarefree d := Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
  calc
    ν d = ∏ p ∈ d.primeFactors, ν p :=
      eq_comm.mp (prod_factors_of_mult ν s.nu_mult hd_sq)
    _ < ∏ p ∈ d.primeFactors, 1 := by
      have hd_ne_zero : d ≠ 0 := by aesopDiv
      apply prod_lt_prod_of_nonempty
      · intro p hp
        simp only [mem_primeFactors] at hp
        apply s.nu_pos_of_prime p (by aesop) (by aesopDiv)
      · intro p hpd; rw [mem_primeFactors_of_ne_zero hd_ne_zero] at hpd
        apply s.nu_lt_one_of_prime p hpd.left (by aesopDiv)
      · apply primeDivisors_nonempty _ <| (two_le_iff d).mpr ⟨hd_ne_zero, hd_ne_one⟩
    _ = 1 := by
      simp

-- Facts about g
@[aesop safe]
theorem selbergTerms_pos (l : ℕ) (hl : l ∣ P) : 0 < g l := by
  rw [selbergTerms_apply]
  apply mul_pos
  · exact s.nu_pos_of_dvd_prodPrimes hl
  · apply prod_pos
    intro p hp
    rw [one_div_pos]
    have hp_prime : p.Prime := prime_of_mem_primeFactors hp
    have hp_dvd : p ∣ P := (Nat.dvd_of_mem_primeFactors hp).trans hl
    linarith only [s.nu_lt_one_of_prime p hp_prime hp_dvd]

theorem selbergTerms_mult : ArithmeticFunction.IsMultiplicative g := by
  unfold selbergTerms
  arith_mult

theorem one_div_selbergTerms_eq_conv_moebius_nu (l : ℕ) (hl : Squarefree l)
    (hnu_nonzero : ν l ≠ 0) : 1 / g l = ∑ d ∈ l.divisors, (μ <| l / d) * (ν d)⁻¹ :=
  by
  rw [selbergTerms_apply]
  simp only [one_div, mul_inv, inv_inv, Finset.prod_inv_distrib]
  rw [(s.nu_mult).prodPrimeFactors_one_sub_of_squarefree _ hl]
  rw [mul_sum]
  apply symm
  rw [← Nat.sum_divisorsAntidiagonal' fun d e : ℕ => ↑(μ d) * (ν e)⁻¹]
  rw [Nat.sum_divisorsAntidiagonal fun d e : ℕ => ↑(μ d) * (ν e)⁻¹]
  apply sum_congr rfl; intro d hd
  have hd_dvd : d ∣ l := dvd_of_mem_divisors hd
  rw [←div_mult_of_dvd_squarefree ν s.nu_mult l d (dvd_of_mem_divisors hd) hl, inv_div]
  · ring
  · revert hnu_nonzero; contrapose!
    exact multiplicative_zero_of_zero_dvd ν s.nu_mult hl hd_dvd

theorem nu_eq_conv_one_div_selbergTerms (d : ℕ) (hdP : d ∣ P) :
    (ν d)⁻¹ = ∑ l ∈ divisors P, if l ∣ d then 1 / g l else 0 := by
  apply symm
  rw [←sum_filter, Nat.divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero hdP]
  have hd_pos : 0 < d :=
    Nat.pos_of_ne_zero <| ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hdP
  revert hdP; revert d
  apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on _ (fun _ _ => Nat.dvd_trans)).mpr
  intro l _ hlP
  rw [sum_divisorsAntidiagonal' (f:=fun x y => (μ <| x) * (ν y)⁻¹) (n:=l)]
  apply symm
  exact s.one_div_selbergTerms_eq_conv_moebius_nu l
    (Squarefree.squarefree_of_dvd hlP s.prodPrimes_squarefree)
    (_root_.ne_of_gt <| s.nu_pos_of_dvd_prodPrimes hlP)

theorem conv_selbergTerms_eq_selbergTerms_mul_nu {d : ℕ} (hd : d ∣ P) :
    (∑ l ∈ divisors P, if l ∣ d then g l else 0) = g d * (ν d)⁻¹ := by
  calc
    (∑ l ∈ divisors P, if l ∣ d then g l else 0) =
        ∑ l ∈ divisors P, if l ∣ d then g (d / l) else 0 := by
      rw [← sum_over_dvd_ite s.prodPrimes_ne_zero hd]
      rw [← Nat.sum_divisorsAntidiagonal fun x _ => g x]
      rw [Nat.sum_divisorsAntidiagonal' fun x _ => g x]
      rw [sum_over_dvd_ite s.prodPrimes_ne_zero hd]
    _ = g d * ∑ l ∈ divisors P, if l ∣ d then 1 / g l else 0 := by
      rw [mul_sum]; apply sum_congr rfl; intro l hl
      rw [mul_ite_zero]
      apply if_ctx_congr Iff.rfl _ (fun _ => rfl)
      intro h
      rw [← div_mult_of_dvd_squarefree g s.selbergTerms_mult d l]
      · ring
      · exact h
      · apply Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree
      · apply _root_.ne_of_gt
        rw [mem_divisors] at hl
        apply selbergTerms_pos
        exact hl.left
    _ = g d * (ν d)⁻¹ := by rw [← s.nu_eq_conv_one_div_selbergTerms d hd]

theorem upper_bound_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
    s.siftedSum ≤ ∑ d ∈ divisors P, μPlus d * s.multSum d := by
  have hμ : ∀ n, δ n ≤ ∑ d ∈ n.divisors, μPlus d := μPlus.hμPlus
  rw [siftedSum_as_delta]
  trans (∑ n ∈ s.support, a n * ∑ d ∈ (Nat.gcd P n).divisors, μPlus d)
  · apply Finset.sum_le_sum; intro n _
    exact mul_le_mul_of_nonneg_left (hμ (Nat.gcd P n)) (s.weights_nonneg n)
  apply le_of_eq
  trans (∑ n ∈ s.support, ∑ d ∈ divisors P, if d ∣ n then a n * μPlus d else 0)
  · apply sum_congr rfl; intro n _
    rw [mul_sum, sum_over_dvd_ite s.prodPrimes_ne_zero (Nat.gcd_dvd_left _ _),
      sum_congr rfl]; intro d hd
    apply if_congr _ rfl rfl
    rw [Nat.dvd_gcd_iff, and_iff_right (dvd_of_mem_divisors hd)]
  rw [sum_comm, sum_congr rfl]; intro d _
  dsimp only [multSum]
  rw [mul_sum, sum_congr rfl]; intro n _
  rw [←ite_zero_mul, mul_comm]

theorem siftedSum_le_mainSum_errSum_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
    s.siftedSum ≤ X * s.mainSum μPlus + s.errSum μPlus := by
  dsimp only [mainSum, errSum]
  trans (∑ d ∈ divisors P, μPlus d * s.multSum d)
  · apply upper_bound_of_UpperBoundSieve
  trans ( X * ∑ d ∈ divisors P, μPlus d * ν d + ∑ d ∈ divisors P, μPlus d * R d )
  · apply le_of_eq
    rw [mul_sum, ←sum_add_distrib]
    apply sum_congr rfl; intro d _
    dsimp only [rem]; ring
  apply _root_.add_le_add (le_rfl)
  apply sum_le_sum; intro d _
  rw [←abs_mul]
  exact le_abs_self (UpperBoundSieve.μPlus μPlus d * rem s d)

end SieveLemmas

section LambdaSquared

/-- Lambda-squared upper-bound weights generated from a function on divisors. -/
def lambdaSquared (weights : ℕ → ℝ) : ℕ → ℝ := fun d =>
  ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0

private theorem lambdaSquared_eq_zero_of_support_wlog {w : ℕ → ℝ} {y : ℝ}
    (hw : ∀ (d : ℕ), ¬↑(d ^ 2) ≤ y → w d = 0)
    {d : ℕ} (hd : ¬↑d ≤ y) (d1 : ℕ) (d2 : ℕ) (h : d = Nat.lcm d1 d2)
    (hle : d1 ≤ d2) :
    w d1 * w d2 = 0 := by
  rw [hw d2]
  · ring
  by_contra hyp
  apply hd
  apply le_trans _ hyp
  norm_cast
  calc _ ≤ (d1.lcm d2) := by rw [h]
      _ ≤ (d1*d2) := Nat.div_le_self _ _
      _ ≤ _       := ?_
  · rw [sq]; gcongr
theorem lambdaSquared_eq_zero_of_support (w : ℕ → ℝ) (y : ℝ)
    (hw : ∀ d : ℕ, ¬d ^ 2 ≤ y → w d = 0) (d : ℕ) (hd : ¬d ≤ y) :
    lambdaSquared w d = 0 := by
  dsimp only [lambdaSquared]
  by_cases hy : 0 ≤ y
  swap
  · push Not at hd hy
    have : ∀ d' : ℕ, w d' = 0 := by
      intro d'; apply hw
      have : (0:ℝ) ≤ (d') ^ 2 := by norm_num
      linarith
    apply sum_eq_zero; intro d1 _
    apply sum_eq_zero; intro d2 _
    rw [this d1, this d2]
    simp only [ite_self, MulZeroClass.mul_zero]
  apply sum_eq_zero; intro d1 _; apply sum_eq_zero; intro d2 _
  split_ifs with h
  swap
  · rfl
  rcases Nat.le_or_le d1 d2 with hle | hle
  · apply lambdaSquared_eq_zero_of_support_wlog hw hd d1 d2 h hle
  · rw[mul_comm]
    apply lambdaSquared_eq_zero_of_support_wlog hw hd d2 d1 (Nat.lcm_comm d1 d2 ▸ h) hle

theorem upperMoebius_of_lambda_sq (weights : ℕ → ℝ) (hw : weights 1 = 1) :
    UpperMoebius <| lambdaSquared weights := by
  dsimp [UpperMoebius, lambdaSquared]
  intro n
  have h_sq :
    (∑ d ∈ n.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
      if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0) =
      (∑ d ∈ n.divisors, weights d) ^ 2 := by
    rw [sq, mul_sum, conv_lambda_sq_larger_sum _ n, sum_comm]
    apply sum_congr rfl; intro d1 hd1
    rw [sum_mul, sum_comm]
    apply sum_congr rfl; intro d2 hd2
    rw [←Aux.sum_intro]
    · ring
    · rw [mem_divisors, Nat.lcm_dvd_iff]
      exact ⟨⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩, (mem_divisors.mp hd1).2⟩
  rw [h_sq]
  split_ifs with hn
  · rw [hn]; simp [hw]
  · apply sq_nonneg

-- local notation3 "ν" => LPSieve.nu s
-- local notation3 "P" => LPSieve.prodPrimes s
-- local notation3 "a" => LPSieve.weights s
-- local notation3 "X" => LPSieve.totalMass s
-- local notation3 "R" => LPSieve.rem s
-- local notation3 "g" => LPSieve.selbergTerms s

theorem lambdaSquared_mainSum_eq_quad_form (w : ℕ → ℝ) :
    s.mainSum (lambdaSquared w) =
      ∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P,
        ν d1 * w d1 * ν d2 * w d2 * (ν (d1.gcd d2))⁻¹ := by
  dsimp only [mainSum, lambdaSquared]
  trans (∑ d ∈ divisors P, ∑ d1 ∈ divisors d, ∑ d2 ∈ divisors d,
          if d = d1.lcm d2 then w d1 * w d2 * ν d else 0)
  · rw [sum_congr rfl]; intro d _
    rw [sum_mul, sum_congr rfl]; intro d1 _
    rw [sum_mul, sum_congr rfl]; intro d2 _
    rw [ite_zero_mul]
  trans (∑ d ∈ divisors P, ∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P,
          if d = d1.lcm d2 then w d1 * w d2 * ν d else 0)
  · apply conv_lambda_sq_larger_sum
  rw [sum_comm, sum_congr rfl]; intro d1 hd1
  rw [sum_comm, sum_congr rfl]; intro d2 hd2
  have h : d1.lcm d2 ∣ P := Nat.lcm_dvd_iff.mpr ⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩
  rw [←sum_intro (divisors P) (d1.lcm d2) (mem_divisors.mpr ⟨h, s.prodPrimes_ne_zero⟩ )]
  rw [mult_lcm_eq_of_ne_zero ν s.nu_mult _ _ _]
  · ring
  · refine _root_.ne_of_gt (s.nu_pos_of_dvd_prodPrimes ?_)
    trans d1
    · exact Nat.gcd_dvd_left d1 d2
    · exact dvd_of_mem_divisors hd1

theorem lambdaSquared_mainSum_eq_diag_quad_form (w : ℕ → ℝ) :
    s.mainSum (lambdaSquared w) =
      ∑ l ∈ divisors P,
        1 / g l * (∑ d ∈ divisors P, if l ∣ d then ν d * w d else 0) ^ 2 :=
  by
  rw [s.lambdaSquared_mainSum_eq_quad_form w]
  trans (∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P, (∑ l ∈ divisors P,
          if l ∣ d1.gcd d2 then 1 / g l * (ν d1 * w d1) * (ν d2 * w d2) else 0))
  · apply sum_congr rfl; intro d1 hd1; apply sum_congr rfl; intro d2 _
    have hgcd_dvd: d1.gcd d2 ∣ P := Trans.trans (Nat.gcd_dvd_left d1 d2) (dvd_of_mem_divisors hd1)
    rw [s.nu_eq_conv_one_div_selbergTerms _ hgcd_dvd, mul_sum]
    apply sum_congr rfl; intro l _
    rw [mul_ite_zero]; apply if_congr Iff.rfl _ rfl
    ring
  trans (∑ l ∈ divisors P, ∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P,
        if l ∣ Nat.gcd d1 d2 then 1 / selbergTerms s l * (ν d1 * w d1) * (ν d2 * w d2) else 0)
  · apply symm; rw [sum_comm, sum_congr rfl]; intro d1 _; rw[sum_comm];
  apply sum_congr rfl; intro l _
  rw [sq, sum_mul, mul_sum, sum_congr rfl]; intro d1 _
  rw [mul_sum, mul_sum, sum_congr rfl]; intro d2 _
  rw [ite_zero_mul_ite_zero, mul_ite_zero]
  apply if_congr (Nat.dvd_gcd_iff) _ rfl;
  ring

end LambdaSquared

end LPSieve

end -- close `noncomputable section` opened in SieveLemmas



-- === Inlined from SelbergSieve4.Selberg ===
/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

/-!
# LeanPool.SelbergSieve4.Selberg
-/

noncomputable section

open scoped BigOperators LPSieve ArithmeticFunction.Moebius ArithmeticFunction.omega

open Finset Real Nat LPSieve.UpperBoundSieve ArithmeticFunction LPSieve

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-- A Selberg sieve is a finite sieve together with a sieve level. -/
structure LPSelbergSieve extends LPSieve where mk ::
  /-- LPSieve level. -/
  level : ℝ
  one_le_level : 1 ≤ level

namespace LPSelbergSieve

variable (s : LPSelbergSieve)
local notation3 "ν" => LPSieve.nu (toLPSieve s)
local notation3 "P" => LPSieve.prodPrimes (toLPSieve s)
local notation3 "a" => LPSieve.weights (toLPSieve s)
local notation3 "X" => LPSieve.totalMass (toLPSieve s)
local notation3 "R" => LPSieve.rem (toLPSieve s)  -- this one seems broken
local notation3 "g" => LPSieve.selbergTerms (toLPSieve s)
local notation3 "y" => LPSelbergSieve.level s
local notation3 "hy" => LPSelbergSieve.one_le_level s

/-- Selberg bounding sum over divisors below the square-root level. -/
def selbergBoundingSum : ℝ :=
  ∑ l ∈ divisors P, if l ^ 2 ≤ y then g l else 0
local notation3 "S" => LPSelbergSieve.selbergBoundingSum s

@[aesop safe]
theorem selbergBoundingSum_pos :
    0 < S := by
  dsimp only [selbergBoundingSum]
  rw [← sum_filter]
  apply sum_pos;
  · intro l hl
    rw [mem_filter, mem_divisors] at hl
    · apply s.selbergTerms_pos _ (hl.1.1)
  · simp_rw [Finset.Nonempty, mem_filter]; use 1
    constructor
    · apply one_mem_divisors.mpr s.prodPrimes_ne_zero
    rw [one_pow, cast_one]
    exact s.one_le_level

theorem selbergBoundingSum_ne_zero : S ≠ 0 := by
  apply _root_.ne_of_gt
  exact s.selbergBoundingSum_pos

theorem selbergBoundingSum_nonneg : 0 ≤ S := _root_.le_of_lt s.selbergBoundingSum_pos

/-- Selberg weights attached to the sieve. -/
def selbergWeights : ℕ → ℝ := fun d =>
  if d ∣ P then
    (ν d)⁻¹ * g d * μ d * S⁻¹ *
      ∑ m ∈ divisors P, if (d * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
  else 0

-- This notation traditionally uses λ, which is unavailable in lean
local notation3 "γ" => LPSelbergSieve.selbergWeights s

theorem selbergWeights_eq_zero_of_not_dvd {d : ℕ} (hd : ¬ d ∣ P) :
    γ d = 0 := by
  rw [selbergWeights, if_neg hd]

theorem selbergWeights_eq_zero (d : ℕ) (hd : ¬d ^ 2 ≤ y) :
    γ d = 0 := by
  dsimp only [selbergWeights]
  split_ifs with h
  · rw [mul_eq_zero_of_right _]
    apply Finset.sum_eq_zero
    refine fun m hm => if_neg ?_
    intro hyp
    have : (d^2:ℝ) ≤ (d*m)^2 := by
      norm_cast;
      refine Nat.pow_le_pow_left ?h 2
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_mem_divisors hm)
    linarith [hyp.1]
  · rfl

@[aesop safe]
theorem selbergWeights_mul_mu_nonneg (d : ℕ) (hdP : d ∣ P) :
    0 ≤ γ d * μ d :=
  by
  have := s.selbergBoundingSum_nonneg
  dsimp only [selbergWeights]
  rw [if_pos hdP]; rw [mul_assoc]
  trans ((μ d :ℝ)^2 * (ν d)⁻¹ * g d * S⁻¹ * ∑ m ∈ divisors P,
          if (d * m) ^ 2 ≤ y ∧ Coprime m d then g m else 0)
  swap
  · apply le_of_eq
    ring
  apply mul_nonneg
  · apply div_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · apply sq_nonneg
        · rw [inv_nonneg]
          exact le_of_lt <| s.nu_pos_of_dvd_prodPrimes hdP
      · exact le_of_lt <| s.selbergTerms_pos d hdP
    · exact s.selbergBoundingSum_nonneg
  · apply sum_nonneg; intro m hm
    split_ifs with h
    · exact le_of_lt <| s.selbergTerms_pos m (dvd_of_mem_divisors hm)
    · rfl

lemma sum_mul_subst (k n : ℕ) {f : ℕ → ℝ} (h : ∀ l, l ∣ n → ¬ k ∣ l → f l = 0) :
      ∑ l ∈ n.divisors, f l
    = ∑ m ∈ n.divisors, if k*m ∣ n then f (k*m) else 0 := by
  by_cases hn: n = 0
  · simp [hn]
  by_cases hkn : k ∣ n
  swap
  · rw [sum_eq_zero, sum_eq_zero]
    · rintro m _
      rw [if_neg]
      rintro h
      apply hkn
      exact (Nat.dvd_mul_right k m).trans h
    · intro l hl; apply h l (dvd_of_mem_divisors hl)
      apply fun hkl => hkn <| hkl.trans (dvd_of_mem_divisors hl)
  trans (∑ l ∈ n.divisors, ∑ m ∈ n.divisors, if l=k*m then f l else 0)
  · rw [sum_congr rfl]; intro l hl
    by_cases hkl : k ∣ l
    swap
    · rw [h l (dvd_of_mem_divisors hl) hkl, sum_eq_zero]
      intro m _
      rw [ite_id]
    rw [sum_eq_single (l/k)]
    · rw[if_pos]; rw [Nat.mul_div_cancel' hkl]
    · intro m hmn hmlk
      apply if_neg; revert hmlk; contrapose!; intro hlkm
      rw [hlkm, mul_comm, Nat.mul_div_cancel]
      aesopDiv
    · contrapose!; intro _
      rw [mem_divisors]
      exact ⟨Trans.trans (Nat.div_dvd_of_dvd hkl) (dvd_of_mem_divisors hl), hn⟩
  · rw [sum_comm, sum_congr rfl]; intro m _
    split_ifs with hdvd
    · rw [←Aux.sum_intro]
      aesopDiv
    · apply sum_eq_zero; intro l hl
      apply if_neg;
      aesopDiv

--Important facts about the selberg weights
theorem selbergWeights_eq_dvds_sum (d : ℕ) :
    ν d * γ d =
      S⁻¹ * μ d *
        ∑ l ∈ divisors P, if d ∣ l ∧ l ^ 2 ≤ y then g l else 0 := by
  by_cases h_dvd : d ∣ P
  swap
  · dsimp only [selbergWeights]; rw [if_neg h_dvd]
    rw [sum_eq_zero]
    · ring
    · intro l hl; rw [mem_divisors] at hl
      rw [if_neg]; push Not; intro h
      exfalso; exact h_dvd (dvd_trans h hl.left)
  dsimp only [selbergWeights]
  rw [if_pos h_dvd]
  repeat rw [mul_sum]
  -- change of variables l=m*d
  apply symm
  rw [sum_mul_subst d P]
  · apply sum_congr rfl
    intro m hm
    rw [mul_ite_zero, ←ite_and, mul_ite_zero, mul_ite_zero]
    apply if_ctx_congr _ _ fun _ => rfl
    · rw [coprime_comm]
      constructor
      · intro h
        exact ⟨h.2.2,
          coprime_of_squarefree_mul <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree⟩
      · intro h
        exact ⟨Coprime.mul_dvd_of_dvd_of_dvd h.2 h_dvd (dvd_of_mem_divisors hm),
          Nat.dvd_mul_right d m, h.1⟩
    · intro h
      trans ((ν d)⁻¹ * (ν d) * g d * μ d / S * g m)
      · rw [inv_mul_cancel₀ (s.nu_ne_zero h_dvd), s.selbergTerms_mult.map_mul_of_coprime
          <| coprime_comm.mp h.2]
        ring
      ring
  · intro l _ hdl
    rw [if_neg, mul_zero]
    push Not; intro h; contradiction

theorem selbergWeights_diagonalisation (l : ℕ) (hl : l ∈ divisors P) :
    (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) =
      if l ^ 2 ≤ y then g l * μ l * S⁻¹ else 0 := by
  calc
    (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) =
        ∑ d ∈ divisors P, ∑ k ∈ divisors P,
          if l ∣ d ∧ d ∣ k ∧ k ^ 2 ≤ y then g k * S⁻¹ * (μ d:ℝ) else 0 := by
      apply sum_congr rfl; intro d _
      rw [selbergWeights_eq_dvds_sum, ← boole_mul, mul_sum, mul_sum]
      apply sum_congr rfl; intro k _
      rw [mul_ite_zero, ite_zero_mul_ite_zero]
      apply if_ctx_congr Iff.rfl _ (fun _ => rfl);
      intro _; ring
    _ = ∑ k ∈ divisors P, if k ^ 2 ≤ y then
            (∑ d ∈ divisors P, if l ∣ d ∧ d ∣ k then (μ d:ℝ) else 0) * g k * S⁻¹
          else 0 := by
      rw [sum_comm]; apply sum_congr rfl; intro k _
      apply symm
      rw [← boole_mul, sum_mul, sum_mul, mul_sum, sum_congr rfl]
      intro d _
      rw [ite_zero_mul, ite_zero_mul, ite_zero_mul, one_mul, ←ite_and]
      apply if_ctx_congr _ _ (fun _ => rfl)
      · tauto
      intro _; ring
    _ = if l ^ 2 ≤ y then g l * μ l * S⁻¹ else 0 := by
      rw [Aux.sum_intro (f:=fun _ => if l^2 ≤ y then g l * μ l * S⁻¹ else 0) (divisors P) l hl]
      apply sum_congr rfl; intro k hk
      rw [Aux.moebius_inv_dvd_lower_bound_real s.prodPrimes_squarefree l _ (dvd_of_mem_divisors hk),
        ←ite_and, ite_zero_mul, ite_zero_mul, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · rw [and_comm, eq_comm]
        apply and_congr_right
        intro heq
        rw [heq]
      intro h
      rw[h.1]
      ring

/-- Lambda-squared upper-bound weight generated by the Selberg weights. -/
def selbergMuPlus : ℕ → ℝ :=
  LPSieve.lambdaSquared γ
local notation3 "μ⁺" => LPSelbergSieve.selbergMuPlus s

theorem weight_one_of_selberg : γ 1 = 1 := by
  dsimp only [selbergWeights]
  rw [if_pos (one_dvd P), s.nu_mult.left, s.selbergTerms_mult.left]
  -- rw [ArithmeticFunction.moebius_apply_one, Int.cast_one]
  simp only [inv_one, mul_one, isUnit_one, IsUnit.squarefree, moebius_apply_of_squarefree,
    cardFactors_one, _root_.pow_zero, Int.cast_one, selbergBoundingSum, cast_pow, one_mul,
    coprime_one_right_eq_true, and_true]
  have hS : (∑ x ∈ divisors P, if (x : ℝ) ^ 2 ≤ y then g x else 0) ≠ 0 := by
    simpa [selbergBoundingSum, Nat.cast_pow] using s.selbergBoundingSum_ne_zero
  exact inv_mul_cancel₀ hS

theorem selbergμPlus_eq_zero (d : ℕ) (hd : ¬d ≤ y) : μ⁺ d = 0 :=
  by
  apply LPSieve.lambdaSquared_eq_zero_of_support _ y _ d hd
  apply s.selbergWeights_eq_zero

/-- Upper-bound sieve induced by the Selberg weights. -/
def selbergUbSieve : UpperBoundSieve :=
  ⟨μ⁺, LPSieve.upperMoebius_of_lambda_sq γ (s.weight_one_of_selberg)⟩

-- proved for general lambda squared sieves
theorem mainSum_eq_diag_quad_form :
    s.mainSum μ⁺ =
      ∑ l ∈ divisors P,
        1 / g l *
          (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) ^ 2 :=
  by apply lambdaSquared_mainSum_eq_diag_quad_form

theorem selberg_bound_simple_mainSum :
    s.mainSum μ⁺ = S⁻¹ :=
  by
  rw [mainSum_eq_diag_quad_form]
  trans (∑ l ∈ divisors P, (if l ^ 2 ≤ y then g l *  (S⁻¹) ^ 2 else 0))
  · apply sum_congr rfl; intro l hl
    rw [s.selbergWeights_diagonalisation l hl, ite_pow, zero_pow, mul_ite_zero]
    · apply if_congr Iff.rfl _ rfl
      trans (1 / g l * g l * g l * (μ l : ℝ)^2  * (S⁻¹) ^ 2)
      · ring
      norm_cast
      rw [moebius_sq_eq_one_of_squarefree <| s.squarefree_of_mem_divisors_prodPrimes hl]
      rw [one_div_mul_cancel <| _root_.ne_of_gt <| s.selbergTerms_pos l <| dvd_of_mem_divisors hl]
      ring
    · linarith
  conv => {lhs; congr; {skip}; {ext i; rw [← ite_zero_mul]}}
  dsimp only [selbergBoundingSum]
  rw [←sum_mul, sq, ←mul_assoc]
  have hS : (∑ l ∈ divisors P, if ↑(l ^ 2) ≤ y then g l else 0) ≠ 0 := by
    simpa [selbergBoundingSum] using s.selbergBoundingSum_ne_zero
  rw [mul_inv_cancel₀ hS, one_mul]

lemma eq_gcd_mul_of_dvd_of_coprime {k d m : ℕ} (hkd : k ∣ d) (hmd : Coprime m d)
    (hk : k ≠ 0) :
    k = d.gcd (k*m) := by
  rcases hkd with ⟨r, hr⟩
  have hrdvd : r ∣ d := by
    use k
    rw [mul_comm]
    exact hr
  apply symm; rw [hr, Nat.gcd_mul_left, mul_eq_left₀ hk, Nat.gcd_comm]
  apply Coprime.coprime_dvd_right hrdvd hmd

private lemma _helper {k m d : ℕ} (hkd : k ∣ d) (hk : k ∈ divisors P)
    (hm : m ∈ divisors P) :
    k * m ∣ P ∧ k = Nat.gcd d (k * m) ∧ (k * m) ^ 2 ≤ y ↔
    (k * m) ^ 2 ≤ y ∧ Coprime m d := by
  constructor
  · intro h
    constructor
    · exact h.2.2
    · rcases hkd with ⟨r, hr⟩
      rw [hr, Nat.gcd_mul_left, eq_comm, mul_eq_left₀ (by aesopDiv)] at h
      rw [hr, coprime_comm, Nat.coprime_mul_iff_left]
      constructor
      · apply coprime_of_squarefree_mul <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree
      · exact h.2.1
  · intro h
    constructor
    · apply Coprime.mul_dvd_of_dvd_of_dvd
      · rw [coprime_comm]; exact Coprime.coprime_dvd_right hkd h.2
      · exact dvd_of_mem_divisors hk
      · exact dvd_of_mem_divisors hm
    constructor
    · exact eq_gcd_mul_of_dvd_of_coprime hkd h.2 (by aesopDiv)
    · exact h.1

theorem selbergBoundingSum_ge {d : ℕ} (hdP : d ∣ P) :
    S ≥ γ d * ↑(μ d) * S := by
  calc
  _ = (∑ k ∈ divisors P, ∑ l ∈ divisors P, if k = d.gcd l ∧ l ^ 2 ≤ y then g l else 0) := by
    dsimp only [selbergBoundingSum]
    rw [sum_comm, sum_congr rfl]; intro l _
    simp_rw [ite_and]
    rw [←Aux.sum_intro]
    · rw [mem_divisors]
      exact ⟨(Nat.gcd_dvd_left d l).trans (hdP), s.prodPrimes_ne_zero⟩
  _ = (∑ k ∈ divisors P,
          if k ∣ d then
            g k * ∑ m ∈ divisors P, if (k * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
          else 0) := by
    apply sum_congr rfl; intro k hk
    rw [mul_sum]
    split_ifs with hkd
    swap
    · rw [sum_eq_zero]; intro l _
      rw [if_neg]
      push Not; intro h; exfalso
      rw [h] at hkd
      exact hkd <| Nat.gcd_dvd_left d l
    rw [sum_mul_subst k P]
    · rw [sum_congr rfl]; intro m hm
      rw [mul_ite_zero, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · apply s._helper hkd hk hm
      · intro h
        apply s.selbergTerms_mult.2
        rw [coprime_comm]
        apply h.2.coprime_dvd_right hkd
    · intro l _ hkl
      apply if_neg
      push Not; intro h; exfalso
      rw [h] at hkl
      exact hkl (Nat.gcd_dvd_right d l)
  _ ≥ (∑ k ∈ divisors P, if k ∣ d
          then g k * ∑ m ∈ divisors P, if (d * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
          else 0 ) := by
    apply sum_le_sum; intro k _
    split_ifs with hkd
    swap
    · rfl
    apply mul_le_mul le_rfl
    · apply sum_le_sum; intro m hm
      split_ifs with h h' h'
      · rfl
      · exfalso; apply h'
        refine ⟨?_, h.2⟩
        trans ((d*m)^2:ℝ)
        · norm_cast
          gcongr
          refine Nat.le_of_dvd ?_ hkd
          apply Nat.pos_of_ne_zero
          apply ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hdP
        exact h.1
      · refine le_of_lt <| s.selbergTerms_pos m <| dvd_of_mem_divisors hm
      · rfl
    · apply sum_nonneg; intro m hm
      split_ifs
      · apply le_of_lt <| s.selbergTerms_pos m <| dvd_of_mem_divisors hm
      · rfl
    · exact le_of_lt <| s.selbergTerms_pos k <| Trans.trans hkd hdP
  _ = _ := by
    conv => enter [1, 2, k]; rw [← ite_zero_mul]
    rw [←sum_mul, s.conv_selbergTerms_eq_selbergTerms_mul_nu hdP]
    trans (S * S⁻¹ * (μ d:ℝ)^2 * (ν d)⁻¹ * g d *
      (∑ m ∈ divisors P, if (d*m) ^ 2 ≤ y ∧ Coprime m d then g m else 0))
    · rw [mul_inv_cancel₀ s.selbergBoundingSum_ne_zero, ←Int.cast_pow,
        moebius_sq_eq_one_of_squarefree]
      · ring
      · exact Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
    dsimp only [selbergWeights]; rw [if_pos hdP]
    ring

theorem selberg_bound_weights (d : ℕ) : |γ d| ≤ 1 := by
  by_cases hdP : d ∣ P
  swap
  · rw [s.selbergWeights_eq_zero_of_not_dvd hdP]; simp only [zero_le_one, abs_zero]
  have : 1*S ≥ γ d * ↑(μ d) * S := by
    rw[one_mul]
    exact s.selbergBoundingSum_ge hdP
  replace this : γ d * μ d ≤ 1 := by
    apply le_of_mul_le_mul_of_pos_right this (s.selbergBoundingSum_pos)
  convert this using 1
  rw [← abs_of_nonneg <| s.selbergWeights_mul_mu_nonneg d hdP,
    abs_mul, ←Int.cast_abs, abs_moebius_eq_one_of_squarefree <|
    (s.prodPrimes_squarefree.squarefree_of_dvd hdP), Int.cast_one, mul_one]


theorem selberg_bound_muPlus (n : ℕ) (hn : n ∈ divisors P) :
    |μ⁺ n| ≤ (3:ℝ) ^ ω n := by
  let f : ℕ → ℕ → ℝ := fun x z : ℕ => if n = x.lcm z then 1 else 0
  dsimp only [selbergMuPlus, lambdaSquared]
  calc
    |∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, if n = d1.lcm d2 then γ d1 * γ d2 else 0| ≤
        ∑ d1 ∈ n.divisors, |∑ d2 ∈ n.divisors, if n = d1.lcm d2 then γ d1 * γ d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, |if n = d1.lcm d2 then γ d1 * γ d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, f d1 d2 := ?_
    _ = (n.divisors ×ˢ n.divisors).sum fun p => f p.fst p.snd := ?_
    _ = Finset.card ((n.divisors ×ˢ n.divisors).filter fun p : ℕ × ℕ => n = p.fst.lcm p.snd) := ?_
    _ = (3:ℕ) ^ ω n := ?_
    _ = (3:ℝ) ^ ω n := ?_
  · apply abs_sum_le_sum_abs
  · gcongr; apply abs_sum_le_sum_abs
  · gcongr with d1 _ d2
    rw [apply_ite abs, abs_zero, abs_mul]
    simp only [f]
    by_cases h : n = d1.lcm d2
    · rw [if_pos h, if_pos h]
      apply mul_le_one₀ (s.selberg_bound_weights d1) (abs_nonneg <| γ d2)
        (s.selberg_bound_weights d2)
    · rw [if_neg h, if_neg h]
  · rw [← Finset.sum_product']
  · rw [← sum_filter, Finset.sum_const, nsmul_one]
  · rw [← Nat.card_pair_lcm_eq (s.squarefree_of_mem_divisors_prodPrimes hn)]
    congr; ext; rw[eq_comm]
  norm_num

theorem selberg_bound_simple_errSum :
    s.errSum μ⁺ ≤
      ∑ d ∈ divisors P, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |R d| else 0 := by
  dsimp only [errSum]
  gcongr with d hd
  split_ifs with h
  · apply mul_le_mul
    · apply s.selberg_bound_muPlus d hd
    · exact le_rfl
    · exact abs_nonneg <| R d
    · exact pow_nonneg (by linarith) (ω d)
  · rw [s.selbergμPlus_eq_zero d h, abs_zero, zero_mul]

theorem selberg_bound_simple :
    s.siftedSum ≤
      X / S +
        ∑ d ∈ divisors P, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |R d| else 0 := by
  let μPlus := s.selbergUbSieve
  calc
    s.siftedSum ≤ X * s.mainSum μPlus + s.errSum μPlus :=
      s.siftedSum_le_mainSum_errSum_of_UpperBoundSieve μPlus
    _ ≤ _ := ?_
  gcongr
  · erw [s.selberg_bound_simple_mainSum, div_eq_mul_inv]
  · apply s.selberg_bound_simple_errSum

end LPSelbergSieve

end -- close `noncomputable section` opened in Selberg



-- === Inlined from SelbergSieve4.Applications.PrimeCountingUpperBound ===
/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

/-!
# LeanPool.SelbergSieve4.Applications.PrimeCountingUpperBound
-/

noncomputable section
open scoped Nat Nat.Prime ArithmeticFunction.zeta ArithmeticFunction.Moebius
open scoped ArithmeticFunction.omega BigOperators

namespace PrimeUpperBound

attribute [local instance] Classical.propDecidable

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

lemma prodDistinctPrimes_squarefree (s : Finset ℕ) (h : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  refine Iff.mpr Nat.squarefree_iff_prime_squarefree ?_
  intro p hp; by_contra h_dvd
  by_cases hps : p ∈ s
  · rw [← Finset.mul_prod_erase (a := p) (h := hps),
      mul_dvd_mul_iff_left (Nat.Prime.ne_zero hp)] at h_dvd
    obtain ⟨q, hq⟩ := Prime.exists_mem_finset_dvd (Nat.Prime.prime hp) h_dvd
    rw [Finset.mem_erase] at hq
    exact hq.1.1 <| ((Nat.prime_dvd_prime_iff_eq hp (h q hq.1.2)).mp hq.2).symm
  · have : p ∣ ∏ p ∈ s, p := Trans.trans (dvd_mul_right p p) h_dvd
    obtain ⟨q, hq⟩ := Prime.exists_mem_finset_dvd (Nat.Prime.prime hp) this
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp (h q hq.1)).mp hq.2
    rw [heq] at hps; exact hps hq.1

lemma primorial_squarefree (n : ℕ) : Squarefree (primorial n) := by
  apply prodDistinctPrimes_squarefree
  simp_rw [Finset.mem_filter]
  exact fun _ h => h.2

theorem zeta_pos_of_prime :
    ∀ (p : ℕ), Nat.Prime p → (0 : ℝ) < (↑ζ : ArithmeticFunction ℝ) p := by
  intro p hp
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg (Nat.Prime.ne_zero hp)]
  norm_num

theorem zeta_lt_self_of_prime :
    ∀ (p : ℕ), Nat.Prime p → (↑ζ : ArithmeticFunction ℝ) p < (p : ℝ) := by
  intro p hp
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg (Nat.Prime.ne_zero hp)]
  norm_num
  exact Nat.succ_le_iff.mp (Nat.Prime.two_le hp)

/-- Selberg sieve specialized to primes at most the real level `y`. -/
def primeSieve (N : ℕ) (y : ℝ) (hy : 1 ≤ y) : LPSelbergSieve := {
  support := Finset.range (N + 1)
  prodPrimes := primorial (Nat.floor y)
  prodPrimes_squarefree := primorial_squarefree _
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := N
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ => by
    simp [if_neg hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ => by
    simpa [hp.ne_zero] using
      (inv_lt_one_of_one_lt₀ (by norm_cast; exact hp.one_lt) : (p : ℝ)⁻¹ < 1)
  level := y
  one_le_level := hy
}

theorem prime_dvd_primorial_iff (n p : ℕ) (hp : p.Prime) :
    p ∣ primorial n ↔ p ≤ n := by
  unfold primorial
  constructor
  · intro h
    let h' : ∃ i, i ∈ Finset.filter Nat.Prime (Finset.range (n + 1)) ∧ p ∣ i :=
      Prime.exists_mem_finset_dvd (Nat.Prime.prime hp) h
    obtain ⟨q, hq⟩ := h'
    rw [Finset.mem_filter, Finset.mem_range] at hq
    rw [prime_dvd_prime_iff_eq (Nat.Prime.prime hp) (Nat.Prime.prime hq.1.2)] at hq
    rw [hq.2]
    exact Nat.lt_succ_iff.mp hq.1.1
  · intro h
    apply Finset.dvd_prod_of_mem
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_iff.mpr h, hp⟩

theorem siftedSum_eq (s : LPSelbergSieve) (hw : ∀ i ∈ s.support, s.weights i = 1)
    (z : ℝ) (hz : 1 ≤ z) (hP : s.prodPrimes = primorial (Nat.floor z)) :
    s.siftedSum =
      (s.support.filter (fun d => ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card := by
  dsimp only [LPSieve.siftedSum]
  rw [Finset.card_eq_sum_ones, ←Finset.sum_filter, Nat.cast_sum]
  apply Finset.sum_congr
  · rw [hP]
    ext d
    constructor
    · intro hd
      rw [Finset.mem_filter] at *
      constructor
      · exact hd.1
      · intro p hpp hpy
        rw [← Nat.Prime.coprime_iff_not_dvd hpp]
        apply Nat.Coprime.coprime_dvd_left _ hd.2
        rw [prime_dvd_primorial_iff _ _ hpp]
        apply Nat.le_floor hpy
    · intro h
      rw [Finset.mem_filter] at *
      constructor
      · exact h.1
      refine Nat.coprime_of_dvd ?_
      intro p hp
      erw [prime_dvd_primorial_iff _ _ hp]
      intro hpy
      apply h.2 p hp
      trans ↑(Nat.floor z)
      · norm_cast
      · apply Nat.floor_le
        linarith only [hz]
  · simp_rw [Nat.cast_one]
    intro x hx
    rw [Finset.mem_filter] at hx
    apply hw x hx.1

theorem primeSieve_siftedSum_eq (N : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    (primeSieve N y hy).siftedSum =
      ((Finset.range (N + 1)).filter (fun d => ∀ p : ℕ, p.Prime → p ≤ y → ¬p ∣ d)).card := by
  apply siftedSum_eq
  · exact fun _ _ => rfl
  · exact hy
  · rfl

theorem prime_subset (N : ℕ) (y : ℝ) :
    (Finset.range (N + 1)).filter Nat.Prime ⊆
      ((Finset.range (N + 1)).filter (fun d => ∀ p : ℕ, p.Prime → p ≤ y → ¬p ∣ d))
      ∪ Finset.Icc 1 (Nat.floor y) := by
  intro p
  simp_rw [Finset.mem_union, Finset.mem_filter]
  intro h
  by_cases hp_le : p ≤ y
  · right
    rw [Finset.mem_Icc]
    exact ⟨le_of_lt h.2.one_lt, Nat.le_floor hp_le⟩
  · left
    constructor
    · exact h.1
    · intro q hq hq'
      rw [prime_dvd_prime_iff_eq hq.prime h.2.prime]
      intro hqp
      rw [hqp] at hq'
      linarith only [hp_le, hq']


theorem pi_le_siftedSum (N : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    π N ≤ (primeSieve N y hy).siftedSum + y := by
  trans ((primeSieve N y hy).siftedSum + Nat.floor y)
  · have : (Finset.Icc 1 (Nat.floor y)).card = Nat.floor y := by
      rw [Nat.card_Icc]; norm_num
    rw [primeSieve_siftedSum_eq, ←this]
    unfold Nat.primeCounting
    unfold Nat.primeCounting'
    rw [Nat.count_eq_card_filter_range]
    norm_cast
    trans (((Finset.range (N + 1)).filter
        (fun d => ∀ p : ℕ, p.Prime → p ≤ y → ¬p ∣ d))
      ∪ Finset.Icc 1 (Nat.floor y)).card
    · exact Finset.card_le_card (prime_subset N y)
    apply Finset.card_union_le
  · gcongr
    apply Nat.floor_le
    linarith only [hy]

/-- Predicate asserting that an arithmetic function is completely multiplicative. -/
def CompletelyMultiplicative (f : ArithmeticFunction ℝ) : Prop :=
  f 1 = 1 ∧ ∀ a b, f (a * b) = f a * f b

namespace CompletelyMultiplicative
open ArithmeticFunction
theorem zeta : CompletelyMultiplicative ζ := by
  unfold CompletelyMultiplicative
  constructor
  · simp [ArithmeticFunction.zeta_apply]
  intro a b
  by_cases ha : a = 0
  · simp [ArithmeticFunction.zeta_apply, ha]
  by_cases hb : b = 0
  · simp [ArithmeticFunction.zeta_apply, hb]
  simp [ArithmeticFunction.zeta_apply, ha, hb, mul_eq_zero]

theorem id : CompletelyMultiplicative ArithmeticFunction.id := by
  constructor <;> simp

theorem pmul (f g : ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f)
    (hg : CompletelyMultiplicative g) :
    CompletelyMultiplicative (ArithmeticFunction.pmul f g) := by
  constructor
  · rw [pmul_apply, hf.1, hg.1, mul_one]
  intro a b
  simp_rw [pmul_apply, hf.2, hg.2]; ring

theorem pdiv {f g : ArithmeticFunction ℝ} (hf : CompletelyMultiplicative f)
    (hg : CompletelyMultiplicative g) :
    CompletelyMultiplicative (ArithmeticFunction.pdiv f g) := by
  constructor
  · rw [pdiv_apply, hf.1, hg.1, div_one]
  intro a b
  simp_rw [pdiv_apply, hf.2, hg.2]; ring

theorem isMultiplicative {f : ArithmeticFunction ℝ} (hf : CompletelyMultiplicative f) :
    ArithmeticFunction.IsMultiplicative f :=
  ⟨hf.1, fun _ => hf.2 _ _⟩

theorem apply_pow (f : ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (a n : ℕ) :
    f (a^n) = f a ^ n := by
  induction n with
  | zero => simpa using hf.1
  | succ n' ih =>
      calc
        f (a ^ (n' + 1)) = f (a ^ n' * a) := by rw [pow_succ]
        _ = f (a ^ n') * f a := hf.2 _ _
        _ = f a ^ n' * f a := by rw [ih]
        _ = f a ^ (n' + 1) := by rw [pow_succ]

end CompletelyMultiplicative

theorem prod_factors_one_div_compMult_ge (M : ℕ) (f : ArithmeticFunction ℝ)
    (hf : CompletelyMultiplicative f) (hf_nonneg : ∀ n, 0 ≤ f n) (d : ℕ)
    (hd : Squarefree d) (hf_size : ∀ n, n.Prime → n ∣ d → f n < 1) :
    f d * ∏ p ∈ d.primeFactors, 1 / (1 - f p)
    ≥ ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p ^ n) := by
  calc
    f d * ∏ p ∈ d.primeFactors, 1 / (1 - f p)
        = ∏ p ∈ d.primeFactors, f p / (1 - f p) := by
      conv => { lhs; congr; rw [←Nat.prod_primeFactors_of_squarefree hd] }
      rw [hf.isMultiplicative.map_prod_of_subset_primeFactors _ _ subset_rfl,
        ← Finset.prod_mul_distrib]
      simp_rw [one_div, div_eq_mul_inv]
    _ ≥ ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, (f p) ^ n := by
      gcongr with p hp
      · exact fun p _ => Finset.sum_nonneg fun n _ => pow_nonneg (hf_nonneg p) n
      rw [Nat.mem_primeFactors_of_ne_zero hd.ne_zero] at hp
      simpa [← Finset.Ico_succ_right_eq_Icc, pow_one] using
        (geom_sum_Ico_le_of_lt_one (m := 1) (n := M.succ) (x := f p) (hf_nonneg p)
          (hf_size p hp.1 hp.2))
    _ = ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p ^ n) := by
      simp_rw [hf.apply_pow]

theorem prod_factors_sum_pow_compMult (M : ℕ) (hM : M ≠ 0)
    (f : ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (d : ℕ)
    (hd : Squarefree d) :
    ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p ^ n)
    = ∑ m ∈ (d ^ M).divisors.filter (d ∣ ·), f m := by
  rw [Finset.prod_sum]
  let i : (a : _) → (ha : a ∈ Finset.pi d.primeFactors fun p => Finset.Icc 1 M) → ℕ :=
    fun a _ => ∏ p ∈ d.primeFactors.attach, p.1 ^ (a p p.2)
  have hfact_i : ∀ a ha,
      ∀ p, Nat.factorization (i a ha) p = if hp : p ∈ d.primeFactors then a p hp else 0 := by
    intro a ha p
    by_cases hp : p ∈ d.primeFactors
    · rw [dif_pos hp, Nat.factorization_prod, Finset.sum_apply',
        Finset.sum_eq_single ⟨p, hp⟩, Nat.factorization_pow, Finsupp.smul_apply,
          Nat.Prime.factorization_self (Nat.prime_of_mem_primeFactors hp)]
      · ring
      · intro q _ hq
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_zero]
        right
        apply Nat.factorization_eq_zero_of_not_dvd
        rw [Nat.Prime.dvd_iff_eq (Nat.prime_of_mem_primeFactors q.2)
          (Nat.prime_of_mem_primeFactors hp).ne_one, ← exists_eq_subtype_mk_iff]
        push Not
        exact fun _ => hq
      · intro h
        exfalso
        exact h (Finset.mem_attach _ _)
      · exact fun q _ => pow_ne_zero _ (ne_of_gt (Nat.pos_of_mem_primeFactors q.2))
    · rw [dif_neg hp]
      by_cases hpp : p.Prime
      swap
      · apply Nat.factorization_eq_zero_of_not_prime _ hpp
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hp_dvd
      obtain ⟨⟨q, hq⟩, _, hp_dvd_pow⟩ := Prime.exists_mem_finset_dvd hpp.prime hp_dvd
      apply hp
      rw [Nat.mem_primeFactors]
      constructor
      · exact hpp
      · refine ⟨?_, hd.ne_zero⟩
        trans q
        · apply Nat.Prime.dvd_of_dvd_pow hpp hp_dvd_pow
        · apply Nat.dvd_of_mem_primeFactors hq
  have hi_ne_zero : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      i a ha ≠ 0 := by
    intro a ha
    erw [Finset.prod_ne_zero_iff]
    exact fun p _ => pow_ne_zero _ (ne_of_gt (Nat.pos_of_mem_primeFactors p.property))
  have hi : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      i a ha ∈ (d ^ M).divisors.filter (d ∣ ·) := by
    intro a ha
    rw [Finset.mem_filter, Nat.mem_divisors,
      ← Nat.factorization_le_iff_dvd hd.ne_zero (hi_ne_zero a ha),
      ←Nat.factorization_le_iff_dvd (hi_ne_zero a ha) (pow_ne_zero _ hd.ne_zero)]
    constructor; constructor
    · rw [Finsupp.le_iff]; intro p _
      rw [hfact_i a ha]
      by_cases hp : p ∈ d.primeFactors
      · rw [dif_pos hp]
        rw [Nat.factorization_pow, Finsupp.smul_apply]
        simp_rw [Finset.mem_pi, Finset.mem_Icc] at ha
        trans (M • 1)
        · norm_num
          exact (ha p hp).2
        · gcongr
          rw [Nat.mem_primeFactors_of_ne_zero hd.ne_zero] at hp
          rw [←Nat.Prime.dvd_iff_one_le_factorization hp.1 hd.ne_zero]
          exact hp.2
      · rw [dif_neg hp]; norm_num
    · apply pow_ne_zero _ hd.ne_zero
    · rw [Finsupp.le_iff]; intro p hp
      rw [Nat.support_factorization] at hp
      rw [hfact_i a ha]
      rw [dif_pos hp]
      trans 1
      · exact hd.natFactorization_le_one p
      simp_rw [Finset.mem_pi, Finset.mem_Icc] at ha
      exact (ha p hp).1
  have h : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      ∏ p ∈ d.primeFactors.attach, f (p.1 ^ (a p p.2)) = f (i a ha) := by
    intro a ha
    apply symm
    apply hf.isMultiplicative.map_prod
    intro x _ y _ hxy
    simp_rw [Finset.mem_pi, Finset.mem_Icc, Nat.succ_le_iff] at ha
    apply (Nat.coprime_pow_left_iff (ha x x.2).1 ..).mpr
    apply (Nat.coprime_pow_right_iff (ha y y.2).1 ..).mpr
    have hxp := Nat.prime_of_mem_primeFactors x.2
    rw [Nat.Prime.coprime_iff_not_dvd hxp]
    rw [Nat.prime_dvd_prime_iff_eq hxp (Nat.prime_of_mem_primeFactors y.2)]
    exact fun hc => hxy (Subtype.ext hc)
  have i_inj : ∀ a ha b hb, i a ha = i b hb → a = b := by
    intro a ha b hb hiab
    apply_fun Nat.factorization at hiab
    ext p hp
    obtain hiabp := DFunLike.ext_iff.mp hiab p
    rw [hfact_i a ha, hfact_i b hb, dif_pos hp, dif_pos hp] at hiabp
    exact hiabp
  have i_surj : ∀ (b : ℕ), b ∈ (d^M).divisors.filter (d ∣ ·) → ∃ a ha, i a ha = b := by
    intro b hb
    have h : (fun p _ => (Nat.factorization b) p) ∈
        Finset.pi d.primeFactors fun p => Finset.Icc 1 M := by
      rw [Finset.mem_pi]
      intro p hp
      rw [Finset.mem_Icc]
      rw [Finset.mem_filter] at hb
      have hb_ne_zero : b ≠ 0 := ne_of_gt <| Nat.pos_of_mem_divisors hb.1
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      constructor
      · rw [←Nat.Prime.dvd_iff_one_le_factorization hpp hb_ne_zero]
        · exact Trans.trans (Nat.dvd_of_mem_primeFactors hp) hb.2
      · rw [Nat.mem_divisors] at hb
        trans Nat.factorization (d^M) p
        · exact (Nat.factorization_le_iff_dvd hb_ne_zero hb.left.right).mpr hb.left.left p
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
        have : d.factorization p ≤ 1 := by
          apply hd.natFactorization_le_one
        exact (mul_le_iff_le_one_right (Nat.pos_of_ne_zero hM)).mpr this
    use (fun p _ => Nat.factorization b p)
    use h
    apply Nat.eq_of_factorization_eq
    · apply hi_ne_zero _ h
    · exact ne_of_gt <| Nat.pos_of_mem_divisors (Finset.mem_filter.mp hb).1
    intro p
    rw [hfact_i (fun p _ => (Nat.factorization b) p) h p]
    rw [Finset.mem_filter, Nat.mem_divisors] at hb
    by_cases hp : p ∈ d.primeFactors
    · rw [dif_pos hp]
    · rw [dif_neg hp, eq_comm, Nat.factorization_eq_zero_iff, ←or_assoc]
      rw [Nat.mem_primeFactors] at hp
      left
      push Not at hp
      by_cases hpp : p.Prime
      · right
        intro hpb
        exact hd.ne_zero <| hp hpp (hpp.dvd_of_dvd_pow (hpb.trans hb.1.1))
      · left
        exact hpp
  exact Finset.sum_bij i hi i_inj i_surj h

theorem lem0 (P : ℕ) {s : Finset ℕ} (h : ∀ p ∈ s, p ∣ P) (h' : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s, p ∣ P := by
  simp_rw [Nat.prime_iff] at h'
  apply Finset.prod_primes_dvd _ h' h

lemma sqrt_le_self (x : ℝ) (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  refine Iff.mpr Real.sqrt_le_iff ?_
  constructor
  · linarith
  nlinarith [sq_nonneg (x - 1)]

lemma nat_squarefree_dvd_pow (a b N : ℕ) (ha : Squarefree a) (hab : a ∣ b ^ N) :
    a ∣ b := by
  by_cases hb : b = 0
  · rw [hb]
    exact Nat.dvd_zero a
  rw [← Nat.factorization_le_iff_dvd ha.ne_zero hb]
  intro p
  by_cases hp : p.Prime
  · by_cases hpa : p ∣ a
    · have hp_b : p ∣ b := hp.dvd_of_dvd_pow (hpa.trans hab)
      exact (ha.natFactorization_le_one p).trans
        ((hp.dvd_iff_one_le_factorization hb).mp hp_b)
    · rw [Nat.factorization_eq_zero_of_not_dvd hpa]
      exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime a hp]
    exact Nat.zero_le _

theorem selbergBoundingSum_ge_sum_div (s : LPSelbergSieve)
    (hP : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ s.level → p ∣ s.prodPrimes)
    (hnu : CompletelyMultiplicative s.nu) (hnu_nonneg : ∀ n, 0 ≤ s.nu n)
    (hnu_lt : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p < 1) :
    s.selbergBoundingSum ≥
      ∑ m ∈ Finset.Icc 1 (Nat.floor (Real.sqrt s.level)), s.nu m := by
  calc ∑ l ∈ s.prodPrimes.divisors, (if l ^ 2 ≤ s.level then s.selbergTerms l else 0)
     ≥ ∑ l ∈ s.prodPrimes.divisors.filter (fun l : ℕ => l ^ 2 ≤ s.level),
        ∑ m ∈ (l ^ Nat.floor s.level).divisors.filter (l ∣ ·), s.nu m := ?_
   _ ≥ ∑ m ∈ Finset.Icc 1 (Nat.floor (Real.sqrt s.level)), s.nu m := ?_
  · rw [← Finset.sum_filter]
    apply Finset.sum_le_sum
    intro l hl
    rw [Finset.mem_filter, Nat.mem_divisors] at hl
    have hlsq : Squarefree l := Squarefree.squarefree_of_dvd hl.1.1 s.prodPrimes_squarefree
    trans (∏ p ∈ l.primeFactors, ∑ n ∈ Finset.Icc 1 (Nat.floor s.level), s.nu (p ^ n))
    · rw [prod_factors_sum_pow_compMult (Nat.floor s.level) _ s.nu]
      · exact hnu
      · exact hlsq
      · rw [ne_eq, Nat.floor_eq_zero, not_lt]
        exact s.one_le_level
    · rw [s.selbergTerms_apply l]
      apply prod_factors_one_div_compMult_ge _ _ hnu _ _ hlsq
      · intro p hpp hpl
        apply hnu_lt p hpp (Trans.trans hpl hl.1.1)
      · exact hnu_nonneg
  rw [← Finset.sum_biUnion]
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      have hprod_pos : 0 < (∏ p ∈ m.primeFactors, p) := by
        apply Finset.prod_pos
        intro p hp
        exact Nat.pos_of_mem_primeFactors hp
      have hprod_ne_zero : (∏ p ∈ m.primeFactors, p) ^ ⌊s.level⌋₊ ≠ 0 :=
        pow_ne_zero _ (ne_of_gt hprod_pos)
      rw [Finset.mem_biUnion]
      simp_rw [Finset.mem_filter, Nat.mem_divisors]
      rw [Finset.mem_Icc, Nat.le_floor_iff (Real.sqrt_nonneg s.level)] at hm
      have hm_ne_zero : m ≠ 0 := by
        exact ne_of_gt <| Nat.succ_le_iff.mp hm.1
      use ∏ p ∈ m.primeFactors, p
      constructor
      · constructor
        · constructor
          · apply lem0 <;> intro p hp
            · apply hP p <| Nat.prime_of_mem_primeFactors hp
              trans (m : ℝ)
              · norm_cast
                exact Nat.le_of_mem_primeFactors hp
              trans (Real.sqrt s.level)
              · exact hm.2
              apply sqrt_le_self s.level s.one_le_level
            · exact Nat.prime_of_mem_primeFactors hp
          · exact s.prodPrimes_ne_zero
        · rw [← Real.sqrt_le_sqrt_iff (by linarith only [s.one_le_level]), Nat.cast_pow,
            Real.sqrt_sq]
          · trans (m : ℝ)
            · norm_cast
              apply Nat.le_of_dvd (Nat.succ_le_iff.mp hm.1)
              exact Nat.prod_primeFactors_dvd m
            · exact hm.2
          · apply le_of_lt
            norm_cast
      · constructor
        · constructor
          · rw [← Nat.factorization_le_iff_dvd _ hprod_ne_zero, Nat.factorization_pow]
            · intro p
              have hy_mul_prod_nonneg :
                  0 ≤ ⌊s.level⌋₊ * (Nat.factorization (∏ p ∈ m.primeFactors, p)) p :=
                Nat.zero_le _
              trans (Nat.factorization m) p * 1
              · rw [mul_one]
              trans ⌊s.level⌋₊ * Nat.factorization (∏ p ∈ m.primeFactors, p) p
              swap
              · apply le_rfl
              by_cases hpp : p.Prime
              swap
              · rw [Nat.factorization_eq_zero_of_not_prime _ hpp, zero_mul]
                exact hy_mul_prod_nonneg
              by_cases hpdvd : p ∣ m
              swap
              · rw [Nat.factorization_eq_zero_of_not_dvd hpdvd, zero_mul]
                exact hy_mul_prod_nonneg
              apply mul_le_mul
              · trans m
                · exact le_of_lt <| Nat.factorization_lt p hm_ne_zero
                apply Nat.le_floor
                refine le_trans hm.2 ?_
                apply sqrt_le_self _ s.one_le_level
              · rw [← Nat.Prime.pow_dvd_iff_le_factorization hpp <| ne_of_gt hprod_pos,
                  pow_one]
                apply Finset.dvd_prod_of_mem
                rw [Nat.mem_primeFactors]
                exact ⟨hpp, hpdvd, hm_ne_zero⟩
              · norm_num
              · norm_num
            · exact hm_ne_zero
          · exact hprod_ne_zero
        · exact Nat.prod_primeFactors_dvd m
    · intro i _ _
      apply hnu_nonneg
  · intro i hi j hj hij t hti htj x hx
    exfalso
    specialize hti hx
    specialize htj hx
    simp_rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at *
    have h : ∀ i j {n}, i ∣ s.prodPrimes → i ∣ x → x ∣ j ^ n → i ∣ j := by
      intro i j n hiP hix hij
      apply nat_squarefree_dvd_pow i j n (s.squarefree_of_dvd_prodPrimes hiP)
      exact Trans.trans hix hij
    have hidvdj : i ∣ j := by
      apply h i j hi.1.1 hti.2 htj.1.1
    have hjdvdi : j ∣ i := by
      apply h j i hj.1.1 htj.2 hti.1.1
    exact hij <| Nat.dvd_antisymm hidvdj hjdvdi

theorem boundingSum_ge_sum (s : LPSelbergSieve) (hnu : s.nu = (ζ : ArithmeticFunction ℝ).pdiv .id)
    (hP : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ s.level → p ∣ s.prodPrimes) :
    s.selbergBoundingSum ≥
      ∑ m ∈ Finset.Icc 1 (Nat.floor (Real.sqrt s.level)), 1 / (m : ℝ) := by
  trans ∑ m ∈ Finset.Icc 1 (Nat.floor (Real.sqrt s.level)),
      (ζ : ArithmeticFunction ℝ).pdiv .id m
  · rw [← hnu]
    apply selbergBoundingSum_ge_sum_div
    · intro p hpp hple
      apply hP p hpp hple
    · rw [hnu]
      exact CompletelyMultiplicative.zeta.pdiv CompletelyMultiplicative.id
    · intro n
      rw [hnu]
      apply div_nonneg
      · by_cases h : n = 0 <;> simp [h]
      · simp
    · intro p hpp _
      rw [hnu]
      simpa [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.zeta_apply, if_neg hpp.ne_zero, ArithmeticFunction.id_apply,
        one_div] using
          (inv_lt_one_of_one_lt₀ (by norm_cast; exact hpp.one_lt) : (p : ℝ)⁻¹ < 1)
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_Icc] at hm
  simp only [one_div, ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne (show m ≠ 0 by omega), Nat.cast_one,
    ArithmeticFunction.id_apply]

theorem boundingSum_ge_log (s : LPSelbergSieve) (hnu : s.nu = (ζ : ArithmeticFunction ℝ).pdiv .id)
    (hP : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ s.level → p ∣ s.prodPrimes) :
    s.selbergBoundingSum ≥ Real.log (s.level) / 2 := by
  trans (∑ m ∈ Finset.Icc 1 (Nat.floor (Real.sqrt s.level)), 1 / (m : ℝ))
  · exact boundingSum_ge_sum s hnu hP
  trans (Real.log (Real.sqrt s.level))
  · rw [ge_iff_le]
    simp_rw [one_div]
    apply Aux.log_le_sum_inv (Real.sqrt s.level)
    rw [Real.le_sqrt] <;> linarith [s.one_le_level]
  · apply ge_of_eq
    refine Real.log_sqrt ?h.hx
    linarith [s.one_le_level]

theorem primeSieve_boundingSum_ge (N : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    (primeSieve N y hy).selbergBoundingSum ≥ Real.log y / 2 := by
  apply boundingSum_ge_log
  · rfl
  · intro p hpp hp
    erw [prime_dvd_primorial_iff _ _ hpp]
    exact Nat.le_floor hp

theorem card_range_filter_dvd (N d : ℕ) (hd : d ≠ 0) :
    ((Finset.range N).filter (d ∣ ·)).card = Nat.ceil ((N : ℝ) / d) := by
  let f : (i : ℕ) → i < (Nat.ceil ((N : ℝ) / d)) → ℕ := fun i _ => d * i
  apply Finset.card_eq_of_bijective f
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    use k / d
    constructor
    · refine Nat.mul_div_cancel' hk.2
    · rw [Nat.lt_ceil]
      rw [Nat.cast_div hk.2 (by exact_mod_cast hd : (d : ℝ) ≠ 0)]
      exact div_lt_div_of_pos_right
        (by exact_mod_cast hk.1 : (k : ℝ) < N)
        (by norm_cast; exact Nat.pos_of_ne_zero hd)
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range]
    rw [Nat.lt_ceil, lt_div_iff₀ (by norm_cast; exact Nat.pos_of_ne_zero hd : (0 : ℝ) < d),
      mul_comm] at hk
    norm_cast at hk
    exact ⟨hk, dvd_mul_right ..⟩
  · exact fun _ _ _ _ hij => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd) hij

theorem primeSieve_multSum_eq (N : ℕ) (y : ℝ) (hy : 1 ≤ y) (d : ℕ) (hd : d ≠ 0) :
    (primeSieve N y hy).multSum d = Nat.ceil (((N + 1 : ℕ) : ℝ) / d) := by
  unfold primeSieve
  simp only [LPSieve.multSum, Finset.sum_boole, Nat.cast_inj]
  apply card_range_filter_dvd
  exact hd


theorem primeSieve_rem_eq (N : ℕ) (y : ℝ) (hy : 1 ≤ y) (d : ℕ) (hd : d ≠ 0) :
    (primeSieve N y hy).rem d = Nat.ceil (((N + 1 : ℕ) : ℝ) / d) - N / d := by
  unfold LPSieve.rem
  rw [primeSieve_multSum_eq (hd := hd)]
  unfold primeSieve
  rw [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply, if_neg hd]
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.id_apply]
  ring_nf

theorem primeSieve_abs_rem_eq (N : ℕ) (y : ℝ) (hy : 1 ≤ y) (d : ℕ) (hd : d ≠ 0) :
    |(primeSieve N y hy).rem d| ≤ 2 := by
  rw [primeSieve_rem_eq (hd:=hd), abs_le]
  constructor
  · apply le_sub_right_of_add_le
    trans ((N + 1) / ↑d)
    · rw [add_comm, add_div]
      have : 0 ≤ 1/(d:ℝ) := by
        norm_num
      linarith
    simpa [Nat.cast_add, Nat.cast_one] using Nat.le_ceil (((N + 1 : ℕ) : ℝ) / d)
  · apply sub_left_le_of_le_add
    trans ↑(Nat.floor ((N+1)/d:ℝ)+1)
    · norm_cast
      apply Nat.ceil_le_floor_add_one
    trans ((N+1)/d+1:ℝ)
    · push_cast
      have hfloor : (↑⌊(↑N + 1) / (d : ℝ)⌋₊ : ℝ) ≤ (↑N + 1) / (d : ℝ) := by
        exact Nat.floor_le
          (div_nonneg (by norm_cast; norm_num) (by norm_num) :
            0 ≤ ((↑N + 1) / (d : ℝ)))
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hfloor 1
    have : 1 / (d : ℝ) ≤ 1 := by
      rw [one_div]
      apply inv_le_one_of_one_le₀
      norm_cast
      linarith [Nat.pos_of_ne_zero hd]
    rw [add_div]
    linarith

open ArithmeticFunction

theorem rem_sum_le_of_const (s : LPSelbergSieve) (C : ℝ) (hrem : ∀ d > 0, |s.rem d| ≤ C) :
    ∑ d ∈ s.prodPrimes.divisors,
        (if (d : ℝ) ≤ s.level then (3 : ℝ) ^ ω d * |s.rem d| else 0)
      ≤ C * s.level * (1 + Real.log s.level) ^ 3 := by
  rw [← Finset.sum_filter]
  trans (∑ d ∈ Finset.filter (fun d : ℕ => ↑d ≤ s.level)
      (s.toLPSieve.prodPrimes.divisors), 3 ^ ω d * C)
  · gcongr with d hd
    · norm_cast
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    apply hrem d
    apply Nat.pos_of_ne_zero
    apply ne_zero_of_dvd_ne_zero hd.1.2 hd.1.1
  rw [← Finset.sum_mul, mul_comm, mul_assoc]
  gcongr
  · linarith [abs_nonneg <| s.rem 1, hrem 1 (by norm_num)]
  simp_rw [Nat.cast_pow]
  push_cast
  rw [Finset.sum_filter]
  apply Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow (hx := s.one_le_level)
  apply LPSieve.prodPrimes_squarefree

theorem primeSieve_rem_sum_le (N : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    ∑ d ∈ (primeSieve N y hy).prodPrimes.divisors,
        (if (d : ℝ) ≤ y then (3 : ℝ) ^ ω d * |(primeSieve N y hy).rem d| else 0)
      ≤ 2 * y * (1 + Real.log y) ^ 3 := by
  apply rem_sum_le_of_const
  intro d hd
  push_cast
  apply primeSieve_abs_rem_eq
  omega

theorem pi_le_of_y (N : ℕ) (y : ℝ) (hy_lt : 1 < y) :
    π N ≤ 2 * N / Real.log y + 3 * y * (1 + Real.log y) ^ 3 := by
  have hy : 1 ≤ y := le_of_lt hy_lt
  trans ((primeSieve N y hy).siftedSum + y)
  · apply pi_le_siftedSum
  suffices LPSieve.siftedSum (primeSieve N y hy).toLPSieve ≤
      2 * N / Real.log y + 2 * y * (1 + Real.log y) ^ 3 by
    push_cast at *
    have : y * (1 : ℝ) ≤ y * (1 + Real.log y) ^ 3 := by
      have hy_nonneg : 0 ≤ y := by linarith
      have hbase : (1 : ℝ) ≤ 1 + Real.log y := by linarith [Real.log_nonneg hy]
      have hpow : (1 : ℝ) ≤ (1 + Real.log y)^3 := one_le_pow₀ hbase
      have hdiff : (0 : ℝ) ≤ y * ((1 + Real.log y)^3 - 1) :=
        mul_nonneg hy_nonneg (sub_nonneg.mpr hpow)
      nlinarith
    rw [mul_one] at this
    linarith
  trans ((primeSieve N y hy).totalMass / (primeSieve N y hy).selbergBoundingSum) +
      ∑ d ∈ (primeSieve N y hy).prodPrimes.divisors,
        (if (d : ℝ) ≤ y then (3 : ℝ) ^ ω d * |(primeSieve N y hy).rem d| else 0)
  · apply (LPSelbergSieve.selberg_bound_simple)
  gcongr (?_ + ?_)
  · trans (N / (Real.log y / 2))
    · gcongr (?_ / ?_)
      · linarith [Real.log_pos hy_lt]
      · rfl
      rw [←ge_iff_le]
      apply primeSieve_boundingSum_ge
    rw [div_eq_mul_inv, inv_div, ←mul_div_assoc, mul_comm]
    push_cast
    rfl
  · apply primeSieve_rem_sum_le

lemma primeCounting_zero :
  π 0 = 0 := by decide
lemma primeCounting_one :
  π 1 = 0 := by decide

theorem loglog_nonneg (x : ℝ) (hx : 3 ≤ x) :
    0 ≤ Real.log (Real.log x) := by
  apply Real.log_nonneg
  rw [← Real.log_exp 1]
  gcongr
  trans 3
  · have := Real.exp_one_lt_d9
    trans (2.7182818286)
    · linarith [Real.exp_one_lt_d9]
    · norm_num
  · exact hx

theorem loglog_bigO_log :
    (fun N : ℕ => Real.log (Real.log N)) =O[Filter.atTop] (fun N : ℕ => Real.log N) := by
  apply Asymptotics.IsBigO.of_bound'
  rw [Filter.eventually_iff, Filter.mem_atTop_sets]
  use 10
  intro x hx; simp only [Real.norm_eq_abs, Set.mem_setOf_eq]
  rw [ge_iff_le, ←Nat.cast_le (α:=ℝ)] at hx
  conv at hx => {lhs; norm_num}
  rw [le_abs]; left
  rw [abs_le]
  constructor
  · linarith only [Real.log_natCast_nonneg x, loglog_nonneg x (by linarith)]
  linarith [Real.log_le_sub_one_of_pos (x:= Real.log x) (Real.log_pos (by linarith))]


theorem _lemma5 : (Real.log ∘ Real.log) =o[Filter.atTop] Real.log := by
  simpa [Function.comp_def] using
    Asymptotics.IsLittleO.comp_tendsto Real.isLittleO_log_id_atTop Real.tendsto_log_atTop

theorem _lemma4 :
    (fun N : ℕ => Real.log (Real.log N)) =o[Filter.atTop] (fun N : ℕ => Real.log N) := by
  exact Asymptotics.IsLittleO.comp_tendsto _lemma5 tendsto_natCast_atTop_atTop

theorem _lemma3 (c : ℝ) :
    (fun N : ℕ => Real.log N) =O[Filter.atTop]
      (fun N : ℕ => Real.log N - c * Real.log (Real.log N)) := by
  exact (_lemma4.const_mul_left c).right_isBigO_sub

theorem _lemma2 (c : ℝ) :
    (fun N : ℕ => Real.log N + c * Real.log (Real.log N)) =O[Filter.atTop]
      (fun N : ℕ => Real.log N) := by
  apply Asymptotics.IsBigO.add
  · exact Asymptotics.isBigO_refl _ _
  apply Asymptotics.IsBigO.const_mul_left
  apply loglog_bigO_log

theorem pi_le_id_div_log_of_eps (N : ℕ) (ε : ℝ) (_hε_pos : ε > 0) (hε : ε < 1) :
    π N ≤ 2 / (1 - ε) * N / Real.log N +
      3 * (N : ℝ) ^ (1 - ε) * (1 + (1 - ε) * Real.log N) ^ 3 := by
  by_cases hN : N = 0
  · rw [hN, primeCounting_zero]
    norm_num
    rw [Real.zero_rpow (by linarith : 1 - ε ≠ 0)]
  by_cases hN_one : N = 1
  · rw [hN_one, primeCounting_one]
    norm_num
  · have : 1 < (N : ℝ) ^ (1 - ε) := by
      apply Real.one_lt_rpow
      · norm_cast
        rw [Nat.one_lt_iff_ne_zero_and_ne_one]
        exact ⟨hN, hN_one⟩
      · linarith
    have h := pi_le_of_y N ((N : ℝ) ^ (1 - ε)) this
    rw [Real.log_rpow (by norm_cast; exact Nat.pos_of_ne_zero hN)] at h
    apply le_trans h
    gcongr (?_ + ?_)
    apply le_of_eq
    field_simp
    ring_nf

theorem pi_le_id_div_log (N : ℕ) :
    π N ≤ (4 : ℝ) * N / Real.log N +
      (3 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) * (1 + (1 / 2) * Real.log N) ^ 3 := by
  have h := pi_le_id_div_log_of_eps N (1 / 2) (by linarith) (by linarith)
  apply le_trans h
  gcongr ?_ + ?_
  · norm_num
  · norm_num

theorem _lemma0 :
    (fun N : ℕ => 4 * N / Real.log N) =O[Filter.atTop]
      fun N : ℕ => N / Real.log N := by
  simp_rw [mul_div_assoc]
  apply Asymptotics.IsBigO.const_mul_left
  exact Asymptotics.isBigO_refl _ _

theorem _lemma7 :
    ((fun x : ℝ => 1 + 1 / 2 * Real.log x) ∘ fun N : ℕ => (N : ℝ)) =O[Filter.atTop]
      ((fun x : ℝ => x ^ (1 / 12 : ℝ)) ∘ fun N : ℕ => ↑N) := by
  apply Asymptotics.IsBigO.comp_tendsto (l := Filter.atTop)
  · apply Asymptotics.IsBigO.add
    · apply Asymptotics.IsBigO.of_bound'
      rw [Filter.eventually_iff, Filter.mem_atTop_sets]
      use 1
      intro x hx
      simp only [norm_one, Real.norm_eq_abs, Set.mem_setOf_eq]
      rw [Real.abs_rpow_of_nonneg (by linarith)]
      apply Real.one_le_rpow
      · rw [le_abs]
        left
        linarith
      · norm_num
    · apply (isLittleO_log_rpow_atTop (by norm_num)).isBigO.const_mul_left _
  · exact tendsto_natCast_atTop_atTop

theorem _lemma8 :
    ((fun x : ℝ => x ^ (1 / 2 : ℝ) * x ^ (1 / 4 : ℝ)) ∘ fun N : ℕ => (N : ℝ))
      =O[Filter.atTop] ((fun x : ℝ => x / Real.log x) ∘ fun N : ℕ => ↑N) := by
  apply Asymptotics.IsBigO.comp_tendsto (l := Filter.atTop)
  · simp_rw [div_eq_mul_inv]
    trans (fun x => x * x ^ (-1 / 4 : ℝ))
    · apply Asymptotics.IsBigO.of_bound'
      rw [Filter.eventually_iff, Filter.mem_atTop_sets]
      use 1
      intro x hx
      simp only [norm_mul, Real.norm_eq_abs, Set.mem_setOf_eq]
      rw [← abs_mul, ← abs_mul]
      apply le_of_eq
      apply congr_arg
      trans (x ^ (1 : ℝ) * x ^ (-1 / 4 : ℝ))
      · rw [← Real.rpow_add (by linarith), ← Real.rpow_add (by linarith)]
        norm_num
      · rw [Real.rpow_one]
    · apply Asymptotics.IsBigO.mul
      · apply Asymptotics.isBigO_refl
      trans (fun x => (x ^ (1 / 4 : ℝ))⁻¹)
      · apply Asymptotics.IsBigO.of_bound'
        rw [Filter.eventually_iff, Filter.mem_atTop_sets]
        use 1
        intro x hx
        simp only [Real.norm_eq_abs, Set.mem_setOf_eq]
        rw [neg_div, Real.rpow_neg (by linarith : 0 ≤ x), abs_inv]
      apply Asymptotics.IsBigO.inv_rev
      · apply (isLittleO_log_rpow_atTop (by norm_num)).isBigO
      · rw [Filter.eventually_iff, Filter.mem_atTop_sets]
        use 100
        intro x hx
        rw [Set.mem_setOf_eq]
        intro hlog
        exfalso
        have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
        linarith
  · exact tendsto_natCast_atTop_atTop

theorem _lemma1 :
    (fun N : ℕ => (3 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) *
      (1 + (1 / 2) * Real.log N) ^ 3) =O[Filter.atTop]
      fun N : ℕ => N / Real.log N := by
  simp_rw [mul_assoc]
  apply Asymptotics.IsBigO.const_mul_left
  trans (fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ))
  · have h0 : (fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ)) =O[Filter.atTop]
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ)) := by
      apply Asymptotics.isBigO_refl
    have h1 : (fun N : ℕ => (1 + 1 / 2 * Real.log N) ^ 3) =O[Filter.atTop]
        (fun N : ℕ => (N : ℝ) ^ (1 / 4 : ℝ)) := by
      trans (fun N : ℕ => ((N : ℝ) ^ (1 / 12 : ℝ)) ^ 3)
      · apply Asymptotics.IsBigO.pow
        apply _lemma7
      · simp_rw [← Real.rpow_natCast]
        conv => { lhs; ext N; rw [← Real.rpow_mul (Nat.cast_nonneg N)] }
        norm_num
        apply Asymptotics.isBigO_refl
    apply h0.mul h1
  · apply _lemma8

lemma _lemma9 :
    (fun N : ℕ => (π N : ℝ)) =O[Filter.atTop]
      (fun N : ℕ => 4 * N / Real.log N +
        3 * (N : ℝ) ^ (1 / 2 : ℝ) * (1 + (1 / 2) * Real.log N) ^ 3) := by
  apply Asymptotics.isBigO_of_le
  intro N
  simp_rw [RCLike.norm_natCast, Nat.cast_ofNat, Real.norm_eq_abs]
  apply le_trans _ (le_abs_self _)
  apply pi_le_id_div_log N


theorem pi_ll :
    (fun N : ℕ => (π N : ℝ)) =O[Filter.atTop] (fun N : ℕ => N / Real.log N) := by
  trans (fun N : ℕ => 4 * N / Real.log N +
      3 * (N : ℝ) ^ (1 / 2 : ℝ) * (1 + (1 / 2) * Real.log N) ^ 3)
  · exact _lemma9
  · apply Asymptotics.IsBigO.add
    · simp_rw [mul_div_assoc]
      apply Asymptotics.IsBigO.const_mul_left
      apply Asymptotics.isBigO_refl
    · apply _lemma1

theorem pi_le_mul : ∃ N C, ∀ n ≥ N, π n ≤ C*n/Real.log n := by
  obtain ⟨C, h⟩ := pi_ll.bound
  rw [Filter.eventually_iff, Filter.mem_atTop_sets] at h
  obtain ⟨N, h⟩ := h
  simp only [ge_iff_le, RCLike.norm_natCast, norm_div, Real.norm_eq_abs, Set.mem_setOf_eq] at h
  use N
  use C
  intro n
  specialize h n
  rw [abs_of_nonneg (Real.log_natCast_nonneg n)] at h
  intro hnN
  rw [mul_div_assoc]
  apply h (by linarith only [hnN])

end PrimeUpperBound
end



-- === Inlined from SelbergSieve4.Applications.BrunTitchmarsh ===
/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

/-!
# LeanPool.SelbergSieve4.Applications.BrunTitchmarsh
-/

noncomputable section
open PrimeUpperBound
open scoped Nat ArithmeticFunction.zeta ArithmeticFunction.Moebius ArithmeticFunction.omega
  BigOperators

namespace BrunTitchmarsh

/-- LPSieve that removes primes at most `z` from the interval `[x, x + y]`. -/
def primeInterSieve (x y z : ℝ) (hz : 1 ≤ z) : LPSelbergSieve := {
  support := Finset.Icc (Nat.ceil x) (Nat.floor (x+y))
  prodPrimes := primorial (Nat.floor z)
  prodPrimes_squarefree := primorial_squarefree _
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := y
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ => by
    simp[if_neg hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ => by
    simpa [hp.ne_zero] using
      (inv_lt_one_of_one_lt₀ (by norm_cast; exact hp.one_lt) : (p : ℝ)⁻¹ < 1)
  level := z
  one_le_level := hz
}

/-- Number of primes in the real interval `[a, b]`. -/
def primesBetween (a b : ℝ) : ℕ :=
  (Finset.Icc (Nat.ceil a) (Nat.floor b)).filter (Nat.Prime) |>.card

theorem primesBetween_eq_ncard {a b : ℝ} (hb : 0 ≤ b) :
    primesBetween a b = Set.ncard {p : ℕ | a ≤ p ∧ p ≤ b ∧ p.Prime} := by
  unfold primesBetween
  rw [← Set.ncard_coe_finset]
  congr
  ext p
  simp only [Finset.coe_filter, Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff hb,
    Set.mem_setOf_eq, and_assoc]

variable (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 1 ≤ z)

open Classical in
theorem siftedSum_eq_card :
    (primeInterSieve x y z hz).siftedSum =
      ((Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
        (fun d => ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card := by
  apply PrimeUpperBound.siftedSum_eq
  · exact fun _ _ => rfl
  · exact hz
  · rfl

open Classical in
theorem primesBetween_subset :
  (Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter (Nat.Prime) ⊆
    (Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
      (fun d => ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d) ∪
    (Finset.Icc 1 (Nat.floor z)) := by
  intro p hp_mem
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp_mem
  rw [Finset.mem_union]
  rcases hp_mem with ⟨hp_range, hp⟩
  by_cases hpz : p ≤ z
  · right
    exact Finset.mem_Icc.mpr ⟨hp.one_le, (Nat.le_floor_iff (by linarith)).mpr hpz⟩
  · left
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hp_range, ?_⟩
    intro q hq hqz
    rw[hp.dvd_iff_eq (hq.ne_one)]
    rintro rfl
    exact hpz hqz

theorem primesBetween_le_siftedSum_add :
    primesBetween x (x+y) ≤ (primeInterSieve x y z hz).siftedSum + z := by
  classical
  trans ↑(((Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
      (fun d => ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d)) ∪
        (Finset.Icc 1 (Nat.floor z))).card
  · rw[primesBetween]
    norm_cast
    apply Finset.card_le_card
    apply primesBetween_subset
  trans ↑((Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
      (fun d => ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card
    + ↑(Finset.Icc 1 (Nat.floor z)).card
  · norm_cast
    apply Finset.card_union_le
  rw[siftedSum_eq_card]
  gcongr
  rw[Nat.card_Icc]
  simp only [add_tsub_cancel_right]
  apply Nat.floor_le
  linarith

section Remainder

theorem Ioc_filter_dvd_eq (d a b : ℕ) (hd : d ≠ 0) :
  Finset.filter (fun x => d ∣ x) (Finset.Ioc a b) =
    Finset.image (fun x => x * d) (Finset.Ioc (a / d) (b / d)) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image]
  constructor
  · intro hn
    use  n/d
    rcases hn with ⟨⟨han, hnb⟩, hd⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Nat.div_lt_div_of_lt_of_dvd hd han
    · exact Nat.div_le_div_right hnb
    · exact Nat.div_mul_cancel hd
  · rintro ⟨r, ⟨ha, ha'⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine (Nat.div_lt_iff_lt_mul ?_).mp ha
      omega
    · exact Nat.mul_le_of_le_div d r b ha'
    · exact Nat.dvd_mul_left d r

theorem card_Ioc_filter_dvd (d a b : ℕ) (hd : d ≠ 0) :
    (Finset.filter (fun x => d ∣ x) (Finset.Ioc a b)).card = b / d - a / d  := by
  rw [Ioc_filter_dvd_eq _ _ _ hd]
  rw [Finset.card_image_of_injective _ <| mul_left_injective₀ hd]
  simp

theorem multSum_eq (hx : 0 < x) (d : ℕ) (hd : d ≠ 0) :
    (primeInterSieve x y z hz).multSum d = ↑(⌊x + y⌋₊ / d - (⌈x⌉₊ - 1) / d) := by
  unfold LPSieve.multSum
  rw[primeInterSieve]
  simp only [Finset.sum_boole, Nat.cast_inj]
  trans ↑(Finset.Ioc (Nat.ceil x - 1) (Nat.floor (x+y)) |>.filter (d ∣ ·) |>.card)
  · rw [← Finset.Icc_succ_left_eq_Ioc]
    congr
    simpa [Nat.pred_eq_sub_one] using
      (Nat.succ_pred_eq_of_pos (Nat.ceil_pos.mpr hx)).symm
  · rw[card_Ioc_filter_dvd _ _ _ hd]

theorem rem_eq (hx : 0 < x) (d : ℕ) (hd : d ≠ 0) :
    (primeInterSieve x y z hz).rem d =
      ↑(⌊x + y⌋₊ / d - (⌈x⌉₊ - 1) / d) - (↑d)⁻¹ * y := by
  unfold LPSieve.rem
  rw[multSum_eq x y z hz hx d hd]
  simp [primeInterSieve, if_neg hd]

theorem natCeil_le_self_add_one (x : ℝ) (hx : 0 ≤ x) : Nat.ceil x ≤ x + 1 := by
  trans Nat.floor x + 1
  · norm_cast
    exact Nat.ceil_le_floor_add_one x
  gcongr
  apply Nat.floor_le hx

theorem floor_approx (x : ℝ) (hx : 0 ≤ x) : ∃ C, |C| ≤ 1 ∧  ↑((Nat.floor x)) = x + C := by
  use ↑(Nat.floor x) - x
  constructor
  · rw[abs_le]
    constructor
    · simp only [neg_le_sub_iff_le_add]
      linarith [Nat.lt_floor_add_one x]
    · simp only [tsub_le_iff_right]
      linarith [Nat.floor_le hx]
  · ring

theorem ceil_approx (x : ℝ) (hx : 0 ≤ x) : ∃ C, |C| ≤ 1 ∧  ↑((Nat.ceil x)) = x + C := by
  use ↑(Nat.ceil x) - x
  constructor
  · rw[abs_le]
    constructor
    · simp only [neg_le_sub_iff_le_add]
      linarith [Nat.le_ceil x]
    · simp only [tsub_le_iff_right]
      rw[add_comm]
      exact natCeil_le_self_add_one x hx
  · ring

theorem nat_div_approx (a b : ℕ) : ∃ C, |C| ≤ 1 ∧ ↑(a/b) = (a/b : ℝ) + C := by
  rw[←Nat.floor_div_eq_div (K:=ℝ)]
  apply floor_approx (a/b:ℝ) (by positivity)

theorem floor_div_approx (x : ℝ) (hx : 0 ≤ x) (d : ℕ) :
    ∃ C, |C| ≤ 2 ∧  ↑((Nat.floor x)/d) = x / d + C := by
  by_cases hd : d = 0
  · simp [hd]
  obtain ⟨C₁, hC₁_le, hC₁⟩ := nat_div_approx (Nat.floor x) d
  obtain ⟨C₂, hC₂_le, hC₂⟩ := floor_approx x hx
  rw[hC₁, hC₂]
  use  C₁ + C₂/d
  refine ⟨?_, by ring⟩
  have : |C₁ + C₂/d| ≤ |C₁| + |C₂/d| := abs_add_le C₁ (C₂ / ↑d)
  have : |C₂/d| ≤ |C₂| := by
    rw[abs_div]
    apply div_le_self
    · exact abs_nonneg C₂
    · simp only [Nat.abs_cast, Nat.one_le_cast]
      omega
  linarith

theorem abs_rem_le (hx : 0 < x) (hy : 0 < y) {d : ℕ} (hd : d ≠ 0) :
    |(primeInterSieve x y z hz).rem d| ≤ 5 := by
  rw[rem_eq x y z hz hx _ hd]
  have hpush : ↑(⌊x + y⌋₊ / d - (⌈x⌉₊ - 1) / d) =
      (↑(⌊x + y⌋₊ / d) - ↑((⌈x⌉₊ - 1) / d) : ℝ) := by
    rw [Nat.cast_sub]
    gcongr
    rw[Nat.le_floor_iff]
    · rw[←add_le_add_iff_right 1]
      norm_cast
      rw [Nat.sub_add_cancel]
      · linarith [natCeil_le_self_add_one x (le_of_lt hx)]
      · simp [hx]
    · linarith
  rw[hpush]
  obtain ⟨C₁, hC₁_le, hC₁⟩ := floor_div_approx (x + y) (by linarith) d
  obtain ⟨C₂, hC₂_le, hC₂⟩ := nat_div_approx (Nat.ceil x - 1) d
  obtain ⟨C₃, hC₃_le, hC₃⟩ := ceil_approx (x) (by linarith)
  rw[hC₁, hC₂, Nat.cast_sub, hC₃]
  · ring_nf
    have hinv : |(d:ℝ)⁻¹| ≤ 1 := by
      rw[abs_inv]
      simp only [Nat.abs_cast]
      apply Nat.cast_inv_le_one
    have hmul : |(↑d)⁻¹*C₃| ≤ |C₃| := by
      rw[inv_mul_eq_div, abs_div]
      apply div_le_self
      · exact abs_nonneg _
      · simp only [Nat.abs_cast, Nat.one_le_cast]
        omega
    calc
      |(↑d)⁻¹ - (↑d)⁻¹ * C₃ + C₁ - C₂|
          = |(↑d)⁻¹ - (↑d)⁻¹ * C₃ + (C₁ - C₂)| := by ring
      _
        ≤ |(↑d)⁻¹ - (↑d)⁻¹*C₃| + |C₁ - C₂| := abs_add_le _ _
      _ ≤ (|(↑d)⁻¹| + |(↑d)⁻¹*C₃|) + (|C₁| + |C₂|) := by
        exact add_le_add (abs_sub _ _) (abs_sub _ _)
      _ ≤ (1 + |C₃|) + (2 + 1) := by
        gcongr
      _ ≤ 5 := by
        linarith
  · simp [hx]

end Remainder

theorem boudingSum_ge :
    (primeInterSieve x y z hz).selbergBoundingSum ≥ Real.log z / 2 := by
  apply boundingSum_ge_log
  · rfl
  · intro p hpp hp
    erw [prime_dvd_primorial_iff]
    · exact Nat.le_floor hp
    · exact hpp

theorem primeSieve_rem_sum_le (hx : 0 < x) (hy : 0 < y) :
    ∑ d ∈ (primeInterSieve x y z hz).prodPrimes.divisors,
      (if (d : ℝ) ≤ z then (3:ℝ) ^ ω d * |(primeInterSieve x y z hz).rem d| else 0)
      ≤ 5 * z * (1+Real.log z)^3 := by
  apply rem_sum_le_of_const (primeInterSieve x y z hz) 5 ?_
  intro d hd
  exact abs_rem_le x y z hz hx hy (ne_of_gt hd)

theorem siftedSum_le (hx : 0 < x) (hy : 0 < y) (hz : 1 < z) :
    (primeInterSieve x y z (le_of_lt hz)).siftedSum ≤
      2 * y / Real.log z + 5 * z * (1+Real.log z)^3  := by
  apply le_trans (LPSelbergSieve.selberg_bound_simple ..)
  calc _ ≤ y / (Real.log z / 2) + 5 * z * (1+Real.log z)^3 := ?_
       _ = _ := by ring
  gcongr
  · linarith [Real.log_pos hz]
  · rfl
  · apply boudingSum_ge
  · apply primeSieve_rem_sum_le x y z (le_of_lt hz) hx hy

theorem primesBetween_le (hx : 0 < x) (hy : 0 < y) (hz : 1 < z) :
    primesBetween x (x+y) ≤ 2 * y / Real.log z + 6 * z * (1+Real.log z)^3 := by
  have : z ≤ z * (1+Real.log z)^3 := by
    apply le_mul_of_one_le_right
    · linarith
    apply one_le_pow₀
    linarith [Real.log_nonneg (by linarith)]
  linarith [siftedSum_le x y z hx hy hz,
    primesBetween_le_siftedSum_add x y z (le_of_lt hz)]

end BrunTitchmarsh

end -- close `noncomputable section` opened in Applications.BrunTitchmarsh



-- === Inlined from SelbergSieve4.MainResults ===
/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

/-!
# LeanPool.SelbergSieve4.MainResults
-/

section LPSieveMainResults

open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius ArithmeticFunction.omega
  LPSieve Nat Nat.Prime
end LPSieveMainResults



-- === Inlined from Mertens ===

namespace Mertens

open scoped BigOperators Topology
open Nat Real Finset Filter MeasureTheory ArithmeticFunction


noncomputable section

/-! ### Step 1: Von Mangoldt sum identity

Using ∑_{d|n} Λ(d) = log n, we get:
∑_{n=1}^{N} Λ(n) · ⌊N/n⌋ = ∑_{n=1}^{N} log n = log(N!)
-/

/-
∑_{n=1}^{N} log n = log(N!).
-/
lemma sum_log_eq_log_factorial (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) = Real.log (N ! : ℝ) := by
  erw [ Finset.sum_Ico_eq_sum_range ];
  rw [ ← Real.log_prod ] <;> norm_cast <;> norm_num [ add_comm, Finset.prod_range_succ' ]

/-
∑_{n=1}^{N} Λ(n) · ⌊N/n⌋ = log(N!).
This follows from ∑_{d|n} Λ(d) = log n by swapping the order of summation.
-/
lemma sum_vonMangoldt_floor (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) * (N / n : ℕ) = Real.log (N ! : ℝ) := by
  -- By interchanging the order of summation, we get:
  have h_interchange : ∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors, (Λ d : ℝ)) = ∑ d ∈ Finset.Icc 1 N, (Λ d : ℝ) * (N / d : ℕ) := by
    -- By Fubini's theorem, we can interchange the order of summation.
    have h_fubini : ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, (Λ d : ℝ) = ∑ d ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, (if d ∣ n then (Λ d : ℝ) else 0) := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl ];
      simp +contextual [ Finset.sum_ite, Nat.mem_divisors ];
      intro x hx₁ hx₂; rw [ ← Finset.sum_subset ( show x.divisors ⊆ Finset.filter ( fun d => d ∣ x ) ( Finset.Icc 1 N ) from fun y hy => Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ Nat.pos_of_mem_divisors hy, Nat.le_trans ( Nat.divisor_le hy ) hx₂ ⟩, Nat.dvd_of_mem_divisors hy ⟩ ) ] ; aesop;
    simp_all +decide [ Finset.sum_ite ];
    refine' Finset.sum_congr rfl fun x hx => _;
    rw [ mul_comm, show Finset.filter ( fun y => x ∣ y ) ( Finset.Icc 1 N ) = Finset.image ( fun y => x * y ) ( Finset.Icc 1 ( N / x ) ) from ?_, Finset.card_image_of_injective _ fun y z h => mul_left_cancel₀ ( by linarith [ Finset.mem_Icc.mp hx ] ) h ] ; aesop;
    ext y; simp [Finset.mem_image];
    exact ⟨ fun h => ⟨ y / x, ⟨ Nat.div_pos ( Nat.le_of_dvd h.1.1 h.2 ) ( Finset.mem_Icc.mp hx |>.1 ), Nat.div_le_div_right h.1.2 ⟩, Nat.mul_div_cancel' h.2 ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by nlinarith [ Finset.mem_Icc.mp hx |>.1 ], by nlinarith [ Finset.mem_Icc.mp hx |>.2, Nat.div_mul_le_self N x ] ⟩, by simp +decide ⟩ ⟩;
  simp_all +decide [ ArithmeticFunction.vonMangoldt_sum ];
  exact h_interchange ▸ sum_log_eq_log_factorial N

/-! ### Step 2: Stirling-type bound for log(N!)

We need log(N!) = N log N - N + O(log N).
-/

/-
log(N!) ≤ N · log N. This is a weak upper bound.
-/
lemma log_factorial_le (N : ℕ) (hN : 1 ≤ N) :
    Real.log (N ! : ℝ) ≤ N * Real.log N := by
  rw [ ← Real.log_pow ] ; gcongr ; norm_cast ; induction hN <;> simp_all +decide [ Nat.factorial_succ, pow_succ' ];
  exact le_trans ‹_› ( by gcongr ; linarith )

/-
log(N!) ≥ N · log N - N. This follows from Stirling or direct estimation.
-/
lemma log_factorial_ge (N : ℕ) (hN : 1 ≤ N) :
    N * Real.log N - N ≤ Real.log (N ! : ℝ) := by
  induction hN <;> simp_all +decide [ Nat.factorial_succ ];
  rw [ Real.log_mul ( by positivity ) ( by positivity ), add_mul ];
  have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( ( Nat.cast:ℕ →ℝ ) ‹_› + 1 ) / ( Nat.cast:ℕ →ℝ ) ‹_› );
  rw [ Real.log_div ] at this <;> first | positivity | ring_nf at * ; nlinarith [ mul_inv_cancel₀ ( by positivity : ( ( Nat.cast:ℕ →ℝ ) ‹_› ) ≠ 0 ) ] ;

/-! ### Step 3: ∑ Λ(n)/n = log N + O(1) -/

/-
∑_{n=1}^{N} Λ(n)/n is bounded between log N - C and log N + C.
-/
lemma vonMangoldt_reciprocal_bounded :
    ∃ C : ℝ, ∀ N : ℕ, N ≥ 2 →
      |∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) / n - Real.log N| ≤ C := by
  use Real.log 4 + 5;
  intro N hN
  have h_sum : ∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) * (N / n : ℕ) = Real.log (N ! : ℝ) := by
    convert sum_vonMangoldt_floor N using 1;
  -- Write ⌊N/n⌋ = N/n - frac(N/n) where 0 ≤ frac < 1. Then:
  have h_frac : ∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) * (N / n : ℕ) = N * ∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) / n - ∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) * (Int.fract (N / n : ℝ)) := by
    rw [ Finset.mul_sum _ _ _ ];
    rw [ ← Finset.sum_sub_distrib ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rw [ Int.fract ] ; ring;
    rw [ show ⌊ ( N : ℝ ) * ( x : ℝ ) ⁻¹⌋ = N / x from Int.floor_eq_iff.mpr ⟨ by rw [ ← div_eq_mul_inv ] ; rw [ le_div_iff₀ ( Nat.cast_pos.mpr <| Finset.mem_Icc.mp hx |>.1 ) ] ; norm_cast; linarith [ Nat.div_mul_le_self N x ], by rw [ ← div_eq_mul_inv ] ; rw [ div_lt_iff₀ ( Nat.cast_pos.mpr <| Finset.mem_Icc.mp hx |>.1 ) ] ; norm_cast; linarith [ Nat.div_add_mod N x, Nat.mod_lt N ( Finset.mem_Icc.mp hx |>.1 ) ] ⟩ ];
    norm_cast;
  -- Now: 0 ≤ ∑ Λ(n) · frac(N/n) ≤ ∑ Λ(n) = ψ(N) ≤ (log 4 + 4) · N (by Chebyshev.psi_le_const_mul_self)
  have h_frac_bound : ∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) * (Int.fract (N / n : ℝ)) ≤ (Real.log 4 + 4) * N := by
    have h_frac_bound : ∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) ≤ (Real.log 4 + 4) * N := by
      convert Chebyshev.psi_le_const_mul_self ( show 0 ≤ ( N : ℝ ) by positivity ) using 1;
      refine' Finset.sum_bij ( fun x hx => x ) _ _ _ _ <;> aesop;
    exact le_trans ( Finset.sum_le_sum fun _ _ => mul_le_of_le_one_right ( by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg ) ( Int.fract_lt_one _ |> le_of_lt ) ) h_frac_bound;
  -- Now: log(N!) is between N·log(N) - N and N·log(N) (by log_factorial_ge and log_factorial_le)
  have h_log_factorial : N * Real.log N - N ≤ Real.log (N ! : ℝ) ∧ Real.log (N ! : ℝ) ≤ N * Real.log N := by
    exact ⟨ log_factorial_ge N ( by linarith ), log_factorial_le N ( by linarith ) ⟩;
  rw [ abs_le ];
  constructor <;> nlinarith [ show ( N : ℝ ) ≥ 2 by norm_cast, show ( ∑ n ∈ Finset.Icc 1 N, Λ n * Int.fract ( N / n : ℝ ) ) ≥ 0 by exact Finset.sum_nonneg fun _ _ => mul_nonneg ( by exact_mod_cast vonMangoldt_nonneg ) ( Int.fract_nonneg _ ) ]

/-! ### Step 4: ∑_{p≤N} log(p)/p = log N + O(1)

Subtracting the prime power contributions. -/

/-
The prime power contribution ∑_{p^k, k≥2} log(p)/p^k converges.
-/
lemma prime_power_reciprocal_bounded :
    ∃ C : ℝ, ∀ N : ℕ,
      ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
        ∑ k ∈ Finset.Icc 2 (Nat.log p N),
          Real.log p / (p : ℝ) ^ k ≤ C := by
  -- We bound the inner sum using the formula $\sum_{k=2}^{\infty} \frac{\log p}{p^k} = \frac{\log p}{p^2} \frac{1}{1 - 1/p} = \frac{\log p}{p(p-1)}$.
  have h_inner_bound : ∀ p : ℕ, p.Prime → ∑' k : ℕ, Real.log p / (p ^ (k + 2) : ℝ) ≤ Real.log p / (p * (p - 1) : ℝ) := by
    intro p hp
    have h_inner_sum : ∑' k : ℕ, (Real.log p) / (p ^ (k + 2) : ℝ) = (Real.log p) / (p ^ 2 : ℝ) * (1 / (1 - 1 / (p : ℝ))) := by
      ring_nf;
      rw [ tsum_mul_left, tsum_geometric_of_lt_one ( by positivity ) ( inv_lt_one_of_one_lt₀ ( mod_cast hp.one_lt ) ) ];
    convert h_inner_sum.le using 1 ; ring;
    grind;
  -- We sum the inner bounds over all primes $p$.
  have h_sum_inner_bound : Summable (fun p : ℕ => if p.Prime then Real.log p / (p * (p - 1) : ℝ) else 0) := by
    -- We compare our sum to a convergent p-series.
    have h_compare : ∀ p : ℕ, p ≥ 2 → (if p.Prime then Real.log p / (p * (p - 1) : ℝ) else 0) ≤ 2 * (Real.log p / p ^ 2 : ℝ) := by
      intro p hp; split_ifs <;> ring_nf <;> norm_num;
      · field_simp;
        rw [ div_le_iff₀ ] <;> nlinarith [ show ( p : ℝ ) ≥ 2 by norm_cast, Real.log_nonneg ( show ( p : ℝ ) ≥ 1 by norm_cast; linarith ) ];
      · positivity;
    -- We know that $\sum_{p} \frac{\log p}{p^2}$ converges.
    have h_sum_log_p : Summable (fun p : ℕ => Real.log p / p ^ 2 : ℕ → ℝ) := by
      -- We can compare our series with the convergent p-series $\sum_{n=1}^{\infty} \frac{1}{n^{3/2}}$.
      have h_compare : ∀ n : ℕ, n ≥ 2 → (Real.log n / n ^ 2 : ℝ) ≤ 1 / n ^ (3 / 2 : ℝ) := by
        intro n hn
        have : Real.log n ≤ Real.sqrt n := by
          have := Real.log_le_sub_one_of_pos ( by positivity : 0 < Real.sqrt n / 2 );
          rw [ Real.log_div ( by positivity ) ( by positivity ), Real.log_sqrt ( by positivity ) ] at this;
          have := Real.log_two_lt_d9 ; norm_num at * ; linarith;
        rw [ div_le_div_iff₀ ] <;> try positivity;
        exact le_trans ( mul_le_mul_of_nonneg_right this <| by positivity ) <| by rw [ Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add <| by positivity ] ; norm_num;
      exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => if hn : n < 2 then by interval_cases n <;> norm_num else h_compare n ( le_of_not_gt hn ) ) ( Real.summable_one_div_nat_rpow.2 ( by norm_num ) );
    rw [ ← summable_nat_add_iff 2 ] at *;
    exact Summable.of_nonneg_of_le ( fun n => by split_ifs <;> first | positivity | exact div_nonneg ( Real.log_nonneg <| by norm_cast; linarith ) <| mul_nonneg ( Nat.cast_nonneg _ ) <| sub_nonneg.mpr <| Nat.one_le_cast.mpr <| by linarith ) ( fun n => h_compare _ <| by linarith ) <| h_sum_log_p.mul_left 2;
  -- We use the bound on the inner sum to bound the outer sum.
  have h_outer_bound : ∀ N : ℕ, ∑ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), ∑ k ∈ Finset.Icc 2 (Nat.log p N), Real.log p / (p ^ k : ℝ) ≤ ∑ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), Real.log p / (p * (p - 1) : ℝ) := by
    intro N
    apply Finset.sum_le_sum
    intro p hp
    have h_inner_bound_p : ∑ k ∈ Finset.Icc 2 (Nat.log p N), Real.log p / (p ^ k : ℝ) ≤ ∑' k : ℕ, Real.log p / (p ^ (k + 2) : ℝ) := by
      erw [ Finset.sum_Ico_eq_sum_range ];
      simpa only [ add_comm ] using Summable.sum_le_tsum ( Finset.range ( Nat.log p N + 1 - 2 ) ) ( fun _ _ => by positivity ) ( by exact Summable.mul_left _ <| by simpa using summable_geometric_of_lt_one ( by positivity ) ( inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| by aesop ) |> Summable.comp_injective <| by intro a; aesop );
    exact le_trans h_inner_bound_p <| h_inner_bound p <| Finset.mem_filter.mp hp |>.2;
  exact ⟨ _, fun N => le_trans ( h_outer_bound N ) ( by simpa [ Finset.sum_filter ] using Summable.sum_le_tsum ( Finset.range ( N + 1 ) ) ( fun _ _ => by split_ifs <;> first | positivity | exact div_nonneg ( Real.log_nonneg <| Nat.one_le_cast.2 <| Nat.Prime.pos <| by assumption ) <| mul_nonneg ( Nat.cast_nonneg _ ) <| sub_nonneg.2 <| Nat.one_le_cast.2 <| Nat.Prime.pos <| by assumption ) h_sum_inner_bound ) ⟩

/-
∑_{p≤N} log(p)/p = log N + O(1).
-/
lemma prime_log_reciprocal_bounded :
    ∃ C : ℝ, ∀ N : ℕ, N ≥ 2 →
      |∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
        Real.log p / (p : ℝ) - Real.log N| ≤ C := by
  -- By definition of von Mangoldt function, we have $\sum_{n=1}^{N} \Lambda(n)/n = \sum_{p \leq N, p \text{ prime}} \sum_{k=1}^{\log_p(N)} \frac{\log(p)}{p^k}$.
  have h_vonMangoldt_sum : ∀ N : ℕ, N ≥ 2 → (∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) / n) = (∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (∑ k ∈ Finset.Icc 1 (Nat.log p N), (Real.log p) / (p : ℝ) ^ k)) := by
    intro N hN;
    have h_sum_prime_powers : ∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) / n = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), ∑ k ∈ Finset.Icc 1 (Nat.log p N), (vonMangoldt (p^k) : ℝ) / p^k := by
      have h_sum_prime_powers : Finset.filter (fun n => vonMangoldt n ≠ 0) (Finset.Icc 1 N) = Finset.biUnion (Finset.filter Nat.Prime (Finset.range (N + 1))) (fun p => Finset.image (fun k => p^k) (Finset.Icc 1 (Nat.log p N))) := by
        ext n
        simp [vonMangoldt];
        constructor <;> intro hn
        all_goals generalize_proofs at *;
        · obtain ⟨ p, k, hp, hk, rfl ⟩ := hn.2.1;
          exact ⟨ p, ⟨ by linarith [ Nat.le_self_pow hk.ne' p ], hp.nat_prime ⟩, k, ⟨ hk, Nat.le_log_of_pow_le hp.nat_prime.one_lt hn.1.2 ⟩, rfl ⟩;
        · rcases hn with ⟨ p, ⟨ hp₁, hp₂ ⟩, k, ⟨ hk₁, hk₂ ⟩, rfl ⟩ ; refine' ⟨ ⟨ Nat.one_le_pow _ _ hp₂.pos, Nat.pow_le_of_le_log ( by linarith [ hp₂.pos ] ) hk₂ ⟩, _, _, _, _ ⟩ <;> norm_cast <;> simp_all +decide [ Nat.Prime.ne_zero, Nat.Prime.ne_one ] ;
          · exact hp₂.isPrimePow.pow ( by linarith );
          · exact Nat.ne_of_gt ( Nat.minFac_pos _ );
          · lia
      generalize_proofs at *; (
      have h_sum_prime_powers : ∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) / n = ∑ n ∈ Finset.filter (fun n => vonMangoldt n ≠ 0) (Finset.Icc 1 N), (vonMangoldt n : ℝ) / n := by
        rw [ Finset.sum_filter_of_ne ] ; aesop
      generalize_proofs at *; (
      rw [ h_sum_prime_powers, ‹ { n ∈ Icc 1 N | Λ n ≠ 0 } = _ ›, Finset.sum_biUnion ];
      · exact Finset.sum_congr rfl fun p hp => by rw [ Finset.sum_image <| by intros a ha b hb hab; exact Nat.pow_right_injective ( Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ) hab ] ; norm_cast;
      · intros p hp q hq hpq; simp_all +decide [ Finset.disjoint_left ] ;
        intro a x hx₁ hx₂ hx₃ y hy₁ hy₂ hy₃; subst_vars; have := Nat.Prime.dvd_of_dvd_pow hp.2 ( hy₃.symm ▸ dvd_pow_self _ ( by linarith ) ) ; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;))
    generalize_proofs at *; (
    convert h_sum_prime_powers using 3;
    rw [ ArithmeticFunction.vonMangoldt_apply ];
    rw [ if_pos ];
    · rw [ Nat.Prime.pow_minFac ] ; aesop;
      linarith [ Finset.mem_Icc.mp ‹_› ];
    · exact Nat.Prime.isPrimePow ( Finset.mem_filter.mp ‹_› |>.2 ) |> fun h => h.pow ( by linarith [ Finset.mem_Icc.mp ‹_› ] ));
  obtain ⟨ C₁, hC₁ ⟩ := vonMangoldt_reciprocal_bounded
  obtain ⟨ C₂, hC₂ ⟩ := prime_power_reciprocal_bounded
  use C₁ + C₂
  intro N hN
  have h_sum_eq : (∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (∑ k ∈ Finset.Icc 1 (Nat.log p N), (Real.log p) / (p : ℝ) ^ k)) = (∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (Real.log p) / (p : ℝ)) + (∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (∑ k ∈ Finset.Icc 2 (Nat.log p N), (Real.log p) / (p : ℝ) ^ k)) := by
    rw [ ← Finset.sum_add_distrib, Finset.sum_congr rfl ];
    intro p hp; erw [ Finset.Icc_eq_cons_Ioc ( Nat.succ_le_of_lt ( Nat.log_pos ( Nat.Prime.one_lt ( Finset.mem_filter.mp hp |>.2 ) ) ( by linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hp |>.1 ) ] ) ) ), Finset.sum_cons ] ; aesop;
  have := hC₁ N hN; rw [ abs_le ] at *; constructor <;> linarith [ hC₂ N, h_vonMangoldt_sum N hN, show ( 0 : ℝ ) ≤ ∑ p ∈ Finset.filter Nat.Prime ( Finset.range ( N + 1 ) ), ∑ k ∈ Finset.Icc 2 ( Nat.log p N ), Real.log p / p ^ k from Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => div_nonneg ( Real.log_nonneg <| mod_cast Nat.Prime.pos <| by aesop ) <| pow_nonneg ( Nat.cast_nonneg _ ) _ ] ;

/-! ### Step 5: Abel summation gives convergence of ∑ 1/p - log log N

The key idea: from the bounded estimate |∑ log(p)/p - log N| ≤ C,
Abel summation converts this into convergence of ∑ 1/p - log log N.

Abel summation: ∑_{p≤N} 1/p = S(N)/log N + ∫₂^N S(t)/(t·log²t) dt
where S(t) = ∑_{p≤t} log(p)/p = log t + O(1).

The integral ∫ (log t + O(1))/(t·log²t) dt = ∫ 1/(t·log t) dt + ∫ O(1)/(t·log²t) dt
= log log t + convergent integral.

So ∑ 1/p - log log N → some constant M.
-/

/-
The prime reciprocal sum ∑_{p≤N} 1/p - log(log N) converges to some limit.
This follows from Abel summation applied to the bounded estimate
|∑ log(p)/p - log N| ≤ C.
-/
set_option maxHeartbeats 800000 in
lemma prime_reciprocal_sum_convergence :
    ∃ M : ℝ, Tendsto
      (fun N : ℕ => ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
        1 / (p : ℝ) - Real.log (Real.log N))
      atTop (𝓝 M) := by
  obtain ⟨ C, hC ⟩ := prime_log_reciprocal_bounded;
  -- Let $S(N) = \sum_{p \leq N} \frac{\log p}{p}$. Then $S(N) = \log N + e(N)$ where $|e(N)| \leq C$.
  set S : ℕ → ℝ := fun N => ∑ p ∈ ((Finset.range (N + 1)).filter Nat.Prime), (Real.log p) / (p : ℝ)
  have hS : ∀ N : ℕ, N ≥ 2 → |S N - Real.log N| ≤ C := by
    assumption;
  -- By Abel's summation formula, we have $\sum_{p \leq N} \frac{1}{p} = \frac{S(N)}{\log N} + \int_{2}^{N} \frac{S(t)}{t \log^2 t} dt$.
  have h_abel : ∀ N : ℕ, N ≥ 2 → (∑ p ∈ ((Finset.range (N + 1)).filter Nat.Prime), (1 : ℝ) / p) = S N / Real.log N + ∫ t in (2 : ℝ)..N, S (Nat.floor t) / (t * (Real.log t)^2) := by
    intro N hN
    have h_abel_step : ∀ n : ℕ, 2 ≤ n → (∑ p ∈ ((Finset.range (n + 1)).filter Nat.Prime), (1 : ℝ) / p) = S n / Real.log n + ∑ k ∈ Finset.Ico 2 n, S k * (1 / Real.log k - 1 / Real.log (k + 1)) := by
      intro n hn;
      induction hn <;> simp_all +decide [ Finset.sum_Ico_succ_top ];
      · norm_num [ Finset.sum_filter, Finset.sum_range_succ, S ];
        ring_nf; norm_num;
      · simp_all +decide [ Finset.sum_filter, Finset.sum_range_succ ];
        simp +zetaDelta at *;
        split_ifs <;> simp_all +decide [ Finset.sum_filter, Finset.sum_range_succ ];
        · field_simp;
          rw [ eq_comm, div_add', div_eq_iff ] <;> ring;
          · norm_num [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( Real.log_pos ( show ( 1 + ( ‹ℕ› : ℝ ) ) > 1 by norm_cast; linarith ) ), ne_of_gt ( Real.log_pos ( show ( ‹ℕ› : ℝ ) > 1 by norm_cast ) ) ] ; ring;
          · exact ne_of_gt <| Real.log_pos <| by norm_cast; linarith;
          · exact ne_of_gt <| Real.log_pos <| by norm_cast; linarith;
        · ring;
    -- The integral of $S(t)/(t \log^2 t)$ over $[k, k+1]$ is equal to $S(k) \cdot (1/\log k - 1/\log(k+1))$.
    have h_integral_step : ∀ k : ℕ, 2 ≤ k → ∫ t in (k : ℝ)..((k + 1) : ℝ), S (Nat.floor t) / (t * (Real.log t)^2) = S k * (1 / Real.log k - 1 / Real.log (k + 1)) := by
      intro k hk; erw [ intervalIntegral.integral_of_le ( by norm_num ) ] ; erw [ MeasureTheory.integral_Ioc_eq_integral_Ioo ] ; erw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => by rw [ show ⌊x⌋₊ = k from Nat.floor_eq_iff ( by linarith [ hx.1 ] ) |>.2 ⟨ by linarith [ hx.1 ], by linarith [ hx.2 ] ⟩ ] ] ; norm_num;
      rw [ ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ] <;> norm_num;
      rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
      rotate_right;
      use fun x => -S k / Real.log x;
      · ring;
      · intro x hx; convert HasDerivAt.div ( hasDerivAt_const _ _ ) ( Real.hasDerivAt_log ( show x ≠ 0 from by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ) ) ( ne_of_gt <| Real.log_pos <| show x > 1 from by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ) using 1 ; ring;
      · apply_rules [ ContinuousOn.intervalIntegrable ];
        exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const ( ContinuousAt.mul continuousAt_id <| ContinuousAt.pow ( Real.continuousAt_log <| by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ) _ ) <| ne_of_gt <| mul_pos ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ) <| sq_pos_of_pos <| Real.log_pos <| by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ;
    induction hN <;> simp_all +decide [ Finset.sum_Ico_succ_top ];
    rename_i k hk ih; rw [ h_abel_step _ ( by linarith ) ] ; simp_all +decide [ Finset.sum_Ico_succ_top ] ;
    rw [ ← h_integral_step k hk, intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ MeasureTheory.IntegrableOn.intervalIntegrable ];
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun t => ( Real.log t + C ) / ( t * Real.log t ^ 2 );
      · exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div ( ContinuousAt.add ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ) ) continuousAt_const ) ( ContinuousAt.mul continuousAt_id ( ContinuousAt.pow ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ) ) 2 ) ) ( ne_of_gt ( mul_pos ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ) ( sq_pos_of_pos ( Real.log_pos ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ) ) ) ) ) );
      · refine' Measurable.aestronglyMeasurable _;
        fun_prop;
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with x hx;
        rw [ Real.norm_of_nonneg ( div_nonneg ( Finset.sum_nonneg fun _ _ => div_nonneg ( Real.log_nonneg ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( by aesop ) ) ) ) ( Nat.cast_nonneg _ ) ) ( mul_nonneg ( by cases Set.mem_uIcc.mp hx <;> linarith ) ( sq_nonneg _ ) ) ) ];
        gcongr;
        · exact mul_nonneg ( by cases Set.mem_uIcc.mp hx <;> linarith ) ( sq_nonneg _ );
        · have := hS ⌊x⌋₊ ( Nat.le_floor <| by norm_num; cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ) ; rw [ abs_le ] at this ; linarith [ Real.log_le_log ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ) <| Nat.floor_le <| show 0 ≤ x by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ] ;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun t => ( ∑ p ∈ Finset.range ( k + 2 ), Real.log p / p ) / ( t * Real.log t ^ 2 );
      · exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const ( ContinuousAt.mul continuousAt_id <| ContinuousAt.pow ( Real.continuousAt_log <| by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ) _ ) <| ne_of_gt <| mul_pos ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] ) <| sq_pos_of_pos <| Real.log_pos <| by cases Set.mem_uIcc.mp hx <;> linarith [ show ( k : ℝ ) ≥ 2 by norm_cast ] );
      · refine' Measurable.aestronglyMeasurable _;
        fun_prop;
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with x hx;
        rw [ Real.norm_of_nonneg ( div_nonneg ( Finset.sum_nonneg fun _ _ => div_nonneg ( Real.log_nonneg ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( by aesop ) ) ) ) ( Nat.cast_nonneg _ ) ) ( mul_nonneg ( by cases Set.mem_uIcc.mp hx <;> linarith ) ( sq_nonneg _ ) ) ) ];
        gcongr;
        · exact mul_nonneg ( by cases Set.mem_uIcc.mp hx <;> linarith ) ( sq_nonneg _ );
        · exact fun p hp => Finset.mem_range.mpr ( Nat.lt_succ_of_le ( Nat.le_trans ( Finset.mem_range_succ_iff.mp ( Finset.mem_filter.mp hp |>.1 ) ) ( Nat.floor_le_of_le ( by cases Set.mem_uIcc.mp hx <;> norm_num at * <;> linarith ) ) ) );
  -- We'll use the fact that $\int_{2}^{N} \frac{S(t)}{t \log^2 t} dt$ converges to a constant as $N \to \infty$.
  have h_integral : ∃ M : ℝ, Filter.Tendsto (fun N : ℕ => ∫ t in (2 : ℝ)..N, S (Nat.floor t) / (t * (Real.log t)^2) - 1 / (t * Real.log t)) Filter.atTop (nhds M) := by
    -- We'll use the fact that $\int_{2}^{N} \frac{S(t) - \log t}{t \log^2 t} dt$ converges to a constant as $N \to \infty$.
    have h_integral : ∃ M : ℝ, Filter.Tendsto (fun N : ℕ => ∫ t in (2 : ℝ)..N, (S (Nat.floor t) - Real.log t) / (t * (Real.log t)^2)) Filter.atTop (nhds M) := by
      -- We'll use the fact that $\int_{2}^{N} \frac{S(t) - \log t}{t \log^2 t} dt$ is absolutely convergent.
      have h_abs_conv : MeasureTheory.IntegrableOn (fun t : ℝ => |(S (Nat.floor t) - Real.log t) / (t * (Real.log t)^2)|) (Set.Ici 2) := by
        -- We'll use the fact that $|S(t) - \log t| \leq C$ for all $t \geq 2$.
        have h_bound : ∀ t : ℝ, 2 ≤ t → |(S (Nat.floor t) - Real.log t) / (t * (Real.log t)^2)| ≤ (C + 1) / (t * (Real.log t)^2) := by
          intros t ht
          have h_abs : |S (Nat.floor t) - Real.log t| ≤ C + 1 := by
            have := hS ⌊t⌋₊ ( Nat.le_floor <| mod_cast ht );
            rw [ abs_le ] at *;
            constructor <;> linarith [ show Real.log t ≤ Real.log ⌊t⌋₊ + 1 by rw [ Real.log_le_iff_le_exp ( by positivity ) ] ; rw [ Real.exp_add, Real.exp_log ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by linarith ) ] ; nlinarith [ Nat.lt_floor_add_one t, Real.add_one_le_exp 1, Real.log_le_sub_one_of_pos <| show 0 < ( ⌊t⌋₊ : ℝ ) by exact Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by linarith ], show Real.log ⌊t⌋₊ ≤ Real.log t by exact Real.log_le_log ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by linarith ) <| Nat.floor_le <| by positivity ];
          rw [ abs_div, abs_of_nonneg ( by positivity : 0 ≤ t * Real.log t ^ 2 ) ] ; gcongr;
        -- We'll use the fact that $\int_{2}^{\infty} \frac{1}{t \log^2 t} dt$ converges.
        have h_integral_conv : MeasureTheory.IntegrableOn (fun t : ℝ => 1 / (t * (Real.log t)^2)) (Set.Ici 2) := by
          -- We can use the substitution $u = \log t$, then $du = \frac{1}{t} dt$.
          suffices h_subst : MeasureTheory.IntegrableOn (fun u : ℝ => 1 / u^2) (Set.Ici (Real.log 2)) by
            have h_subst : MeasureTheory.IntegrableOn (fun t : ℝ => 1 / (t * (Real.log t)^2)) (Set.Ici 2) := by
              have : MeasureTheory.IntegrableOn (fun u : ℝ => 1 / u^2) (Set.image Real.log (Set.Ici 2)) := by
                exact h_subst.mono_set <| Set.image_subset_iff.mpr fun x hx => Real.log_le_log ( by norm_num ) hx
              rw [ MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul ] at this;
              any_goals intro x hx; exact Real.hasDerivAt_log ( by linarith [ Set.mem_Ici.mp hx ] ) |> HasDerivAt.hasDerivWithinAt;
              · refine' this.congr_fun _ _;
                · intro x hx; simp +decide [ abs_of_nonneg ( inv_nonneg.mpr ( show 0 ≤ x by linarith [ Set.mem_Ici.mp hx ] ) ), mul_comm ] ;
                · norm_num;
              · norm_num;
              · exact fun x hx y hy hxy => Real.log_injOn_pos ( show 0 < x by linarith [ Set.mem_Ici.mp hx ] ) ( show 0 < y by linarith [ Set.mem_Ici.mp hy ] ) hxy;
            convert h_subst using 1;
          have h_integral_conv : MeasureTheory.IntegrableOn (fun u : ℝ => u ^ (-2 : ℝ)) (Set.Ici (Real.log 2)) := by
            rw [ integrableOn_Ici_iff_integrableOn_Ioi ] ; rw [ integrableOn_Ioi_rpow_iff ] <;> norm_num ; positivity;
          norm_cast at * ; aesop;
        refine' h_integral_conv.const_mul ( C + 1 ) |> fun h => h.mono' _ _;
        · refine' Measurable.aestronglyMeasurable _;
          fun_prop;
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ici ] with t ht using by simpa [ div_eq_mul_inv ] using h_bound t ht;
      have h_abs_conv : MeasureTheory.IntegrableOn (fun t : ℝ => (S (Nat.floor t) - Real.log t) / (t * (Real.log t)^2)) (Set.Ici 2) := by
        refine' h_abs_conv.mono' _ _;
        · refine' Measurable.aestronglyMeasurable _;
          fun_prop;
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ici ] with x hx using le_rfl;
      have h_abs_conv : Filter.Tendsto (fun N : ℕ => ∫ t in (2 : ℝ)..N, (S (Nat.floor t) - Real.log t) / (t * (Real.log t)^2)) Filter.atTop (nhds (∫ t in Set.Ici 2, (S (Nat.floor t) - Real.log t) / (t * (Real.log t)^2))) := by
        rw [ MeasureTheory.integral_Ici_eq_integral_Ioi ];
        apply_rules [ MeasureTheory.intervalIntegral_tendsto_integral_Ioi ];
        · exact h_abs_conv.mono_set <| Set.Ioi_subset_Ici_self;
        · exact tendsto_natCast_atTop_atTop;
      exact ⟨ _, h_abs_conv ⟩;
    convert h_integral using 4;
    grind +qlia;
  obtain ⟨ M, hM ⟩ := h_integral;
  have h_integral_split : ∀ N : ℕ, N ≥ 2 → ∫ t in (2 : ℝ)..N, S (Nat.floor t) / (t * (Real.log t)^2) - 1 / (t * Real.log t) = (∫ t in (2 : ℝ)..N, S (Nat.floor t) / (t * (Real.log t)^2)) - (Real.log (Real.log N) - Real.log (Real.log 2)) := by
    intro N hN; rw [ intervalIntegral.integral_sub ] <;> norm_num;
    · rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
      rotate_right;
      use fun x => Real.log ( Real.log x );
      · norm_cast;
      · intro x hx; convert HasDerivAt.log ( Real.hasDerivAt_log ( show x ≠ 0 by cases Set.mem_uIcc.mp hx <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) ) ( ne_of_gt <| Real.log_pos <| show x > 1 by cases Set.mem_uIcc.mp hx <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) using 1 ; ring;
      · apply_rules [ ContinuousOn.intervalIntegrable ];
        exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.mul ( ContinuousAt.inv₀ ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) ) ( ne_of_gt ( Real.log_pos ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) ) ) ) ( ContinuousAt.inv₀ ( continuousAt_id ) ( ne_of_gt ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) ) );
    · apply_rules [ MeasureTheory.IntegrableOn.intervalIntegrable ];
      refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun t => ( C + Real.log N ) / ( t * Real.log t ^ 2 );
      · exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div continuousAt_const ( ContinuousAt.mul continuousAt_id <| ContinuousAt.pow ( Real.continuousAt_log <| by cases Set.mem_uIcc.mp ht <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) _ ) <| ne_of_gt <| mul_pos ( by cases Set.mem_uIcc.mp ht <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) <| sq_pos_of_pos <| Real.log_pos <| by cases Set.mem_uIcc.mp ht <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] );
      · refine' Measurable.aestronglyMeasurable _;
        fun_prop;
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with t ht;
        rw [ Real.norm_of_nonneg ( div_nonneg ( Finset.sum_nonneg fun _ _ => div_nonneg ( Real.log_nonneg ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( by aesop ) ) ) ) ( Nat.cast_nonneg _ ) ) ( mul_nonneg ( by cases Set.mem_uIcc.mp ht <;> linarith ) ( sq_nonneg _ ) ) ) ];
        gcongr;
        · exact mul_nonneg ( by cases Set.mem_uIcc.mp ht <;> linarith ) ( sq_nonneg _ );
        · have := hS ⌊t⌋₊ ( Nat.le_floor <| by norm_num; cases Set.mem_uIcc.mp ht <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] );
          linarith [ abs_le.mp this, Real.log_le_log ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by cases Set.mem_uIcc.mp ht <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) <| Nat.floor_le ( by cases Set.mem_uIcc.mp ht <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] : 0 ≤ t ) |> le_trans <| show ( t : ℝ ) ≤ N by cases Set.mem_uIcc.mp ht <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ];
    · apply_rules [ ContinuousOn.intervalIntegrable ];
      exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.mul ( ContinuousAt.inv₀ ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) ) ( ne_of_gt ( Real.log_pos ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) ) ) ) ( ContinuousAt.inv₀ ( continuousAt_id ) ( ne_of_gt ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) ) );
  have h_limit : Filter.Tendsto (fun N : ℕ => S N / Real.log N + (Real.log (Real.log N) - Real.log (Real.log 2)) + (∫ t in (2 : ℝ)..N, S (Nat.floor t) / (t * (Real.log t)^2) - 1 / (t * Real.log t)) - Real.log (Real.log N)) Filter.atTop (nhds (1 + M - Real.log (Real.log 2))) := by
    have h_limit : Filter.Tendsto (fun N : ℕ => S N / Real.log N) Filter.atTop (nhds 1) := by
      have h_limit : Filter.Tendsto (fun N : ℕ => (S N - Real.log N) / Real.log N) Filter.atTop (nhds 0) := by
        refine' squeeze_zero_norm' _ _;
        use fun N => C / Real.log N;
        · filter_upwards [ Filter.eventually_ge_atTop 2 ] with N hN using by rw [ Real.norm_eq_abs, abs_div, abs_of_nonneg ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith ) ) ) ] ; exact div_le_div_of_nonneg_right ( hS N hN ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith ) ) ) ;
        · exact tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
      simpa using h_limit.add_const 1 |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with N hN using by rw [ sub_div, div_self <| ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hN ] ; ring );
    convert Filter.Tendsto.add ( Filter.Tendsto.add h_limit hM ) tendsto_const_nhds using 2 ; ring;
  exact ⟨ _, Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_ge_atTop 2 ] with N hN; rw [ h_abel N hN, h_integral_split N hN ] ; ring ) h_limit ⟩

end


noncomputable section

/-! ### Helper lemmas -/

/-- The integral of log(u) * exp(-u) over (0, ∞) equals -γ (Euler-Mascheroni constant). -/
lemma gamma_integral :
    ∫ u in Set.Ioi (0 : ℝ), Real.log u * Real.exp (-u) =
    -Real.eulerMascheroniConstant := by
  convert ( HasDerivAt.deriv ( Real.hasDerivAt_Gamma_one ) ) using 1;
  have h_gamma_deriv : deriv Gamma 1 = ∫ u in Set.Ioi 0, Real.log u * Real.exp (-u) := by
    have h_lim : Filter.Tendsto (fun s : ℝ => (Gamma s - Gamma 1) / (s - 1)) (nhdsWithin 1 (Set.Ioi 1)) (nhds (∫ u in Set.Ioi 0, Real.log u * Real.exp (-u))) := by
      have h_dominate : ∀ s ∈ Set.Ioo (1 : ℝ) 2, ∀ u ∈ Set.Ioi 0, abs ((u^(s-1) - 1) / (s - 1) * Real.exp (-u)) ≤ abs (Real.log u) * Real.exp (-u) * (u + 1) := by
        have h_mean_value : ∀ s ∈ Set.Ioo (1 : ℝ) 2, ∀ u ∈ Set.Ioi 0, ∃ c ∈ Set.Ioo 0 (s - 1), u^(s-1) - 1 = (s - 1) * Real.log u * u^c := by
          intro s hs u hu;
          have := exists_deriv_eq_slope ( f := fun x => u ^ x ) ( show 0 < s - 1 by linarith [ hs.1 ] );
          norm_num [ Real.rpow_def_of_pos hu, mul_comm ] at *;
          exact this ( Continuous.continuousOn <| by continuity ) ( Differentiable.differentiableOn <| by norm_num ) |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, hc₁, by rw [ eq_div_iff ] at hc₂ <;> linarith ⟩;
        intro s hs u hu; obtain ⟨ c, hc₁, hc₂ ⟩ := h_mean_value s hs u hu; rw [ hc₂ ] ; simp +decide [ abs_mul, abs_div, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ] ;
        by_cases h : s - 1 = 0 <;> simp_all +decide [ ne_of_gt ];
        by_cases hu₁ : u ≤ 1;
        · exact mul_le_mul_of_nonneg_right ( by rw [ abs_of_nonneg ( Real.rpow_nonneg hu.le _ ) ] ; exact le_trans ( Real.rpow_le_one hu.le hu₁ hc₁.1.le ) ( by linarith ) ) ( by positivity );
        · exact mul_le_mul_of_nonneg_right ( by rw [ abs_of_nonneg ( Real.rpow_nonneg hu.le _ ) ] ; exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( by linarith ) ( show c ≤ 1 by linarith ) ) ( by norm_num ) ) ( by positivity );
      have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => abs (Real.log u) * Real.exp (-u) * (u + 1)) (Set.Ioi 0) := by
        have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => abs (Real.log u) * Real.exp (-u) * u) (Set.Ioi 0) := by
          have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => u * Real.exp (-u) * abs (Real.log u)) (Set.Ioi 0) := by
            have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => u * Real.exp (-u) * Real.log u) (Set.Ioi 0) := by
              have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => u * Real.exp (-u) * Real.log u) (Set.Ioc 0 1) := by
                have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => u * Real.log u) (Set.Ioc 0 1) := by
                  exact Continuous.integrableOn_Ioc ( Real.continuous_mul_log );
                refine' h_integrable.norm.mono' _ _;
                · exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.mul ( measurable_id.aestronglyMeasurable ) ( Real.continuous_exp.comp_aestronglyMeasurable ( measurable_neg.aestronglyMeasurable ) ) ) ( Real.measurable_log.aestronglyMeasurable );
                · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using by rw [ mul_right_comm ] ; exact by simpa [ abs_mul ] using mul_le_mul_of_nonneg_left ( Real.exp_le_one_iff.mpr <| neg_nonpos.mpr hx.1.le ) <| by positivity;
              have h_integrable' : MeasureTheory.IntegrableOn (fun u : ℝ => u * Real.exp (-u) * Real.log u) (Set.Ioi 1) := by
                have h_integrable' : MeasureTheory.IntegrableOn (fun u : ℝ => u * Real.exp (-u) * u) (Set.Ioi 1) := by
                  have h_integrable' : MeasureTheory.IntegrableOn (fun u : ℝ => u^2 * Real.exp (-u)) (Set.Ioi 1) := by
                    have h_gamma : ∫ u in Set.Ioi 0, u^2 * Real.exp (-u) = Real.Gamma 3 := by
                      rw [ Real.Gamma_eq_integral ( by norm_num ) ];
                      norm_cast ; ac_rfl;
                    exact MeasureTheory.IntegrableOn.mono_set ( by exact ( by contrapose! h_gamma; rw [ MeasureTheory.integral_undef h_gamma ] ; positivity ) ) ( Set.Ioi_subset_Ioi zero_le_one );
                  exact h_integrable'.congr_fun ( fun x hx => by ring ) measurableSet_Ioi;
                refine' h_integrable'.mono' _ _;
                · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( measurable_id.mul ( Real.continuous_exp.measurable.comp measurable_neg ) ) ( Real.measurable_log ) );
                · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with u hu using by rw [ Real.norm_eq_abs, abs_of_nonneg ( mul_nonneg ( mul_nonneg ( by linarith [ hu.out ] ) ( Real.exp_nonneg _ ) ) ( Real.log_nonneg ( by linarith [ hu.out ] ) ) ) ] ; exact mul_le_mul_of_nonneg_left ( le_trans ( Real.log_le_sub_one_of_pos ( by linarith [ hu.out ] ) ) ( by linarith [ hu.out ] ) ) ( mul_nonneg ( by linarith [ hu.out ] ) ( Real.exp_nonneg _ ) ) ;
              convert h_integrable.union h_integrable' using 1 ; norm_num;
            refine' h_integrable.norm.congr _;
            filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with u hu using by rw [ Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hu.out.le, abs_of_nonneg ( Real.exp_pos _ |> le_of_lt ) ] ;
          exact h_integrable.congr_fun ( fun x hx => by ring ) measurableSet_Ioi;
        have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => abs (Real.log u) * Real.exp (-u)) (Set.Ioi 0) := by
          have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => abs (Real.log u) * Real.exp (-u)) (Set.Ioc 0 1) := by
            have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => abs (Real.log u)) (Set.Ioc 0 1) := by
              have h_integrable : ∫ u in Set.Ioc 0 1, abs (Real.log u) = 1 := by
                rw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => abs_of_nonpos ( Real.log_nonpos hx.1.le hx.2 ), ← intervalIntegral.integral_of_le ] <;> norm_num;
              exact ( by contrapose! h_integrable; rw [ MeasureTheory.integral_undef h_integrable ] ; norm_num );
            refine' h_integrable.mono' _ _;
            · exact MeasureTheory.AEStronglyMeasurable.mul ( h_integrable.aestronglyMeasurable ) ( Continuous.aestronglyMeasurable ( by continuity ) );
            · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with u hu using by simpa [ abs_mul ] using mul_le_mul_of_nonneg_left ( Real.exp_le_one_iff.mpr <| neg_nonpos.mpr hu.1.le ) <| abs_nonneg <| Real.log u;
          have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => abs (Real.log u) * Real.exp (-u)) (Set.Ioi 1) := by
            have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => u * Real.exp (-u)) (Set.Ioi 1) := by
              have := @integral_rpow_mul_exp_neg_rpow 1;
              specialize @this 1 ; norm_num at this;
              exact MeasureTheory.IntegrableOn.mono_set ( by exact ( by contrapose! this; rw [ MeasureTheory.integral_undef this ] ; norm_num ) ) ( Set.Ioi_subset_Ioi zero_le_one );
            refine' h_integrable.mono' _ _;
            · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( Real.measurable_log.norm ) ( Real.continuous_exp.measurable.comp measurable_neg ) );
            · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with u hu using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact mul_le_mul_of_nonneg_right ( by rw [ abs_of_nonneg ( Real.log_nonneg hu.out.le ) ] ; exact le_trans ( Real.log_le_sub_one_of_pos ( by linarith [ hu.out ] ) ) ( by linarith [ hu.out ] ) ) ( by positivity ) ;
          convert MeasureTheory.IntegrableOn.union ‹IntegrableOn ( fun u : ℝ => |Real.log u| * Real.exp ( -u ) ) ( Set.Ioc 0 1 ) volume› ‹IntegrableOn ( fun u : ℝ => |Real.log u| * Real.exp ( -u ) ) ( Set.Ioi 1 ) volume› using 1 ; norm_num;
        simp_all +decide [ mul_add ];
        exact MeasureTheory.Integrable.add ‹_› ‹_›;
      have h_dominated_convergence : Filter.Tendsto (fun s : ℝ => ∫ u in Set.Ioi 0, (u^(s-1) - 1) / (s - 1) * Real.exp (-u)) (nhdsWithin 1 (Set.Ioi 1)) (nhds (∫ u in Set.Ioi 0, Real.log u * Real.exp (-u))) := by
        apply_rules [ MeasureTheory.tendsto_integral_filter_of_dominated_convergence ];
        · filter_upwards [ self_mem_nhdsWithin ] with s hs using Measurable.aestronglyMeasurable ( by exact Measurable.mul ( Measurable.div_const ( by exact Measurable.sub ( measurable_id.pow_const _ ) measurable_const ) _ ) ( Real.continuous_exp.measurable.comp measurable_neg ) );
        · filter_upwards [ Ioo_mem_nhdsGT one_lt_two ] with s hs using Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioi ) fun u hu => h_dominate s hs u hu;
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with u hu;
          have h_lim : Filter.Tendsto (fun s : ℝ => (u^(s-1) - 1) / (s - 1)) (nhdsWithin 1 (Set.Ioi 1)) (nhds (Real.log u)) := by
            have h_pointwise : HasDerivAt (fun s : ℝ => u^(s-1)) (Real.log u) 1 := by
              convert HasDerivAt.rpow ( hasDerivAt_const _ _ ) ( hasDerivAt_id 1 |> HasDerivAt.sub <| hasDerivAt_const _ _ ) _ using 1 <;> aesop;
            rw [ hasDerivAt_iff_tendsto_slope ] at h_pointwise;
            convert h_pointwise.mono_left <| nhdsWithin_mono _ _ using 2 <;> norm_num [ div_eq_inv_mul, slope_def_field ];
          exact h_lim.mul tendsto_const_nhds;
      refine' h_dominated_convergence.congr' _;
      filter_upwards [ Ioo_mem_nhdsGT one_lt_two ] with s hs;
      have h_split : ∫ u in Set.Ioi 0, (u^(s-1) - 1) * Real.exp (-u) = (∫ u in Set.Ioi 0, u^(s-1) * Real.exp (-u)) - (∫ u in Set.Ioi 0, Real.exp (-u)) := by
        rw [ ← MeasureTheory.integral_sub ] ; congr ; ext u ; ring;
        · have h_gamma : ∫ u in Set.Ioi 0, u^(s-1) * Real.exp (-u) = Real.Gamma s := by
            rw [ Real.Gamma_eq_integral ( by linarith [ hs.1 ] ) ] ; congr ; ext ; ring;
          exact ( by contrapose! h_gamma; rw [ MeasureTheory.integral_undef h_gamma ] ; linarith [ Real.Gamma_pos_of_pos ( show 0 < s by linarith [ hs.1 ] ) ] );
        · exact MeasureTheory.integrable_of_integral_eq_one ( by simpa using integral_exp_neg_Ioi_zero );
      simp_all +decide [ div_mul_eq_mul_div, MeasureTheory.integral_div ];
      rw [ Real.Gamma_eq_integral ( by linarith : 0 < s ) ];
      simp +decide [ mul_comm, integral_exp_Iic ]
    refine' tendsto_nhds_unique _ h_lim;
    have h_deriv : HasDerivAt Gamma (deriv Gamma 1) 1 := by
      exact DifferentiableAt.hasDerivAt ( Real.differentiableAt_Gamma fun m => by linarith );
    rw [ hasDerivAt_iff_tendsto_slope ] at h_deriv;
    convert h_deriv.mono_left <| nhdsWithin_mono _ _ using 2 <;> norm_num [ div_eq_inv_mul, slope ];
  exact h_gamma_deriv.symm

/-- The integral of exp(-u) over (a, b] equals exp(-a) - exp(-b). -/
lemma integral_exp_neg_Ioc (a b : ℝ) (hab : a ≤ b) :
    ∫ u in Set.Ioc a b, Real.exp (-u) = Real.exp (-a) - Real.exp (-b) := by
  rw [ ← intervalIntegral.integral_of_le hab, intervalIntegral.integral_comp_neg ] ; norm_num

/-- The integral of |log u| over (0, δ] tends to 0 as δ → 0+. -/
lemma integral_abs_log_near_zero_tendsto :
    Tendsto (fun δ : ℝ => ∫ u in Set.Ioc 0 δ, |Real.log u|)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  have h_small_delta : ∀ δ > 0, δ ≤ 1 → ∫ u in Set.Ioc 0 δ, |Real.log u| = δ * (1 - Real.log δ) := by
    intro δ hδ_pos hδ_le_one
    have h_integral : ∫ u in Set.Ioc (0 : ℝ) δ, |Real.log u| = ∫ u in Set.Ioc (0 : ℝ) δ, -Real.log u := by
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => by rw [ abs_of_nonpos ( Real.log_nonpos hx.1.le ( hx.2.trans hδ_le_one ) ) ] ;
    rw [ h_integral, ← intervalIntegral.integral_of_le hδ_pos.le ];
    norm_num [ hδ_pos.le ] ; ring;
  have h_lim : Filter.Tendsto (fun δ : ℝ => δ * (1 - Real.log δ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have := Real.continuous_mul_log.tendsto 0;
    simpa [ mul_sub ] using Filter.Tendsto.mono_left ( Filter.tendsto_id.mul_const ( 1 : ℝ ) |> Filter.Tendsto.sub <| this ) nhdsWithin_le_nhds;
  exact Filter.Tendsto.congr' ( Filter.eventuallyEq_of_mem ( Ioo_mem_nhdsGT zero_lt_one ) fun x hx => by rw [ h_small_delta x hx.1 hx.2.le ] ) h_lim

/-- For n ≥ 2 and ε ∈ (0, 1], n^{-ε} - (n+1)^{-ε} ≤ ε/n. -/
lemma rpow_diff_le_eps_div (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε) ≤ ε / n := by
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo (n : ℝ) (n + 1), deriv (fun x : ℝ => x ^ (-ε)) c = ((n + 1 : ℝ) ^ (-ε) - (n : ℝ) ^ (-ε)) / ((n + 1 : ℝ) - n) := by
    have := exists_deriv_eq_slope ( f := fun x => x ^ ( -ε ) ) ( show ( n : ℝ ) < ( n + 1 ) by norm_num );
    exact this ( continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.rpow ( continuousAt_id ) continuousAt_const <| Or.inl <| by linarith [ hx.1, show ( n : ℝ ) ≥ 2 by norm_cast ] ) ( fun x hx => by exact DifferentiableAt.differentiableWithinAt <| by apply_rules [ DifferentiableAt.rpow ] <;> norm_num ; linarith [ hx.1, show ( n : ℝ ) ≥ 2 by norm_cast ] );
  norm_num [ show c ≠ 0 by linarith [ hc.1.1 ] ] at hc;
  rw [ show ( -ε - 1 : ℝ ) = - ( 1 + ε ) by ring, Real.rpow_neg ( by linarith ) ] at hc;
  ring_nf at *;
  nlinarith [ inv_anti₀ ( by positivity ) ( show ( c : ℝ ) ^ ( 1 + ε ) ≥ n by exact le_trans ( by norm_num ) ( Real.rpow_le_rpow ( by positivity ) hc.1.1.le ( by positivity ) ) |> le_trans <| Real.rpow_le_rpow_of_exponent_le ( by linarith [ show ( n :ℝ ) ≥ 2 by norm_cast ] ) ( show 1 + ε ≥ 1 by linarith ) ) ]

/-- For n ≥ 2, ε > 0, and u ∈ [ε log n, ε log(n+1)]:
|log u - log(ε log n)| ≤ 1/(n log n). -/
lemma log_diff_on_interval (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε)
    (u : ℝ) (hu1 : ε * Real.log n ≤ u) (hu2 : u ≤ ε * Real.log ((n : ℝ) + 1)) :
    |Real.log u - Real.log (ε * Real.log n)| ≤ 1 / ((n : ℝ) * Real.log n) := by
  have h_mean_value : ∃ c ∈ Set.Ioo (ε * Real.log n) (ε * Real.log (n + 1)), Real.log u - Real.log (ε * Real.log n) = (u - ε * Real.log n) / c := by
    cases eq_or_lt_of_le hu1;
    · exact ⟨ ε * Real.log ( n + 1 ) / 2 + ε * Real.log n / 2, ⟨ by linarith [ show ε * Real.log ( n + 1 ) > ε * Real.log n from mul_lt_mul_of_pos_left ( Real.log_lt_log ( by positivity ) ( by norm_cast; linarith ) ) hε ], by linarith [ show ε * Real.log ( n + 1 ) > ε * Real.log n from mul_lt_mul_of_pos_left ( Real.log_lt_log ( by positivity ) ( by norm_cast; linarith ) ) hε ] ⟩, by aesop ⟩;
    · have := exists_deriv_eq_slope ( Real.log ) ‹_›;
      norm_num at *;
      exact this ( continuousOn_of_forall_continuousAt fun x hx => Real.continuousAt_log <| ne_of_gt <| lt_of_lt_of_le ( mul_pos hε <| Real.log_pos <| Nat.one_lt_cast.mpr hn ) hx.1 ) ( fun x hx => DifferentiableAt.differentiableWithinAt <| Real.differentiableAt_log <| ne_of_gt <| lt_of_lt_of_le ( mul_pos hε <| Real.log_pos <| Nat.one_lt_cast.mpr hn ) hx.1.le ) |> fun ⟨ c, hc1, hc2 ⟩ => ⟨ c, ⟨ hc1.1, hc1.2.trans_le hu2 ⟩, by rw [ eq_div_iff ] at hc2 <;> ring_nf at * <;> linarith ⟩;
  obtain ⟨c, hc1, hc2⟩ := h_mean_value
  have h_bound : (u - ε * Real.log n) / c ≤ (Real.log (n + 1) - Real.log n) / Real.log n := by
    rw [ div_le_div_iff₀ ] <;> nlinarith [ hc1.1, hc1.2, Real.log_pos <| show ( n:ℝ ) > 1 by norm_cast, Real.log_lt_log ( by positivity ) <| show ( n:ℝ ) + 1 > n by norm_num ];
  have h_log_bound : Real.log (n + 1) - Real.log n ≤ 1 / n := by
    rw [ ← Real.log_div ( by positivity ) ( by positivity ) ] ; exact le_trans ( Real.log_le_sub_one_of_pos ( by positivity ) ) ( by ring_nf; norm_num [ show n ≠ 0 by positivity ] ) ;
  rw [ abs_of_nonneg ( sub_nonneg_of_le <| Real.log_le_log ( by exact mul_pos hε <| Real.log_pos <| by norm_cast ) hu1 ) ] ; convert h_bound.trans <| div_le_div_of_nonneg_right h_log_bound <| Real.log_nonneg <| Nat.one_le_cast.2 <| by linarith using 1 ; ring;

/-- The series ∑_{n≥2} 1/(n² log n) converges. -/
lemma summable_inv_sq_log :
    Summable (fun n : ℕ => if (n : ℕ) ≥ 2 then 1 / ((n : ℝ) ^ 2 * Real.log n) else 0) := by
  have h_pseries : Summable (fun n : ℕ => if n ≥ 2 then 1 / (n ^ 2 * Real.log 2) else 0) := by
    rw [ ← summable_nat_add_iff 2 ];
    norm_num;
    exact Summable.mul_left _ <| by simpa using summable_nat_add_iff 2 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two;
  refine Summable.of_nonneg_of_le ( fun n => by split_ifs <;> positivity ) ( fun n => ?_ ) h_pseries;
  split_ifs <;> first | positivity | gcongr ; norm_cast

/-- log ε * (1 - 2^{-ε}) → 0 as ε → 0+. -/
lemma log_eps_one_minus_rpow_tendsto :
    Tendsto (fun ε : ℝ => Real.log ε * (1 - (2 : ℝ) ^ (-ε)))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  have h_approx : Filter.Tendsto (fun ε : ℝ => (1 - 2 ^ (-ε)) / ε) (𝓝[>] 0) (nhds (Real.log 2)) := by
    simpa [ div_eq_inv_mul, Real.rpow_def_of_pos ] using HasDerivAt.tendsto_slope_zero_right ( HasDerivAt.const_sub 1 <| HasDerivAt.exp <| HasDerivAt.const_mul ( -Real.log 2 ) <| hasDerivAt_id 0 );
  convert h_approx.mul ( Real.continuous_mul_log.continuousWithinAt ) using 2 <;> ring;
  by_cases h : ‹ℝ› = 0 <;> simp +decide [ h, mul_assoc, mul_comm, mul_left_comm ] ; ring

/-- The function log(u) * exp(-u) is integrable on (0, ∞). -/
lemma integrable_log_mul_exp_neg :
    IntegrableOn (fun u : ℝ => Real.log u * Real.exp (-u)) (Set.Ioi 0) := by
  have h_split : MeasureTheory.IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Set.Ioc 0 1) ∧ MeasureTheory.IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Set.Ioi 1) := by
    constructor;
    · have h_integrable_left : MeasureTheory.IntegrableOn (fun u => Real.log u) (Set.Ioc 0 1) := by
        rw [ ← intervalIntegrable_iff_integrableOn_Ioc_of_le ] <;> norm_num;
      refine' h_integrable_left.norm.mono' _ _;
      · exact MeasureTheory.AEStronglyMeasurable.mul ( h_integrable_left.aestronglyMeasurable ) ( Continuous.aestronglyMeasurable ( by continuity ) );
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using by rw [ norm_mul, Real.norm_of_nonneg ( Real.exp_pos _ |> le_of_lt ) ] ; exact mul_le_of_le_one_right ( norm_nonneg _ ) ( Real.exp_le_one_iff.mpr <| by linarith [ hx.1, hx.2 ] ) ;
    · have h_integrable : MeasureTheory.IntegrableOn (fun u => u * Real.exp (-u)) (Set.Ioi 1) := by
        have := @integral_rpow_mul_exp_neg_rpow 1;
        specialize @this 1 ; norm_num at this;
        exact MeasureTheory.IntegrableOn.mono_set ( by exact ( by contrapose! this; rw [ MeasureTheory.integral_undef this ] ; norm_num ) ) ( Set.Ioi_subset_Ioi zero_le_one );
      refine' h_integrable.mono' _ _;
      · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( Real.measurable_log ) ( Real.continuous_exp.measurable.comp measurable_neg ) );
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with x hx using by rw [ Real.norm_eq_abs, abs_of_nonneg ( mul_nonneg ( Real.log_nonneg hx.out.le ) ( Real.exp_nonneg _ ) ) ] ; exact mul_le_mul_of_nonneg_right ( le_trans ( Real.log_le_sub_one_of_pos ( zero_lt_one.trans hx.out ) ) ( by linarith ) ) ( Real.exp_nonneg _ ) ;
  convert h_split.1.union h_split.2 using 1 ; norm_num

/-- The integral of |log u * exp(-u)| over (0, δ] tends to 0 as δ → 0+. -/
lemma integral_log_exp_near_zero_tendsto :
    Tendsto (fun δ : ℝ => ∫ u in Set.Ioc 0 δ, |Real.log u * Real.exp (-u)|)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  have h_log_abs : ∀ δ : ℝ, 0 < δ → ∫ u in Set.Ioc 0 δ, |Real.log u * Real.exp (-u)| ≤ ∫ u in Set.Ioc 0 δ, |Real.log u| := by
    intro δ hδ; refine' MeasureTheory.integral_mono_of_nonneg _ _ _ <;> norm_num [ abs_mul ];
    · exact Filter.eventually_inf_principal.mpr ( Filter.Eventually.of_forall fun x hx => by positivity );
    · have h_integrable : MeasureTheory.IntegrableOn (fun u => Real.log u) (Set.Ioc 0 δ) := by
        rw [ ← intervalIntegrable_iff_integrableOn_Ioc_of_le hδ.le ] ; aesop;
      exact h_integrable.abs;
    · exact Filter.eventually_inf_principal.mpr ( Filter.Eventually.of_forall fun x hx => mul_le_of_le_one_right ( abs_nonneg _ ) ( Real.exp_le_one_iff.mpr <| by linarith [ hx.1 ] ) );
  refine' squeeze_zero_norm' _ integral_abs_log_near_zero_tendsto;
  filter_upwards [ self_mem_nhdsWithin ] with δ hδ using by rw [ Real.norm_of_nonneg ( MeasureTheory.integral_nonneg fun _ => abs_nonneg _ ) ] ; exact h_log_abs δ hδ

/-- The integral of |log u * exp(-u)| over (A, ∞) tends to 0 as A → ∞. -/
lemma integral_log_exp_tail_tendsto :
    Tendsto (fun A : ℝ => ∫ u in Set.Ioi A, |Real.log u * Real.exp (-u)|)
      atTop (𝓝 0) := by
  convert MeasureTheory.tendsto_setIntegral_of_antitone _ _ _ using 1;
  · rw [ show ( ⋂ n : ℝ, Set.Ioi n ) = ∅ by rw [ Set.eq_empty_iff_forall_notMem ] ; rintro x hx; exact absurd ( Set.mem_iInter.mp hx ( x + 1 ) ) ( by norm_num ) ] ; norm_num;
  · infer_instance;
  · exact fun i => measurableSet_Ioi;
  · exact fun x y hxy => Set.Ioi_subset_Ioi hxy;
  · use 1;
    have h_integrable : MeasureTheory.IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Set.Ioi 0) := by
      convert integrable_log_mul_exp_neg using 1;
    exact MeasureTheory.IntegrableOn.mono_set ( h_integrable.abs ) ( Set.Ioi_subset_Ioi zero_le_one )

/-! ### Change of variables and main Riemann sum lemma -/

/-
Change of variables: ε ∫₁^∞ log(log t) t^{-(1+ε)} dt = ε ∫₀^∞ log(u) exp(-εu) du.
Combined with laplace_log_identity, gives the value -γ - log ε.
-/
lemma laplace_log_change_var (ε : ℝ) (hε : 0 < ε) :
    ε * ∫ t in Set.Ioi (1 : ℝ), Real.log (Real.log t) * t ^ (-(1 + ε)) =
    -Real.eulerMascheroniConstant - Real.log ε := by
  -- Use the substitution $u = \log t$ to transform the integral.
  have h_subst : ∫ t in Set.Ioi 1, Real.log (Real.log t) * t ^ (-(1 + ε)) = ∫ u in Set.Ioi 0, Real.log u * Real.exp (-ε * u) := by
    -- Apply the substitution $u = \log t$ to transform the integral.
    have h_subst : ∫ t in Set.Ioi (1 : ℝ), Real.log (Real.log t) * t ^ (-(1 + ε)) = ∫ u in (fun t => Real.log t) '' Set.Ioi (1 : ℝ), Real.log u * Real.exp (-ε * u) := by
      rw [ MeasureTheory.integral_image_eq_integral_abs_deriv_smul ] <;> norm_num [ Real.deriv_log ];
      any_goals intro x hx; exact Real.hasDerivAt_log ( by linarith ) |> HasDerivAt.hasDerivWithinAt;
      · refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => _ ; rw [ abs_of_pos ( inv_pos.mpr <| zero_lt_one.trans hx ) ] ; rw [ Real.rpow_def_of_pos ( zero_lt_one.trans hx ) ] ; ring;
        rw [ sub_eq_add_neg, Real.exp_add, Real.exp_neg, Real.exp_log ( zero_lt_one.trans hx ) ] ; ring;
      · exact fun x hx y hy hxy => Real.log_injOn_pos ( show 0 < x by linarith [ hx.out ] ) ( show 0 < y by linarith [ hy.out ] ) hxy;
    convert h_subst using 3 ; norm_num [ Set.ext_iff ];
    exact fun x => ⟨ fun hx => ⟨ Real.exp x, by norm_num; linarith, by norm_num ⟩, fun ⟨ y, hy, hy' ⟩ => hy'.symm ▸ Real.log_pos hy ⟩;
  -- Use the substitution $v = \epsilon u$ to transform the integral.
  have h_subst_v : ∫ u in Set.Ioi 0, Real.log u * Real.exp (-ε * u) = (1 / ε) * ∫ v in Set.Ioi 0, (Real.log v - Real.log ε) * Real.exp (-v) := by
    have h_subst_v : ∫ u in Set.Ioi 0, Real.log u * Real.exp (-ε * u) = (1 / ε) * ∫ v in Set.Ioi 0, Real.log (v / ε) * Real.exp (-v) := by
      have h_subst' : ∀ {f : ℝ → ℝ}, ∫ u in Set.Ioi 0, f u = (1 / ε) * ∫ v in Set.Ioi 0, f (v / ε) := by
        intro f; simp +decide [ div_eq_inv_mul, MeasureTheory.integral_const_mul, hε.ne' ] ;
        rw [ MeasureTheory.integral_comp_mul_left_Ioi ] <;> norm_num [ hε.ne' ];
        positivity;
      convert h_subst' using 3 ; ring_nf ; norm_num [ hε.ne' ];
      ac_rfl;
    exact h_subst_v.trans ( by refine' congr_arg _ ( MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [ Real.log_div hx.out.ne' hε.ne' ] ) );
  -- Use the fact that $\int_0^\infty \log v \exp(-v) dv = -\gamma$ and $\int_0^\infty \exp(-v) dv = 1$.
  have h_integrals : ∫ v in Set.Ioi 0, Real.log v * Real.exp (-v) = -Real.eulerMascheroniConstant ∧ ∫ v in Set.Ioi 0, Real.exp (-v) = 1 := by
    exact ⟨ by simpa using gamma_integral, by simpa using integral_exp_neg_Ioi 0 ⟩;
  simp_all +decide [ sub_mul ];
  rw [ MeasureTheory.integral_sub, MeasureTheory.integral_const_mul ] <;> norm_num [ h_integrals, hε.ne' ];
  · have := @integrable_log_mul_exp_neg;
    exact this;
  · exact MeasureTheory.Integrable.const_mul ( MeasureTheory.integrable_of_integral_eq_one ( by simpa using integral_exp_neg_Ioi_zero ) ) _

/-- Splitting an integral at a point: ∫_{Ioi 0} f = ∫_{Ioc 0 δ} f + ∫_{Ioi δ} f -/
lemma integral_Ioi_split (δ : ℝ) (hδ : 0 < δ)
    (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Ioi 0)) :
    ∫ u in Set.Ioi 0, f u = (∫ u in Set.Ioc 0 δ, f u) + ∫ u in Set.Ioi δ, f u := by
  have h : Set.Ioi (0 : ℝ) = Set.Ioc 0 δ ∪ Set.Ioi δ := (Set.Ioc_union_Ioi_eq_Ioi hδ.le).symm
  simp only [h, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi (hf.mono_set Set.Ioc_subset_Ioi_self)
    (hf.mono_set (Set.Ioi_subset_Ioi hδ.le))]

/-
Decomposing ∫_{Ioi a₀} f as a tsum of integrals over (aₙ, aₙ₊₁] for a strictly monotone
sequence aₙ tending to ∞.
-/
lemma integral_Ioi_eq_tsum_Ioc (a : ℕ → ℝ) (ha : StrictMono a) (ha_lim : Tendsto a atTop atTop)
    (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Ioi (a 0))) :
    ∫ u in Set.Ioi (a 0), f u = ∑' n, ∫ u in Set.Ioc (a n) (a (n + 1)), f u := by
  convert MeasureTheory.integral_iUnion ?_ ?_ ?_ using 1;
  · congr with x;
    simp +zetaDelta at *;
    constructor <;> intro hx;
    · -- Since $a$ is strictly monotone and tends to infinity, there exists some $n$ such that $a n \geq x$.
      obtain ⟨n, hn⟩ : ∃ n, a n ≥ x := by
        exact ( ha_lim.eventually_ge_atTop x ) |> fun h => h.exists;
      contrapose! hn;
      exact Nat.recOn n ( by linarith ) hn;
    · exact lt_of_le_of_lt ( ha.monotone ( Nat.zero_le _ ) ) hx.choose_spec.1;
  · infer_instance;
  · exact fun i => measurableSet_Ioc;
  · exact fun i j hij => Set.disjoint_left.mpr fun x hx₁ hx₂ => hij <| le_antisymm ( le_of_not_gt fun hi => by linarith [ hx₁.1, hx₁.2, hx₂.1, hx₂.2, ha.monotone hi, ha.monotone ( Nat.succ_le_of_lt hi ) ] ) ( le_of_not_gt fun hj => by linarith [ hx₁.1, hx₁.2, hx₂.1, hx₂.2, ha.monotone hj, ha.monotone ( Nat.succ_le_of_lt hj ) ] );
  · refine' hf.mono_set _;
    exact Set.iUnion_subset fun i => Set.Ioc_subset_Ioi_self.trans ( Set.Ioi_subset_Ioi <| ha.monotone <| Nat.zero_le _ )

/-
Quantitative bound: the Riemann sum T(ε) = ∑ log(ε log n)(n^{-ε} - (n+1)^{-ε})
is within O(ε) + o(1) of -γ.
-/
set_option maxHeartbeats 3200000 in
lemma riemann_sum_bound (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |∑' n : ℕ, (if n ≥ 2 then
      Real.log (ε * Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε))
    else 0) - (-Real.eulerMascheroniConstant)| ≤
    (∫ u in Set.Ioc 0 (ε * Real.log 2), |Real.log u * Real.exp (-u)|) +
    ε * ∑' n : ℕ, (if n ≥ 2 then 1 / ((n : ℝ) ^ 2 * Real.log n) else 0) := by
  -- The proof decomposes -γ = ∫_0^∞ log(u) e^{-u} du into pieces and bounds the Riemann sum error.
  have h_decomp : -Real.eulerMascheroniConstant = (∫ u in Set.Ioc 0 (ε * Real.log 2), Real.log u * Real.exp (-u)) + (∑' n : ℕ, if n ≥ 2 then (∫ u in Set.Ioc (ε * Real.log n) (ε * Real.log (n + 1)), Real.log u * Real.exp (-u)) else 0) := by
    have h_decomp : -Real.eulerMascheroniConstant = (∫ u in Set.Ioc 0 (ε * Real.log 2), Real.log u * Real.exp (-u)) + (∑' n : ℕ, ∫ u in Set.Ioc (ε * Real.log (n + 2)) (ε * Real.log (n + 3)), Real.log u * Real.exp (-u)) := by
      rw [ ← gamma_integral, integral_Ioi_split, integral_Ioi_eq_tsum_Ioc ];
      case a => exact fun n => ε * Real.log ( n + 2 );
      all_goals norm_num [ add_assoc ];
      · exact fun n m hnm => mul_lt_mul_of_pos_left ( Real.log_lt_log ( by positivity ) ( by norm_cast; linarith ) ) hε;
      · exact Filter.Tendsto.const_mul_atTop hε ( Real.tendsto_log_atTop.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop );
      · exact MeasureTheory.IntegrableOn.mono_set ( integrable_log_mul_exp_neg ) ( Set.Ioi_subset_Ioi <| by positivity );
      · positivity;
      · exact?;
    rw [ h_decomp, ← tsum_eq_tsum_of_ne_zero_bij ];
    use fun x => x + 2;
    · aesop_cat;
    · intro x hx; use ⟨ x - 2, by
        rcases x with ( _ | _ | x ) <;> simp_all +decide [ Function.support ];
        exact_mod_cast hx ⟩ ; aesop;
    · norm_num [ add_assoc ];
  -- For each term in the sum, we have:
  have h_term : ∀ n : ℕ, n ≥ 2 → |Real.log (ε * Real.log n) * (n ^ (-ε : ℝ) - (n + 1) ^ (-ε : ℝ)) - (∫ u in Set.Ioc (ε * Real.log n) (ε * Real.log (n + 1)), Real.log u * Real.exp (-u))| ≤ ε / ((n : ℝ) ^ 2 * Real.log n) := by
    intro n hn
    have h_term : |Real.log (ε * Real.log n) * (n ^ (-ε : ℝ) - (n + 1) ^ (-ε : ℝ)) - (∫ u in Set.Ioc (ε * Real.log n) (ε * Real.log (n + 1)), Real.log u * Real.exp (-u))| ≤ (∫ u in Set.Ioc (ε * Real.log n) (ε * Real.log (n + 1)), |Real.log (ε * Real.log n) - Real.log u| * Real.exp (-u)) := by
      have h_term : Real.log (ε * Real.log n) * (n ^ (-ε : ℝ) - (n + 1) ^ (-ε : ℝ)) = ∫ u in Set.Ioc (ε * Real.log n) (ε * Real.log (n + 1)), Real.log (ε * Real.log n) * Real.exp (-u) := by
        rw [ ← intervalIntegral.integral_of_le ( mul_le_mul_of_nonneg_left ( Real.log_le_log ( by positivity ) ( by linarith ) ) hε.le ), intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_neg ] ; norm_num;
        rw [ Real.rpow_def_of_pos ( by positivity ), Real.rpow_def_of_pos ( by positivity ) ] ; ring ; norm_num;
      rw [ h_term, ← MeasureTheory.integral_sub ];
      · convert MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) using 1;
        norm_num [ ← sub_mul, abs_mul, Real.exp_pos ];
      · exact Continuous.integrableOn_Ioc ( by continuity );
      · exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun u hu => by exact ContinuousAt.mul ( Real.continuousAt_log ( by nlinarith [ hu.1, hu.2, show ( 0 :ℝ ) < ε * Real.log n by exact mul_pos hε ( Real.log_pos ( by norm_cast ) ) ] ) ) ( Real.continuous_exp.continuousAt.comp ( ContinuousAt.neg continuousAt_id ) ) ) |> fun h => h.mono_set ( Set.Ioc_subset_Icc_self );
    -- Using the bound from `log_diff_on_interval`, we get:
    have h_bound : ∫ u in Set.Ioc (ε * Real.log n) (ε * Real.log (n + 1)), |Real.log (ε * Real.log n) - Real.log u| * Real.exp (-u) ≤ ∫ u in Set.Ioc (ε * Real.log n) (ε * Real.log (n + 1)), (1 / ((n : ℝ) * Real.log n)) * Real.exp (-u) := by
      refine' MeasureTheory.setIntegral_mono_on _ _ _ _ <;> norm_num;
      · exact ContinuousOn.integrableOn_Icc ( by exact ContinuousOn.mul ( ContinuousOn.abs ( continuousOn_const.sub ( Real.continuousOn_log.mono <| by intro u hu; exact ne_of_gt <| lt_of_lt_of_le ( by exact mul_pos hε <| Real.log_pos <| by norm_cast ) hu.1 ) ) ) <| ContinuousOn.rexp <| ContinuousOn.neg continuousOn_id ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
      · exact Continuous.integrableOn_Ioc ( by continuity );
      · intro u hu₁ hu₂; rw [ abs_sub_comm ] ; gcongr;
        convert log_diff_on_interval n hn ε hε u hu₁.le hu₂ using 1 ; ring;
    -- Using the bound from `rpow_diff_le_eps_div`, we get:
    have h_bound2 : ∫ u in Set.Ioc (ε * Real.log n) (ε * Real.log (n + 1)), Real.exp (-u) ≤ ε / (n : ℝ) := by
      rw [ ← intervalIntegral.integral_of_le ( mul_le_mul_of_nonneg_left ( Real.log_le_log ( by positivity ) ( by linarith ) ) hε.le ), intervalIntegral.integral_comp_neg ] ; norm_num;
      have := rpow_diff_le_eps_div n hn ε hε hε1; simp_all +decide [ Real.rpow_def_of_pos ( by positivity : 0 < ( n : ℝ ) ), Real.rpow_def_of_pos ( by positivity : 0 < ( n + 1 : ℝ ) ) ] ; ring_nf at *; aesop;
    simp_all +decide [ MeasureTheory.integral_const_mul ];
    refine le_trans h_term <| h_bound.trans ?_;
    convert mul_le_mul_of_nonneg_left h_bound2 ( show 0 ≤ ( Real.log n ) ⁻¹ * ( n : ℝ ) ⁻¹ by positivity ) using 1 ; ring;
  -- Applying the triangle inequality to the sum, we get:
  have h_triangle : |(∑' n : ℕ, if n ≥ 2 then Real.log (ε * Real.log n) * (n ^ (-ε : ℝ) - (n + 1) ^ (-ε : ℝ)) else 0) - (∑' n : ℕ, if n ≥ 2 then (∫ u in Set.Ioc (ε * Real.log n) (ε * Real.log (n + 1)), Real.log u * Real.exp (-u)) else 0)| ≤ ε * ∑' n : ℕ, if n ≥ 2 then (1 / ((n : ℝ) ^ 2 * Real.log n)) else 0 := by
    rw [ ← Summable.tsum_sub, ← tsum_mul_left ];
    · refine' le_trans ( le_of_eq ( by rw [ ← Real.norm_eq_abs ] ) ) ( le_trans ( norm_tsum_le_tsum_norm _ ) _ );
      · refine' Summable.of_nonneg_of_le ( fun n => norm_nonneg _ ) ( fun n => _ ) ( Summable.mul_left ε <| summable_inv_sq_log );
        split_ifs <;> simp_all +decide [ div_eq_mul_inv ];
      · refine' Summable.tsum_le_tsum _ _ _;
        · intro n; split_ifs <;> simp_all +decide [ div_eq_mul_inv ] ;
        · refine' Summable.of_nonneg_of_le ( fun n => norm_nonneg _ ) ( fun n => _ ) ( Summable.mul_left ε <| summable_inv_sq_log );
          split_ifs <;> simp_all +decide [ div_eq_mul_inv ];
        · exact Summable.mul_left _ <| by simpa using summable_inv_sq_log;
    · rw [ ← summable_nat_add_iff 2 ] at *;
      have h_summable : Summable (fun n : ℕ => ε / ((n + 2 : ℝ) ^ 2 * Real.log (n + 2))) := by
        have h_summable : Summable (fun n : ℕ => 1 / ((n + 2 : ℝ) ^ 2 * Real.log (n + 2))) := by
          have h_summable : Summable (fun n : ℕ => 1 / ((n + 2 : ℝ) ^ 2 * Real.log 2)) := by
            norm_num +zetaDelta at *;
            exact Summable.mul_left _ <| by simpa using summable_nat_add_iff 2 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two;
          exact h_summable.of_nonneg_of_le ( fun n => one_div_nonneg.mpr <| mul_nonneg ( sq_nonneg _ ) <| Real.log_nonneg <| by linarith ) fun n => one_div_le_one_div_of_le ( mul_pos ( sq_pos_of_pos <| by linarith ) <| Real.log_pos <| by linarith ) <| mul_le_mul_of_nonneg_left ( Real.log_le_log ( by linarith ) <| by linarith ) <| sq_nonneg _;
        convert h_summable.mul_left ε using 2 ; ring;
      have h_summable : Summable (fun n : ℕ => Real.log (ε * Real.log (n + 2)) * ((n + 2 : ℝ) ^ (-ε : ℝ) - (n + 3 : ℝ) ^ (-ε : ℝ)) - (∫ u in Set.Ioc (ε * Real.log (n + 2)) (ε * Real.log (n + 3)), Real.log u * Real.exp (-u))) := by
        have h_summable : Summable (fun n : ℕ => |Real.log (ε * Real.log (n + 2)) * ((n + 2 : ℝ) ^ (-ε : ℝ) - (n + 3 : ℝ) ^ (-ε : ℝ)) - ∫ u in Set.Ioc (ε * Real.log (n + 2)) (ε * Real.log (n + 3)), Real.log u * Real.exp (-u)|) := by
          exact Summable.of_nonneg_of_le ( fun n => abs_nonneg _ ) ( fun n => by exact_mod_cast h_term ( n + 2 ) ( by linarith ) ) h_summable;
        exact h_summable.of_abs;
      convert h_summable.add ( show Summable fun n : ℕ => ∫ u in Set.Ioc ( ε * Real.log ( n + 2 ) ) ( ε * Real.log ( n + 3 ) ), Real.log u * Real.exp ( -u ) from ?_ ) using 2 ; norm_num [ add_assoc ];
      have h_summable : Summable (fun n : ℕ => ∫ u in Set.Ioc (ε * Real.log (n + 2)) (ε * Real.log (n + 3)), |Real.log u * Real.exp (-u)|) := by
        have h_summable : Summable (fun n : ℕ => ∫ u in Set.Ioc (ε * Real.log (n + 2)) (ε * Real.log (n + 3)), |Real.log u * Real.exp (-u)|) := by
          have h_integrable : IntegrableOn (fun u : ℝ => |Real.log u * Real.exp (-u)|) (Set.Ioi (ε * Real.log 2)) := by
            have h_integrable : IntegrableOn (fun u : ℝ => Real.log u * Real.exp (-u)) (Set.Ioi 0) := by
              exact?;
            exact MeasureTheory.IntegrableOn.mono_set ( h_integrable.abs ) ( Set.Ioi_subset_Ioi ( by positivity ) )
          have h_summable : Summable (fun n : ℕ => ∫ u in (ε * Real.log (n + 2))..(ε * Real.log (n + 3)), |Real.log u * Real.exp (-u)|) := by
            have h_integral_split : ∀ N : ℕ, ∑ n ∈ Finset.range N, ∫ u in (ε * Real.log (n + 2))..(ε * Real.log (n + 3)), |Real.log u * Real.exp (-u)| = ∫ u in (ε * Real.log 2)..(ε * Real.log (N + 2)), |Real.log u * Real.exp (-u)| := by
              intro N; induction N <;> simp_all +decide [ add_assoc, Finset.sum_range_succ ] ; ring;
              rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ ContinuousOn.intervalIntegrable ];
              · exact continuousOn_of_forall_continuousAt fun u hu => ContinuousAt.mul ( ContinuousAt.abs ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hu <;> nlinarith [ Real.log_pos one_lt_two, Real.log_le_log ( by positivity ) ( by linarith : ( 2 : ℝ ) ≤ 2 + ↑‹ℕ› ) ] ) ) ) ( Real.continuous_exp.continuousAt.comp ( ContinuousAt.neg continuousAt_id ) );
              · exact continuousOn_of_forall_continuousAt fun u hu => ContinuousAt.mul ( ContinuousAt.abs ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hu <;> nlinarith [ Real.log_pos ( show ( 2 : ℝ ) + ↑‹ℕ› > 1 by linarith ), Real.log_pos ( show ( 3 : ℝ ) + ↑‹ℕ› > 1 by linarith ) ] ) ) ) ( Real.continuous_exp.continuousAt.comp ( ContinuousAt.neg continuousAt_id ) )
            have h_integral_split : Filter.Tendsto (fun N : ℕ => ∫ u in (ε * Real.log 2)..(ε * Real.log (N + 2)), |Real.log u * Real.exp (-u)|) Filter.atTop (nhds (∫ u in Set.Ioi (ε * Real.log 2), |Real.log u * Real.exp (-u)|)) := by
              apply_rules [ MeasureTheory.intervalIntegral_tendsto_integral_Ioi ];
              exact Filter.Tendsto.const_mul_atTop hε ( Real.tendsto_log_atTop.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop );
            rw [ summable_iff_not_tendsto_nat_atTop_of_nonneg ];
            · exact fun h => not_tendsto_atTop_of_tendsto_nhds h_integral_split <| h.congr <| by aesop;
            · exact fun n => intervalIntegral.integral_nonneg ( by gcongr ; linarith ) fun u hu => abs_nonneg _;
          exact h_summable.congr fun n => by rw [ intervalIntegral.integral_of_le ( mul_le_mul_of_nonneg_left ( Real.log_le_log ( by positivity ) ( by linarith ) ) hε.le ) ] ;
        convert h_summable using 1;
      convert h_summable.of_norm_bounded _ using 2;
      · infer_instance;
      · exact fun n => MeasureTheory.norm_integral_le_integral_norm _;
    · -- The series $\sum_{n=2}^\infty \int_{\epsilon \log n}^{\epsilon \log (n+1)} |\log u| e^{-u} du$ is absolutely convergent.
      have h_abs_conv : Summable (fun n : ℕ => if n ≥ 2 then ∫ u in Set.Ioc (ε * Real.log n) (ε * Real.log (n + 1)), |Real.log u * Real.exp (-u)| else 0) := by
        have h_abs_conv : Summable (fun n : ℕ => if n ≥ 2 then ∫ u in Set.Ioc (ε * Real.log n) (ε * Real.log (n + 1)), |Real.log u * Real.exp (-u)| else 0) := by
          have h_integrable : IntegrableOn (fun u : ℝ => |Real.log u * Real.exp (-u)|) (Set.Ioi 0) := by
            exact MeasureTheory.Integrable.abs ( integrable_log_mul_exp_neg )
          have h_summable : Summable (fun n : ℕ => ∫ u in Set.Ioc (ε * Real.log (n + 2)) (ε * Real.log (n + 3)), |Real.log u * Real.exp (-u)|) := by
            have h_summable : Summable (fun n : ℕ => ∫ u in (ε * Real.log (n + 2))..(ε * Real.log (n + 3)), |Real.log u * Real.exp (-u)|) := by
              have h_integral_split : ∀ N : ℕ, ∑ n ∈ Finset.range N, ∫ u in (ε * Real.log (n + 2))..(ε * Real.log (n + 3)), |Real.log u * Real.exp (-u)| = ∫ u in (ε * Real.log 2)..(ε * Real.log (N + 2)), |Real.log u * Real.exp (-u)| := by
                intro N; induction N <;> simp_all +decide [ add_assoc, Finset.sum_range_succ ] ; ring;
                rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ MeasureTheory.IntegrableOn.intervalIntegrable ];
                · exact h_integrable.mono_set ( fun x hx => by cases Set.mem_uIcc.mp hx <;> exact Set.mem_Ioi.mpr <| by nlinarith [ Real.log_pos one_lt_two, Real.log_le_log ( by positivity ) ( by linarith : ( 2 : ℝ ) ≤ 2 + ↑‹ℕ› ) ] );
                · exact h_integrable.mono_set ( fun x hx => by cases Set.mem_uIcc.mp hx <;> exact Set.mem_Ioi.mpr <| by nlinarith [ Real.log_pos <| show ( 2 : ℝ ) + ↑‹ℕ› > 1 by linarith, Real.log_pos <| show ( 3 : ℝ ) + ↑‹ℕ› > 1 by linarith ] )
              have h_integral_split : Filter.Tendsto (fun N : ℕ => ∫ u in (ε * Real.log 2)..(ε * Real.log (N + 2)), |Real.log u * Real.exp (-u)|) Filter.atTop (nhds (∫ u in Set.Ioi (ε * Real.log 2), |Real.log u * Real.exp (-u)|)) := by
                apply_rules [ MeasureTheory.intervalIntegral_tendsto_integral_Ioi ];
                · exact h_integrable.mono_set <| Set.Ioi_subset_Ioi <| by positivity;
                · exact Filter.Tendsto.const_mul_atTop hε ( Real.tendsto_log_atTop.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop );
              rw [ summable_iff_not_tendsto_nat_atTop_of_nonneg ];
              · exact fun h => not_tendsto_atTop_of_tendsto_nhds h_integral_split <| h.congr <| by aesop;
              · exact fun n => intervalIntegral.integral_nonneg ( by gcongr ; linarith ) fun u hu => abs_nonneg _;
            exact h_summable.congr fun n => by rw [ intervalIntegral.integral_of_le ( mul_le_mul_of_nonneg_left ( Real.log_le_log ( by positivity ) ( by linarith ) ) hε.le ) ] ;
          rw [ ← summable_nat_add_iff 2 ];
          convert h_summable using 2 ; norm_num [ add_assoc ];
        convert h_abs_conv using 1;
      refine' .of_norm <| h_abs_conv.of_nonneg_of_le ( fun n => _ ) ( fun n => _ );
      · positivity;
      · split_ifs <;> [ exact MeasureTheory.norm_integral_le_integral_norm _; norm_num ];
  refine' le_trans _ ( add_le_add ( le_of_eq _ ) h_triangle );
  rotate_left;
  exact |∫ u in Set.Ioc 0 ( ε * Real.log 2 ), Real.log u * Real.exp ( -u )|;
  · rw [ abs_of_nonpos ];
    · rw [ ← MeasureTheory.integral_neg ] ; refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => _ ; rw [ abs_of_nonpos ] ; exact mul_nonpos_of_nonpos_of_nonneg ( Real.log_nonpos hx.1.le <| by nlinarith [ hx.2, Real.log_le_sub_one_of_pos zero_lt_two ] ) ( Real.exp_nonneg _ ) ;
    · exact MeasureTheory.setIntegral_nonpos measurableSet_Ioc fun x hx => mul_nonpos_of_nonpos_of_nonneg ( Real.log_nonpos hx.1.le ( by nlinarith [ hx.2, Real.log_le_sub_one_of_pos zero_lt_two ] ) ) ( Real.exp_nonneg _ );
  · grind

end


noncomputable section

/-- The mertensH' constant from the main file, restated here for convenience. -/
def mertensH_val : ℝ := ∑' (p : Nat.Primes), (Real.log (1 / (1 - 1 / (p : ℝ))) - 1 / (p : ℝ))

/-! ### Step 1: The limit of ζ(σ)(σ-1) as σ → 1+ -/

/-
For real σ > 1, the Riemann zeta function equals 1/(σ-1) + γ + O(σ-1).
In particular, (σ-1)·ζ(σ) → 1 and ζ(σ) - 1/(σ-1) → γ.
-/
lemma zeta_near_one_real :
    Filter.Tendsto (fun σ : ℝ => (riemannZeta (σ : ℂ)).re - 1 / (σ - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (𝓝 Real.eulerMascheroniConstant) := by
  have h_zeta : Filter.Tendsto (fun s : ℂ => riemannZeta s - 1 / (s - 1)) (nhdsWithin 1 {1}ᶜ) (nhds (Complex.ofReal (Real.eulerMascheroniConstant))) := by
    convert tendsto_riemannZeta_sub_one_div using 1;
  have := h_zeta.comp ( show Filter.Tendsto ( fun σ : ℝ => ↑σ ) ( nhdsWithin 1 ( Set.Ioi 1 ) ) ( nhdsWithin 1 { 1 } ᶜ ) from ?_ );
  · convert Complex.continuous_re.continuousAt.tendsto.comp this using 2 ; norm_num;
    norm_num [ Complex.normSq, sq ];
  · refine' Filter.Tendsto.inf _ _ <;> norm_num;
    · exact Complex.continuous_ofReal.tendsto 1;
    · exact fun x hx => ne_of_gt hx

/-! ### Step 2: Log ζ(σ) = -log(σ-1) + O(σ-1) -/

/-
As σ → 1+ (real), log(ζ(σ)) + log(σ-1) → 0.
-/
lemma log_zeta_plus_log_sigma_minus_one :
    Filter.Tendsto (fun σ : ℝ => Real.log ((riemannZeta (σ : ℂ)).re) + Real.log (σ - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (𝓝 0) := by
  -- Use the fact that $(σ-1)ζ(σ) → 1$ as $σ → 1+$.
  have h_prod : Filter.Tendsto (fun σ : ℝ => (σ - 1) * (riemannZeta (σ : ℂ)).re) (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
    have h_zeta_approx : Filter.Tendsto (fun σ : ℝ => (σ - 1) * ((riemannZeta (σ : ℂ)).re - 1 / (σ - 1))) (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
      convert Filter.Tendsto.mul ( continuousWithinAt_id.sub continuousWithinAt_const ) ( zeta_near_one_real ) using 2 ; norm_num;
    have := h_zeta_approx.const_add 1;
    simpa using this.congr' ( by filter_upwards [ self_mem_nhdsWithin ] with x hx using by rw [ mul_sub, mul_div_cancel₀ _ ( sub_ne_zero_of_ne hx.out.ne' ) ] ; ring );
  convert Filter.Tendsto.congr' _ ( Filter.Tendsto.log h_prod _ ) using 1 <;> norm_num;
  filter_upwards [ h_prod.eventually ( lt_mem_nhds one_pos ) ] with x hx using by rw [ Real.log_mul ( by aesop ) ( by aesop ) ] ; ring;

/-! ### Step 3: Euler product identity (real-valued) -/

/-
For real σ > 1, ζ(σ) equals the Euler product ∏_p (1 - p^{-σ})^{-1}.
-/
lemma zeta_real_eq_euler_product (σ : ℝ) (hσ : 1 < σ) :
    (riemannZeta (σ : ℂ)).re =
      ∏' (p : Nat.Primes), (1 - (p : ℝ) ^ (-σ))⁻¹ := by
  have h_euler : ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-σ : ℂ))⁻¹ = riemannZeta σ := by
    convert riemannZeta_eulerProduct_tprod _;
    exact_mod_cast hσ;
  convert congr_arg Complex.re h_euler.symm using 1;
  have h_prod_real : ∀ p : Nat.Primes, (1 - (p : ℂ) ^ (-σ : ℂ))⁻¹ = (1 - (p : ℝ) ^ (-σ : ℝ))⁻¹ := by
    norm_num [ Complex.ofReal_cpow, Real.rpow_neg ];
    exact fun p => by rw [ Complex.cpow_neg ] ;
  rw [ tprod_congr h_prod_real ];
  have h_prod_real : Multipliable (fun p : Nat.Primes => (1 - (p : ℝ) ^ (-σ : ℝ))⁻¹) := by
    have h_prod_real : Summable (fun p : Nat.Primes => Real.log (1 - (p : ℝ) ^ (-σ : ℝ))⁻¹) := by
      have h_prod_real : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-σ : ℝ)) := by
        exact_mod_cast Summable.comp_injective ( Real.summable_nat_rpow.2 <| by linarith ) Subtype.coe_injective;
      have h_prod_real : ∀ p : Nat.Primes, Real.log (1 - (p : ℝ) ^ (-σ : ℝ))⁻¹ ≤ 2 * (p : ℝ) ^ (-σ : ℝ) := by
        intro p
        have h_log_bound : Real.log (1 - (p : ℝ) ^ (-σ : ℝ))⁻¹ ≤ 2 * (p : ℝ) ^ (-σ : ℝ) := by
          have h_log_bound_step : ∀ x : ℝ, 0 < x ∧ x ≤ 1 / 2 → Real.log (1 - x)⁻¹ ≤ 2 * x := by
            norm_num +zetaDelta at *;
            exact fun x hx₁ hx₂ => by nlinarith [ Real.log_inv ( 1 - x ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < 1 - x ) ), mul_inv_cancel₀ ( by linarith : ( 1 - x ) ≠ 0 ) ] ;
          apply h_log_bound_step;
          norm_num [ Real.rpow_neg ];
          exact ⟨ Real.rpow_pos_of_pos ( Nat.cast_pos.mpr p.prop.pos ) _, by rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> first | positivity | nlinarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast p.prop.two_le, show ( p : ℝ ) ^ σ ≥ 2 ^ σ by gcongr ; exact_mod_cast p.prop.two_le, Real.rpow_le_rpow_of_exponent_le ( by norm_num : ( 1 : ℝ ) ≤ 2 ) hσ.le ] ⟩;
        exact h_log_bound;
      exact Summable.of_nonneg_of_le ( fun p => Real.log_nonneg <| by exact le_trans ( by norm_num ) <| inv_anti₀ ( sub_pos.mpr <| by simpa using Real.rpow_lt_rpow_of_exponent_lt ( Nat.one_lt_cast.mpr p.2.one_lt ) <| neg_lt_zero.mpr <| by positivity ) <| sub_le_self _ <| by positivity ) h_prod_real <| Summable.mul_left _ <| by assumption;
    have h_prod_real : Multipliable (fun p : Nat.Primes => Real.exp (Real.log (1 - (p : ℝ) ^ (-σ : ℝ))⁻¹)) := by
      refine' ⟨ _, _ ⟩;
      exact Real.exp ( ∑' p : Nat.Primes, Real.log ( 1 - ( p : ℝ ) ^ ( -σ ) ) ⁻¹ );
      convert h_prod_real.hasSum.exp using 1;
      · exact funext fun p => by rw [ Function.comp_apply, Real.exp_eq_exp_ℝ ] ;
      · rw [ Real.exp_eq_exp_ℝ ];
    convert h_prod_real using 1;
    exact funext fun p => by rw [ Real.exp_log ( inv_pos.mpr ( sub_pos.mpr ( by simpa using Real.rpow_lt_rpow_of_exponent_lt ( Nat.one_lt_cast.mpr p.2.one_lt ) ( neg_lt_zero.mpr ( by positivity ) ) ) ) ) ] ;
  convert rfl;
  convert Complex.ofReal_re _;
  convert HasProd.tprod_eq ( HasProd.map ( h_prod_real.hasProd ) ( algebraMap ℝ ℂ ) _ ) using 1;
  exact Complex.continuous_ofReal

/-
For real σ > 1, log ζ(σ) = ∑_p [-log(1 - p^{-σ})].
-/
lemma log_zeta_eq_sum_primes (σ : ℝ) (hσ : 1 < σ) :
    Real.log ((riemannZeta (σ : ℂ)).re) =
      ∑' (p : Nat.Primes), (-Real.log (1 - (p : ℝ) ^ (-σ))) := by
  -- From riemannZeta_eulerProduct_exp_log (Mathlib): exp(∑' p, -log(1 - p^{-s})) = ζ(s) for Re(s) > 1.
  have h_exp_sum : Real.exp (∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-σ))) = (riemannZeta (σ : ℂ)).re := by
    convert congr_arg Complex.re ( riemannZeta_eulerProduct_exp_log ( show 1 < ( σ : ℂ ).re from mod_cast hσ ) ) using 1;
    convert Complex.ofReal_re _;
    rw [ Complex.ofReal_tsum ] ; congr ; ext ; norm_cast ; norm_num [ Real.rpow_def_of_pos, Nat.Prime.pos ];
    rw [ Complex.ofReal_log ( sub_nonneg.2 <| by simpa using Real.rpow_le_rpow_of_exponent_le ( Nat.one_le_cast.2 <| Nat.Prime.pos <| Subtype.property _ ) <| neg_nonpos.2 <| by positivity ) ];
    norm_num [ Complex.ofReal_cpow, Nat.Prime.pos ];
  rw [ ← h_exp_sum, Real.log_exp ]

/-! ### Step 4: Decompose log ζ(σ) = P(σ) + H(σ) -/

/-- The "prime zeta function" P(σ) = ∑_p p^{-σ}. -/
def primeZetaReal (σ : ℝ) : ℝ := ∑' (p : Nat.Primes), (p : ℝ) ^ (-σ)

/-- The "tail" H(σ) = ∑_p ∑_{k≥2} p^{-kσ}/k. -/
def mertensH_sigma (σ : ℝ) : ℝ :=
  ∑' (p : Nat.Primes), ((-Real.log (1 - (p : ℝ) ^ (-σ))) - (p : ℝ) ^ (-σ))

/-
H(σ) → mertensH_val as σ → 1+.
-/
lemma mertensH_sigma_tendsto :
    Filter.Tendsto mertensH_sigma (nhdsWithin 1 (Set.Ioi 1)) (𝓝 mertensH_val) := by
  refine' ( tendsto_tsum_of_dominated_convergence _ _ _ );
  refine' fun p => ( p : ℝ ) ⁻¹ ^ 2 * 2;
  · exact Summable.mul_right _ <| by simpa using Summable.subtype ( Real.summable_one_div_nat_pow.2 one_lt_two ) _;
  · intro p; convert Filter.Tendsto.sub ( Filter.Tendsto.neg ( Filter.Tendsto.log ( tendsto_const_nhds.sub ( tendsto_const_nhds.rpow ( Filter.tendsto_id.mono_left inf_le_left ) _ ) ) _ ) ) ( tendsto_const_nhds.rpow ( Filter.tendsto_id.mono_left inf_le_left ) _ ) using 2 <;> norm_num ; ring;
    rotate_left;
    congr! 1;
    · exact ne_of_gt ( sub_pos_of_lt ( inv_lt_one_of_one_lt₀ ( mod_cast p.2.one_lt ) ) );
    · norm_num [ Real.rpow_neg, Real.inv_rpow ];
  · -- For any prime $p$, we have $|-\log(1 - p^{-\sigma}) - p^{-\sigma}| \leq \frac{p^{-2\sigma}}{1 - p^{-\sigma}}$.
    have h_bound : ∀ p : Nat.Primes, ∀ σ : ℝ, 1 ≤ σ → |-(Real.log (1 - (p : ℝ) ^ (-σ))) - (p : ℝ) ^ (-σ)| ≤ (p : ℝ) ^ (-2 * σ) / (1 - (p : ℝ) ^ (-σ)) := by
      intros p σ hσ
      have h_log_bound : ∀ x : ℝ, 0 < x ∧ x < 1 → |-(Real.log (1 - x)) - x| ≤ x^2 / (1 - x) := by
        intro x hx; rw [ abs_le ] ; constructor <;> nlinarith [ Real.log_inv ( 1 - x ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < 1 - x ) ), Real.log_le_sub_one_of_pos ( by linarith : 0 < 1 - x ), mul_inv_cancel₀ ( by linarith : ( 1 - x ) ≠ 0 ), div_mul_cancel₀ ( x ^ 2 ) ( by linarith : ( 1 - x ) ≠ 0 ) ] ;
      convert h_log_bound ( ( p : ℝ ) ^ ( -σ ) ) ⟨ Real.rpow_pos_of_pos ( Nat.cast_pos.mpr p.prop.pos ) _, by simpa using Real.rpow_lt_rpow_of_exponent_lt ( Nat.one_lt_cast.mpr p.prop.one_lt ) ( neg_lt_zero.mpr ( by positivity ) ) ⟩ using 1 ; ring;
      rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ; ring;
    -- For any prime $p$, we have $|-\log(1 - p^{-\sigma}) - p^{-\sigma}| \leq \frac{p^{-2\sigma}}{1 - p^{-\sigma}} \leq \frac{p^{-2}}{1 - p^{-1}}$.
    have h_bound_simplified : ∀ p : Nat.Primes, ∀ σ : ℝ, 1 ≤ σ → |-(Real.log (1 - (p : ℝ) ^ (-σ))) - (p : ℝ) ^ (-σ)| ≤ (p : ℝ) ^ (-2 : ℝ) / (1 - (p : ℝ) ^ (-1 : ℝ)) := by
      intros p σ hσ
      specialize h_bound p σ hσ
      have h_bound_simplified : (p : ℝ) ^ (-2 * σ) / (1 - (p : ℝ) ^ (-σ)) ≤ (p : ℝ) ^ (-2 : ℝ) / (1 - (p : ℝ) ^ (-1 : ℝ)) := by
        gcongr <;> norm_num;
        · exact lt_of_lt_of_le ( Real.rpow_lt_rpow_of_exponent_lt ( mod_cast p.2.one_lt ) ( show ( -1 : ℝ ) < 0 by norm_num ) ) ( by norm_num );
        · exact_mod_cast p.2.one_lt.le;
        · linarith;
        · exact_mod_cast p.2.one_lt.le;
      exact h_bound.trans h_bound_simplified;
    -- For any prime $p$, we have $\frac{p^{-2}}{1 - p^{-1}} \leq \frac{1}{p^2} \cdot 2$.
    have h_bound_final : ∀ p : Nat.Primes, (p : ℝ) ^ (-2 : ℝ) / (1 - (p : ℝ) ^ (-1 : ℝ)) ≤ (p : ℝ) ^ (-2 : ℝ) * 2 := by
      norm_cast ; norm_num;
      exact fun p => by rw [ div_eq_mul_inv ] ; exact mul_le_mul_of_nonneg_left ( by rw [ inv_eq_one_div, div_le_iff₀ ] <;> nlinarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast p.2.two_le, inv_mul_cancel₀ ( show ( p : ℝ ) ≠ 0 by exact_mod_cast p.2.ne_zero ) ] ) ( by positivity ) ;
    filter_upwards [ self_mem_nhdsWithin ] with σ hσ using fun p => le_trans ( h_bound_simplified p σ hσ.out.le ) ( le_trans ( h_bound_final p ) ( by norm_cast; norm_num ) )

/-
P(σ) + log(σ-1) → -mertensH_val as σ → 1+.
-/
lemma primeZeta_plus_log_tendsto :
    Filter.Tendsto (fun σ : ℝ => primeZetaReal σ + Real.log (σ - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (𝓝 (-mertensH_val)) := by
  have h_decomp : ∀ σ : ℝ, 1 < σ → primeZetaReal σ + Real.log (σ - 1) = (Real.log ((riemannZeta (σ : ℂ)).re) + Real.log (σ - 1)) - mertensH_sigma σ := by
    intro σ hσ
    have h_sum : ∑' (p : Nat.Primes), (-Real.log (1 - (p : ℝ) ^ (-σ))) = ∑' (p : Nat.Primes), (p : ℝ) ^ (-σ) + ∑' (p : Nat.Primes), ((-Real.log (1 - (p : ℝ) ^ (-σ))) - (p : ℝ) ^ (-σ)) := by
      rw [ ← Summable.tsum_add ] ; congr ; ext p ; ring;
      · exact Summable.subtype ( Real.summable_nat_rpow.2 <| by linarith ) _;
      · -- We'll use the fact that if the series $\sum_{p} p^{-\sigma}$ converges, then the series $\sum_{p} (-\log(1 - p^{-\sigma}) - p^{-\sigma})$ also converges.
        have h_summable : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-σ)) := by
          exact Summable.subtype ( Real.summable_nat_rpow.2 <| by linarith ) _;
        refine' .of_nonneg_of_le ( fun p => _ ) ( fun p => _ ) ( h_summable.mul_left 2 );
        · linarith [ Real.log_le_sub_one_of_pos ( show 0 < 1 - ( p : ℝ ) ^ ( -σ ) by exact sub_pos.mpr ( by simpa using Real.rpow_lt_rpow_of_exponent_lt ( Nat.one_lt_cast.mpr p.prop.one_lt ) ( neg_lt_zero.mpr ( by positivity ) ) ) ) ];
        · have h_log_bound : ∀ x : ℝ, 0 < x ∧ x ≤ 1 / 2 → -Real.log (1 - x) ≤ 2 * x := by
            exact fun x hx => by nlinarith [ Real.log_inv ( 1 - x ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < 1 - x ) ), mul_inv_cancel₀ ( by linarith : ( 1 - x ) ≠ 0 ) ] ;
          have h_log_bound : 0 < (p : ℝ) ^ (-σ) ∧ (p : ℝ) ^ (-σ) ≤ 1 / 2 := by
            norm_num [ Real.rpow_neg ];
            exact ⟨ Real.rpow_pos_of_pos ( Nat.cast_pos.mpr p.prop.pos ) _, by rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> first | positivity | nlinarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast p.prop.two_le, show ( p : ℝ ) ^ σ ≥ p by exact le_trans ( by norm_num ) ( Real.rpow_le_rpow_of_exponent_le ( Nat.one_le_cast.mpr p.prop.pos ) hσ.le ) ] ⟩;
          linarith [ ‹∀ x : ℝ, 0 < x ∧ x ≤ 1 / 2 → -Real.log ( 1 - x ) ≤ 2 * x› _ h_log_bound ];
    linarith! [ log_zeta_eq_sum_primes σ hσ ];
  rw [ Filter.tendsto_congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by rw [ h_decomp x hx ] ) ] ; convert ( log_zeta_plus_log_sigma_minus_one.sub mertensH_sigma_tendsto ) using 1 ; ring;

/-! ### Step 5: Abel summation + Abelian theorem -/

/-
Abel summation for the prime zeta function: discrete version.
For ε > 0: ∑_p (1/p)·p^{-ε} = ∑_{n≥2} A(n)·(n^{-ε} - (n+1)^{-ε}) where A(n) = ∑_{p≤n} 1/p.
-/
lemma abel_summation_primeZeta (ε : ℝ) (hε : 0 < ε) :
    primeZetaReal (1 + ε) =
      ∑' n : ℕ, (if n ≥ 2 then
        (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, 1 / (p : ℝ)) *
        ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε))
      else 0) := by
  -- By definition of primeZetaReal, we have primeZetaReal (1 + ε) = ∑' p : Nat.Primes, (p : ℝ) ^ (-(1 + ε)).
  have h_primeZetaReal : primeZetaReal (1 + ε) = ∑' p : Nat.Primes, (1 / (p : ℝ)) * (p : ℝ) ^ (-ε) := by
    unfold primeZetaReal;
    norm_num [ Real.rpow_add, Real.rpow_neg, mul_comm ];
    exact tsum_congr fun p => by rw [ Real.rpow_add ( Nat.cast_pos.mpr p.2.pos ), Real.rpow_neg ( Nat.cast_nonneg _ ), Real.rpow_neg_one ] ; ring;
  have h_abel_summation : ∀ N : ℕ, ∑ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), (1 / (p : ℝ)) * (p : ℝ) ^ (-ε) = (∑ n ∈ Finset.Icc 2 N, (∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (1 / (p : ℝ))) * ((n : ℝ) ^ (-ε) - (n + 1 : ℝ) ^ (-ε))) + (∑ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), (1 / (p : ℝ))) * (N + 1 : ℝ) ^ (-ε) := by
    intro N; induction' N with N ih <;> norm_num [ Finset.sum_range_succ, Finset.sum_filter ] at *;
    rcases N with ( _ | N ) <;> simp_all +decide [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
    norm_num [ Finset.sum_range_succ ] ; ring;
    grind;
  -- Let's choose any $N$ and look at the expression.
  have h_limit : Filter.Tendsto (fun N : ℕ => ∑ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), (1 / (p : ℝ)) * (p : ℝ) ^ (-ε)) Filter.atTop (nhds (primeZetaReal (1 + ε))) := by
    have h_limit : Summable (fun p : Nat.Primes => (1 / (p : ℝ)) * (p : ℝ) ^ (-ε)) := by
      have h_summable : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(1 + ε))) := by
        exact Summable.subtype ( Real.summable_nat_rpow.2 <| by linarith ) _;
      convert h_summable using 2 ; norm_num [ Real.rpow_add, Real.rpow_neg ] ; ring;
      rw [ ← Real.rpow_neg ( Nat.cast_nonneg _ ), ← Real.rpow_neg_one, ← Real.rpow_add ( Nat.cast_pos.mpr <| Nat.Prime.pos <| Subtype.property _ ) ] ; ring;
    convert h_limit.hasSum.comp _;
    rotate_left;
    use fun N => Finset.filter ( fun p => Nat.Prime p.val ) ( Finset.filter ( fun p => p.val ≤ N ) ( Finset.subtype ( fun p => Nat.Prime p ) ( Finset.range ( N + 1 ) ) ) );
    · simp +decide [ SummationFilter.unconditional ];
      rw [ Filter.tendsto_atTop_atTop ];
      intro b; use b.sup ( fun p => p.val ) ; intro a ha; intro p hp; simp_all +decide [ Finset.subset_iff ] ;
      exact ⟨ Finset.mem_subtype.mpr ( Finset.mem_range.mpr ( Nat.lt_succ_of_le ( ha p hp ) ) ), p.2 ⟩;
    · refine' Finset.sum_bij ( fun p hp => ⟨ p, by aesop ⟩ ) _ _ _ _ <;> simp +decide;
      · exact fun a ha ha' => ⟨ ⟨ Finset.mem_subtype.mpr <| Finset.mem_range.mpr <| Nat.lt_succ_of_le ha, ha ⟩, ha' ⟩;
      · grind;
      · exact fun p hp hp' hp'' => ⟨ p, ⟨ hp', hp'' ⟩, rfl ⟩;
  have h_limit_zero : Filter.Tendsto (fun N : ℕ => (∑ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), (1 / (p : ℝ))) * (N + 1 : ℝ) ^ (-ε)) Filter.atTop (nhds 0) := by
    -- We'll use the fact that $\sum_{p \leq N} \frac{1}{p}$ is bounded above by $\log \log N + C$ for some constant $C$.
    have h_bound : ∃ C : ℝ, ∀ N : ℕ, N ≥ 2 → (∑ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), (1 / (p : ℝ))) ≤ Real.log (Real.log N) + C := by
      obtain ⟨ M, hM ⟩ := prime_reciprocal_sum_convergence;
      have := hM.bddAbove_range;
      exact ⟨ this.choose, fun N hN => by linarith [ this.choose_spec ( Set.mem_range_self N ) ] ⟩;
    -- Using the bound, we can show that the limit is zero.
    obtain ⟨C, hC⟩ := h_bound;
    have h_lim_zero : Filter.Tendsto (fun N : ℕ => (Real.log (Real.log N) + C) * (N + 1 : ℝ) ^ (-ε)) Filter.atTop (nhds 0) := by
      -- We'll use the fact that $(N + 1)^{-\epsilon}$ tends to $0$ faster than $\log \log N$ tends to infinity.
      have h_lim_zero : Filter.Tendsto (fun N : ℕ => (Real.log (Real.log N)) * (N + 1 : ℝ) ^ (-ε)) Filter.atTop (nhds 0) := by
        -- We can use the fact that $(N + 1)^{-\epsilon}$ tends to $0$ faster than $\log \log N$ tends to infinity.
        have h_lim_zero : Filter.Tendsto (fun N : ℕ => (Real.log N) * (N : ℝ) ^ (-ε)) Filter.atTop (nhds 0) := by
          -- Let $y = \log x$, therefore the expression becomes $\frac{y}{e^{y \epsilon}}$.
          suffices h_log : Filter.Tendsto (fun y : ℝ => y * Real.exp (-y * ε)) Filter.atTop (nhds 0) by
            have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
            refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with N hN using by simp +decide [ Real.rpow_def_of_pos ( Nat.cast_pos.mpr hN ), mul_comm ] );
          -- Let $z = y \epsilon$, therefore the expression becomes $\frac{z}{e^z}$.
          suffices h_z : Filter.Tendsto (fun z : ℝ => z * Real.exp (-z)) Filter.atTop (nhds 0) by
            have := h_z.comp ( Filter.tendsto_id.atTop_mul_const hε );
            convert this.div_const ε using 2 <;> norm_num [ div_eq_mul_inv, mul_assoc, mul_comm ε, hε.ne' ];
          convert ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 ) using 2 ; norm_num;
        refine' squeeze_zero_norm' _ h_lim_zero;
        filter_upwards [ Filter.eventually_gt_atTop 2 ] with N hN;
        rw [ Real.norm_of_nonneg ( mul_nonneg ( Real.log_nonneg ( show 1 ≤ Real.log N by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( N : ℝ ) ≥ 3 by norm_cast ] ) ) ) ( Real.rpow_nonneg ( by positivity ) _ ) ) ];
        exact mul_le_mul ( Real.log_le_sub_one_of_pos ( Real.log_pos ( by norm_cast; linarith ) ) |> le_trans <| by linarith ) ( by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> norm_num <;> linarith [ show ( N : ℝ ) ≥ 3 by norm_cast ] ) ( by positivity ) ( by exact Real.log_nonneg <| by linarith [ show ( N : ℝ ) ≥ 3 by norm_cast ] );
      simpa [ add_mul ] using h_lim_zero.add ( tendsto_const_nhds.mul ( tendsto_rpow_neg_atTop hε |> Filter.Tendsto.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) );
    refine' squeeze_zero_norm' _ h_lim_zero;
    filter_upwards [ Filter.eventually_ge_atTop 2 ] with N hN using by rw [ Real.norm_of_nonneg ( mul_nonneg ( Finset.sum_nonneg fun _ _ => by positivity ) ( by positivity ) ) ] ; exact mul_le_mul_of_nonneg_right ( hC N hN ) ( by positivity ) ;
  have h_limit_sum : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 2 N, (∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (1 / (p : ℝ))) * ((n : ℝ) ^ (-ε) - (n + 1 : ℝ) ^ (-ε))) Filter.atTop (nhds (primeZetaReal (1 + ε))) := by
    simpa using h_limit.sub h_limit_zero |> Filter.Tendsto.congr ( by aesop );
  refine' tendsto_nhds_unique h_limit_sum _;
  have h_limit_sum : Summable (fun n : ℕ => if n ≥ 2 then (∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)), (1 / (p : ℝ))) * ((n : ℝ) ^ (-ε) - (n + 1 : ℝ) ^ (-ε)) else 0) := by
    rw [ summable_iff_not_tendsto_nat_atTop_of_nonneg ];
    · intro H;
      convert not_tendsto_atTop_of_tendsto_nhds h_limit_sum _;
      convert H.comp ( Filter.tendsto_add_atTop_nat 1 ) using 2 ; norm_num [ Finset.sum_range_succ' ];
      erw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, add_left_comm, add_assoc ];
      cases ‹_› <;> norm_num [ add_comm, add_left_comm, add_assoc, Finset.sum_range_succ' ];
    · intro n; split_ifs <;> norm_num;
      exact mul_nonneg ( Finset.sum_nonneg fun _ _ => by positivity ) ( sub_nonneg_of_le <| by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> norm_num <;> linarith );
  convert h_limit_sum.hasSum.tendsto_sum_nat.comp ( Filter.tendsto_add_atTop_nat 1 ) using 1;
  ext ( _ | N ) <;> norm_num [ Finset.sum_range_succ' ];
  erw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, add_left_comm, add_assoc ]

/-
Abelian theorem for bounded convergent sequences: if r(n) → 0 and r is bounded,
then ∑ r(n) · (n^{-ε} - (n+1)^{-ε}) → 0 as ε → 0+.
-/
lemma abelian_theorem_bounded_convergent (r : ℕ → ℝ) (hr_bdd : ∃ C, ∀ n, |r n| ≤ C)
    (hr_lim : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun ε : ℝ =>
      ∑' n : ℕ, (if n ≥ 2 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  rcases hr_bdd with ⟨ C, hC ⟩ ; have := @hC 0 ; norm_num at this ⊢;
  -- For any $\delta > 0$, choose $N$ large enough that $\sup_{n > N} |r(n)| < \delta$.
  have h_sup : ∀ δ > 0, ∃ N : ℕ, ∀ n > N, |r n| < δ := by
    exact fun δ δ_pos => by rcases Metric.tendsto_atTop.mp hr_lim δ δ_pos with ⟨ N, hN ⟩ ; exact ⟨ N, fun n hn => by simpa using hN n hn.le ⟩ ;
  -- For any $\delta > 0$, choose $N$ large enough that $\sup_{n > N} |r(n)| < \delta$. Then for $\varepsilon$ sufficiently small, the sum can be bounded.
  have h_bound : ∀ δ > 0, ∃ N : ℕ, ∀ ε : ℝ, 0 < ε → ε < 1 → |∑' n : ℕ, (if n ≥ 2 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)| ≤ C * (2 ^ (-ε) - (N + 1 : ℝ) ^ (-ε)) + δ * (N + 1 : ℝ) ^ (-ε) := by
    intro δ hδ_pos
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n > N, |r n| < δ := h_sup δ hδ_pos
    use N + 1
    intro ε hε_pos hε_lt_1
    have h_split : |∑' n : ℕ, (if n ≥ 2 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)| ≤ |∑ n ∈ Finset.Icc 2 (N + 1), r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε))| + |∑' n : ℕ, (if n > N + 1 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)| := by
      have h_split : ∑' n : ℕ, (if n ≥ 2 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) = (∑ n ∈ Finset.Icc 2 (N + 1), r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε))) + (∑' n : ℕ, (if n > N + 1 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)) := by
        have h_split : ∑' n : ℕ, (if n ≥ 2 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) = ∑' n : ℕ, (if n ≥ 2 ∧ n ≤ N + 1 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) + ∑' n : ℕ, (if n > N + 1 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) := by
          rw [ ← Summable.tsum_add ];
          · grind;
          · refine' summable_of_ne_finset_zero _;
            exacts [ Finset.Icc 2 ( N + 1 ), fun n hn => if_neg fun h => hn <| Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ];
          · have h_summable : Summable (fun n : ℕ => r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε))) := by
              have h_summable : Summable (fun n : ℕ => (n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) := by
                have h_telescope : ∀ N : ℕ, ∑ n ∈ Finset.range N, ((n + 1 : ℝ) ^ (-ε) - (n + 2 : ℝ) ^ (-ε)) = 1 - (N + 1 : ℝ) ^ (-ε) := by
                  exact fun N => by induction' N with N ih <;> norm_num [ add_assoc, Finset.sum_range_succ ] at * ; linarith;
                rw [ ← summable_nat_add_iff 1 ];
                rw [ summable_iff_not_tendsto_nat_atTop_of_nonneg ];
                · norm_num [ add_assoc, h_telescope ];
                  exact not_tendsto_atTop_of_tendsto_nhds ( tendsto_const_nhds.sub ( tendsto_rpow_neg_atTop ( by linarith ) |> Filter.Tendsto.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) );
                · exact fun n => sub_nonneg_of_le <| by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> norm_num <;> linarith;
              exact Summable.of_norm <| by simpa [ abs_mul ] using Summable.of_nonneg_of_le ( fun n => mul_nonneg ( abs_nonneg _ ) ( abs_nonneg _ ) ) ( fun n => mul_le_mul_of_nonneg_right ( hC n ) ( abs_nonneg _ ) ) ( h_summable.norm.mul_left C ) ;
            rw [ ← summable_nat_add_iff ( N + 2 ) ] at *;
            exact h_summable.congr fun n => by rw [ if_pos ( by linarith ) ] ;
        convert h_split using 2;
        rw [ tsum_eq_sum ];
        exacts [ Finset.sum_congr rfl fun x hx => by rw [ if_pos ⟨ by linarith [ Finset.mem_Icc.mp hx ], by linarith [ Finset.mem_Icc.mp hx ] ⟩ ], fun x hx => if_neg <| by simpa using hx ];
      grind +qlia;
    -- Bound the first part of the sum.
    have h_first_part : |∑ n ∈ Finset.Icc 2 (N + 1), r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε))| ≤ C * (2 ^ (-ε) - (N + 2 : ℝ) ^ (-ε)) := by
      have h_first_part : |∑ n ∈ Finset.Icc 2 (N + 1), r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε))| ≤ C * ∑ n ∈ Finset.Icc 2 (N + 1), ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) := by
        rw [ Finset.mul_sum _ _ _ ];
        exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun i hi => by rw [ abs_mul, abs_of_nonneg ( sub_nonneg_of_le <| Real.rpow_le_rpow_of_nonpos ( by norm_cast; linarith [ Finset.mem_Icc.mp hi ] ) ( by linarith ) <| by linarith ) ] ; exact mul_le_mul_of_nonneg_right ( hC i ) <| sub_nonneg_of_le <| Real.rpow_le_rpow_of_nonpos ( by norm_cast; linarith [ Finset.mem_Icc.mp hi ] ) ( by linarith ) <| by linarith );
      convert h_first_part using 2;
      erw [ Finset.sum_Ico_eq_sum_range ];
      convert rfl using 1;
      convert Finset.sum_range_sub' _ _ using 3 <;> push_cast <;> ring;
    -- Bound the second part of the sum.
    have h_second_part : |∑' n : ℕ, (if n > N + 1 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)| ≤ δ * ∑' n : ℕ, (if n > N + 1 then ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) := by
      rw [ ← tsum_mul_left ];
      have h_second_part : ∀ n : ℕ, |(if n > N + 1 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)| ≤ δ * (if n > N + 1 then ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) := by
        intro n; split_ifs <;> norm_num [ abs_mul, abs_of_nonneg, Real.rpow_nonneg, hε_pos.le ];
        rw [ abs_of_nonneg ( sub_nonneg_of_le <| by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> norm_num <;> linarith ) ] ; exact mul_le_mul_of_nonneg_right ( le_of_lt <| hN n <| by linarith ) <| sub_nonneg_of_le <| by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> norm_num <;> linarith;
      refine' le_trans ( le_of_eq ( by rw [ ← Real.norm_eq_abs ] ) ) ( le_trans ( norm_tsum_le_tsum_norm _ ) _ );
      · refine' Summable.of_nonneg_of_le ( fun n => abs_nonneg _ ) ( fun n => h_second_part n ) _;
        refine' Summable.mul_left _ _;
        rw [ ← summable_nat_add_iff ( N + 2 ) ];
        -- The series $\sum_{n=0}^{\infty} (n + N + 2)^{-\epsilon} - (n + N + 3)^{-\epsilon}$ is a telescoping series.
        have h_telescoping : ∀ N : ℕ, Summable (fun n : ℕ => (n + N + 2 : ℝ) ^ (-ε) - (n + N + 3 : ℝ) ^ (-ε)) := by
          intro N;
          refine' summable_iff_not_tendsto_nat_atTop_of_nonneg ( fun n => sub_nonneg_of_le <| Real.rpow_le_rpow_of_nonpos ( by positivity ) ( by linarith ) <| by linarith ) |>.2 _;
          -- The series $\sum_{n=0}^{\infty} \left( (n + N + 2)^{-\epsilon} - (n + N + 3)^{-\epsilon} \right)$ is a telescoping series, so most terms cancel out.
          have h_telescoping : ∀ n : ℕ, ∑ i ∈ Finset.range n, ((i + N + 2 : ℝ) ^ (-ε) - (i + N + 3 : ℝ) ^ (-ε)) = (N + 2 : ℝ) ^ (-ε) - (n + N + 2 : ℝ) ^ (-ε) := by
            exact fun n => by convert Finset.sum_range_sub' _ _ using 3 <;> push_cast <;> ring;
          exact fun h => absurd ( h.congr h_telescoping ) ( by exact not_tendsto_atTop_of_tendsto_nhds ( by simpa using tendsto_const_nhds.sub ( tendsto_rpow_neg_atTop hε_pos |> Filter.Tendsto.comp <| Filter.tendsto_atTop_mono ( fun n => by linarith ) tendsto_natCast_atTop_atTop ) ) );
        convert h_telescoping N using 2 ; norm_num ; ring;
        rw [ if_pos ( by linarith ) ];
      · refine' Summable.tsum_le_tsum h_second_part _ _;
        · refine' Summable.of_nonneg_of_le ( fun n => norm_nonneg _ ) ( fun n => h_second_part n ) _;
          refine' Summable.mul_left _ _;
          rw [ ← summable_nat_add_iff ( N + 2 ) ];
          -- The series $\sum_{n=0}^{\infty} \left( (n + N + 2)^{-\epsilon} - (n + N + 3)^{-\epsilon} \right)$ is a telescoping series.
          have h_telescoping : ∀ N : ℕ, Summable (fun n : ℕ => ((n + N + 2 : ℝ) ^ (-ε) - (n + N + 3 : ℝ) ^ (-ε))) := by
            intro N;
            refine' summable_iff_not_tendsto_nat_atTop_of_nonneg ( fun n => sub_nonneg_of_le <| Real.rpow_le_rpow_of_nonpos ( by positivity ) ( by linarith ) <| by linarith ) |>.2 _;
            -- The series $\sum_{n=0}^{\infty} \left( (n + N + 2)^{-\epsilon} - (n + N + 3)^{-\epsilon} \right)$ is a telescoping series, so most terms cancel out.
            have h_telescoping : ∀ n : ℕ, ∑ i ∈ Finset.range n, ((i + N + 2 : ℝ) ^ (-ε) - (i + N + 3 : ℝ) ^ (-ε)) = (N + 2 : ℝ) ^ (-ε) - (n + N + 2 : ℝ) ^ (-ε) := by
              exact fun n => by convert Finset.sum_range_sub' _ _ using 3 <;> push_cast <;> ring;
            exact fun h => absurd ( h.congr h_telescoping ) ( by exact not_tendsto_atTop_of_tendsto_nhds ( by simpa using tendsto_const_nhds.sub ( tendsto_rpow_neg_atTop hε_pos |> Filter.Tendsto.comp <| Filter.tendsto_atTop_mono ( fun n => by linarith ) tendsto_natCast_atTop_atTop ) ) );
          convert h_telescoping N using 2 ; norm_num ; ring;
          rw [ if_pos ( by linarith ) ];
        · refine' Summable.mul_left _ _;
          rw [ ← summable_nat_add_iff ( N + 2 ) ];
          -- The series $\sum_{n=0}^{\infty} \left( \frac{1}{(n+N+2)^{\varepsilon}} - \frac{1}{(n+N+3)^{\varepsilon}} \right)$ is a telescoping series.
          have h_telescoping : ∀ N : ℕ, Summable (fun n : ℕ => (n + N + 2 : ℝ) ^ (-ε) - (n + N + 3 : ℝ) ^ (-ε)) := by
            intro N;
            refine' summable_iff_not_tendsto_nat_atTop_of_nonneg ( fun n => sub_nonneg_of_le <| Real.rpow_le_rpow_of_nonpos ( by positivity ) ( by linarith ) <| by linarith ) |>.2 _;
            -- The series $\sum_{n=0}^{\infty} \left( (n + N + 2)^{-\epsilon} - (n + N + 3)^{-\epsilon} \right)$ is a telescoping series, so most terms cancel out.
            have h_telescoping : ∀ n : ℕ, ∑ i ∈ Finset.range n, ((i + N + 2 : ℝ) ^ (-ε) - (i + N + 3 : ℝ) ^ (-ε)) = (N + 2 : ℝ) ^ (-ε) - (n + N + 2 : ℝ) ^ (-ε) := by
              exact fun n => by convert Finset.sum_range_sub' _ _ using 3 <;> push_cast <;> ring;
            exact fun h => absurd ( h.congr h_telescoping ) ( by exact not_tendsto_atTop_of_tendsto_nhds ( by simpa using tendsto_const_nhds.sub ( tendsto_rpow_neg_atTop hε_pos |> Filter.Tendsto.comp <| Filter.tendsto_atTop_mono ( fun n => by linarith ) tendsto_natCast_atTop_atTop ) ) );
          convert h_telescoping N using 2 ; norm_num ; ring;
          rw [ if_pos ( by linarith ) ];
    -- The series $\sum_{n=N+2}^{\infty} (n^{-\varepsilon} - (n+1)^{-\varepsilon})$ is a telescoping series.
    have h_telescoping : ∑' n : ℕ, (if n > N + 1 then ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) = (N + 2 : ℝ) ^ (-ε) := by
      have h_telescoping : ∀ M : ℕ, M > N + 1 → ∑ n ∈ Finset.range (M + 1), (if n > N + 1 then ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) = (N + 2 : ℝ) ^ (-ε) - (M + 1 : ℝ) ^ (-ε) := by
        intro M hM; induction hM <;> simp_all +decide [ Finset.sum_range_succ ] ;
        · rw [ Finset.sum_eq_zero fun x hx => if_neg ( by linarith [ Finset.mem_range.mp hx ] ) ] ; ring;
        · rw [ if_pos ( by linarith ) ] ; ring;
      have h_telescoping_limit : Filter.Tendsto (fun M : ℕ => ∑ n ∈ Finset.range (M + 1), (if n > N + 1 then ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)) Filter.atTop (nhds ((N + 2 : ℝ) ^ (-ε))) := by
        rw [ Filter.tendsto_congr' ( Filter.eventuallyEq_of_mem ( Filter.Ioi_mem_atTop ( N + 1 ) ) h_telescoping ) ];
        simpa using tendsto_const_nhds.sub ( tendsto_rpow_neg_atTop hε_pos |> Filter.Tendsto.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop );
      refine' HasSum.tsum_eq _;
      rw [ hasSum_iff_tendsto_nat_of_nonneg ];
      · rwa [ ← Filter.tendsto_add_atTop_iff_nat ];
      · intro n; split_ifs <;> first | positivity | exact sub_nonneg_of_le <| by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> norm_num <;> linarith;
    grind;
  -- As $\varepsilon \to 0^+$, $(N+1)^{-\varepsilon} \to 1$, so the bound tends to $C \cdot (1 - 1) + \delta \cdot 1 = \delta$.
  have h_tendsto : ∀ δ > 0, ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → |∑' n : ℕ, (if n ≥ 2 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)| ≤ 2 * δ := by
    intros δ hδ_pos
    obtain ⟨N, hN⟩ := h_bound δ hδ_pos
    have h_lim : Filter.Tendsto (fun ε : ℝ => C * (2 ^ (-ε) - (N + 1 : ℝ) ^ (-ε)) + δ * (N + 1 : ℝ) ^ (-ε)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (C * (1 - 1) + δ * 1)) := by
      convert Filter.Tendsto.add ( tendsto_const_nhds.mul ( Filter.Tendsto.sub ( tendsto_const_nhds.rpow ( Filter.Tendsto.neg ( Filter.tendsto_id.mono_left inf_le_left ) ) _ ) ( tendsto_const_nhds.rpow ( Filter.Tendsto.neg ( Filter.tendsto_id.mono_left inf_le_left ) ) _ ) ) ) ( tendsto_const_nhds.mul ( tendsto_const_nhds.rpow ( Filter.Tendsto.neg ( Filter.tendsto_id.mono_left inf_le_left ) ) _ ) ) using 2 <;> norm_num; all_goals linarith;
    have := Metric.tendsto_nhdsWithin_nhds.mp h_lim δ hδ_pos;
    obtain ⟨ ε₀, hε₀_pos, hε₀ ⟩ := this; exact ⟨ Min.min ε₀ 1, lt_min hε₀_pos zero_lt_one, fun ε hε₁ hε₂ => le_trans ( hN ε hε₁ ( lt_of_lt_of_le hε₂ ( min_le_right _ _ ) ) ) ( by linarith [ abs_lt.mp ( hε₀ hε₁ ( by simpa [ abs_of_pos hε₁ ] using lt_of_lt_of_le hε₂ ( min_le_left _ _ ) ) ) ] ) ⟩ ;
  rw [ Metric.tendsto_nhdsWithin_nhds ];
  exact fun ε hε => by rcases h_tendsto ( ε / 4 ) ( by positivity ) with ⟨ δ, hδ, H ⟩ ; exact ⟨ δ, hδ, fun x hx₁ hx₂ => by simpa [ abs_mul ] using lt_of_le_of_lt ( H x hx₁ ( by linarith [ abs_lt.mp hx₂ ] ) ) ( by linarith ) ⟩ ;

/-
The integral identity: ε ∫_0^∞ log(u) e^{-εu} du = -γ - log ε.
This follows from Γ'(1) = -γ via substitution v = εu.
-/
lemma laplace_log_identity (ε : ℝ) (hε : 0 < ε) :
    ε * ∫ u in Set.Ioi (0 : ℝ), Real.log u * Real.exp (-ε * u) =
    -Real.eulerMascheroniConstant - Real.log ε := by
  have h_int : ∫ u in Set.Ioi 0, Real.log u * Real.exp (-u) = -Real.eulerMascheroniConstant := by
    -- The integral of log(u) * exp(-u) is the derivative of the Gamma function at 1.
    have h_gamma_deriv : ∫ u in Set.Ioi 0, Real.log u * Real.exp (-u) = deriv (fun s => Real.Gamma s) 1 := by
      have h_gamma_deriv : deriv (fun s => Real.Gamma s) 1 = ∫ u in Set.Ioi 0, Real.log u * Real.exp (-u) := by
        have h_gamma_int : ∀ s > 0, Real.Gamma s = ∫ u in Set.Ioi 0, u^(s-1) * Real.exp (-u) := by
          exact fun s hs => by rw [ Real.Gamma_eq_integral hs ] ; congr; ext; ring;
        -- Apply the dominated convergence theorem to interchange the derivative and the integral.
        have h_dominated_convergence : Filter.Tendsto (fun h => ∫ u in Set.Ioi 0, (u^h - 1) / h * Real.exp (-u)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ u in Set.Ioi 0, Real.log u * Real.exp (-u))) := by
          -- To apply the dominated convergence theorem, we need to show that the integrand is dominated by an integrable function.
          have h_dominated : ∀ h ∈ Set.Ioo 0 1, ∀ u ∈ Set.Ioi 0, |(u^h - 1) / h * Real.exp (-u)| ≤ |Real.log u| * Real.exp (-u) * (u + 1) := by
            intros h hh u hu
            have h_abs : |(u^h - 1) / h| ≤ |Real.log u| * (u + 1) := by
              -- Using the mean value theorem, we can find a $c \in (0, h)$ such that $u^h - 1 = h \cdot u^c \cdot \log u$.
              obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo 0 h, u^h - 1 = h * u^c * Real.log u := by
                have := exists_deriv_eq_slope ( f := fun x => u ^ x ) hh.1;
                norm_num [ Real.rpow_def_of_pos hu, mul_assoc, mul_comm, mul_left_comm ] at *;
                exact this ( Continuous.continuousOn <| by continuity ) ( Differentiable.differentiableOn <| by norm_num ) |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, hc₁, by rw [ eq_div_iff ] at hc₂ <;> linarith ⟩;
              rw [ hc.2, mul_assoc, mul_div_cancel_left₀ _ hh.1.ne' ];
              rw [ abs_mul, mul_comm ];
              by_cases hu1 : u ≤ 1;
              · exact mul_le_mul_of_nonneg_left ( by rw [ abs_of_nonneg ( Real.rpow_nonneg hu.out.le _ ) ] ; exact le_trans ( Real.rpow_le_one hu.out.le hu1 hc.1.1.le ) ( by linarith [ hu.out ] ) ) ( abs_nonneg _ );
              · exact mul_le_mul_of_nonneg_left ( by rw [ abs_of_nonneg ( Real.rpow_nonneg hu.out.le _ ) ] ; exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( by linarith ) ( show c ≤ 1 by linarith [ hc.1.2, hh.2 ] ) ) ( by norm_num ) ) ( abs_nonneg _ );
            rw [ abs_mul, abs_of_nonneg ( Real.exp_pos _ |> LT.lt.le ) ] ; nlinarith [ Real.exp_pos ( -u ) ];
          -- The function $| \log u | e^{-u} (u + 1)$ is integrable on $(0, \infty)$.
          have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => |Real.log u| * Real.exp (-u) * (u + 1)) (Set.Ioi 0) := by
            have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => |Real.log u| * Real.exp (-u) * u) (Set.Ioi 0) := by
              have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => u * Real.exp (-u) * |Real.log u|) (Set.Ioi 0) := by
                have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => u * Real.exp (-u) * |Real.log u|) (Set.Ioc 0 1) := by
                  have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => u * |Real.log u|) (Set.Ioc 0 1) := by
                    have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => u * Real.log u) (Set.Ioc 0 1) := by
                      exact Continuous.integrableOn_Ioc ( Real.continuous_mul_log );
                    refine' h_integrable.norm.congr _;
                    filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with u hu using by rw [ Real.norm_eq_abs, abs_mul, abs_of_nonneg hu.1.le ] ;
                  refine' h_integrable.mono' _ _;
                  · exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.mul ( measurable_id.aestronglyMeasurable ) ( Real.continuous_exp.comp_aestronglyMeasurable ( measurable_neg.aestronglyMeasurable ) ) ) ( Real.measurable_log.norm.aestronglyMeasurable );
                  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with u hu using by rw [ Real.norm_of_nonneg ( mul_nonneg ( mul_nonneg hu.1.le ( Real.exp_nonneg _ ) ) ( abs_nonneg _ ) ) ] ; exact mul_le_mul_of_nonneg_right ( mul_le_of_le_one_right hu.1.le ( Real.exp_le_one_iff.mpr ( neg_nonpos.mpr hu.1.le ) ) ) ( abs_nonneg _ ) ;
                have h_integrable' : MeasureTheory.IntegrableOn (fun u : ℝ => u * Real.exp (-u) * |Real.log u|) (Set.Ioi 1) := by
                  have h_integrable' : MeasureTheory.IntegrableOn (fun u : ℝ => u * Real.exp (-u) * u) (Set.Ioi 1) := by
                    have h_integrable' : MeasureTheory.IntegrableOn (fun u : ℝ => u^2 * Real.exp (-u)) (Set.Ioi 1) := by
                      have h_integrable' : ∫ u in Set.Ioi 0, u^2 * Real.exp (-u) = Real.Gamma 3 := by
                        rw [ h_gamma_int ] <;> norm_num;
                      exact MeasureTheory.IntegrableOn.mono_set ( by exact ( by contrapose! h_integrable'; rw [ MeasureTheory.integral_undef h_integrable' ] ; positivity ) ) ( Set.Ioi_subset_Ioi zero_le_one );
                    exact h_integrable'.congr_fun ( fun x hx => by ring ) measurableSet_Ioi;
                  refine' h_integrable'.mono' _ _;
                  · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( measurable_id.mul ( Real.continuous_exp.measurable.comp measurable_neg ) ) ( Real.measurable_log.norm ) );
                  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with u hu using by rw [ Real.norm_of_nonneg ( mul_nonneg ( mul_nonneg ( by linarith [ hu.out ] ) ( Real.exp_nonneg _ ) ) ( abs_nonneg _ ) ) ] ; exact mul_le_mul_of_nonneg_left ( by rw [ abs_of_nonneg ( Real.log_nonneg hu.out.le ) ] ; exact le_trans ( Real.log_le_sub_one_of_pos ( by linarith [ hu.out ] ) ) ( by linarith [ hu.out ] ) ) ( mul_nonneg ( by linarith [ hu.out ] ) ( Real.exp_nonneg _ ) ) ;
                convert h_integrable.union h_integrable' using 1 ; norm_num;
              exact h_integrable.congr_fun ( fun x hx => by ring ) measurableSet_Ioi;
            have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => |Real.log u| * Real.exp (-u)) (Set.Ioi 0) := by
              have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => |Real.log u| * Real.exp (-u)) (Set.Ioi 1) := by
                refine' h_integrable.mono_set ( Set.Ioi_subset_Ioi zero_le_one ) |> fun h => h.mono' _ _;
                · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( Real.measurable_log.norm ) ( Real.continuous_exp.measurable.comp measurable_neg ) );
                · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with u hu using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact le_mul_of_one_le_right ( by positivity ) hu.out.le;
              have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => |Real.log u| * Real.exp (-u)) (Set.Ioc 0 1) := by
                have h_integrable : MeasureTheory.IntegrableOn (fun u : ℝ => |Real.log u|) (Set.Ioc 0 1) := by
                  have h_integrable : ∫ u in Set.Ioc 0 1, |Real.log u| = 1 := by
                    rw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => abs_of_nonpos ( Real.log_nonpos hx.1.le hx.2 ), ← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_neg ] ; norm_num;
                  exact ( by contrapose! h_integrable; rw [ MeasureTheory.integral_undef h_integrable ] ; norm_num );
                refine' h_integrable.mono' _ _;
                · exact MeasureTheory.AEStronglyMeasurable.mul ( h_integrable.aestronglyMeasurable ) ( Continuous.aestronglyMeasurable ( by continuity ) );
                · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with u hu using by simpa [ abs_mul ] using mul_le_mul_of_nonneg_left ( Real.exp_le_one_iff.mpr <| neg_nonpos.mpr hu.1.le ) <| abs_nonneg <| Real.log u;
              convert h_integrable.union ‹MeasureTheory.IntegrableOn ( fun u => |Real.log u| * Real.exp ( -u ) ) ( Set.Ioi 1 ) MeasureTheory.volume› using 1 ; ext ; aesop;
            simp_all +decide [ mul_add ];
            exact MeasureTheory.Integrable.add ‹_› ‹_›;
          refine' MeasureTheory.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _;
          use fun u => |Real.log u| * Real.exp (-u) * (u + 1);
          · filter_upwards [ self_mem_nhdsWithin ] with n hn using Measurable.aestronglyMeasurable ( by exact Measurable.mul ( Measurable.div_const ( by exact Measurable.sub ( measurable_id.pow_const _ ) measurable_const ) _ ) ( Real.continuous_exp.measurable.comp measurable_neg ) );
          · filter_upwards [ Ioo_mem_nhdsGT zero_lt_one ] with h hh using Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioi ) fun u hu => h_dominated h hh u hu;
          · exact h_integrable;
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with u hu;
            have h_lim : Filter.Tendsto (fun n => (u^n - 1) / n) (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.log u)) := by
              simpa [ div_eq_inv_mul, Real.rpow_def_of_pos hu ] using HasDerivAt.tendsto_slope_zero_right ( HasDerivAt.sub ( HasDerivAt.exp ( HasDerivAt.const_mul ( Real.log u ) ( hasDerivAt_id 0 ) ) ) ( hasDerivAt_const 0 1 ) );
            exact h_lim.mul tendsto_const_nhds;
        have h_deriv : Filter.Tendsto (fun h => (Real.Gamma (1 + h) - Real.Gamma 1) / h) (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ u in Set.Ioi 0, Real.log u * Real.exp (-u))) := by
          refine' h_dominated_convergence.congr' _;
          filter_upwards [ self_mem_nhdsWithin ] with h hh;
          rw [ h_gamma_int ( 1 + h ) ( by linarith [ hh.out ] ), h_gamma_int 1 zero_lt_one ];
          rw [ ← MeasureTheory.integral_sub ];
          · rw [ ← MeasureTheory.integral_div ] ; congr ; ext u ; norm_num ; ring;
          · have := @integral_rpow_mul_exp_neg_rpow 1;
            norm_num +zetaDelta at *;
            exact ( by have := @this h ( by linarith ) ; exact ( by contrapose! this; rw [ MeasureTheory.integral_undef this ] ; positivity ) );
          · simpa using MeasureTheory.integrable_of_integral_eq_one ( by simpa using integral_exp_neg_Ioi_zero );
        refine' tendsto_nhds_unique _ h_deriv;
        have h_deriv : HasDerivAt (fun s => Real.Gamma s) (deriv (fun s => Real.Gamma s) 1) 1 := by
          exact hasDerivAt_deriv_iff.mpr ( Real.differentiableAt_Gamma fun m => by linarith );
        simpa [ div_eq_inv_mul ] using h_deriv.tendsto_slope_zero_right;
      exact h_gamma_deriv.symm;
    rw [ h_gamma_deriv, Real.hasDerivAt_Gamma_one.deriv ];
  have h_subst : ∫ u in Set.Ioi 0, Real.log u * Real.exp (-ε * u) = (1 / ε) * ∫ u in Set.Ioi 0, (Real.log u - Real.log ε) * Real.exp (-u) := by
    have h_int_subst : ∀ {f : ℝ → ℝ}, ∫ u in Set.Ioi 0, f u = ∫ u in Set.Ioi 0, f (u / ε) * (1 / ε) := by
      intro f; rw [ MeasureTheory.integral_mul_const ] ; simp +decide [ div_eq_inv_mul, MeasureTheory.integral_const_mul, hε.ne' ] ;
      rw [ mul_comm, MeasureTheory.integral_comp_mul_left_Ioi ] <;> norm_num [ hε.ne' ];
      positivity;
    rw [ h_int_subst, ← MeasureTheory.integral_const_mul ] ; refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u hu => _ ; rw [ ← Real.log_div ( ne_of_gt hu ) ( ne_of_gt hε ) ] ; ring;
    norm_num [ hε.ne' ];
  simp_all +decide [ sub_mul ];
  rw [ MeasureTheory.integral_sub, h_int ];
  · rw [ MeasureTheory.integral_const_mul, integral_exp_neg_Ioi ] ; norm_num [ hε.ne' ];
  · contrapose! h_int;
    rw [ MeasureTheory.integral_undef h_int ] ; norm_num;
    grind +suggestions;
  · exact MeasureTheory.Integrable.const_mul ( MeasureTheory.integrable_of_integral_eq_one ( by simpa using integral_exp_neg_Ioi_zero ) ) _

/-
Key computation: the weighted sum of log log with Dirichlet weights tends to
-γ - log ε as ε → 0+. Uses Γ'(1) = -γ.
-/
lemma loglog_dirichlet_sum_tendsto :
    Tendsto (fun ε : ℝ =>
      (∑' n : ℕ, (if n ≥ 2 then
        Real.log (Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε))
      else 0)) + Real.log ε)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (-Real.eulerMascheroniConstant)) := by
  -- By definition of $S(ε)$, we can write it as $T(ε) + \log ε(1 - 2^{-ε})$.
  have h_decomp : ∀ ε : ℝ, 0 < ε → (∑' n : ℕ, if n ≥ 2 then Real.log (Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) + Real.log ε = (∑' n : ℕ, if n ≥ 2 then Real.log (ε * Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) + Real.log ε * (1 - (2 : ℝ) ^ (-ε)) := by
    intro ε hε
    have h_split : (∑' n : ℕ, if n ≥ 2 then Real.log (ε * Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) = (∑' n : ℕ, if n ≥ 2 then Real.log (Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) + (∑' n : ℕ, if n ≥ 2 then Real.log ε * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) := by
      rw [ ← Summable.tsum_add ];
      · congr with n ; split_ifs <;> simp_all +decide [ Real.log_mul, ne_of_gt ] ; ring;
        rw [ Real.log_mul ( by positivity ) ( by exact ne_of_gt ( Real.log_pos ( by norm_cast ) ) ) ] ; ring;
      · -- Since $\log(\log n)$ is bounded for $n \geq 2$, we can apply the comparison test.
        have h_bounded : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → |Real.log (Real.log n)| ≤ C * n ^ (ε / 2) := by
          have h_bounded : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → |Real.log (Real.log n)| ≤ C * Real.log n := by
            use 1;
            intro n hn; rw [ abs_le ] ; constructor <;> norm_num;
            · rw [ ← Real.log_inv ];
              exact Real.log_le_log ( by positivity ) ( by nlinarith [ Real.log_inv ( n : ℝ ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by positivity : 0 < ( n : ℝ ) ) ), Real.log_le_sub_one_of_pos ( by positivity : 0 < ( n : ℝ ) ), mul_inv_cancel₀ ( by positivity : ( n : ℝ ) ≠ 0 ), show ( n : ℝ ) ≥ 2 by norm_cast ] );
            · exact le_trans ( Real.log_le_sub_one_of_pos ( Real.log_pos ( by norm_cast ) ) ) ( by linarith );
          have h_bounded : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → Real.log n ≤ C * (n : ℝ) ^ (ε / 2) := by
            use 2 / ε;
            intro n hn; rw [ div_mul_eq_mul_div, le_div_iff₀ ( by positivity ) ] ; have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( n : ℝ ) ^ ( ε / 2 ) ) ; rw [ Real.log_rpow ( by positivity ) ] at this; ring_nf at *; nlinarith;
          obtain ⟨ C₁, hC₁ ⟩ := ‹∃ C₁ : ℝ, ∀ n : ℕ, 2 ≤ n → |Real.log ( Real.log n )| ≤ C₁ * Real.log n›
          obtain ⟨ C₂, hC₂ ⟩ := h_bounded
          use C₁ * C₂;
          intro n hn; convert le_trans ( hC₁ n hn ) ( mul_le_mul_of_nonneg_left ( hC₂ n hn ) ( show 0 ≤ C₁ by have := hC₁ 2 ( by norm_num ) ; norm_num at this ; nlinarith [ abs_le.mp this, Real.log_pos one_lt_two ] ) ) using 1 ; ring;
        obtain ⟨ C, hC ⟩ := h_bounded;
        have h_comparison : Summable (fun n : ℕ => if n ≥ 2 then C * (n : ℝ) ^ (ε / 2) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) := by
          have h_comparison : Summable (fun n : ℕ => if n ≥ 2 then (n : ℝ) ^ (ε / 2) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) := by
            have h_bound : ∀ n : ℕ, 2 ≤ n → (n : ℝ) ^ (ε / 2) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) ≤ ε * (n : ℝ) ^ (-1 - ε / 2) := by
              intro n hn
              have h_bound : (n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε) ≤ ε * (n : ℝ) ^ (-1 - ε) := by
                have h_bound : (n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε) ≤ ε * (n : ℝ) ^ (-1 - ε) := by
                  have h_mean_val : ∃ c ∈ Set.Ioo (n : ℝ) (n + 1), deriv (fun x => x ^ (-ε)) c = ((n + 1 : ℝ) ^ (-ε) - (n : ℝ) ^ (-ε)) / ((n + 1 : ℝ) - (n : ℝ)) := by
                    have := exists_deriv_eq_slope ( f := fun x => x ^ ( -ε ) ) ( show ( n : ℝ ) < ( n + 1 ) by norm_num );
                    exact this ( continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.rpow ( continuousAt_id ) continuousAt_const <| Or.inl <| by linarith [ hx.1, show ( n : ℝ ) ≥ 2 by norm_cast ] ) ( fun x hx => by exact DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.rpow ( differentiableAt_id ) ( by norm_num ) <| by linarith [ hx.1, show ( n : ℝ ) ≥ 2 by norm_cast ] )
                  obtain ⟨ c, hc₁, hc₂ ⟩ := h_mean_val; norm_num [ show c ≠ 0 by linarith [ hc₁.1, show ( n : ℝ ) ≥ 2 by norm_cast ] ] at hc₂ ⊢;
                  rw [ show ( -1 - ε : ℝ ) = -ε - 1 by ring ];
                  nlinarith [ show ( n : ℝ ) ^ ( -ε - 1 ) ≥ c ^ ( -ε - 1 ) by rw [ ge_iff_le ] ; rw [ Real.rpow_le_rpow_iff_of_neg ] <;> linarith [ hc₁.1, hc₁.2, show ( n : ℝ ) ≥ 2 by norm_cast ] ];
                exact h_bound;
              convert mul_le_mul_of_nonneg_left h_bound ( Real.rpow_nonneg ( Nat.cast_nonneg n ) ( ε / 2 ) ) using 1 ; ring;
              rw [ mul_assoc, ← Real.rpow_add ( by positivity ) ] ; ring
            have h_comparison : Summable (fun n : ℕ => if n ≥ 2 then ε * (n : ℝ) ^ (-1 - ε / 2) else 0) := by
              rw [ ← summable_nat_add_iff 2 ];
              simpa using Summable.mul_left _ <| Real.summable_nat_rpow.2 ( by linarith ) |> Summable.comp_injective <| add_left_injective 2;
            refine' h_comparison.of_nonneg_of_le _ _;
            · intro n; split_ifs <;> first | positivity | exact mul_nonneg ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ( sub_nonneg_of_le <| by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> norm_num <;> linarith ) ;
            · grind;
          convert h_comparison.mul_left C using 2 ; split_ifs <;> ring;
        -- Apply the comparison test with the summable series.
        have h_comparison_test : ∀ n : ℕ, |if n ≥ 2 then Real.log (Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0| ≤ |if n ≥ 2 then C * (n : ℝ) ^ (ε / 2) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0| := by
          intro n; split_ifs <;> norm_num [ abs_mul ];
          exact mul_le_mul_of_nonneg_right ( by rw [ abs_of_nonneg ( show 0 ≤ C by have := hC 2 ( by norm_num ) ; norm_num at this ; nlinarith [ abs_le.mp this, Real.rpow_pos_of_pos zero_lt_two ( ε / 2 ) ] ), abs_of_nonneg ( show 0 ≤ ( n : ℝ ) ^ ( ε / 2 ) by positivity ) ] ; exact hC n ‹_› ) ( abs_nonneg _ );
        -- Apply the comparison test with the summable series to conclude that the original series is summable.
        have h_comparison_test : Summable (fun n : ℕ => |if n ≥ 2 then Real.log (Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0|) := by
          exact Summable.of_nonneg_of_le ( fun n => abs_nonneg _ ) ( fun n => h_comparison_test n ) ( h_comparison.abs );
        exact h_comparison_test.of_abs;
      · rw [ ← summable_nat_add_iff 2 ];
        -- The series $\sum_{n=2}^{\infty} (n^{-\epsilon} - (n+1)^{-\epsilon})$ is a telescoping series.
        have h_telescoping : Summable (fun n : ℕ => (n + 2 : ℝ) ^ (-ε) - (n + 3 : ℝ) ^ (-ε)) := by
          have h_telescoping : ∀ N : ℕ, ∑ n ∈ Finset.range N, ((n + 2 : ℝ) ^ (-ε) - (n + 3 : ℝ) ^ (-ε)) = (2 : ℝ) ^ (-ε) - (N + 2 : ℝ) ^ (-ε) := by
            exact fun N => by induction' N with N ih <;> norm_num [ add_assoc, Finset.sum_range_succ ] at * ; linarith;
          rw [ summable_iff_not_tendsto_nat_atTop_of_nonneg ];
          · exact fun h => absurd ( h.congr h_telescoping ) ( by exact not_tendsto_atTop_of_tendsto_nhds ( by simpa using tendsto_const_nhds.sub ( tendsto_rpow_neg_atTop hε |> Filter.Tendsto.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) );
          · exact fun n => sub_nonneg_of_le <| by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> linarith;
        convert h_telescoping.mul_left ( Real.log ε ) using 2 ; norm_num [ add_assoc ];
    have h_sum : ∑' n : ℕ, (if n ≥ 2 then ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) = 2 ^ (-ε) := by
      have h_sum : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), (if n ≥ 2 then ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)) Filter.atTop (nhds (2 ^ (-ε))) := by
        have h_sum : ∀ N : ℕ, N ≥ 2 → ∑ n ∈ Finset.range (N + 1), (if n ≥ 2 then ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) = 2 ^ (-ε) - (N + 1) ^ (-ε) := by
          intro N hN; induction hN <;> simp_all +decide [ Finset.sum_range_succ ] ; ring;
          rw [ if_pos ( by linarith ) ] ; ring;
        rw [ Filter.tendsto_congr' ( Filter.eventuallyEq_of_mem ( Filter.Ici_mem_atTop 2 ) h_sum ) ];
        simpa using tendsto_const_nhds.sub ( tendsto_rpow_neg_atTop hε |> Filter.Tendsto.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop );
      refine' HasSum.tsum_eq _;
      rw [ hasSum_iff_tendsto_nat_of_nonneg ];
      · rwa [ ← Filter.tendsto_add_atTop_iff_nat ];
      · intro n; split_ifs <;> first | positivity | exact sub_nonneg_of_le <| by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> norm_num <;> linarith;
    rw [ h_split, show ( ∑' n : ℕ, if n ≥ 2 then Real.log ε * ( ( n : ℝ ) ^ ( -ε ) - ( n + 1 ) ^ ( -ε ) ) else 0 ) = Real.log ε * ( ∑' n : ℕ, if n ≥ 2 then ( ( n : ℝ ) ^ ( -ε ) - ( n + 1 ) ^ ( -ε ) ) else 0 ) by rw [ ← tsum_mul_left ] ; exact tsum_congr fun n => by split_ifs <;> ring ] ; rw [ h_sum ] ; ring;
  -- By the properties of the Riemann sum and the integral, we know that the difference between the sum and the integral tends to zero.
  have h_diff_zero : Filter.Tendsto (fun ε : ℝ => (∑' n : ℕ, if n ≥ 2 then Real.log (ε * Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) - (-Real.eulerMascheroniConstant)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h_riemann_sum : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0), |(∑' n : ℕ, if n ≥ 2 then Real.log (ε * Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) - (-Real.eulerMascheroniConstant)| ≤ (∫ u in Set.Ioc 0 (ε * Real.log 2), |Real.log u * Real.exp (-u)|) + ε * (∑' n : ℕ, if n ≥ 2 then 1 / ((n : ℝ) ^ 2 * Real.log n) else 0) := by
      filter_upwards [ Ioo_mem_nhdsGT zero_lt_one ] with ε hε using riemann_sum_bound ε hε.1 hε.2.le;
    have h_integral_zero : Filter.Tendsto (fun ε : ℝ => ∫ u in Set.Ioc 0 (ε * Real.log 2), |Real.log u * Real.exp (-u)|) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have := integral_log_exp_near_zero_tendsto.comp ( show Filter.Tendsto ( fun ε : ℝ => ε * Real.log 2 ) ( nhdsWithin 0 ( Set.Ioi 0 ) ) ( nhdsWithin 0 ( Set.Ioi 0 ) ) from Filter.Tendsto.inf ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ) <| Filter.tendsto_principal_principal.mpr <| by intros x hx; exact mul_pos hx.out <| Real.log_pos one_lt_two ) ; aesop;
    exact squeeze_zero_norm' h_riemann_sum ( by simpa using h_integral_zero.add ( Filter.Tendsto.mul ( Filter.tendsto_id.mono_left inf_le_left ) tendsto_const_nhds ) );
  have := h_diff_zero.add ( log_eps_one_minus_rpow_tendsto );
  simpa using this.sub_const ( Real.eulerMascheroniConstant ) |> Filter.Tendsto.congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by rw [ h_decomp x hx ] ; ring )

/-
The key identification: the Meissel-Mertens constant equals γ - H.
-/
set_option maxHeartbeats 800000 in
theorem meisselMertens_eq_euler_mascheroni_sub_mertensH :
    ∀ M : ℝ, Tendsto (fun N : ℕ => ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
      1 / (p : ℝ) - Real.log (Real.log N)) atTop (𝓝 M) →
    M = Real.eulerMascheroniConstant - mertensH_val := by
  -- Let $A(N) = \sum_{p \leq N} \frac{1}{p}$ and $r(n) = A(n) - \log \log n - M$.
  intros M hM
  set A : ℕ → ℝ := fun N => ∑ p ∈ ((Finset.range (N + 1)).filter Nat.Prime), (1 / (p : ℝ))
  set r : ℕ → ℝ := fun n => A n - Real.log (Real.log (n : ℝ)) - M;
  -- From the Abel summation result, we have $P(1+ε) = M \cdot 2^{-ε} + \sum r(n) \cdot (n^{-ε} - (n+1)^{-ε}) + \sum (\log \log n) \cdot (n^{-ε} - (n+1)^{-ε})$.
  have h_abel : ∀ ε > 0, primeZetaReal (1 + ε) = M * 2⁻¹ ^ ε + ∑' n : ℕ, (if n ≥ 2 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) + ∑' n : ℕ, (if n ≥ 2 then Real.log (Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) := by
    intro ε hε_pos
    have h_abel : primeZetaReal (1 + ε) = ∑' n : ℕ, (if n ≥ 2 then A n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) := by
      convert abel_summation_primeZeta ε hε_pos using 1;
    -- Split the sum into three parts: the term involving $M$, the term involving $r(n)$, and the term involving $\log \log n$.
    have h_split : ∑' n : ℕ, (if n ≥ 2 then A n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) = (∑' n : ℕ, (if n ≥ 2 then M * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)) + (∑' n : ℕ, (if n ≥ 2 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)) + (∑' n : ℕ, (if n ≥ 2 then Real.log (Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)) := by
      rw [ ← Summable.tsum_add, ← Summable.tsum_add ] ; congr ; ext n ; split_ifs <;> ring;
      · have h_summable : Summable (fun n : ℕ => (if n ≥ 2 then (n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε) else 0)) := by
          rw [ ← summable_nat_add_iff 2 ];
          -- The series $\sum_{n=2}^{\infty} (n^{-\epsilon} - (n+1)^{-\epsilon})$ is a telescoping series.
          have h_telescoping : ∀ N : ℕ, ∑ n ∈ Finset.range N, ((n + 2 : ℝ) ^ (-ε) - ((n + 2 : ℝ) + 1) ^ (-ε)) = (2 : ℝ) ^ (-ε) - ((N + 2 : ℝ) ^ (-ε)) := by
            exact fun N => by induction' N with N ih <;> norm_num [ add_assoc, Finset.sum_range_succ ] at * ; linarith;
          rw [ summable_iff_not_tendsto_nat_atTop_of_nonneg ];
          · norm_num [ h_telescoping ];
            exact not_tendsto_atTop_of_tendsto_nhds ( tendsto_const_nhds.sub ( tendsto_rpow_neg_atTop ( by linarith ) |> Filter.Tendsto.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) );
          · exact fun n => by rw [ if_pos ( by linarith ) ] ; exact sub_nonneg_of_le ( by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> norm_num <;> linarith ) ;
        have h_summable_r : Summable (fun n : ℕ => (if n ≥ 2 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)) := by
          have h_bounded : ∃ C, ∀ n ≥ 2, |r n| ≤ C := by
            have := hM.sub_const M;
            exact ⟨ _, fun n hn => le_csSup ( this.abs.bddAbove_range ) ⟨ n, rfl ⟩ ⟩;
          obtain ⟨ C, hC ⟩ := h_bounded;
          have h_summable : Summable (fun n : ℕ => if n ≥ 2 then C * |(n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)| else 0) := by
            convert h_summable.abs.mul_left C using 2 ; aesop;
          -- Since $|r n| \leq C$ for $n \geq 2$, we can apply the comparison test.
          have h_comparison : ∀ n ≥ 2, |r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε))| ≤ C * |(n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)| := by
            exact fun n hn => by rw [ abs_mul ] ; exact mul_le_mul_of_nonneg_right ( hC n hn ) ( abs_nonneg _ ) ;
          have h_comparison : Summable (fun n : ℕ => if n ≥ 2 then |r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε))| else 0) := by
            exact Summable.of_nonneg_of_le ( fun n => by split_ifs <;> positivity ) ( fun n => by split_ifs <;> first | positivity | exact h_comparison n ‹_› ) h_summable;
          exact Summable.of_norm <| by convert h_comparison using 1; ext n; split_ifs <;> norm_num;
        exact Summable.add ( by simpa [ mul_sub ] using h_summable.mul_left M ) h_summable_r;
      · -- We'll use the fact that if the series $\sum_{n=2}^{\infty} a_n$ converges absolutely, then the series $\sum_{n=2}^{\infty} |a_n|$ also converges.
        have h_abs_conv : Summable (fun n : ℕ => if n ≥ 2 then |Real.log (Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε))| else 0) := by
          -- We'll use the fact that if the series $\sum_{n=2}^{\infty} a_n$ converges absolutely, then the series $\sum_{n=2}^{\infty} |a_n|$ also converges. Hence, we need to show that $\sum_{n=2}^{\infty} |\log \log n \cdot (n^{-\epsilon} - (n+1)^{-\epsilon})|$ converges.
          have h_abs_conv : Summable (fun n : ℕ => if n ≥ 2 then |Real.log (Real.log (n : ℝ))| * (n : ℝ) ^ (-ε - 1) else 0) := by
            -- We'll use the fact that |log log n| grows slower than any polynomial function.
            have h_log_log_growth : ∃ C : ℝ, ∀ n : ℕ, n ≥ 2 → |Real.log (Real.log (n : ℝ))| ≤ C * (n : ℝ) ^ (ε / 2) := by
              have h_log_log_growth : ∃ C : ℝ, ∀ n : ℕ, n ≥ 2 → |Real.log (Real.log (n : ℝ))| ≤ C * (n : ℝ) ^ (ε / 2) := by
                have h_log_log_growth_aux : Filter.Tendsto (fun n : ℕ => |Real.log (Real.log (n : ℝ))| / (n : ℝ) ^ (ε / 2)) Filter.atTop (nhds 0) := by
                  -- We can use the fact that $|\log \log n| \leq \log n$ for all $n \geq 2$.
                  have h_log_log_bound : Filter.Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ)) / (n : ℝ) ^ (ε / 2)) Filter.atTop (nhds 0) := by
                    -- We can use the fact that $\frac{\log \log n}{n^{\epsilon/2}}$ tends to $0$ as $n$ tends to infinity.
                    have h_log_log_div_n_eps : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ (ε / 2)) Filter.atTop (nhds 0) := by
                      -- Let $y = \log x$, therefore the expression becomes $\frac{y}{e^{y \cdot \frac{\epsilon}{2}}}$.
                      suffices h_log : Filter.Tendsto (fun y : ℝ => y / Real.exp (y * (ε / 2))) Filter.atTop (nhds 0) by
                        have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
                        refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; simp +decide [ Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn ), mul_comm ] );
                      -- Let $z = y \cdot \frac{\epsilon}{2}$, therefore the expression becomes $\frac{2z}{\epsilon e^z}$.
                      suffices h_z : Filter.Tendsto (fun z : ℝ => 2 * z / (ε * Real.exp z)) Filter.atTop (nhds 0) by
                        convert h_z.comp ( Filter.tendsto_id.atTop_mul_const ( show 0 < ε / 2 by positivity ) ) using 2 ; norm_num ; ring;
                        norm_num [ mul_assoc, mul_comm ε, hε_pos.ne' ];
                      -- We can factor out the constant $2 / \epsilon$ from the limit.
                      suffices h_factor : Filter.Tendsto (fun z : ℝ => z / Real.exp z) Filter.atTop (nhds 0) by
                        convert h_factor.const_mul ( 2 / ε ) using 2 <;> ring;
                      simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1;
                    refine' squeeze_zero_norm' _ h_log_log_div_n_eps;
                    filter_upwards [ Filter.eventually_gt_atTop 2 ] with n hn using by rw [ Real.norm_of_nonneg ( div_nonneg ( Real.log_nonneg <| show 1 ≤ Real.log n from by rw [ Real.le_log_iff_exp_le <| by positivity ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ] ) <| by positivity ) ] ; exact div_le_div_of_nonneg_right ( le_trans ( Real.log_le_sub_one_of_pos <| Real.log_pos <| by norm_cast; linarith ) <| by norm_num ) <| by positivity;
                  exact tendsto_zero_iff_norm_tendsto_zero.mpr ( by simpa [ abs_div, abs_of_nonneg ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ] using h_log_log_bound.norm )
                have := h_log_log_growth_aux.bddAbove_range;
                exact ⟨ this.choose, fun n hn => by rw [ ← div_le_iff₀ ( by positivity ) ] ; exact this.choose_spec ⟨ n, rfl ⟩ ⟩;
              exact h_log_log_growth;
            obtain ⟨ C, hC ⟩ := h_log_log_growth;
            -- Using the bound from hC, we can show that the series is dominated by a convergent p-series.
            have h_dominate : ∀ n : ℕ, n ≥ 2 → |Real.log (Real.log (n : ℝ))| * (n : ℝ) ^ (-ε - 1) ≤ C * (n : ℝ) ^ (-ε / 2 - 1) := by
              intro n hn; convert mul_le_mul_of_nonneg_right ( hC n hn ) ( Real.rpow_nonneg ( Nat.cast_nonneg n ) ( -ε - 1 ) ) using 1 ; rw [ mul_assoc, ← Real.rpow_add ( by positivity ) ] ; ring;
            rw [ ← summable_nat_add_iff 2 ];
            exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => by simpa using h_dominate ( n + 2 ) ( by linarith ) ) ( Summable.mul_left _ <| by simpa using summable_nat_add_iff 2 |>.2 <| Real.summable_nat_rpow.2 <| by linarith );
          -- We'll use the fact that $|n^{-\epsilon} - (n+1)^{-\epsilon}| \leq \epsilon n^{-\epsilon-1}$ for all $n \geq 2$.
          have h_bound : ∀ n : ℕ, n ≥ 2 → |(n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)| ≤ ε * (n : ℝ) ^ (-ε - 1) := by
            -- We'll use the mean value theorem to bound the difference.
            intros n hn
            have h_mean_value : ∃ c ∈ Set.Ioo (n : ℝ) (n + 1), (n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε) = ε * c ^ (-ε - 1) := by
              have := exists_deriv_eq_slope ( f := fun x => x ^ ( -ε ) ) ( show ( n : ℝ ) < ( n + 1 ) by norm_num );
              norm_num +zetaDelta at *;
              exact this ( continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.rpow ( continuousAt_id ) continuousAt_const <| Or.inl <| by linarith [ hx.1, show ( n : ℝ ) ≥ 2 by norm_cast ] ) ( fun x hx => by exact DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.rpow ( differentiableAt_id ) ( by norm_num ) <| by linarith [ hx.1, show ( n : ℝ ) ≥ 2 by norm_cast ] ) |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, hc₁, by norm_num [ show c ≠ 0 by linarith ] at *; linarith ⟩;
            obtain ⟨ c, hc₁, hc₂ ⟩ := h_mean_value; rw [ hc₂, abs_mul, abs_of_nonneg hε_pos.le ] ;
            rw [ abs_of_nonneg ( Real.rpow_nonneg ( by linarith [ hc₁.1 ] ) _ ) ] ; exact mul_le_mul_of_nonneg_left ( by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> linarith [ hc₁.1, hc₁.2, show ( n : ℝ ) ≥ 2 by norm_cast ] ) hε_pos.le;
          refine' .of_nonneg_of_le ( fun n => _ ) ( fun n => _ ) ( h_abs_conv.mul_left ε );
          · positivity;
          · split_ifs <;> simp_all +decide [ abs_mul, mul_assoc, mul_comm, mul_left_comm ];
            simpa only [ mul_assoc ] using mul_le_mul_of_nonneg_right ( h_bound n ‹_› ) ( abs_nonneg _ );
        -- Since the absolute value of the series is summable, the original series must also be summable.
        have h_summable : Summable (fun n : ℕ => if n ≥ 2 then Real.log (Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) := by
          have := h_abs_conv
          rw [ ← summable_nat_add_iff 2 ] at *;
          exact Summable.of_norm <| by simpa using this;
        convert h_summable using 1;
      · rw [ ← summable_nat_add_iff 2 ];
        -- The series $\sum_{n=2}^{\infty} \left( \frac{1}{n^{\epsilon}} - \frac{1}{(n+1)^{\epsilon}} \right)$ is a telescoping series.
        have h_telescoping : Summable (fun n : ℕ => ((n + 2 : ℝ) ^ (-ε) - ((n + 2 : ℝ) + 1) ^ (-ε))) := by
          have h_telescoping : ∀ N : ℕ, ∑ n ∈ Finset.range N, ((n + 2 : ℝ) ^ (-ε) - ((n + 2 : ℝ) + 1) ^ (-ε)) = (2 : ℝ) ^ (-ε) - ((N + 2 : ℝ) ^ (-ε)) := by
            exact fun N => by induction' N with N ih <;> norm_num [ add_assoc, Finset.sum_range_succ ] at * ; linarith;
          rw [ summable_iff_not_tendsto_nat_atTop_of_nonneg ];
          · exact fun h => absurd ( h.congr h_telescoping ) ( by exact not_tendsto_atTop_of_tendsto_nhds ( by simpa using tendsto_const_nhds.sub ( tendsto_rpow_neg_atTop hε_pos |> Filter.Tendsto.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) );
          · exact fun n => sub_nonneg_of_le <| by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> linarith;
        simpa using h_telescoping.mul_left M;
      · have h_bounded : ∃ C, ∀ n ≥ 2, |r n| ≤ C := by
          have := hM.sub_const M;
          exact ⟨ _, fun n hn => le_csSup ( this.abs.bddAbove_range ) ⟨ n, rfl ⟩ ⟩;
        have h_summable : Summable (fun n : ℕ => if n ≥ 2 then (n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε) else 0) := by
          rw [ ← summable_nat_add_iff 2 ];
          -- The series $\sum_{n=2}^{\infty} (n^{-\epsilon} - (n+1)^{-\epsilon})$ is a telescoping series.
          have h_telescoping : ∀ N : ℕ, ∑ n ∈ Finset.range N, ((n + 2 : ℝ) ^ (-ε) - ((n + 2 : ℝ) + 1) ^ (-ε)) = (2 : ℝ) ^ (-ε) - ((N + 2 : ℝ) ^ (-ε)) := by
            exact fun N => by induction' N with N ih <;> norm_num [ add_assoc, Finset.sum_range_succ ] at * ; linarith;
          rw [ summable_iff_not_tendsto_nat_atTop_of_nonneg ];
          · norm_num [ h_telescoping ];
            exact not_tendsto_atTop_of_tendsto_nhds ( tendsto_const_nhds.sub ( by simpa using tendsto_rpow_neg_atTop hε_pos |> Filter.Tendsto.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) );
          · exact fun n => by rw [ if_pos ( by linarith ) ] ; exact sub_nonneg_of_le ( by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> norm_num <;> linarith ) ;
        obtain ⟨ C, hC ⟩ := h_bounded;
        have h_summable : Summable (fun n : ℕ => if n ≥ 2 then C * |(n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)| else 0) := by
          convert h_summable.abs.mul_left C using 2 ; aesop;
        -- Since $|r n| \leq C$ for $n \geq 2$, we can apply the comparison test.
        have h_comparison : ∀ n ≥ 2, |r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε))| ≤ C * |(n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)| := by
          exact fun n hn => by rw [ abs_mul ] ; exact mul_le_mul_of_nonneg_right ( hC n hn ) ( abs_nonneg _ ) ;
        have h_comparison : Summable (fun n : ℕ => if n ≥ 2 then |r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε))| else 0) := by
          exact Summable.of_nonneg_of_le ( fun n => by split_ifs <;> positivity ) ( fun n => by split_ifs <;> first | positivity | exact h_comparison n ‹_› ) h_summable;
        exact Summable.of_norm <| by convert h_comparison using 1; ext n; split_ifs <;> norm_num;
    -- Evaluate the sum $\sum_{n=2}^{\infty} (n^{-\epsilon} - (n+1)^{-\epsilon})$.
    have h_sum : ∑' n : ℕ, (if n ≥ 2 then (n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε) else 0) = 2⁻¹ ^ ε := by
      have h_sum : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), (if n ≥ 2 then (n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε) else 0)) Filter.atTop (nhds (2⁻¹ ^ ε)) := by
        have h_sum : ∀ N : ℕ, N ≥ 2 → ∑ n ∈ Finset.range (N + 1), (if n ≥ 2 then (n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε) else 0) = 2⁻¹ ^ ε - ((N + 1) : ℝ) ^ (-ε) := by
          intro N hN; induction hN <;> simp_all +decide [ Finset.sum_range_succ ] ; ring;
          · norm_num [ Real.rpow_neg, Real.div_rpow ];
          · rw [ if_pos ( by linarith ) ] ; ring;
        rw [ Filter.tendsto_congr' ( Filter.eventuallyEq_of_mem ( Filter.Ici_mem_atTop 2 ) h_sum ) ];
        simpa using tendsto_const_nhds.sub ( tendsto_rpow_neg_atTop hε_pos |> Filter.Tendsto.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop );
      refine' HasSum.tsum_eq _;
      rw [ hasSum_iff_tendsto_nat_of_nonneg ];
      · rwa [ ← Filter.tendsto_add_atTop_iff_nat ];
      · intro n; split_ifs <;> first | positivity | rw [ Real.rpow_neg ( by positivity ), Real.rpow_neg ( by positivity ) ] ; exact sub_nonneg_of_le <| inv_anti₀ ( by positivity ) <| Real.rpow_le_rpow ( by positivity ) ( by linarith ) <| by positivity;
    rw [ ← h_sum, ← tsum_mul_left ] ; aesop;
  -- From the abelian theorem, we have $\sum r(n) \cdot (n^{-ε} - (n+1)^{-ε}) \to 0$ as $\epsilon \to 0+$.
  have h_abelian : Filter.Tendsto (fun ε : ℝ => ∑' n : ℕ, (if n ≥ 2 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    -- Since $r(n)$ is bounded and converges to $0$, we can apply the abelian theorem.
    have hr_bdd : ∃ C, ∀ n, |r n| ≤ C := by
      have := hM.sub_const M;
      exact ⟨ _, fun n => le_csSup ( this.abs.bddAbove_range ) ⟨ n, rfl ⟩ ⟩
    have hr_lim : Filter.Tendsto r Filter.atTop (nhds 0) := by
      convert hM.sub_const M using 2 ; ring!
    exact abelian_theorem_bounded_convergent r hr_bdd hr_lim;
  -- From the loglog_dirichlet_sum_tendsto, we have $\sum (\log \log n) \cdot (n^{-ε} - (n+1)^{-ε}) + \log ε \to -\gamma$ as $\epsilon \to 0+$.
  have h_loglog : Filter.Tendsto (fun ε : ℝ => ∑' n : ℕ, (if n ≥ 2 then Real.log (Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) + Real.log ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds (-Real.eulerMascheroniConstant)) := by
    convert loglog_dirichlet_sum_tendsto using 1;
  -- From the primeZeta_plus_log_tendsto, we have $P(1+ε) + \log ε \to -mertensH_val$ as $\epsilon \to 0+$.
  have h_primeZeta : Filter.Tendsto (fun ε : ℝ => primeZetaReal (1 + ε) + Real.log ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds (-mertensH_val)) := by
    convert primeZeta_plus_log_tendsto.comp ( show Filter.Tendsto ( fun ε : ℝ => 1 + ε ) ( nhdsWithin 0 ( Set.Ioi 0 ) ) ( nhdsWithin 1 ( Set.Ioi 1 ) ) from ?_ ) using 2;
    · norm_num;
    · rw [ Metric.tendsto_nhdsWithin_nhdsWithin ] ; aesop;
  -- By combining the results from h_abel, h_abelian, and h_loglog, we get:
  have h_combined : Filter.Tendsto (fun ε : ℝ => M * 2⁻¹ ^ ε + (∑' n : ℕ, (if n ≥ 2 then r n * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0)) + (∑' n : ℕ, (if n ≥ 2 then Real.log (Real.log (n : ℝ)) * ((n : ℝ) ^ (-ε) - ((n : ℝ) + 1) ^ (-ε)) else 0) + Real.log ε)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (-mertensH_val)) := by
    exact h_primeZeta.congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by rw [ h_abel x hx ] ; ring );
  have := tendsto_nhds_unique h_combined ( Filter.Tendsto.add ( Filter.Tendsto.add ( tendsto_const_nhds.mul ( tendsto_const_nhds.rpow ( Filter.tendsto_id.mono_left inf_le_left ) ( by norm_num ) ) ) h_abelian ) h_loglog ) ; norm_num at this ; linarith;

end


noncomputable section

/-! ### Definitions -/

/-- The product of `(1 - 1/p)` over primes `p ≤ N`. -/
def mertensProd (N : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

/-- The sum of `1/p` over primes `p ≤ N`. -/
def primeReciprocalSum (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, 1 / (p : ℝ)

/-- The "tail" terms: for each prime `p ≤ N`, the sum `∑_{k≥2} 1/(k·p^k)`.
This is `log(1/(1-1/p)) - 1/p`. -/
def mertensTail (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
    (Real.log (1 / (1 - 1 / (p : ℝ))) - 1 / (p : ℝ))

/-- Mertens' constant H = lim_{N→∞} mertensTail N. -/
def mertensH' : ℝ := ∑' (p : Nat.Primes), (Real.log (1 / (1 - 1 / (p : ℝ))) - 1 / (p : ℝ))

/-! ### Key lemma: relating log of product to sums -/

/-
For a prime p ≥ 2, we have 0 < 1 - 1/p < 1 and 1 - 1/p > 0.
-/
lemma one_sub_inv_prime_pos (p : ℕ) (hp : p.Prime) : 0 < 1 - 1 / (p : ℝ) := by
  exact sub_pos_of_lt ( by simpa using inv_lt_one_of_one_lt₀ ( Nat.one_lt_cast.mpr hp.one_lt ) )

/-
The log of the product equals the sum of logs.
-/
lemma log_mertensProd (N : ℕ) :
    Real.log (mertensProd N) =
      ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log (1 - 1 / (p : ℝ)) := by
  rw [ mertensProd, Real.log_prod ];
  exact fun p hp => ne_of_gt <| one_sub_inv_prime_pos p <| Finset.mem_filter.mp hp |>.2

/-
Decompose log(1-1/p) = -1/p + (log(1/(1-1/p)) - 1/p) but with different sign.
-/
lemma log_mertensProd_eq (N : ℕ) :
    Real.log (mertensProd N) = -(primeReciprocalSum N) - mertensTail N := by
  unfold mertensProd primeReciprocalSum mertensTail;
  rw [ Real.log_prod ];
  · simp +zetaDelta at *;
    ring;
  · exact fun x hx => sub_ne_zero_of_ne <| by aesop;

/-! ### The tail converges -/

/-
The tail mertensTail N converges to mertensH' as N → ∞.
-/
lemma mertensTail_tendsto :
    Tendsto mertensTail atTop (𝓝 mertensH') := by
  -- We'll use the fact that mertensTail N is a partial sum of a convergent series.
  have h_series : Summable (fun p : Nat.Primes => (Real.log (1 / (1 - 1 / (p : ℝ))) - 1 / (p : ℝ))) := by
    -- We'll use the fact that $\log(1 + x) \leq x$ for $0 < x < 1$ to bound the terms of the series.
    have h_log_bound : ∀ p : Nat.Primes, Real.log (1 + (1 / ((p : ℝ) - 1))) - 1 / (p : ℝ) ≤ 1 / ((p : ℝ) * (p - 1)) := by
      -- Using the inequality $\log(1 + x) \leq x$ for $x > -1$, we get $\log(1 + 1/(p-1)) \leq 1/(p-1)$.
      have h_log_le : ∀ p : Nat.Primes, Real.log (1 + 1 / ((p : ℝ) - 1)) ≤ 1 / ((p : ℝ) - 1) := by
        exact fun p => le_trans ( Real.log_le_sub_one_of_pos ( by exact add_pos zero_lt_one ( one_div_pos.mpr ( sub_pos.mpr ( Nat.one_lt_cast.mpr p.prop.one_lt ) ) ) ) ) ( by norm_num );
      intro p; convert sub_le_sub ( h_log_le p ) le_rfl using 1 ; rw [ div_sub_div ] <;> ring <;> nlinarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast p.2.two_le ] ;
    -- Since $\sum_{p \text{ prime}} \frac{1}{p(p-1)}$ converges, we can apply the comparison test.
    have h_summable : Summable (fun p : Nat.Primes => 1 / ((p : ℝ) * (p - 1))) := by
      -- We can compare our series with the convergent p-series $\sum_{p \text{ prime}} \frac{1}{p^2}$.
      have h_comparison : ∀ p : Nat.Primes, 1 / ((p : ℝ) * (p - 1)) ≤ 2 / (p : ℝ) ^ 2 := by
        intro p; rw [ div_le_div_iff₀ ] <;> nlinarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast p.2.two_le ] ;
      exact Summable.of_nonneg_of_le ( fun p => one_div_nonneg.mpr <| mul_nonneg ( Nat.cast_nonneg _ ) <| sub_nonneg.mpr <| Nat.one_le_cast.mpr p.2.pos ) ( fun p => h_comparison p ) <| Summable.mul_left _ <| by simpa using Summable.subtype ( Real.summable_one_div_nat_pow.2 one_lt_two ) _;
    refine' .of_nonneg_of_le ( fun p => _ ) ( fun p => _ ) h_summable;
    · rcases p with ⟨ p, hp ⟩ ; norm_num [ hp.ne_zero ];
      exact le_trans ( by norm_num ) ( neg_le_neg ( Real.log_le_sub_one_of_pos ( sub_pos.mpr <| inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr hp.one_lt ) ) );
    · convert h_log_bound p using 1 ; ring;
      rw [ show ( 1 - ( p : ℝ ) ⁻¹ ) = ( p - 1 : ℝ ) / p by rw [ sub_div, inv_eq_one_div, div_self ( Nat.cast_ne_zero.mpr p.2.ne_zero ) ] ] ; norm_num ; ring;
      exact congrArg Real.log ( by linarith [ inv_mul_cancel₀ ( show ( -1 + p : ℝ ) ≠ 0 from by linarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast p.2.two_le ] ) ] );
  convert h_series.hasSum.comp _;
  rotate_left;
  use fun N => Finset.filter ( fun p : Nat.Primes => p.val ≤ N ) ( Finset.subtype ( fun p : ℕ => Nat.Prime p ) ( Finset.range ( N + 1 ) ) );
  · refine' Filter.tendsto_atTop_atTop.mpr _;
    exact fun s => ⟨ s.sup ( fun p => p.val ), fun n hn => Finset.le_iff_subset.mpr fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_subtype.mpr <| Finset.mem_range.mpr <| Nat.lt_succ_of_le <| le_trans ( Finset.le_sup ( f := fun p : Primes => p.val ) hp ) hn, le_trans ( Finset.le_sup ( f := fun p : Primes => p.val ) hp ) hn ⟩ ⟩;
  · ext;
    refine' Finset.sum_bij ( fun p hp => ⟨ p, _ ⟩ ) _ _ _ _ <;> simp_all +decide [ Finset.mem_filter, Finset.mem_range ];
    · exact fun a ha ha' => Finset.mem_subtype.mpr ( Finset.mem_range.mpr ( Nat.lt_succ_of_le ha ) );
    · grind;
    · exact fun b hb hb' => ⟨ b, ⟨ hb', b.2 ⟩, rfl ⟩

/-! ### Mertens' second theorem -/

/-- **Mertens' second theorem**: The sum of prime reciprocals up to N
satisfies ∑_{p≤N} 1/p - log(log N) → M, where M is the Meissel–Mertens constant. -/
def meisselMertensConstant : ℝ := eulerMascheroniConstant - mertensH'

/-- The remaining deep step: identifying the limit of ∑ 1/p - log log N as γ - H.
From `prime_reciprocal_sum_convergence`, we know convergence to SOME limit M.
The identification M = γ - H requires connecting the Euler product to the
harmonic series / Euler-Mascheroni constant. -/
lemma mertens_second_theorem :
    Tendsto (fun N : ℕ => primeReciprocalSum N - Real.log (Real.log N))
      atTop (𝓝 meisselMertensConstant) := by
  obtain ⟨M, hM⟩ := prime_reciprocal_sum_convergence
  have hM_eq : M = eulerMascheroniConstant - mertensH' := by
    exact meisselMertens_eq_euler_mascheroni_sub_mertensH M hM
  rw [show meisselMertensConstant = M from by rw [hM_eq]; rfl]
  exact hM

/-! ### Main theorem: Mertens' third theorem (Equation 15) -/

/-
**Equation 15 (Mertens, 1874).** Mertens' third theorem:
the product `∏_{p ≤ N} (1 - 1/p)` is asymptotic to `e^{-γ} / ln N`,
where `γ` is the Euler–Mascheroni constant. Equivalently,
`∏_{p ≤ N} (1 - 1/p) · ln N → e^{-γ}` as `N → ∞`.
-/
theorem mertens_equation_15 :
    Tendsto (fun N : ℕ => mertensProd N * Real.log N)
      atTop (𝓝 (Real.exp (-eulerMascheroniConstant))) := by
  -- From `log_mertensProd_eq`, we have:
  have h_log_prod : Filter.Tendsto (fun N : ℕ => Real.log (mertensProd N) + Real.log (Real.log N)) Filter.atTop (nhds (-eulerMascheroniConstant)) := by
    have := mertens_second_theorem;
    convert Filter.Tendsto.add ( this.neg ) ( mertensTail_tendsto.neg ) using 2 <;> norm_num [ log_mertensProd_eq ] ; ring!;
    unfold meisselMertensConstant; ring;
  convert h_log_prod.exp.congr' _ using 2;
  · rw [ Real.exp_eq_exp_ℝ ];
  · filter_upwards [ Filter.eventually_gt_atTop 1 ] with N hN;
    rw [ ← Real.exp_eq_exp_ℝ, Real.exp_add, Real.exp_log, Real.exp_log ] <;> norm_cast;
    · exact Real.log_pos <| Nat.one_lt_cast.mpr hN;
    · exact Finset.prod_pos fun p hp => one_sub_inv_prime_pos p <| Finset.mem_filter.mp hp |>.2

end


end Mertens


-- === Inlined from Erdos696Common ===
/-
# Shared definitions for Erdős problem 696

Provides the `piMod` prime-counting function in arithmetic progressions.
Factored out so that the standalone Brun–Titchmarsh proof
(`BrunTitchmarshAP.lean`) can reference it without creating an import
cycle with the main `Erdos696.lean` file.
-/


/-- The prime-counting function in arithmetic progressions:
`piMod t q a = #{p ≤ t : p prime, p ≡ a (mod q)}`. -/
noncomputable def piMod (t : ℝ) (q a : ℕ) : ℕ :=
  Nat.card {p : ℕ | p ≤ ⌊t⌋₊ ∧ p.Prime ∧ p % q = a % q}



-- === Inlined from BrunTitchmarshAP ===
/-
# Brun–Titchmarsh inequality (AP form) for Erdős problem 696

Discharges `brun_titchmarsh` in `Erdos696.lean`.
Strategy: lean-pool's `SelbergSieve4` interval form + restricted Mertens
+ Solymosi-style choice of sieve level. See `PLAN-brun-titchmarsh.md`.
-/

namespace Erdos696BT

open scoped BigOperators Topology ArithmeticFunction.omega
open Filter Real Nat

/-! ## Restricted Mertens product

We need the asymptotic `∏_{p ≤ N, p ∤ q} (1 - 1/p) · log N → e^{-γ} · q / φ(q)`.
Reduce to `Mertens.mertens_equation_15` (the unrestricted form, already proved)
by splitting the product at primes dividing `q`.
-/

/-- Product of `(1 - 1/p)` over primes `p ≤ N` that do not divide `q`. -/
noncomputable def mertensRestrictedProd (q N : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ q), (1 - 1 / (p : ℝ))

/-- Product of `(1 - 1/p)` over primes `p` dividing `q`. Equals `φ(q)/q` for `q ≥ 1`. -/
noncomputable def primeDivProd (q : ℕ) : ℝ :=
  ∏ p ∈ q.primeFactors, (1 - 1 / (p : ℝ))

lemma primeDivProd_eq_phi_div (q : ℕ) (hq : q ≠ 0) :
    primeDivProd q = (q.totient : ℝ) / q := by
  have hQ : (Nat.totient q : ℚ) = q * ∏ p ∈ q.primeFactors, (1 - (p : ℚ)⁻¹) :=
    Nat.totient_eq_mul_prod_factors q
  -- Cast ℚ → ℝ via Rat.cast.
  have hR : (Nat.totient q : ℝ) = q * ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have := congrArg ((↑) : ℚ → ℝ) hQ
    push_cast at this
    exact_mod_cast this
  unfold primeDivProd
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have h_eq : (∏ p ∈ q.primeFactors, (1 - 1 / (p : ℝ))) =
      ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) := by
    apply Finset.prod_congr rfl
    intro p _
    rw [one_div]
  rw [h_eq, eq_div_iff hq', mul_comm, ← hR]

/-- For `N ≥ q`, every prime factor of `q` is at most `N`. -/
lemma primeFactors_subset_of_le {q N : ℕ} (hq : q ≠ 0) (h : q ≤ N) :
    q.primeFactors ⊆ (Finset.range (N + 1)).filter Nat.Prime := by
  intro p hp
  rw [Finset.mem_filter, Finset.mem_range]
  rw [Nat.mem_primeFactors] at hp
  refine ⟨?_, hp.1⟩
  calc p ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hp.2.1
    _ ≤ N := h
    _ < N + 1 := Nat.lt_succ_self _

/-- For `N ≥ q`, primes ≤ N split into those dividing q and those not.
This is the key factorization. -/
lemma mertensProd_eq_restricted_mul (q N : ℕ) (hq : q ≠ 0) (hN : q ≤ N) :
    Mertens.mertensProd N = primeDivProd q * mertensRestrictedProd q N := by
  classical
  unfold Mertens.mertensProd mertensRestrictedProd primeDivProd
  -- The set {p ≤ N : prime, p | q} equals q.primeFactors when q ≤ N.
  have h_subset_eq : ((Finset.range (N + 1)).filter Nat.Prime).filter (fun p => p ∣ q) =
      q.primeFactors := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨_, hp_prime⟩, hp_dvd⟩
      exact ⟨hp_prime, hp_dvd, hq⟩
    · rintro ⟨hp_prime, hp_dvd, _⟩
      have hp_le_q : p ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hp_dvd
      exact ⟨⟨by omega, hp_prime⟩, hp_dvd⟩
  -- Split (filter Prime) into (filter dvd) and (filter not dvd).
  have h_split : (Finset.range (N + 1)).filter Nat.Prime =
      ((Finset.range (N + 1)).filter Nat.Prime).filter (fun p => p ∣ q) ∪
      ((Finset.range (N + 1)).filter Nat.Prime).filter (fun p => ¬ p ∣ q) :=
    (Finset.filter_union_filter_not_eq _ _).symm
  rw [h_split, Finset.prod_union (Finset.disjoint_filter.mpr (fun _ _ h h' => h' h))]
  congr 1
  · rw [h_subset_eq]
  · -- The "not dvd" filter equals filter (Prime ∧ ¬ p∣q) on the original range.
    apply Finset.prod_nbij' id id <;>
      simp +contextual [Finset.mem_filter, Finset.mem_range, and_assoc]

/-- The restricted Mertens product times log N tends to e^{-γ} · q / φ(q). -/
theorem mertens_restricted (q : ℕ) (hq : 1 ≤ q) :
    Tendsto (fun N : ℕ => mertensRestrictedProd q N * Real.log N) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant) * (q : ℝ) / (q.totient : ℝ))) := by
  have hq' : q ≠ 0 := by omega
  have hφ_pos : 0 < q.totient := Nat.totient_pos.mpr (by omega)
  have hφ_ne : (q.totient : ℝ) ≠ 0 := by exact_mod_cast hφ_pos.ne'
  have hq_ne : (q : ℝ) ≠ 0 := by exact_mod_cast hq'
  -- Eventually equal to `mertensProd N · log N · q / φ(q)`.
  have h_eq : ∀ᶠ N in atTop, mertensRestrictedProd q N * Real.log N =
      (Mertens.mertensProd N * Real.log N) * ((q : ℝ) / (q.totient : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop q] with N hN
    have h := mertensProd_eq_restricted_mul q N hq' hN
    have hφ := primeDivProd_eq_phi_div q hq'
    rw [hφ] at h
    -- h : mertensProd N = (φ q / q) * mertensRestrictedProd q N
    have : mertensRestrictedProd q N = Mertens.mertensProd N * (q : ℝ) / (q.totient : ℝ) := by
      rw [h]; field_simp
    rw [this]; ring
  rw [Filter.tendsto_congr' h_eq]
  have h_const : Tendsto (fun _ : ℕ => (q : ℝ) / (q.totient : ℝ)) atTop
      (𝓝 ((q : ℝ) / (q.totient : ℝ))) := tendsto_const_nhds
  have h_target : Real.exp (-Real.eulerMascheroniConstant) * (q : ℝ) / (q.totient : ℝ) =
      Real.exp (-Real.eulerMascheroniConstant) * ((q : ℝ) / (q.totient : ℝ)) := by
    field_simp
  rw [h_target]
  exact Filter.Tendsto.mul Mertens.mertens_equation_15 h_const

/-! ## AP sieve setup -/

open scoped ArithmeticFunction.zeta

/-- The product of primes ≤ N that do not divide q. -/
noncomputable def primorialRestricted (q N : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ q), p

lemma primorialRestricted_squarefree (q N : ℕ) : Squarefree (primorialRestricted q N) := by
  unfold primorialRestricted
  apply PrimeUpperBound.prodDistinctPrimes_squarefree
  intro p hp
  rw [Finset.mem_filter] at hp
  exact hp.2.1

/-- Number of primes in `[a₀, b]` in residue class `a (mod q)`. -/
noncomputable def primesBetween_AP (a₀ b : ℝ) (q a : ℕ) : ℕ :=
  ((Finset.Icc (Nat.ceil a₀) (Nat.floor b)).filter
    (fun n => n.Prime ∧ n % q = a % q)).card

/-- Sieve restricted to integers in `(x, x+y]` lying in `a (mod q)`. -/
noncomputable def primeInterSieveAP
    (x y z : ℝ) (q a : ℕ) (hq : 1 ≤ q) (hz : 1 ≤ z) : LPSelbergSieve where
  support := (Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter (fun n => n % q = a % q)
  prodPrimes := primorialRestricted q (Nat.floor z)
  prodPrimes_squarefree := primorialRestricted_squarefree q _
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := y / q
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ => by
    simp [if_neg hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ => by
    simpa [hp.ne_zero] using
      (inv_lt_one_of_one_lt₀ (by norm_cast; exact hp.one_lt) : (p : ℝ)⁻¹ < 1)
  level := z
  one_le_level := hz

/-! ## AP cardinality lemmas (CRT) -/

/-- For `d` coprime to `q`, the joint condition "d ∣ x" and "x ≡ a (mod q)" reduces
to "x ≡ k (mod dq)" where `k = chineseRemainder hdq 0 a`. -/
private lemma joint_iff_crt {d q a : ℕ} (hd : d ≠ 0) (hq : 1 ≤ q) (hdq : Nat.Coprime d q) :
    ∀ x : ℕ,
      (d ∣ x ∧ x ≡ a [MOD q]) ↔
      x ≡ (Nat.chineseRemainder hdq 0 a : ℕ) [MOD (d * q)] := by
  intro x
  set k : ℕ := (Nat.chineseRemainder hdq 0 a : ℕ) with hk_def
  have hk_props : k ≡ 0 [MOD d] ∧ k ≡ a [MOD q] := (Nat.chineseRemainder hdq 0 a).property
  constructor
  · rintro ⟨hdx, hxq⟩
    -- x ≡ 0 (mod d) and x ≡ a (mod q); k satisfies the same. So x ≡ k mod both.
    have hxd : x ≡ k [MOD d] := by
      have h1 : x ≡ 0 [MOD d] := (Nat.modEq_zero_iff_dvd).mpr hdx
      exact h1.trans hk_props.1.symm
    have hxq' : x ≡ k [MOD q] := hxq.trans hk_props.2.symm
    exact (Nat.modEq_and_modEq_iff_modEq_mul hdq).mp ⟨hxd, hxq'⟩
  · intro hcrt
    have hxd : x ≡ k [MOD d] := hcrt.of_mul_right q
    have hxq : x ≡ k [MOD q] := hcrt.of_mul_left d
    refine ⟨?_, hxq.trans hk_props.2⟩
    exact (Nat.modEq_zero_iff_dvd).mp (hxd.trans hk_props.1)

/-- multSum for the AP sieve at a divisor `d` coprime to `q`, expressed as a count. -/
theorem multSum_AP_eq (x y z : ℝ) (hx : 0 < x) (q a : ℕ) (hq : 1 ≤ q) (hz : 1 ≤ z)
    {d : ℕ} (hd : d ≠ 0) (hdq : Nat.Coprime d q) :
    (primeInterSieveAP x y z q a hq hz).multSum d =
      ↑(((Finset.Ioc (Nat.ceil x - 1) (Nat.floor (x+y))).filter
        (fun n => n ≡ (Nat.chineseRemainder hdq 0 a : ℕ) [MOD (d * q)])).card) := by
  unfold LPSieve.multSum
  simp only [primeInterSieveAP, Finset.sum_boole]
  -- Goal: (filter (d ∣ ·) ((Icc ⌈x⌉ ⌊x+y⌋).filter (· % q = a % q))).card = ...
  rw [Nat.cast_inj]
  -- Reduce Icc to Ioc (⌈x⌉-1)
  rw [show ((Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
      (fun n => n % q = a % q)).filter (fun n => d ∣ n) =
      (Finset.Ioc (Nat.ceil x - 1) (Nat.floor (x+y))).filter
      (fun n => d ∣ n ∧ n ≡ (Nat.chineseRemainder hdq 0 a : ℕ) [MOD (d * q)])
    from ?_]
  · -- Now strip the `d ∣ n` part using joint_iff_crt
    congr 1
    apply Finset.filter_congr
    intro x _
    constructor
    · rintro ⟨hdx, hcrt⟩; exact hcrt
    · intro hcrt
      have : d ∣ x ∧ x ≡ a [MOD q] := (joint_iff_crt hd hq hdq x).mpr hcrt
      exact ⟨this.1, hcrt⟩
  · -- The set equality
    have h_icc_ioc : Finset.Icc (Nat.ceil x) (Nat.floor (x+y)) =
        Finset.Ioc (Nat.ceil x - 1) (Nat.floor (x+y)) := by
      rw [← Finset.Icc_succ_left_eq_Ioc]
      congr
      simpa [Nat.pred_eq_sub_one] using
        (Nat.succ_pred_eq_of_pos (Nat.ceil_pos.mpr hx)).symm
    rw [h_icc_ioc]
    -- Combine the two filters into one
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    have hiff : (d ∣ n ∧ n % q = a % q) ↔
        (d ∣ n ∧ n ≡ (Nat.chineseRemainder hdq 0 a : ℕ) [MOD (d * q)]) := by
      constructor
      · rintro ⟨hdn, hnq⟩
        have : n ≡ a [MOD q] := hnq
        exact ⟨hdn, (joint_iff_crt hd hq hdq n).mp ⟨hdn, this⟩⟩
      · rintro ⟨hdn, hcrt⟩
        have : d ∣ n ∧ n ≡ a [MOD q] := (joint_iff_crt hd hq hdq n).mpr hcrt
        exact ⟨hdn, this.2⟩
    tauto

/-- The remainder term for the AP sieve at coprime `d`. -/
theorem rem_AP_eq (x y z : ℝ) (hx : 0 < x) (q a : ℕ) (hq : 1 ≤ q) (hz : 1 ≤ z)
    {d : ℕ} (hd : d ≠ 0) (hdq : Nat.Coprime d q) :
    (primeInterSieveAP x y z q a hq hz).rem d =
      ↑(((Finset.Ioc (Nat.ceil x - 1) (Nat.floor (x+y))).filter
        (fun n => n ≡ (Nat.chineseRemainder hdq 0 a : ℕ) [MOD (d * q)])).card)
      - (↑d)⁻¹ * (y / (q : ℝ)) := by
  unfold LPSieve.rem
  rw [multSum_AP_eq x y z hx q a hq hz hd hdq]
  simp [primeInterSieveAP, if_neg hd]

/-- `|⌊r⌋ - r| ≤ 1` for real `r`. -/
private lemma abs_floor_sub_le (r : ℝ) : |((⌊r⌋ : ℤ) : ℝ) - r| ≤ 1 := by
  have h1 : (⌊r⌋ : ℝ) ≤ r := Int.floor_le r
  have h2 : r < ⌊r⌋ + 1 := Int.lt_floor_add_one r
  rw [abs_le]
  constructor <;> linarith

/-- Pushing `Int.floor` through `ℚ → ℝ` cast. -/
private lemma floor_rat_cast_eq_floor_real (r : ℚ) :
    ((⌊r⌋ : ℤ) : ℝ) = ((⌊(r : ℝ)⌋ : ℤ) : ℝ) := by
  congr 1; exact (Rat.floor_cast r).symm

/-- The count of integers ≡ v mod m in `Ioc a b` is within 2 of `(b - a) / m`,
provided `a ≤ b`. -/
private lemma abs_count_modEq_sub_le (a b m v : ℕ) (hm : 0 < m) (hab : a ≤ b) :
    |(((Finset.Ioc a b).filter (fun n => n ≡ v [MOD m])).card : ℝ)
        - ((b : ℝ) - a) / m| ≤ 2 := by
  have hcount : (((Finset.Ioc a b).filter (fun n => n ≡ v [MOD m])).card : ℤ) =
      max (⌊((b : ℚ) - v) / m⌋ - ⌊((a : ℚ) - v) / m⌋) 0 :=
    Nat.Ioc_filter_modEq_card a b hm v
  have hm_R : (0 : ℝ) < m := by exact_mod_cast hm
  have h_q_to_R_b : ((⌊((b : ℚ) - v) / m⌋ : ℤ) : ℝ) =
      ((⌊((b : ℝ) - v) / m⌋ : ℤ) : ℝ) := by
    rw [floor_rat_cast_eq_floor_real]; congr 2; push_cast; ring
  have h_q_to_R_a : ((⌊((a : ℚ) - v) / m⌋ : ℤ) : ℝ) =
      ((⌊((a : ℝ) - v) / m⌋ : ℤ) : ℝ) := by
    rw [floor_rat_cast_eq_floor_real]; congr 2; push_cast; ring
  have hN_eq : (((Finset.Ioc a b).filter (fun n => n ≡ v [MOD m])).card : ℝ) =
      ((max (⌊((b : ℚ) - v) / m⌋ - ⌊((a : ℚ) - v) / m⌋) 0 : ℤ) : ℝ) := by
    exact_mod_cast hcount
  rw [hN_eq]
  set FbR : ℝ := ((⌊((b : ℝ) - v) / m⌋ : ℤ) : ℝ) with hFbR_def
  set FaR : ℝ := ((⌊((a : ℝ) - v) / m⌋ : ℤ) : ℝ) with hFaR_def
  have hb_close : |FbR - (((b : ℝ) - v) / m)| ≤ 1 := abs_floor_sub_le _
  have ha_close : |FaR - (((a : ℝ) - v) / m)| ≤ 1 := abs_floor_sub_le _
  have h_FF_close : |(FbR - FaR) - (((b : ℝ) - a) / m)| ≤ 2 := by
    have heq : (FbR - FaR) - (((b : ℝ) - a) / m) =
        (FbR - ((b : ℝ) - v) / m) - (FaR - ((a : ℝ) - v) / m) := by field_simp; ring
    rw [heq]
    calc |(FbR - (((b : ℝ) - v) / m)) - (FaR - (((a : ℝ) - v) / m))|
        ≤ |FbR - (((b : ℝ) - v) / m)| + |FaR - (((a : ℝ) - v) / m)| := abs_sub _ _
      _ ≤ 1 + 1 := by linarith
      _ = 2 := by norm_num
  by_cases h : (⌊((b : ℚ) - v) / m⌋ - ⌊((a : ℚ) - v) / m⌋ : ℤ) ≤ 0
  · rw [max_eq_right h]
    push_cast
    have h_floor_le : FbR ≤ FaR := by
      have hZ : (⌊((b : ℚ) - v) / m⌋ : ℤ) ≤ ⌊((a : ℚ) - v) / m⌋ := by linarith
      have hZ_R : ((⌊((b : ℚ) - v) / m⌋ : ℤ) : ℝ) ≤ ((⌊((a : ℚ) - v) / m⌋ : ℤ) : ℝ) := by
        exact_mod_cast hZ
      rw [h_q_to_R_b, h_q_to_R_a] at hZ_R; exact hZ_R
    have hbv : (((b : ℝ) - v) / m) ≤ FbR + 1 := by rw [abs_le] at hb_close; linarith
    have hav : FaR ≤ (((a : ℝ) - v) / m) + 1 := by rw [abs_le] at ha_close; linarith
    have hba_le : ((b : ℝ) - a) / m ≤ 2 := by
      have : (((b : ℝ) - v) / m) - (((a : ℝ) - v) / m) = ((b : ℝ) - a) / m := by
        field_simp; ring
      linarith
    have hba_nn : 0 ≤ ((b : ℝ) - a) / m := by
      apply div_nonneg
      · have : (a : ℝ) ≤ b := by exact_mod_cast hab
        linarith
      · linarith
    rw [abs_le]; constructor <;> linarith
  · push_neg at h
    rw [max_eq_left h.le]
    push_cast
    rw [h_q_to_R_b, h_q_to_R_a]
    show |FbR - FaR - ((b : ℝ) - a) / m| ≤ 2
    exact h_FF_close

/-- Bound the AP remainder by a fixed constant `5 = 2 + 3`. -/
theorem abs_rem_AP_le (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (q a : ℕ) (hq : 1 ≤ q)
    (hz : 1 ≤ z) {d : ℕ} (hd : d ≠ 0) (hdq : Nat.Coprime d q) :
    |(primeInterSieveAP x y z q a hq hz).rem d| ≤ 5 := by
  rw [rem_AP_eq x y z hx q a hq hz hd hdq]
  set b : ℕ := Nat.floor (x + y) with hb_def
  set a' : ℕ := Nat.ceil x - 1 with ha_def
  set k : ℕ := (Nat.chineseRemainder hdq 0 a : ℕ) with hk_def
  set m : ℕ := d * q with hm_def
  have hm_pos : 0 < m := Nat.mul_pos (Nat.pos_of_ne_zero hd) hq
  have hd_R : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hq_R : (0 : ℝ) < q := by exact_mod_cast hq
  have hm_R : (0 : ℝ) < m := by exact_mod_cast hm_pos
  have hab : a' ≤ b := by
    rw [ha_def, hb_def]
    have h_ceil_le : Nat.ceil x ≤ Nat.floor x + 1 := Nat.ceil_le_floor_add_one x
    have h_floor_le : Nat.floor x ≤ Nat.floor (x + y) := Nat.floor_mono (by linarith)
    omega
  have h_step1 := abs_count_modEq_sub_le a' b m k hm_pos hab
  set N : ℝ := (((Finset.Ioc a' b).filter (fun n => n ≡ k [MOD m])).card : ℝ) with hN_def
  have h_bx : |((b : ℝ) - (x + y))| ≤ 1 := by
    have h1 : (Nat.floor (x + y) : ℝ) ≤ x + y := Nat.floor_le (by linarith)
    have h2 : x + y < (Nat.floor (x + y) : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [hb_def]; rw [abs_le]; constructor <;> linarith
  have ha'_eq : (a' : ℝ) + 1 = (Nat.ceil x : ℝ) := by
    have h_ceil_ge_1 : 1 ≤ Nat.ceil x := Nat.ceil_pos.mpr hx
    rw [ha_def]
    push_cast [Nat.cast_sub h_ceil_ge_1]
    ring
  have h_ceil : |((Nat.ceil x : ℝ) - x)| ≤ 1 := by
    have h1 : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one (le_of_lt hx)
    rw [abs_le]; constructor <;> linarith
  have h_step2 : |((b : ℝ) - a') / m - y / m| ≤ 3 := by
    have h_num : |((b : ℝ) - a') - y| ≤ 3 := by
      have heq : (b : ℝ) - a' - y = ((b : ℝ) - (x + y)) - ((a' : ℝ) + 1 - x) + 1 := by ring
      rw [heq, ha'_eq]
      have h_abs_one : |(1 : ℝ)| = 1 := abs_one
      have h_sub_abs := abs_sub ((b : ℝ) - (x + y)) ((Nat.ceil x : ℝ) - x)
      calc |((b : ℝ) - (x + y)) - ((Nat.ceil x : ℝ) - x) + 1|
          ≤ |((b : ℝ) - (x + y)) - ((Nat.ceil x : ℝ) - x)| + |(1 : ℝ)| := abs_add_le _ _
        _ ≤ (|((b : ℝ) - (x + y))| + |((Nat.ceil x : ℝ) - x)|) + 1 := by linarith
        _ ≤ (1 + 1) + 1 := by linarith
        _ = 3 := by norm_num
    have hdiv : (((b : ℝ) - a') / m - y / m) = ((b : ℝ) - a' - y) / m := by rw [← sub_div]
    rw [hdiv, abs_div, abs_of_pos hm_R]
    have hm_ge_1 : (1 : ℝ) ≤ m := by exact_mod_cast hm_pos
    calc |((b : ℝ) - a' - y)| / m ≤ 3 / m := by gcongr
      _ ≤ 3 := by rw [div_le_iff₀ hm_R]; linarith
  have hyqm : ((d : ℝ))⁻¹ * (y / q) = y / m := by
    rw [hm_def]; push_cast; field_simp
  rw [hyqm]
  show |N - y / m| ≤ 5
  calc |N - y / m|
      = |(N - ((b : ℝ) - a') / m) + (((b : ℝ) - a') / m - y / m)| := by congr 1; ring
    _ ≤ |N - ((b : ℝ) - a') / m| + |((b : ℝ) - a') / m - y / m| := abs_add_le _ _
    _ ≤ 2 + 3 := by linarith
    _ = 5 := by norm_num

/-- Every divisor of `primorialRestricted q N` is coprime to `q`. -/
private lemma coprime_of_dvd_primorialRestricted (q N : ℕ) {d : ℕ} (hd_pos : 0 < d)
    (hd : d ∣ primorialRestricted q N) : Nat.Coprime d q := by
  rw [Nat.Coprime]
  by_contra h_ne
  have h_gcd_pos : 1 < Nat.gcd d q := by
    have h_gcd_ne_zero : Nat.gcd d q ≠ 0 := by
      intro h
      rw [Nat.gcd_eq_zero_iff] at h
      omega
    omega
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd (by omega : Nat.gcd d q ≠ 1)
  have hpd : p ∣ d := hp_dvd.trans (Nat.gcd_dvd_left d q)
  have hpq : p ∣ q := hp_dvd.trans (Nat.gcd_dvd_right d q)
  have hp_in_prim : p ∣ primorialRestricted q N := hpd.trans hd
  unfold primorialRestricted at hp_in_prim
  obtain ⟨p', hp'_mem, hp_dvd_p'⟩ :=
    Prime.exists_mem_finset_dvd hp_prime.prime hp_in_prim
  rw [Finset.mem_filter] at hp'_mem
  have ⟨_, hp'_prime, hp'_ndvd⟩ := hp'_mem
  have hp_eq_p' : p = p' :=
    (Nat.prime_dvd_prime_iff_eq hp_prime hp'_prime).mp hp_dvd_p'
  rw [hp_eq_p'] at hpq
  exact hp'_ndvd hpq

/-- Variant of lean-pool's `rem_sum_le_of_const` where the bound only needs to hold
for divisors of `prodPrimes`. -/
private theorem rem_sum_le_of_const_dvd (s : LPSelbergSieve) (C : ℝ) (hC : 0 ≤ C)
    (hrem : ∀ d, 0 < d → d ∣ s.prodPrimes → |s.rem d| ≤ C) :
    ∑ d ∈ s.prodPrimes.divisors,
        (if (d : ℝ) ≤ s.level then (3 : ℝ) ^ ω d * |s.rem d| else 0)
      ≤ C * s.level * (1 + Real.log s.level) ^ 3 := by
  rw [← Finset.sum_filter]
  trans (∑ d ∈ Finset.filter (fun d : ℕ => ↑d ≤ s.level)
      (s.toLPSieve.prodPrimes.divisors), (3 : ℝ) ^ ω d * C)
  · apply Finset.sum_le_sum
    intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    have hd_ne_zero : d ≠ 0 := ne_zero_of_dvd_ne_zero hd.1.2 hd.1.1
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd_ne_zero
    have h_bound : |s.rem d| ≤ C := hrem d hd_pos hd.1.1
    have h_pow_nn : (0 : ℝ) ≤ (3 : ℝ) ^ ω d := pow_nonneg (by norm_num) _
    have h_abs_nn : (0 : ℝ) ≤ |s.rem d| := abs_nonneg _
    nlinarith
  rw [show C * s.level * (1 + Real.log s.level)^3 =
      C * (s.level * (1 + Real.log s.level)^3) from by ring]
  simp_rw [show ∀ i, (3 : ℝ) ^ ω i * C = C * (3 : ℝ) ^ ω i from fun i => by ring]
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ hC
  rw [Finset.sum_filter]
  have := Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow (P := s.prodPrimes) (h := 3)
    s.level s.one_le_level s.prodPrimes_squarefree
  push_cast at this
  convert this using 2

/-- Sum of `3^ω(d) · |rem(d)|` over divisors of prodPrimes ≤ z bounded by `5z(1+log z)^3`. -/
theorem primeSieve_rem_sum_AP_le (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (q a : ℕ)
    (hq : 1 ≤ q) (hz : 1 ≤ z) :
    ∑ d ∈ (primeInterSieveAP x y z q a hq hz).prodPrimes.divisors,
      (if (d : ℝ) ≤ (primeInterSieveAP x y z q a hq hz).level then
        (3 : ℝ) ^ ω d * |(primeInterSieveAP x y z q a hq hz).rem d| else 0)
      ≤ 5 * z * (1 + Real.log z) ^ 3 := by
  apply rem_sum_le_of_const_dvd (primeInterSieveAP x y z q a hq hz) 5 (by norm_num)
  intro d hd_pos hd_dvd
  have hd_coprime : Nat.Coprime d q :=
    coprime_of_dvd_primorialRestricted q (Nat.floor z) hd_pos hd_dvd
  exact abs_rem_AP_le x y z hx hy q a hq hz hd_pos.ne' hd_coprime

/-! ## Lower bound on Selberg bounding sum (AP form)

We prove `selbergBoundingSum ≥ log(z) · φ(q) / (4q)` under the strong hypothesis
`16 q^4 ≤ z`. Strategy:
1. Lower-bound `selbergBoundingSum` by `∑_{m ∈ [1, ⌊√z⌋], gcd(m,q)=1} 1/m` (adapting
   the `selbergBoundingSum_ge_sum_div` proof from lean-pool).
2. Bound the coprime harmonic sum by a block-counting argument:
   `∑_{m ≤ Mq, gcd(m,q)=1} 1/m ≥ (φ(q)/q) · log(M+1)`.
3. Choose `M = ⌊⌊√z⌋/q⌋`. With `16q^4 ≤ z`, get `M+1 ≥ 3 z^{1/4}/2 ≥ z^{1/4}`,
   so `log(M+1) ≥ log(z)/4`.
-/

/-- Helper: the radical of `m` (coprime to `q`, bounded by `z`) divides
`primorialRestricted q ⌊z⌋`. -/
private lemma rad_dvd_primorialRestricted
    (q : ℕ) (z : ℝ) (hz : 1 ≤ z) {m : ℕ} (hm_pos : 0 < m) (hm_le : (m : ℝ) ≤ z)
    (hmq : Nat.Coprime m q) :
    (∏ p ∈ m.primeFactors, p) ∣ primorialRestricted q (Nat.floor z) := by
  unfold primorialRestricted
  apply Finset.prod_dvd_prod_of_subset
  intro p hp_in
  rw [Nat.mem_primeFactors] at hp_in
  obtain ⟨hp_prime, hp_dvd, _⟩ := hp_in
  have hp_le_m : p ≤ m := Nat.le_of_dvd hm_pos hp_dvd
  have hp_le_z : (p : ℝ) ≤ z := by
    calc (p : ℝ) ≤ (m : ℝ) := by exact_mod_cast hp_le_m
      _ ≤ z := hm_le
  have hp_le_floor : p ≤ Nat.floor z := Nat.le_floor hp_le_z
  have hp_not_dvd_q : ¬ p ∣ q := by
    intro hpq
    have hdvd_gcd : p ∣ Nat.gcd m q := Nat.dvd_gcd hp_dvd hpq
    rw [Nat.Coprime] at hmq
    rw [hmq] at hdvd_gcd
    exact hp_prime.one_lt.ne' (Nat.eq_one_of_dvd_one hdvd_gcd)
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hp_prime, hp_not_dvd_q⟩

/-- Lower bound for the AP-sieve Selberg bounding sum by the coprime harmonic sum.
This is the AP-analogue of `boundingSum_ge_sum`, adapted from `selbergBoundingSum_ge_sum_div`
in lean-pool. The key change is that we restrict the inner sum to `m` coprime to `q`. -/
private lemma selbergBoundingSum_AP_ge_coprime_sum (x y z : ℝ) (hx : 0 < x) (hy : 0 < y)
    (q a : ℕ) (hq : 1 ≤ q) (hz : 1 ≤ z) :
    ((primeInterSieveAP x y z q a hq hz).selbergBoundingSum : ℝ) ≥
      ∑ m ∈ (Finset.Icc 1 (Nat.floor (Real.sqrt z))).filter
        (fun m => Nat.Coprime m q), (1 : ℝ) / (m : ℝ) := by
  set s := primeInterSieveAP x y z q a hq hz with hs_def
  have hnu_cm : PrimeUpperBound.CompletelyMultiplicative s.nu :=
    PrimeUpperBound.CompletelyMultiplicative.zeta.pdiv PrimeUpperBound.CompletelyMultiplicative.id
  have hnu_nonneg : ∀ n, 0 ≤ s.nu n := by
    intro n
    show 0 ≤ ((ζ : ArithmeticFunction ℝ).pdiv .id) n
    by_cases h : n = 0
    · simp [h]
    · apply div_nonneg
      · simp [h]
      · simp
  have hnu_lt : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p < 1 := s.nu_lt_one_of_prime
  have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt z := Real.sqrt_nonneg z
  -- Chain of inequalities mirroring lean-pool's selbergBoundingSum_ge_sum_div.
  show s.selbergBoundingSum ≥ _
  dsimp only [LPSelbergSieve.selbergBoundingSum]
  calc ∑ l ∈ s.prodPrimes.divisors,
          (if ((l ^ 2 : ℕ) : ℝ) ≤ s.level then s.selbergTerms l else 0)
      ≥ ∑ l ∈ s.prodPrimes.divisors.filter (fun l : ℕ => ((l ^ 2 : ℕ) : ℝ) ≤ s.level),
          ∑ m ∈ (l ^ Nat.floor s.level).divisors.filter (l ∣ ·), s.nu m := ?_
    _ ≥ ∑ m ∈ (Finset.Icc 1 (Nat.floor (Real.sqrt s.level))).filter
            (fun m => Nat.Coprime m q), s.nu m := ?_
    _ = ∑ m ∈ (Finset.Icc 1 (Nat.floor (Real.sqrt z))).filter
            (fun m => Nat.Coprime m q), (1 : ℝ) / (m : ℝ) := ?_
  · -- First leg: identical to the lean-pool proof.
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum
    intro l hl
    rw [Finset.mem_filter, Nat.mem_divisors] at hl
    have hlsq : Squarefree l := Squarefree.squarefree_of_dvd hl.1.1 s.prodPrimes_squarefree
    trans (∏ p ∈ l.primeFactors, ∑ n ∈ Finset.Icc 1 (Nat.floor s.level), s.nu (p ^ n))
    · rw [PrimeUpperBound.prod_factors_sum_pow_compMult (Nat.floor s.level) _ s.nu]
      · exact hnu_cm
      · exact hlsq
      · rw [ne_eq, Nat.floor_eq_zero, not_lt]; exact s.one_le_level
    · rw [s.selbergTerms_apply l]
      apply PrimeUpperBound.prod_factors_one_div_compMult_ge _ _ hnu_cm _ _ hlsq
      · intro p hpp hpl; exact hnu_lt p hpp (Trans.trans hpl hl.1.1)
      · exact hnu_nonneg
  · -- Second leg: show the bi-union over l's contains every coprime m ≤ √z.
    rw [← Finset.sum_biUnion]
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        rw [Finset.mem_filter, Finset.mem_Icc] at hm
        obtain ⟨⟨hm1, hm_le⟩, hmq⟩ := hm
        have hm_pos : 0 < m := hm1
        have hm_ne_zero : m ≠ 0 := hm_pos.ne'
        have hm_le_R : (m : ℝ) ≤ Real.sqrt s.level := by
          calc (m : ℝ) ≤ (Nat.floor (Real.sqrt s.level) : ℝ) := by exact_mod_cast hm_le
            _ ≤ Real.sqrt s.level := Nat.floor_le hsqrt_nn
        have hm_le_z : (m : ℝ) ≤ s.level := by
          calc (m : ℝ) ≤ Real.sqrt s.level := hm_le_R
            _ ≤ s.level := PrimeUpperBound.sqrt_le_self s.level s.one_le_level
        have hprod_pos : 0 < (∏ p ∈ m.primeFactors, p) :=
          Finset.prod_pos (fun p hp => Nat.pos_of_mem_primeFactors hp)
        have hprod_ne_zero : (∏ p ∈ m.primeFactors, p) ^ ⌊s.level⌋₊ ≠ 0 :=
          pow_ne_zero _ hprod_pos.ne'
        rw [Finset.mem_biUnion]
        simp_rw [Finset.mem_filter, Nat.mem_divisors]
        refine ⟨∏ p ∈ m.primeFactors, p, ?_, ?_⟩
        · refine ⟨⟨?_, s.prodPrimes_ne_zero⟩, ?_⟩
          · change (∏ p ∈ m.primeFactors, p) ∣ primorialRestricted q (Nat.floor z)
            exact rad_dvd_primorialRestricted q z hz hm_pos hm_le_z hmq
          · rw [← Real.sqrt_le_sqrt_iff (by linarith only [s.one_le_level]),
                Nat.cast_pow, Real.sqrt_sq]
            · trans (m : ℝ)
              · norm_cast
                exact Nat.le_of_dvd hm_pos (Nat.prod_primeFactors_dvd m)
              · exact hm_le_R
            · norm_cast; omega
        · refine ⟨⟨?_, hprod_ne_zero⟩, Nat.prod_primeFactors_dvd m⟩
          rw [← Nat.factorization_le_iff_dvd hm_ne_zero hprod_ne_zero, Nat.factorization_pow]
          intro p
          have hy_mul_prod_nonneg :
              0 ≤ ⌊s.level⌋₊ * (Nat.factorization (∏ p ∈ m.primeFactors, p)) p :=
            Nat.zero_le _
          trans (Nat.factorization m) p * 1
          · rw [mul_one]
          trans ⌊s.level⌋₊ * Nat.factorization (∏ p ∈ m.primeFactors, p) p
          swap
          · apply le_rfl
          by_cases hpp : p.Prime
          swap
          · rw [Nat.factorization_eq_zero_of_not_prime _ hpp, zero_mul]
            exact hy_mul_prod_nonneg
          by_cases hpdvd : p ∣ m
          swap
          · rw [Nat.factorization_eq_zero_of_not_dvd hpdvd, zero_mul]
            exact hy_mul_prod_nonneg
          apply mul_le_mul
          · trans m
            · exact le_of_lt <| Nat.factorization_lt p hm_ne_zero
            apply Nat.le_floor
            calc (m : ℝ) ≤ Real.sqrt s.level := hm_le_R
              _ ≤ s.level := PrimeUpperBound.sqrt_le_self s.level s.one_le_level
          · rw [← Nat.Prime.pow_dvd_iff_le_factorization hpp hprod_pos.ne', pow_one]
            apply Finset.dvd_prod_of_mem
            rw [Nat.mem_primeFactors]
            exact ⟨hpp, hpdvd, hm_ne_zero⟩
          · norm_num
          · norm_num
      · intro i _ _; apply hnu_nonneg
    · intro i hi j hj hij t hti htj n hn
      exfalso
      specialize hti hn
      specialize htj hn
      simp_rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at *
      have hh : ∀ i j {n}, i ∣ s.prodPrimes → i ∣ n → n ∣ j ^ ⌊s.level⌋₊ → i ∣ j := by
        intro i j n hiP hin hij
        apply PrimeUpperBound.nat_squarefree_dvd_pow i j _ (s.squarefree_of_dvd_prodPrimes hiP)
        exact Trans.trans hin hij
      have hidvdj : i ∣ j := hh i j hi.1.1 hti.2 htj.1.1
      have hjdvdi : j ∣ i := hh j i hj.1.1 htj.2 hti.1.1
      exact hij <| Nat.dvd_antisymm hidvdj hjdvdi
  · -- Final equality: ν(m) = 1/m for m ≥ 1, and s.level = z.
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    have hm_ne : m ≠ 0 := by omega
    show ((ζ : ArithmeticFunction ℝ).pdiv .id) m = 1 / (m : ℝ)
    simp [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply_ne hm_ne, ArithmeticFunction.id_apply, one_div]

/-- For `q ≥ 1`, the number of integers in `(k·q, (k+1)·q]` coprime to `q` equals `φ(q)`. -/
private lemma card_block_coprime (q : ℕ) (hq : 1 ≤ q) (k : ℕ) :
    ((Finset.Ioc (k * q) ((k + 1) * q)).filter (fun m => Nat.Coprime m q)).card
      = q.totient := by
  classical
  have hq_pos : 0 < q := hq
  -- Step 1: shift bijection — block of size q starting at k·q matches Ioc 0 q.
  have h_shift_card :
      ((Finset.Ioc (k * q) ((k + 1) * q)).filter (fun m => Nat.Coprime m q)).card =
      ((Finset.Ioc 0 q).filter (fun m => Nat.Coprime m q)).card := by
    apply Finset.card_bij (fun m _ => m - k * q)
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hm
      obtain ⟨⟨h1, h2⟩, hmq⟩ := hm
      have hexp : (k + 1) * q = k * q + q := by ring
      rw [hexp] at h2
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have heq : m = (m - k * q) + k * q := by omega
      rw [Nat.Coprime, heq, Nat.gcd_add_mul_right_left] at hmq
      exact hmq
    · intro a ha b hb hab
      simp only [Finset.mem_filter, Finset.mem_Ioc] at ha hb
      have hexp : (k + 1) * q = k * q + q := by ring
      rw [hexp] at ha hb
      omega
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
      obtain ⟨⟨h1, h2⟩, hnq⟩ := hn
      refine ⟨n + k * q, ?_, by omega⟩
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨by omega, ?_⟩, ?_⟩
      · have hexp : (k + 1) * q = k * q + q := by ring
        omega
      · rw [Nat.Coprime, Nat.gcd_add_mul_right_left]
        exact hnq
  rw [h_shift_card]
  -- Step 2: |{m ∈ Ioc 0 q : Coprime m q}| = φ(q).
  rw [Nat.totient_eq_card_coprime]
  -- target: #{m ∈ Ioc 0 q | m.Coprime q} = #{a ∈ range q | q.Coprime a}
  -- bijection: identity (within the range), using Coprime symmetric.
  by_cases hq1 : q = 1
  · subst hq1
    -- Both sides have card 1.
    have h_left : (Finset.Ioc 0 1).filter (fun m => Nat.Coprime m 1) = {1} := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h1, h2⟩, _⟩; omega
      · rintro rfl; exact ⟨⟨one_pos, le_refl _⟩, Nat.coprime_one_right _⟩
    have h_right : (Finset.range 1).filter (fun a => Nat.Coprime 1 a) = {0} := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, _⟩; omega
      · rintro rfl; exact ⟨one_pos, Nat.coprime_one_left _⟩
    rw [h_left, h_right]
    simp
  · have hq2 : 2 ≤ q := by omega
    have h_q_not_co : ¬ Nat.Coprime q q := by
      rw [Nat.Coprime, Nat.gcd_self]; omega
    have h_0_not_co : ¬ Nat.Coprime 0 q := by
      rw [Nat.Coprime, Nat.gcd_zero_left]; omega
    have h_0_not_co' : ¬ Nat.Coprime q 0 := by
      rw [Nat.Coprime, Nat.gcd_zero_right]; omega
    -- Show both filtered sets equal {a ∈ Ico 1 q : Coprime a q}.
    have hA : (Finset.Ioc 0 q).filter (fun m => Nat.Coprime m q) =
              (Finset.Ico 1 q).filter (fun m => Nat.Coprime m q) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ico]
      constructor
      · rintro ⟨⟨h1, h2⟩, hmq⟩
        refine ⟨⟨h1, ?_⟩, hmq⟩
        by_contra hc; push_neg at hc
        have : m = q := by omega
        rw [this] at hmq; exact h_q_not_co hmq
      · rintro ⟨⟨h1, h2⟩, hmq⟩; exact ⟨⟨h1, by omega⟩, hmq⟩
    have hB : (Finset.range q).filter (fun a => Nat.Coprime q a) =
              (Finset.Ico 1 q).filter (fun m => Nat.Coprime m q) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      constructor
      · rintro ⟨hm, hmq⟩
        refine ⟨⟨?_, hm⟩, Nat.coprime_comm.mp hmq⟩
        by_contra hc; push_neg at hc
        have : m = 0 := by omega
        rw [this] at hmq; exact h_0_not_co' hmq
      · rintro ⟨⟨h1, h2⟩, hmq⟩
        exact ⟨h2, Nat.coprime_comm.mp hmq⟩
    rw [hA, hB]

/-- Coprime harmonic block bound:
`∑_{m ≤ M·q, gcd(m,q)=1} 1/m ≥ (φ(q)/q) · ∑_{k=1}^M 1/k`. -/
private lemma coprime_harmonic_block_lower_bound (q : ℕ) (hq : 1 ≤ q) (M : ℕ) :
    ∑ m ∈ (Finset.Ioc 0 (M * q)).filter (fun m => Nat.Coprime m q), (1 : ℝ) / (m : ℝ)
      ≥ (q.totient : ℝ) / q * ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ) := by
  classical
  have hq_pos : 0 < q := hq
  have hq_R : (0 : ℝ) < q := by exact_mod_cast hq_pos
  -- Partition Ioc 0 (Mq) into blocks ((k-1)q, kq] for k = 1..M (when M ≥ 1).
  -- We use the disjoint union: Ioc 0 (Mq) = ⋃_{k=0}^{M-1} Ioc (k·q) ((k+1)·q).
  -- Then sum over each block contributes ≥ φ(q)/((k+1)q).
  set blocks : ℕ → Finset ℕ := fun k =>
    (Finset.Ioc (k * q) ((k + 1) * q)).filter (fun m => Nat.Coprime m q) with hblocks_def
  have h_block_sum :
      (Finset.Ioc 0 (M * q)).filter (fun m => Nat.Coprime m q) =
        (Finset.range M).biUnion blocks := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_biUnion, Finset.mem_range,
      hblocks_def]
    constructor
    · rintro ⟨⟨h1, h2⟩, hmq⟩
      refine ⟨(m - 1) / q, ?_, ?_⟩
      · -- (m-1)/q < M, since m ≤ Mq so m-1 < Mq, so (m-1)/q < M.
        rw [Nat.div_lt_iff_lt_mul hq_pos]; omega
      · refine ⟨⟨?_, ?_⟩, hmq⟩
        · -- (m-1)/q * q < m
          have h_mod : (m - 1) % q < q := Nat.mod_lt _ hq_pos
          have h_dm := Nat.div_add_mod (m - 1) q
          have h_comm : q * ((m - 1) / q) = (m - 1) / q * q := Nat.mul_comm _ _
          omega
        · -- m ≤ ((m-1)/q + 1) * q
          have hadd : ((m - 1) / q + 1) * q = (m - 1) / q * q + q := by ring
          have hmod : (m - 1) % q < q := Nat.mod_lt _ hq_pos
          have h_dm := Nat.div_add_mod (m - 1) q
          have h_comm : q * ((m - 1) / q) = (m - 1) / q * q := Nat.mul_comm _ _
          omega
    · rintro ⟨k, hkM, ⟨⟨h_lo, h_hi⟩, hmq⟩⟩
      refine ⟨⟨?_, ?_⟩, hmq⟩
      · -- 0 < m: m > k*q ≥ 0.
        have : k * q ≥ 0 := Nat.zero_le _
        omega
      · -- m ≤ M*q
        calc m ≤ (k + 1) * q := h_hi
          _ ≤ M * q := by
            apply Nat.mul_le_mul_right
            omega
  rw [h_block_sum]
  rw [Finset.sum_biUnion]
  · -- Now: ∑_{k=0}^{M-1} ∑_{m ∈ blocks k} 1/m ≥ (φ(q)/q) ∑_{k=1}^M 1/k
    -- Re-index: k' = k+1 so k=0 ↔ k'=1.
    have h_reindex :
        ∑ k ∈ Finset.range M, ∑ m ∈ blocks k, (1 : ℝ) / (m : ℝ) =
        ∑ k ∈ Finset.Icc 1 M, ∑ m ∈ blocks (k - 1), (1 : ℝ) / (m : ℝ) := by
      apply Finset.sum_bij (fun k _ => k + 1)
      · intro k hk
        rw [Finset.mem_Icc]; rw [Finset.mem_range] at hk; omega
      · intro k _ k' _ hk; omega
      · intro k hk
        rw [Finset.mem_Icc] at hk
        refine ⟨k - 1, ?_, ?_⟩
        · rw [Finset.mem_range]; omega
        · omega
      · intro k _; simp
    rw [h_reindex]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk_pos : 0 < k := hk.1
    have hk_R : (0 : ℝ) < k := by exact_mod_cast hk_pos
    have hkq_R : (0 : ℝ) < (k * q : ℕ) := by exact_mod_cast Nat.mul_pos hk_pos hq_pos
    -- block (k-1) has φ(q) elements, each m ≤ k*q, so 1/m ≥ 1/(k*q).
    have hk1 : k - 1 + 1 = k := by omega
    have h_card_block : (blocks (k - 1)).card = q.totient :=
      card_block_coprime q hq (k - 1)
    -- Each m in block (k-1) satisfies m ≤ k*q.
    have h_le_kq : ∀ m ∈ blocks (k - 1), (m : ℝ) ≤ (k * q : ℕ) := by
      intro m hm
      simp only [hblocks_def] at hm
      rw [Finset.mem_filter, Finset.mem_Ioc] at hm
      have hbound := hm.1.2
      rw [hk1] at hbound
      exact_mod_cast hbound
    have h_pos_m : ∀ m ∈ blocks (k - 1), 0 < (m : ℝ) := by
      intro m hm
      simp only [hblocks_def] at hm
      rw [Finset.mem_filter, Finset.mem_Ioc] at hm
      have : 0 < m := by
        have : (k - 1) * q ≥ 0 := Nat.zero_le _
        omega
      exact_mod_cast this
    -- ∑_{m ∈ blocks} 1/m ≥ ∑_{m ∈ blocks} 1/(k*q) = card * 1/(k*q) = φ(q)/(k*q).
    calc ∑ m ∈ blocks (k - 1), (1 : ℝ) / (m : ℝ)
        ≥ ∑ _ ∈ blocks (k - 1), (1 : ℝ) / ((k * q : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro m hm
          have hm_pos : 0 < (m : ℝ) := h_pos_m m hm
          have hm_le := h_le_kq m hm
          apply one_div_le_one_div_of_le hm_pos hm_le
      _ = (blocks (k - 1)).card * (1 / ((k * q : ℕ) : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (q.totient : ℝ) * (1 / ((k * q : ℕ) : ℝ)) := by rw [h_card_block]
      _ = (q.totient : ℝ) / q * (1 / (k : ℝ)) := by
          push_cast; field_simp
  · -- Pairwise disjoint blocks
    intro i hi j hj hij
    rw [Function.onFun, Finset.disjoint_left]
    intro m hm hm'
    simp only [hblocks_def, Finset.mem_filter, Finset.mem_Ioc] at hm hm'
    -- m ∈ (i*q, (i+1)*q] and m ∈ (j*q, (j+1)*q] with i ≠ j: contradiction.
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hi1q : (i + 1) * q ≤ j * q := by
        apply Nat.mul_le_mul_right; omega
      have h1 := hm.1.2
      have h2 := hm'.1.1
      omega
    · have hj1q : (j + 1) * q ≤ i * q := by
        apply Nat.mul_le_mul_right; omega
      have h1 := hm'.1.2
      have h2 := hm.1.1
      omega

/-- The main bound on the AP-sieve Selberg bounding sum.

With the hypothesis `16 q^4 ≤ z`, we have
`selbergBoundingSum ≥ (φ(q)/q) · log(z) / 4`.

The constant `1/4` is explicit. The hypothesis ensures `√z/q ≥ 4q ≥ 4` and
`z^{1/4}/q ≥ 2`, which together give enough room for the `log(z)/4` lower bound
after the elementary block-counting argument. -/
theorem boundingSum_AP_ge (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (q a : ℕ)
    (hq : 1 ≤ q) (hz : 1 ≤ z) (hzq : 16 * (q : ℝ)^4 ≤ z) :
    ((primeInterSieveAP x y z q a hq hz).selbergBoundingSum : ℝ) ≥
      Real.log z * (q.totient : ℝ) / (4 * q) := by
  classical
  have hq_pos : 0 < q := hq
  have hq_R : (0 : ℝ) < q := by exact_mod_cast hq_pos
  have hφ_nn : (0 : ℝ) ≤ (q.totient : ℝ) := by exact_mod_cast Nat.zero_le _
  -- Step 0: hypothesis implications.
  have hq4_nn : (0 : ℝ) ≤ (q : ℝ)^4 := by positivity
  have hq4_ge_1 : (1 : ℝ) ≤ (q : ℝ)^4 := by
    apply one_le_pow₀; exact_mod_cast hq
  have hz4 : (16 : ℝ) ≤ z := by linarith
  have hz_pos : 0 < z := by linarith
  have hsqrt_z_pos : 0 < Real.sqrt z := Real.sqrt_pos.mpr hz_pos
  have hsqrt_z_ge_4 : Real.sqrt z ≥ 4 := by
    have h1 : Real.sqrt 16 = 4 := by
      rw [show (16 : ℝ) = 4^2 from by norm_num]
      exact Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)
    linarith [Real.sqrt_le_sqrt hz4, h1]
  -- 4 q² ≤ √z
  have h_4q2_le_sqrtz : 4 * (q : ℝ)^2 ≤ Real.sqrt z := by
    have h_sq : (4 * (q : ℝ)^2)^2 ≤ z := by
      have heq : (4 * (q : ℝ)^2)^2 = 16 * (q : ℝ)^4 := by ring
      linarith
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 4 * (q : ℝ)^2)]
    exact Real.sqrt_le_sqrt h_sq
  have h_q_le_sqrtz4 : (q : ℝ) ≤ Real.sqrt z / 4 := by
    -- From 4q² ≤ √z and q ≥ 1: q ≤ q² ≤ √z/4.
    have hq_ge_1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hq2_ge_q : (q : ℝ) ≤ (q : ℝ)^2 := by nlinarith
    nlinarith
  -- Step 1: lower-bound by coprime harmonic sum.
  apply le_trans (b := ∑ m ∈ (Finset.Icc 1 (Nat.floor (Real.sqrt z))).filter
        (fun m => Nat.Coprime m q), (1 : ℝ) / (m : ℝ)) ?_
    (selbergBoundingSum_AP_ge_coprime_sum x y z hx hy q a hq hz)
  -- Step 2: choose N = ⌊√z⌋, M = N / q.
  set N : ℕ := Nat.floor (Real.sqrt z) with hN_def
  have hN_R_le : (N : ℝ) ≤ Real.sqrt z := Nat.floor_le (le_of_lt hsqrt_z_pos)
  have hN_R_ge : (N : ℝ) ≥ Real.sqrt z - 1 := by
    rw [hN_def]
    linarith [Nat.lt_floor_add_one (Real.sqrt z)]
  have hN_pos : 0 < N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  set M : ℕ := N / q with hM_def
  have hMq_le_N : M * q ≤ N := Nat.div_mul_le_self N q
  -- Step 3: subset sum: Ioc 0 (M*q) ⊆ Icc 1 N.
  have h_subset_sum :
      ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.Coprime m q), (1 : ℝ) / (m : ℝ)
        ≥ ∑ m ∈ (Finset.Ioc 0 (M * q)).filter (fun m => Nat.Coprime m q),
            (1 : ℝ) / (m : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      rw [Finset.mem_filter, Finset.mem_Ioc] at hm
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hm.1.1, hm.1.2.trans hMq_le_N⟩, hm.2⟩
    · intro i _ _
      positivity
  -- Step 4: apply block bound.
  have h_block := coprime_harmonic_block_lower_bound q hq M
  -- Step 5: bound H_M ≥ log(M+1) ≥ log z / 4.
  -- First show M + 1 ≥ √z/(2q) ≥ z^{1/4}/√? ... actually z^{1/4} ≥ z^{1/4}.
  have hM_R_ge : ((M : ℝ) + 1) ≥ (N : ℝ) / q := by
    -- M = N/q (nat div), so M*q ≤ N, hence (M+1)*q > N, hence M+1 > N/q.
    have h_lt : N < (M + 1) * q := by
      rw [hM_def]
      have h_mod : N % q < q := Nat.mod_lt _ hq_pos
      have h_div := Nat.div_add_mod N q
      have h_div' : N / q * q + N % q = N := by
        rw [Nat.mul_comm] at h_div; omega
      have : (N / q + 1) * q = N / q * q + q := by ring
      omega
    have h_R : ((M + 1 : ℕ) : ℝ) > (N : ℝ) / q := by
      rw [gt_iff_lt, div_lt_iff₀ hq_R]
      exact_mod_cast h_lt
    push_cast at h_R
    linarith
  have hM_R_ge' : ((M : ℝ) + 1) ≥ Real.sqrt z / (2 * q) := by
    -- N ≥ √z - 1, and √z - 1 ≥ √z / 2 (since √z ≥ 2).
    have h_N_ge_half : (N : ℝ) ≥ Real.sqrt z / 2 := by linarith
    have hNq : (N : ℝ) / q ≥ Real.sqrt z / (2 * q) := by
      rw [ge_iff_le, div_le_div_iff₀ (by linarith) hq_R]
      have : Real.sqrt z * q ≤ N * (2 * q) := by nlinarith
      linarith
    linarith
  -- Strategy: work with z^{1/4} via Real.rpow.
  have hzq4_pos : 0 < z^((1:ℝ)/4) := Real.rpow_pos_of_pos hz_pos _
  have hzq4_nn : 0 ≤ z^((1:ℝ)/4) := le_of_lt hzq4_pos
  have h_2q_le_zq : 2 * (q : ℝ) ≤ z^((1:ℝ)/4) := by
    -- From 16 q^4 ≤ z, get (2q)^4 ≤ z, hence 2q ≤ z^{1/4}.
    have h_2q4 : (2 * (q : ℝ))^4 ≤ z := by nlinarith
    have h_2q_nn : (0 : ℝ) ≤ 2 * (q : ℝ) := by positivity
    -- Use Real.rpow_le_rpow_iff_left or similar.
    have h_z_eq : z = (z^((1:ℝ)/4))^4 := by
      rw [← Real.rpow_natCast (z^((1:ℝ)/4)) 4]
      rw [← Real.rpow_mul (le_of_lt hz_pos)]
      norm_num
    rw [h_z_eq] at h_2q4
    have := pow_le_pow_iff_left₀ h_2q_nn hzq4_nn (by norm_num : 4 ≠ 0) |>.mp h_2q4
    exact this
  -- √z = z^{1/2} = (z^{1/4})^2.
  have h_sqrt_eq : Real.sqrt z = z^((1:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow]
  have h_z14_sq : z^((1:ℝ)/2) = (z^((1:ℝ)/4))^2 := by
    rw [show ((1:ℝ)/2) = (1:ℝ)/4 * 2 from by norm_num,
      Real.rpow_mul (le_of_lt hz_pos)]
    rw [show ((2:ℝ)) = ((2:ℕ) : ℝ) from rfl, Real.rpow_natCast]
  have hM_R_ge_zq : ((M : ℝ) + 1) ≥ z^((1:ℝ)/4) := by
    -- M+1 ≥ √z/(2q). √z = (z^{1/4})^2. 2q ≤ z^{1/4}.
    -- So √z/(2q) ≥ (z^{1/4})^2/(z^{1/4}) = z^{1/4}.
    have h_sqrt_z : Real.sqrt z = (z^((1:ℝ)/4))^2 := by rw [h_sqrt_eq, h_z14_sq]
    have h_2q_pos : 0 < 2 * (q : ℝ) := by linarith
    calc (M : ℝ) + 1 ≥ Real.sqrt z / (2 * q) := hM_R_ge'
      _ = (z^((1:ℝ)/4))^2 / (2 * q) := by rw [h_sqrt_z]
      _ ≥ (z^((1:ℝ)/4))^2 / (z^((1:ℝ)/4)) := by
          apply div_le_div_of_nonneg_left (by positivity) h_2q_pos h_2q_le_zq
      _ = z^((1:ℝ)/4) := by
          rw [sq, mul_div_assoc, div_self hzq4_pos.ne', mul_one]
  -- H_M ≥ log(M+1) ≥ log(z^{1/4}) = log(z)/4.
  have h_HM : ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ) ≥ Real.log z / 4 := by
    have h_inv : ∑ d ∈ Finset.Icc 1 M, (d : ℝ)⁻¹ ≥ Real.log (M + 1 : ℕ) :=
      Aux.log_add_one_le_sum_inv M
    have h_eq : ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ) =
        ∑ d ∈ Finset.Icc 1 M, (d : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro k _; rw [one_div]
    rw [h_eq]
    refine le_trans ?_ h_inv
    have h_log_z14 : Real.log z / 4 = Real.log (z^((1:ℝ)/4)) := by
      rw [Real.log_rpow hz_pos]; ring
    rw [h_log_z14]
    apply Real.log_le_log (by positivity)
    have : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; rfl
    rw [this]
    exact hM_R_ge_zq
  -- Conclude.
  calc ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.Coprime m q), (1 : ℝ) / (m : ℝ)
      ≥ ∑ m ∈ (Finset.Ioc 0 (M * q)).filter (fun m => Nat.Coprime m q),
          (1 : ℝ) / (m : ℝ) := h_subset_sum
    _ ≥ (q.totient : ℝ) / q * ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ) := h_block
    _ ≥ (q.totient : ℝ) / q * (Real.log z / 4) := by
        apply mul_le_mul_of_nonneg_left h_HM
        positivity
    _ = Real.log z * (q.totient : ℝ) / (4 * q) := by ring

/-! ## Final Brun–Titchmarsh AP bounds -/

/-- The Selberg sieve bound applied to the AP sieve. -/
theorem siftedSum_AP_le (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (q a : ℕ)
    (hq : 1 ≤ q) (hz : 1 ≤ z) (hzq : 16 * (q : ℝ)^4 ≤ z) (hz1 : 1 < z) :
    (primeInterSieveAP x y z q a hq hz).siftedSum ≤
      4 * q * (y / q) / ((q.totient : ℝ) * Real.log z) +
      5 * z * (1 + Real.log z) ^ 3 := by
  set s := primeInterSieveAP x y z q a hq hz with hs_def
  have hlog_pos : 0 < Real.log z := Real.log_pos hz1
  have hq_pos : 0 < q := hq
  have hq_R : (0 : ℝ) < q := by exact_mod_cast hq_pos
  have hφ_pos : 0 < q.totient := Nat.totient_pos.mpr hq_pos
  have hφ_R : (0 : ℝ) < q.totient := by exact_mod_cast hφ_pos
  have hS_pos : 0 < s.selbergBoundingSum := s.selbergBoundingSum_pos
  have hS_ge : s.selbergBoundingSum ≥ Real.log z * (q.totient : ℝ) / (4 * q) :=
    boundingSum_AP_ge x y z hx hy q a hq hz hzq
  have hbound_pos : 0 < Real.log z * (q.totient : ℝ) / (4 * q) := by positivity
  -- selberg_bound_simple gives siftedSum ≤ totalMass / S + remSum.
  apply le_trans (LPSelbergSieve.selberg_bound_simple s)
  -- totalMass = y/q, level = z.
  have htm : s.totalMass = y / q := rfl
  have hlev : s.level = z := rfl
  rw [htm]
  -- Bound y/q / S ≤ y/q / (lower bound on S).
  have hmain_bound : (y / q) / s.selbergBoundingSum ≤
      (y / q) / (Real.log z * (q.totient : ℝ) / (4 * q)) := by
    apply div_le_div_of_nonneg_left _ hbound_pos hS_ge
    positivity
  have hmain_eq : (y / q) / (Real.log z * (q.totient : ℝ) / (4 * q)) =
      4 * q * (y / q) / ((q.totient : ℝ) * Real.log z) := by
    rw [div_div_eq_mul_div]
    rw [mul_comm (Real.log z) _]
    ring
  rw [hmain_eq] at hmain_bound
  have hrem_bound := primeSieve_rem_sum_AP_le x y z hx hy q a hq hz
  -- Now combine.
  linarith [hmain_bound, hrem_bound]

open Classical in
/-- Express the AP siftedSum as the cardinality of a filtered set. -/
theorem siftedSum_AP_eq_card (x y z : ℝ) (q a : ℕ) (hq : 1 ≤ q) (hz : 1 ≤ z) :
    (primeInterSieveAP x y z q a hq hz).siftedSum =
      (((Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
        (fun n => n % q = a % q ∧
          ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → ¬ p ∣ q → ¬ p ∣ n)).card : ℝ) := by
  classical
  set s := primeInterSieveAP x y z q a hq hz with hs_def
  have h_set_eq :
      (s.support.filter (fun d => Nat.Coprime s.prodPrimes d)) =
      ((Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
        (fun n => n % q = a % q ∧
          ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → ¬ p ∣ q → ¬ p ∣ n)) := by
    ext d
    constructor
    · intro hd
      rw [Finset.mem_filter] at hd
      rcases hd with ⟨hd_supp, hd_cop⟩
      have hd_supp' : d ∈ (Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
          (fun n => n % q = a % q) := hd_supp
      rw [Finset.mem_filter] at hd_supp'
      refine Finset.mem_filter.mpr ⟨hd_supp'.1, hd_supp'.2, ?_⟩
      intro p hpp hpz hpq hpd
      have hp_in : p ∈ ((Finset.range (Nat.floor z + 1)).filter
          (fun p => p.Prime ∧ ¬ p ∣ q)) := by
        refine Finset.mem_filter.mpr ⟨?_, hpp, hpq⟩
        rw [Finset.mem_range]
        have : p ≤ Nat.floor z := Nat.le_floor hpz
        omega
      have hp_dvd_prod : p ∣ s.prodPrimes :=
        Finset.dvd_prod_of_mem _ hp_in
      have h_one : p ∣ 1 := by
        have hgcd : p ∣ Nat.gcd s.prodPrimes d := Nat.dvd_gcd hp_dvd_prod hpd
        rwa [hd_cop] at hgcd
      exact hpp.one_lt.ne' (Nat.eq_one_of_dvd_one h_one)
    · intro hd
      rw [Finset.mem_filter] at hd
      rcases hd with ⟨hd_icc, hd_mod, h_pf⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · -- d ∈ support
        change d ∈ (Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
          (fun n => n % q = a % q)
        exact Finset.mem_filter.mpr ⟨hd_icc, hd_mod⟩
      · -- Nat.Coprime s.prodPrimes d
        rw [Nat.Coprime]
        by_contra hne
        obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
        have hpprod : p ∣ s.prodPrimes := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
        have hpd : p ∣ d := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
        have h_prod_eq : s.prodPrimes = primorialRestricted q (Nat.floor z) := rfl
        rw [h_prod_eq] at hpprod
        unfold primorialRestricted at hpprod
        rcases (Prime.dvd_finset_prod_iff (Nat.prime_iff.mp hpp) _).mp hpprod with ⟨r, hr, hpr⟩
        rcases Finset.mem_filter.mp hr with ⟨hr_range, hr_prime, hr_nq⟩
        have hpr_eq : p = r := (Nat.prime_dvd_prime_iff_eq hpp hr_prime).mp hpr
        have hp_range_mem : p ∈ Finset.range (Nat.floor z + 1) := by
          rw [hpr_eq]; exact hr_range
        rw [Finset.mem_range] at hp_range_mem
        have hpz : (p : ℝ) ≤ z := by
          have : p ≤ Nat.floor z := by omega
          calc (p : ℝ) ≤ (Nat.floor z : ℝ) := by exact_mod_cast this
            _ ≤ z := Nat.floor_le (by linarith)
        have hp_nq : ¬ p ∣ q := by rw [hpr_eq]; exact hr_nq
        exact h_pf p hpp hpz hp_nq hpd
  -- Now unfold siftedSum and convert to filtered card.
  show s.siftedSum = _
  dsimp only [LPSieve.siftedSum]
  -- weights = 1, so siftedSum = ∑ d ∈ A, if Coprime then 1 else 0 = (A.filter Coprime).card
  have h_weights : ∀ d ∈ s.support, s.weights d = 1 := fun _ _ => rfl
  have : (∑ d ∈ s.support, if Nat.Coprime s.prodPrimes d then s.weights d else 0) =
      ((s.support.filter (fun d => Nat.Coprime s.prodPrimes d)).card : ℝ) := by
    rw [← Finset.sum_filter]
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_filter] at hd
    rw [h_weights d hd.1, Nat.cast_one]
  rw [this, h_set_eq]

/-- Number of primes in an AP `≤ siftedSum + z`. -/
theorem primesBetween_AP_le_siftedSum_add (x y z : ℝ) (hx : 0 < x) (hy : 0 < y)
    (q a : ℕ) (hq : 1 ≤ q) (hz : 1 ≤ z) :
    (primesBetween_AP x (x + y) q a : ℝ) ≤
      (primeInterSieveAP x y z q a hq hz).siftedSum + z := by
  classical
  set s := primeInterSieveAP x y z q a hq hz with hs_def
  rw [siftedSum_AP_eq_card x y z q a hq hz]
  -- primesBetween_AP set ⊆ sifted set ∪ Icc 1 ⌊z⌋.
  have h_subset :
      ((Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
        (fun n => n.Prime ∧ n % q = a % q)) ⊆
      (((Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
        (fun n => n % q = a % q ∧
          ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → ¬ p ∣ q → ¬ p ∣ n))) ∪
      (Finset.Icc 1 (Nat.floor z)) := by
    intro p hp_mem
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp_mem
    rw [Finset.mem_union]
    rcases hp_mem with ⟨hp_range, hp_prime, hp_mod⟩
    by_cases hpz : (p : ℝ) ≤ z
    · right
      refine Finset.mem_Icc.mpr ⟨hp_prime.one_le, Nat.le_floor hpz⟩
    · left
      push_neg at hpz
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hp_range, hp_mod, ?_⟩
      intro p' hp'_prime hp'_le _ hp'_dvd
      rw [hp_prime.dvd_iff_eq hp'_prime.ne_one] at hp'_dvd
      rw [← hp'_dvd] at hp'_le
      linarith
  have h_card_le := Finset.card_le_card h_subset
  have h_card_union := Finset.card_union_le
      ((Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
        (fun n => n % q = a % q ∧
          ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → ¬ p ∣ q → ¬ p ∣ n))
      (Finset.Icc 1 (Nat.floor z))
  have h_card_Icc : (Finset.Icc 1 (Nat.floor z)).card ≤ Nat.floor z := by
    rw [Nat.card_Icc]; omega
  have h_floor_le : (Nat.floor z : ℝ) ≤ z := Nat.floor_le (by linarith)
  -- Combine
  have h_chain : (primesBetween_AP x (x + y) q a : ℝ) ≤
      (((Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
        (fun n => n % q = a % q ∧
          ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → ¬ p ∣ q → ¬ p ∣ n)).card : ℝ) +
      (Nat.floor z : ℝ) := by
    have h1 : (primesBetween_AP x (x + y) q a : ℝ) ≤
        ((((Finset.Icc (Nat.ceil x) (Nat.floor (x + y))).filter
          (fun n => n % q = a % q ∧
            ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → ¬ p ∣ q → ¬ p ∣ n))).card +
         (Finset.Icc 1 (Nat.floor z)).card : ℝ) := by
        unfold primesBetween_AP
        exact_mod_cast le_trans h_card_le h_card_union
    have h2 : ((Finset.Icc 1 (Nat.floor z)).card : ℝ) ≤ (Nat.floor z : ℝ) := by
      exact_mod_cast h_card_Icc
    linarith
  linarith

/-- Combined Brun–Titchmarsh AP bound: number of primes in an AP is
bounded by the sifted sum plus z. -/
theorem primesBetween_AP_le (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (q a : ℕ)
    (hq : 1 ≤ q) (hz : 1 ≤ z) (hz1 : 1 < z) (hzq : 16 * (q : ℝ)^4 ≤ z) :
    (primesBetween_AP x (x + y) q a : ℝ) ≤
      4 * q * (y / q) / ((q.totient : ℝ) * Real.log z) +
      5 * z * (1 + Real.log z) ^ 3 + z := by
  have h1 := primesBetween_AP_le_siftedSum_add x y z hx hy q a hq hz
  have h2 := siftedSum_AP_le x y z hx hy q a hq hz hzq hz1
  linarith

/-- `piMod t q a` (from `Erdos696.lean`) is bounded by our `primesBetween_AP 1 t q a`. -/
theorem piMod_le_via_primesBetween_AP (t : ℝ) (q a : ℕ) (hq : 1 ≤ q) (ht : 1 ≤ t) :
    (Erdos696.piMod t q a : ℝ) ≤ primesBetween_AP 1 t q a := by
  classical
  unfold Erdos696.piMod primesBetween_AP
  have h_ceil_one : Nat.ceil (1 : ℝ) = 1 := by simp
  rw [h_ceil_one]
  -- Show the Set equals coe of the filter Finset.
  have h_set :
      {p : ℕ | p ≤ ⌊t⌋₊ ∧ p.Prime ∧ p % q = a % q} =
      ((Finset.Icc 1 ⌊t⌋₊).filter (fun n => n.Prime ∧ n % q = a % q) : Set ℕ) := by
    ext p
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_coe, Finset.mem_Icc,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨hp_le, hp_prime, hp_mod⟩
      exact ⟨⟨hp_prime.one_le, hp_le⟩, hp_prime, hp_mod⟩
    · rintro ⟨⟨_, hp_le⟩, hp_prime, hp_mod⟩
      exact ⟨hp_le, hp_prime, hp_mod⟩
  rw [h_set, Nat.card_coe_set_eq, Set.ncard_coe_finset]

set_option maxHeartbeats 1000000 in
/-- **Brun–Titchmarsh in arithmetic progressions** (strengthened-hypothesis form).

Discharges the original `brun_titchmarsh` in `Erdos696.lean` for the
range `t ≥ 256 · q^9`, which is the range used by every downstream consumer.
The constant `CBT = 30000` is chosen large enough to absorb both the leading
sieve constant and the explicit error term `5 z (1 + log z)^3 + z` at level
`z = √(t/q)`. -/
theorem brun_titchmarsh_large :
    ∃ CBT : ℝ, 0 < CBT ∧
      ∀ q : ℕ, 1 ≤ q →
        ∀ a : ℕ, Nat.Coprime a q →
          ∀ t : ℝ, (256 * (q : ℝ)^9 : ℝ) ≤ t →
            ((Erdos696.piMod t q a : ℝ)) ≤
              CBT * t / ((q.totient : ℝ) * Real.log (t / q)) := by
  refine ⟨30000, by norm_num, ?_⟩
  intro q hq a _hcop t ht
  -- Basic positivity.
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq_pos : (0 : ℝ) < q := by linarith
  have hq4_ge_1 : (1 : ℝ) ≤ (q : ℝ)^4 := one_le_pow₀ hq1
  have hq8_ge_1 : (1 : ℝ) ≤ (q : ℝ)^8 := one_le_pow₀ hq1
  have hq9_ge_1 : (1 : ℝ) ≤ (q : ℝ)^9 := one_le_pow₀ hq1
  have h256q9 : (256 : ℝ) ≤ 256 * (q : ℝ)^9 := by nlinarith [hq9_ge_1]
  have ht256 : (256 : ℝ) ≤ t := le_trans h256q9 ht
  have ht_pos : (0 : ℝ) < t := by linarith
  have ht_gt1 : (1 : ℝ) < t := by linarith
  have htq_pos : 0 < t / q := div_pos ht_pos hq_pos
  -- z := √(t/q).
  set z : ℝ := Real.sqrt (t / q) with hz_def
  have hz_pos : 0 < z := Real.sqrt_pos.mpr htq_pos
  -- t/q ≥ 256 q^8.
  have htq_lb : 256 * (q : ℝ)^8 ≤ t / q := by
    rw [le_div_iff₀ hq_pos]
    have : 256 * (q : ℝ)^8 * q = 256 * (q : ℝ)^9 := by ring
    linarith [this ▸ ht]
  have htq_ge_256 : (256 : ℝ) ≤ t / q := by
    have : (256 : ℝ) ≤ 256 * (q : ℝ)^8 := by nlinarith [hq8_ge_1]
    linarith
  -- 16 q^4 ≤ z.
  have hzq : 16 * (q : ℝ)^4 ≤ z := by
    have hsq : (16 * (q : ℝ)^4)^2 ≤ t / q := by
      have heq : (16 * (q : ℝ)^4)^2 = 256 * (q : ℝ)^8 := by ring
      linarith
    have h16q4_nn : (0 : ℝ) ≤ 16 * (q : ℝ)^4 := by positivity
    rw [hz_def, ← Real.sqrt_sq h16q4_nn]
    exact Real.sqrt_le_sqrt hsq
  -- z ≥ 16 ≥ 1.
  have hz_ge_16 : (16 : ℝ) ≤ z := by
    have : (16 : ℝ) ≤ 16 * (q : ℝ)^4 := by nlinarith [hq4_ge_1]
    linarith
  have hz_ge_1 : (1 : ℝ) ≤ z := by linarith
  have hz_gt_1 : (1 : ℝ) < z := by linarith
  -- log z = (1/2) log (t/q).
  have hlog_z : Real.log z = (1/2) * Real.log (t / q) := by
    rw [hz_def, Real.log_sqrt htq_pos.le]
    ring
  have hlog_tq_pos : 0 < Real.log (t / q) :=
    Real.log_pos (by linarith)
  have hlog_z_pos : 0 < Real.log z := by rw [hlog_z]; linarith
  -- Apply piMod_le_via_primesBetween_AP and primesBetween_AP_le with x=1, y=t-1.
  have hpiMod_le : (Erdos696.piMod t q a : ℝ) ≤ primesBetween_AP 1 t q a :=
    piMod_le_via_primesBetween_AP t q a hq (by linarith)
  have hy_pos : (0 : ℝ) < t - 1 := by linarith
  have h_xy : (1 : ℝ) + (t - 1) = t := by ring
  have hpB : ((primesBetween_AP 1 ((1 : ℝ) + (t - 1)) q a : ℕ) : ℝ) ≤
      4 * (q : ℝ) * ((t - 1) / (q : ℝ)) / ((q.totient : ℝ) * Real.log z) +
        5 * z * (1 + Real.log z)^3 + z :=
    primesBetween_AP_le 1 (t - 1) z (by norm_num) hy_pos q a hq hz_ge_1 hz_gt_1 hzq
  rw [h_xy] at hpB
  -- φ(q) facts.
  have hφ_pos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hq
  have hφ_le_q : (q.totient : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.totient_le q
  -- u = t/q.
  set u : ℝ := t / q with hu_def
  have hu_pos : 0 < u := htq_pos
  have hu_ge_256 : 256 ≤ u := htq_ge_256
  have hu_gt_1 : (1 : ℝ) < u := by linarith
  have hlog_u_pos : 0 < Real.log u := Real.log_pos hu_gt_1
  have h_sqrt_u_eq : z = Real.sqrt u := by rw [hz_def]
  -- log u ≥ log 256 > 5 (since e^5 < 256).
  have hlog256_ge : (5 : ℝ) ≤ Real.log 256 := by
    have he5_le : Real.exp 5 ≤ 256 := by
      have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have h5 : Real.exp 5 = Real.exp 1 ^ 5 := by
        rw [← Real.exp_nat_mul]; ring_nf
      rw [h5]
      have h2 : Real.exp 1 ^ 5 ≤ 2.7182818286 ^ 5 := by
        apply pow_le_pow_left₀ (Real.exp_pos 1).le h1.le
      have h3 : (2.7182818286 : ℝ) ^ 5 ≤ 256 := by norm_num
      linarith
    have := Real.log_le_log (Real.exp_pos 5) he5_le
    rwa [Real.log_exp] at this
  have hlog_u_ge_5 : (5 : ℝ) ≤ Real.log u :=
    le_trans hlog256_ge (Real.log_le_log (by norm_num) hu_ge_256)
  -- (1 + (1/2) log u) ≤ log u  ⇐  (1/2) log u ≥ 1  ⇐  log u ≥ 2.
  have h1pluslog_le : 1 + (1/2) * Real.log u ≤ Real.log u := by linarith
  -- (1 + log z)^3 ≤ (log u)^3.
  have h_pow_le : (1 + Real.log z)^3 ≤ (Real.log u)^3 := by
    rw [hlog_z]
    have h_nn : 0 ≤ 1 + (1/2) * Real.log u := by linarith
    exact pow_le_pow_left₀ h_nn h1pluslog_le 3
  have hlog_u_ge_1 : (1 : ℝ) ≤ Real.log u := by linarith
  have hlog_u_pow3_ge_1 : (1 : ℝ) ≤ (Real.log u)^3 := by
    calc (1 : ℝ) = 1^3 := by ring
      _ ≤ (Real.log u)^3 := pow_le_pow_left₀ (by norm_num) hlog_u_ge_1 3
  -- Combine main + error and bound by 30000 · t / (φ(q) log u).
  -- Strategy: show entire RHS bound ≤ 30000 · u / log u (using φ(q) ≤ q, t = qu).
  -- Main term: 4q · (t-1)/q / (φ(q) (1/2) log u) ≤ 8 u q / (φ(q) log u).
  --   In particular ≤ 8 q² / (φ(q) log u) · u / q ≤ 8 u q / (φ(q) log u),
  --   and bounding by t/(φ(q) log(t/q)) factor: 8t/(φ(q) log u).
  -- Error term: 5 z (1+log z)^3 + z ≤ 6 √u (log u)^3.
  -- Goal: 8t/(φ(q) log u) + 6 √u (log u)^3 ≤ 30000 t/(φ(q) log u).
  -- I.e.,  6 √u (log u)^3 ≤ 29992 t/(φ(q) log u).
  -- Using φ(q) ≤ q and t = qu: t/(φ(q) log u) ≥ qu/(q log u) = u/log u.
  -- So need 6 √u (log u)^3 ≤ 29992 · u/log u, i.e., 6 (log u)^4 / √u ≤ 29992,
  -- i.e., (log u)^4 / √u ≤ 4999.
  -- Bound: log u ≤ 8 u^{1/8}, so (log u)^4 ≤ 4096 √u, so (log u)^4/√u ≤ 4096.
  have h_log_le : Real.log u ≤ u^((1 : ℝ)/8) / ((1 : ℝ)/8) :=
    Real.log_le_rpow_div hu_pos.le (by norm_num)
  have h_log_le' : Real.log u ≤ 8 * u^((1 : ℝ)/8) := by
    have heq : u^((1 : ℝ)/8) / ((1 : ℝ)/8) = 8 * u^((1 : ℝ)/8) := by
      field_simp
    linarith [heq ▸ h_log_le]
  have h_log_nn : 0 ≤ Real.log u := by linarith
  have h_pow4_le : (Real.log u)^4 ≤ (8 * u^((1 : ℝ)/8))^4 :=
    pow_le_pow_left₀ h_log_nn h_log_le' 4
  have hu18_nn : 0 ≤ u^((1 : ℝ)/8) := (Real.rpow_pos_of_pos hu_pos _).le
  have h_pow4_simp : (8 * u^((1 : ℝ)/8))^4 = 4096 * u^((1 : ℝ)/2) := by
    rw [mul_pow]
    have h1 : (8 : ℝ)^4 = 4096 := by norm_num
    have h2 : (u^((1 : ℝ)/8))^4 = u^((1 : ℝ)/2) := by
      rw [← Real.rpow_natCast (u^((1 : ℝ)/8)) 4, ← Real.rpow_mul hu_pos.le]
      norm_num
    rw [h1, h2]
  have h_sqrt_eq : Real.sqrt u = u^((1 : ℝ)/2) := Real.sqrt_eq_rpow u
  have hu12_pos : 0 < u^((1 : ℝ)/2) := Real.rpow_pos_of_pos hu_pos _
  have h_logu4_le : (Real.log u)^4 ≤ 4096 * Real.sqrt u := by
    rw [h_sqrt_eq]
    linarith [h_pow4_le, h_pow4_simp]
  -- φ(q) ≥ 1.
  have hφ_ge_1 : (1 : ℝ) ≤ (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hq
  -- t = q · u.
  have ht_eq_qu : t = (q : ℝ) * u := by
    rw [hu_def]; field_simp
  -- piMod ≤ ... ≤ 30000 t/(φ(q) log(t/q)).
  -- Step 1: piMod ≤ RHS of hpB.
  have h_step1 : (Erdos696.piMod t q a : ℝ) ≤
      4 * (q : ℝ) * ((t - 1) / (q : ℝ)) / ((q.totient : ℝ) * Real.log z) +
        5 * z * (1 + Real.log z)^3 + z :=
    le_trans hpiMod_le hpB
  -- Step 2: bound the entire RHS by 30000 t/(φ(q) log(t/q)).
  have h_target : 4 * (q : ℝ) * ((t - 1) / (q : ℝ)) / ((q.totient : ℝ) * Real.log z) +
        5 * z * (1 + Real.log z)^3 + z ≤
      30000 * t / ((q.totient : ℝ) * Real.log (t / q)) := by
    -- Rewrite main term using log z = (1/2) log u and simplify.
    have h_simp_main : 4 * (q : ℝ) * ((t - 1) / (q : ℝ)) = 4 * (t - 1) := by
      field_simp
    rw [h_simp_main, hlog_z, ← hu_def]
    rw [show (q.totient : ℝ) * ((1 / 2) * Real.log u) =
        (1 / 2) * ((q.totient : ℝ) * Real.log u) from by ring]
    -- LHS = 4(t-1) / ((1/2) (φ(q) log u)) + 5z(1+log z)^3 + z
    --     = 8(t-1)/(φ(q) log u) + 5z(1+log z)^3 + z.
    have h_denom_pos : 0 < (q.totient : ℝ) * Real.log u := by positivity
    have h_main_simp : 4 * (t - 1) / ((1/2) * ((q.totient : ℝ) * Real.log u)) =
        8 * (t - 1) / ((q.totient : ℝ) * Real.log u) := by
      rw [show ((1 : ℝ)/2) * ((q.totient : ℝ) * Real.log u) =
        ((q.totient : ℝ) * Real.log u) / 2 from by ring]
      rw [div_div_eq_mul_div]
      congr 1
      ring
    rw [h_main_simp]
    -- Error bound: 5z(1+log z)^3 + z ≤ 6 √u (log u)^3.
    have h_err : 5 * z * (1 + Real.log z)^3 + z ≤ 6 * Real.sqrt u * (Real.log u)^3 := by
      rw [h_sqrt_u_eq]
      nlinarith [h_pow_le, hz_pos.le, hlog_u_pow3_ge_1,
        Real.sqrt_pos.mpr hu_pos, h_sqrt_u_eq]
    -- Combined: 8(t-1)/(φ(q) log u) + 5z(1+log z)^3 + z ≤
    --          8 t/(φ(q) log u) + 6 √u (log u)^3.
    have h_main_le_t : 8 * (t - 1) / ((q.totient : ℝ) * Real.log u) ≤
        8 * t / ((q.totient : ℝ) * Real.log u) := by
      apply div_le_div_of_nonneg_right _ h_denom_pos.le
      linarith
    -- Bound 6 √u (log u)^3 ≤ (29992 · t)/(φ(q) log u) using log u^4 ≤ 4096 √u.
    -- 6 √u (log u)^3 = 6 √u (log u)^3 · (log u)/(log u) = 6 (log u)^4 / log u · √u/√u · √u
    --                                                  ... let me just do it.
    -- We have (log u)^4 ≤ 4096 √u, so (log u)^4 ≤ 4096 √u.
    -- Then 6 √u (log u)^3 · log u ≤ 6 √u · 4096 √u = 24576 u.
    -- So 6 √u (log u)^3 ≤ 24576 u / log u ≤ 24576 q u / (φ(q) log u) (since φ(q) ≤ q)
    --                                     = 24576 t / (φ(q) log u).
    have h_err_le : 6 * Real.sqrt u * (Real.log u)^3 ≤
        24576 * t / ((q.totient : ℝ) * Real.log u) := by
      have hsqrt_pos : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu_pos
      -- Multiply both sides of (log u)^4 ≤ 4096 √u by 6 √u / log u.
      -- I.e., 6 √u (log u)^3 = 6 √u (log u)^4 / log u ≤ 6 √u · 4096 √u / log u
      --                     = 6 · 4096 · u / log u = 24576 u / log u.
      have h_step : 6 * Real.sqrt u * (Real.log u)^3 ≤ 24576 * u / Real.log u := by
        rw [le_div_iff₀ hlog_u_pos]
        have h_lhs_eq : 6 * Real.sqrt u * (Real.log u)^3 * Real.log u =
            6 * Real.sqrt u * (Real.log u)^4 := by ring
        rw [h_lhs_eq]
        have hmul : 6 * Real.sqrt u * (Real.log u)^4 ≤
            6 * Real.sqrt u * (4096 * Real.sqrt u) := by
          apply mul_le_mul_of_nonneg_left h_logu4_le
          positivity
        have h_sq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu_pos.le
        nlinarith [hmul, h_sq, hu_pos.le]
      have h2 : 24576 * u / Real.log u ≤ 24576 * t / ((q.totient : ℝ) * Real.log u) := by
        rw [ht_eq_qu]
        rw [div_le_div_iff₀ hlog_u_pos h_denom_pos]
        have h1 : 24576 * u * ((q.totient : ℝ) * Real.log u) =
            24576 * u * Real.log u * (q.totient : ℝ) := by ring
        have h2 : 24576 * ((q : ℝ) * u) * Real.log u =
            24576 * u * Real.log u * (q : ℝ) := by ring
        rw [h1, h2]
        have h_factor_nn : 0 ≤ 24576 * u * Real.log u := by positivity
        exact mul_le_mul_of_nonneg_left hφ_le_q h_factor_nn
      linarith
    -- Combine.
    have h_combine : 8 * (t - 1) / ((q.totient : ℝ) * Real.log u) +
        5 * z * (1 + Real.log z)^3 + z ≤
        (8 + 24576) * t / ((q.totient : ℝ) * Real.log u) := by
      have h_sum :
          8 * t / ((q.totient : ℝ) * Real.log u) +
            24576 * t / ((q.totient : ℝ) * Real.log u) =
          (8 + 24576) * t / ((q.totient : ℝ) * Real.log u) := by
        simp only [div_eq_mul_inv]
        ring
      linarith [h_main_le_t, h_err, h_err_le, h_sum]
    have h_final : (8 + 24576 : ℝ) * t / ((q.totient : ℝ) * Real.log u) ≤
        30000 * t / ((q.totient : ℝ) * Real.log u) := by
      apply div_le_div_of_nonneg_right _ h_denom_pos.le
      nlinarith [ht_pos.le]
    -- Rewrite h_combine in terms of (1 + 1/2 * log u)^3 to match the goal.
    rw [hlog_z] at h_combine
    linarith [h_combine, h_final]
  exact le_trans h_step1 h_target

end Erdos696BT
