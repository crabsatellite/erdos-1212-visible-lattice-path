import Erdos1212Kernel.IwaniecStoppedWord

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 650000

theorem iwaniecCubicStoppedWord_ne_nil {offset : Nat} {level : Real} {word : List Nat}
    (hstop : iwaniecCubicStoppedWord offset level word) : word ≠ [] := by
  intro h
  subst word
  exact (iwaniecCubicStoppedWord_nil offset level) hstop

theorem iwaniecStoppedWordWeight_eq_last {offset : Nat} {level : Real} {word : List Nat}
    (hstop : iwaniecCubicStoppedWord offset level word) :
    iwaniecStoppedWordWeight offset level word =
      iwaniecPaperR (word.getLast (iwaniecCubicStoppedWord_ne_nil hstop) : Real) / (word.prod : Real) := by
  induction word generalizing offset level with
  | nil => exact ((iwaniecCubicStoppedWord_nil offset level) hstop).elim
  | cons p tail ih =>
      cases tail with
      | nil =>
          have hc := (iwaniecCubicStoppedWord_singleton offset level p).mp hstop
          simp only [iwaniecStoppedWordWeight, if_neg hc, if_true, List.getLast_singleton,
            List.prod_cons, List.prod_nil, Nat.mul_one]
          ring
      | cons q rest =>
          have hc := (iwaniecCubicStoppedWord_cons_cons offset level p q rest).mp hstop
          rw [iwaniecStoppedWordWeight, if_pos hc.1, ih hc.2]
          simp only [List.getLast_cons_cons, List.prod_cons, Nat.cast_mul]
          ring

/-- The full stopped product, not just an admissible prefix. The
two source parities are proved together through their literal quotient. -/
theorem iwaniecCubicStoppedWord_product_bounds (word : List Nat)
    (hpos : ∀ p ∈ word, 0 < p) (horder : word.Pairwise (fun p q => q ≤ p))
    (level : Real) (hy : 1 < level) :
    (iwaniecCubicStoppedWord 0 level word → (∀ p ∈ word, (p : Real) ^ 2 < level) → (word.prod : Real) < level) ∧
    (iwaniecCubicStoppedWord 1 level word → (∀ p ∈ word, (p : Real) ^ 3 < level) → (word.prod : Real) < level) := by
  induction word generalizing level with
  | nil => simp
  | cons p tail ih =>
      have hp : 0 < p := hpos p (by simp)
      have hp0 : (0 : Real) < p := by exact_mod_cast hp
      have hp1 : (1 : Real) ≤ p := by exact_mod_cast hp
      have htpos : ∀ q ∈ tail, 0 < q := fun q hq => hpos q (by simp [hq])
      have htorder := (List.pairwise_cons.mp horder).2
      have hhead := (List.pairwise_cons.mp horder).1
      constructor
      · intro hstop hsquare
        cases tail with
        | nil =>
            have hc := (iwaniecCubicStoppedWord_singleton 0 level p).mp hstop
            exact (hc (Or.inl ⟨0, rfl⟩)).elim
        | cons q rest =>
            have hchild := ((iwaniecCubicStoppedWord_cons_cons 0 level p q rest).mp hstop).2
            have hpSq := hsquare p (by simp)
            have hpLeSq : (p : Real) ≤ (p : Real) ^ 2 := by nlinarith
            have hychild : 1 < level / p := (one_lt_div hp0).mpr (hpLeSq.trans_lt hpSq)
            cases rest with
            | nil =>
                have hqp : (q : Real) ≤ p := by exact_mod_cast hhead q (by simp)
                have hmul := mul_le_mul_of_nonneg_left hqp hp0.le
                simp only [List.prod_cons, List.prod_nil, Nat.mul_one, Nat.cast_mul]
                nlinarith only [hmul, hpSq]
            | cons r rest =>
                have hc := (iwaniecCubicStoppedWord_cons_cons 1 (level / p) q r rest).mp hchild
                have hqcube : (q : Real) ^ 3 < level / p := by simpa using hc.1
                have htailCube : ∀ a ∈ q :: r :: rest, (a : Real) ^ 3 < level / p := by
                  intro a ha
                  have haq : a ≤ q := by
                    rcases List.mem_cons.mp ha with rfl | ha
                    · exact le_rfl
                    · exact (List.pairwise_cons.mp htorder).1 a ha
                  exact (pow_le_pow_left₀ (Nat.cast_nonneg a : (0 : Real) ≤ a) (by exact_mod_cast haq) 3).trans_lt hqcube
                have hprod := (ih htpos htorder (level / p) hychild).2 hchild htailCube
                have hmul := (lt_div_iff₀ hp0).mp hprod
                simpa only [List.prod_cons, Nat.cast_mul, mul_comm] using hmul
      · intro hstop hcubes
        cases tail with
        | nil =>
            have hc := (iwaniecCubicStoppedWord_singleton 1 level p).mp hstop
            exact (hc (Or.inr (hcubes p (by simp)))).elim
        | cons q rest =>
            have hc := (iwaniecCubicStoppedWord_cons_cons 1 level p q rest).mp hstop
            have hpCube := hcubes p (by simp)
            have hpSqCube : (p : Real) ^ 2 ≤ (p : Real) ^ 3 := by
              nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (sq_nonneg (p : Real))]
            have hpLeSq : (p : Real) ≤ (p : Real) ^ 2 := by nlinarith
            have hychild : 1 < level / p := (one_lt_div hp0).mpr (hpLeSq.trans_lt (hpSqCube.trans_lt hpCube))
            have hpChild : (p : Real) ^ 2 < level / p := by
              apply (lt_div_iff₀ hp0).mpr
              nlinarith only [hpCube]
            have htailSq : ∀ a ∈ q :: rest, (a : Real) ^ 2 < level / p := by
              intro a ha
              have hap : (a : Real) ≤ p := by exact_mod_cast hhead a ha
              exact (pow_le_pow_left₀ (Nat.cast_nonneg a : (0 : Real) ≤ a) hap 2).trans_lt hpChild
            have hchild : iwaniecCubicStoppedWord 0 (level / p) (q :: rest) :=
              (iwaniecCubicStoppedWord_add_two 0 (level / p) (q :: rest)).mp hc.2
            have hprod := (ih htpos htorder (level / p) hychild).1 hchild htailSq
            have hmul := (lt_div_iff₀ hp0).mp hprod
            simpa only [List.prod_cons, Nat.cast_mul, mul_comm] using hmul

end

end Erdos1212Kernel
