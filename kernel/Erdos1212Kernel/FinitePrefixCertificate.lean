import Erdos1212Kernel.PathExtraction

namespace Erdos1212Kernel

inductive GridDirection where
  | east
  | west
  | north
  | south
deriving DecidableEq, Fintype

def gridStep (p : LatticePoint) : GridDirection -> LatticePoint
  | .east => ⟨p.x + 1, p.y⟩
  | .west => ⟨p.x - 1, p.y⟩
  | .north => ⟨p.x, p.y + 1⟩
  | .south => ⟨p.x, p.y - 1⟩

theorem adjacent_gridStep (p : LatticePoint) (direction : GridDirection)
    (hp : SafePoint p) : Adjacent p (gridStep p direction) := by
  rcases hp with ⟨hx, hy, _⟩
  cases direction <;> simp [gridStep, Adjacent] <;> omega

def codedPoint (start : LatticePoint) {n : Nat}
    (code : Fin n -> GridDirection) : Nat -> LatticePoint
  | 0 => start
  | t + 1 =>
      if h : t < n then
        gridStep (codedPoint start code t) (code ⟨t, h⟩)
      else
        codedPoint start code t

theorem codedPoint_succ (start : LatticePoint) {n : Nat}
    (code : Fin n -> GridDirection) {t : Nat} (ht : t < n) :
    codedPoint start code (t + 1) =
      gridStep (codedPoint start code t) (code ⟨t, ht⟩) := by
  simp [codedPoint, ht]

def restrictCode {i j : Nat} (hij : i <= j)
    (code : Fin j -> GridDirection) : Fin i -> GridDirection :=
  fun t => code ⟨t.val, lt_of_lt_of_le t.isLt hij⟩

theorem codedPoint_restrict (start : LatticePoint) {i j : Nat}
    (hij : i <= j) (code : Fin j -> GridDirection) (t : Nat)
    (ht : t <= i) :
    codedPoint start (restrictCode hij code) t = codedPoint start code t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hti : t < i := by omega
      have htj : t < j := lt_of_lt_of_le hti hij
      rw [codedPoint_succ _ _ hti, codedPoint_succ _ _ htj, ih (by omega)]
      rfl

theorem codedPoint_x_le (start : LatticePoint) {n : Nat}
    (code : Fin n -> GridDirection) (t : Nat) :
    (codedPoint start code t).x <= start.x + t := by
  induction t with
  | zero => simp [codedPoint]
  | succ t ih =>
      by_cases ht : t < n
      · rw [codedPoint_succ start code ht]
        cases code ⟨t, ht⟩ <;> simp [gridStep] <;> omega
      · simp [codedPoint, ht]
        omega

theorem codedPoint_y_le (start : LatticePoint) {n : Nat}
    (code : Fin n -> GridDirection) (t : Nat) :
    (codedPoint start code t).y <= start.y + t := by
  induction t with
  | zero => simp [codedPoint]
  | succ t ih =>
      by_cases ht : t < n
      · rw [codedPoint_succ start code ht]
        cases code ⟨t, ht⟩ <;> simp [gridStep] <;> omega
      · simp [codedPoint, ht]
        omega

def SimpleSafeCode (start : LatticePoint) {n : Nat}
    (code : Fin n -> GridDirection) : Prop :=
  (forall t, t <= n -> SafePoint (codedPoint start code t)) /\
  (forall s t, s <= n -> t <= n -> s ≠ t ->
    codedPoint start code s ≠ codedPoint start code t)

theorem simpleSafeCode_restrict (start : LatticePoint) {i j : Nat}
    (hij : i <= j) (code : Fin j -> GridDirection)
    (hcode : SimpleSafeCode start code) :
    SimpleSafeCode start (restrictCode hij code) := by
  constructor
  · intro t ht
    rw [codedPoint_restrict start hij code t ht]
    exact hcode.1 t (le_trans ht hij)
  · intro s t hs ht hst heq
    apply hcode.2 s t (le_trans hs hij) (le_trans ht hij) hst
    rw [← codedPoint_restrict start hij code s hs,
      ← codedPoint_restrict start hij code t ht]
    exact heq

def SimpleSafePrefix (start : LatticePoint) (n : Nat) :=
  {code : Fin n -> GridDirection // SimpleSafeCode start code}

def simpleSafePrefixProject (start : LatticePoint) {i j : Nat}
    (hij : i <= j) (pfx : SimpleSafePrefix start j) :
    SimpleSafePrefix start i :=
  ⟨restrictCode hij pfx.val,
    simpleSafeCode_restrict start hij pfx.val pfx.property⟩

theorem simpleSafePrefixProject_refl (start : LatticePoint) {i : Nat}
    (pfx : SimpleSafePrefix start i) :
    simpleSafePrefixProject start (Nat.le_refl i) pfx = pfx := by
  apply Subtype.ext
  funext t
  rfl

theorem simpleSafePrefixProject_trans (start : LatticePoint)
    {i j k : Nat} (hij : i <= j) (hjk : j <= k)
    (pfx : SimpleSafePrefix start k) :
    simpleSafePrefixProject start hij
        (simpleSafePrefixProject start hjk pfx) =
      simpleSafePrefixProject start (hij.trans hjk) pfx := by
  apply Subtype.ext
  funext t
  rfl

theorem fullClose_of_arbitrarily_long_simple_safe_codes
    (start : LatticePoint)
    (arbitrarilyLong : forall n, exists code : Fin n -> GridDirection,
      SimpleSafeCode start code) :
    Erdos1212FullClose := by
  classical
  let Prefix : Nat -> Type := SimpleSafePrefix start
  letI prefixNonempty : forall n, Nonempty (Prefix n) := fun n =>
    ⟨⟨(arbitrarilyLong n).choose, (arbitrarilyLong n).choose_spec⟩⟩
  letI prefixFinite : forall n, Finite (Prefix n) := fun n =>
    Finite.of_injective Subtype.val Subtype.val_injective
  apply fullClose_of_finite_simple_prefix_system
    (Prefix := Prefix)
    (project := fun hij pfx => simpleSafePrefixProject start hij pfx)
    (point := fun _ pfx t => codedPoint start pfx.val t)
  · intro i pfx
    exact simpleSafePrefixProject_refl start pfx
  · intro i j k hij hjk pfx
    exact simpleSafePrefixProject_trans start hij hjk pfx
  · intro i pfx
    exact Set.toFinite _
  · intro i j hij pfx t ht
    exact codedPoint_restrict start hij pfx.val t ht
  · intro n pfx t ht
    exact pfx.property.1 t ht
  · intro n pfx t ht
    rw [codedPoint_succ start pfx.val ht]
    exact adjacent_gridStep (codedPoint start pfx.val t) (pfx.val ⟨t, ht⟩)
      (pfx.property.1 t (Nat.le_of_lt ht))
  · intro n pfx s t hs ht hst
    exact pfx.property.2 s t hs ht hst

theorem fullClose_of_arbitrarily_far_simple_safe_codes
    (start : LatticePoint)
    (arbitrarilyFar : forall bound, exists n,
      exists code : Fin n -> GridDirection,
        SimpleSafeCode start code /\
        (bound <= (codedPoint start code n).x \/
          bound <= (codedPoint start code n).y)) :
    Erdos1212FullClose := by
  apply fullClose_of_arbitrarily_long_simple_safe_codes start
  intro depth
  obtain ⟨n, code, hcode, hfar⟩ :=
    arbitrarilyFar (max start.x start.y + depth)
  have hdepth : depth <= n := by
    rcases hfar with hx | hy
    · have hupper := codedPoint_x_le start code n
      have hstart : start.x <= max start.x start.y := le_max_left _ _
      omega
    · have hupper := codedPoint_y_le start code n
      have hstart : start.y <= max start.x start.y := le_max_right _ _
      omega
  exact ⟨restrictCode hdepth code,
    simpleSafeCode_restrict start hdepth code hcode⟩

end Erdos1212Kernel
