/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.Blocks
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Defs
public import LeanPool.BeyondBethe.Complexitylib.Encoding.Pairing
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Cobham's algebra — the working toolkit

Derived members of `Complexity.Cobham`: the operations a Turing-machine
interpreter written inside the algebra needs. Each is a single limited recursion
on notation, or a finite composition of such.

Two of these carry the weight. `dispatch` shows that branching is free: the step
functions of `recNotation` are already selected by the bit being peeled, so a
one-step recursion on `v 0` *is* an if-then-else on its leading bit.
`dropPrefix` shows how to move an argument that changes along a recursion —
`recNotation` fixes its parameters, so the changing value has to live in the
recursion's *value*, and iterating `tail` there gives `drop`. With `drop` in
hand, `takePrefix` reads off successive bits, and fixed-width pairing with
projections follows.
-/


@[expose] public section

namespace Complexity

namespace Cobham

/-- The class respects pointwise equality of functions. Useful because the constructors
of `Cobham` produce syntactically specific lambda terms. -/
theorem of_eq {n : ℕ} {f g : (Fin n → List Bool) → List Bool} (hf : Cobham f)
    (h : ∀ v, f v = g v) : Cobham g :=
  (funext h : f = g) ▸ hf

/-- Every constant function is in the class: build the constant string bit by bit from
`empty` and the successors. -/
theorem const {n : ℕ} (s : List Bool) : Cobham fun _ : Fin n → List Bool => s := by
  induction s with
  | nil => exact .empty
  | cons b s ih => exact (Cobham.comp (.bit b) fun _ : Fin 1 => ih).of_eq fun v => rfl

/-- Composition with two inner functions, packaged for readability: the
constructor's `Fin`-indexed family is awkward to supply when the two components
differ. -/
theorem comp₂ {n : ℕ} {f : (Fin 2 → List Bool) → List Bool}
    {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (hf : Cobham f) (h₀ : Cobham g₀) (h₁ : Cobham g₁) :
    Cobham fun v : Fin n → List Bool => f ![g₀ v, g₁ v] := by
  refine (Cobham.comp hf (gs := ![g₀, g₁]) ?_).of_eq fun v => ?_
  · intro i; fin_cases i <;> assumption
  · congr 1
    funext i
    fin_cases i <;> rfl

/-- Composition with three inner functions. -/
theorem comp₃ {n : ℕ} {f : (Fin 3 → List Bool) → List Bool}
    {g₀ g₁ g₂ : (Fin n → List Bool) → List Bool}
    (hf : Cobham f) (h₀ : Cobham g₀) (h₁ : Cobham g₁) (h₂ : Cobham g₂) :
    Cobham fun v : Fin n → List Bool => f ![g₀ v, g₁ v, g₂ v] := by
  refine (Cobham.comp hf (gs := ![g₀, g₁, g₂]) ?_).of_eq fun v => ?_
  · intro i; fin_cases i <;> assumption
  · congr 1
    funext i
    fin_cases i <;> rfl

/-- Concatenation is in the class, by limited recursion on notation on the first
argument with bound `smash (true :: x) (true :: y)`. -/
theorem append : Cobham fun v : Fin 2 → List Bool => v 0 ++ v 1 := by
  -- Recursion on notation computing `x ++ y`: base `y`, step `b :: ·` on the
  -- recursive value.
  have hrec : ∀ (x : List Bool) (v : Fin 1 → List Bool),
      recNotation (fun v : Fin 1 → List Bool => v 0)
        (fun w : Fin 3 → List Bool => false :: w 1)
        (fun w : Fin 3 → List Bool => true :: w 1) x v = x ++ v 0 := by
    intro x v
    induction x with
    | nil => rfl
    | cons b x ih => cases b <;> simp [ih]
  -- The bit-prepending step functions are in the class.
  have hstep : ∀ b : Bool, Cobham fun w : Fin 3 → List Bool => b :: w 1 := fun b =>
    (Cobham.comp (.bit b) fun _ : Fin 1 => .proj 1).of_eq fun v => rfl
  -- The length bound `smash (true :: x) (true :: y)` is in the class.
  have hj : Cobham fun w : Fin 2 → List Bool =>
      Complexity.smash (true :: w 0) (true :: w 1) :=
    (Cobham.comp .smash fun i : Fin 2 =>
      (Cobham.comp (.bit true) fun _ : Fin 1 => .proj i).of_eq fun v => rfl).of_eq
        fun v => rfl
  refine (Cobham.boundedRec (.proj 0) (hstep false) (hstep true) hj ?_).of_eq fun v => ?_
  · intro x v
    rw [hrec]
    have h1 : (Fin.cons x v : Fin 2 → List Bool) 1 = v 0 := rfl
    have hexp : (x.length + 1) * ((v 0).length + 1) =
        x.length * (v 0).length + x.length + (v 0).length + 1 := by ring
    simp only [Fin.cons_zero, h1, smash_length, List.length_append, List.length_cons]
    omega
  · rw [hrec]
    rfl

/-- Concatenation of two members of the class is a member of the class. -/
theorem appendFn {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) :
    Cobham fun v : Fin n → List Bool => g₀ v ++ g₁ v :=
  (comp₂ append h₀ h₁).of_eq fun v => by simp

/-- The self-delimiting pairing `pair x y = delimit x ++ y` is in the class, by
limited recursion on notation on `x`: each peeled bit is doubled onto the
recursive value, and the base case emits the separator `01` followed by `y`. The
bound is exact — `|pair x y| = |x ++ x| + |y ++ [0,1]|`. -/
theorem pairing : Cobham fun v : Fin 2 → List Bool => pair (v 0) (v 1) := by
  have hrec : ∀ (x : List Bool) (v : Fin 1 → List Bool),
      recNotation (fun u : Fin 1 → List Bool => false :: true :: u 0)
        (fun w : Fin 3 → List Bool => false :: false :: w 1)
        (fun w : Fin 3 → List Bool => true :: true :: w 1) x v
        = pair x (v 0) := by
    intro x v
    induction x with
    | nil => rfl
    | cons b x ih => cases b <;> simp [pair_cons_eq, ih]
  have hg : Cobham fun u : Fin 1 → List Bool => false :: true :: u 0 :=
    (Cobham.comp (.bit false) fun _ : Fin 1 =>
      (Cobham.comp (.bit true) fun _ : Fin 1 => .proj 0).of_eq fun v => rfl).of_eq
        fun v => rfl
  have hstep : ∀ b : Bool, Cobham fun w : Fin 3 → List Bool => b :: b :: w 1 := fun b =>
    (Cobham.comp (.bit b) fun _ : Fin 1 =>
      (Cobham.comp (.bit b) fun _ : Fin 1 => .proj 1).of_eq fun v => rfl).of_eq
        fun v => rfl
  have hj : Cobham fun w : Fin 2 → List Bool =>
      (w 0 ++ w 0) ++ (w 1 ++ [false, true]) :=
    appendFn (appendFn (.proj 0) (.proj 0))
      (appendFn (.proj 1) (Cobham.const [false, true]))
  refine (Cobham.boundedRec hg (hstep false) (hstep true) hj ?_).of_eq fun v => ?_
  · intro x v
    rw [hrec]
    have h0 : (Fin.cons x v : Fin 2 → List Bool) 0 = x := rfl
    have h1 : (Fin.cons x v : Fin 2 → List Bool) 1 = v 0 := rfl
    simp only [h0, h1, pair_length, List.length_append, List.length_cons,
      List.length_nil]
    omega
  · rw [hrec]
    rfl

/-- Dropping the leading bit is in the class, by limited recursion on notation:
on `b :: x` both step functions return the peeled tail `x`, and the argument
itself bounds the result. -/
theorem tail : Cobham fun v : Fin 1 → List Bool => (v 0).tail := by
  have hrec : ∀ (x : List Bool) (v : Fin 0 → List Bool),
      recNotation (fun _ : Fin 0 → List Bool => ([] : List Bool))
        (fun w : Fin 2 → List Bool => w 0) (fun w : Fin 2 → List Bool => w 0) x v
        = x.tail := by
    intro x v
    cases x with
    | nil => rfl
    | cons b x => cases b <;> rfl
  refine (Cobham.boundedRec .empty (.proj 0) (.proj 0) (.proj 0) ?_).of_eq fun v => ?_
  · intro x v
    rw [hrec, Fin.cons_zero]
    cases x <;> simp
  · rw [hrec]

/-- **Bit dispatch is in the class.** `caseBit (v 0) (v 1) (v 2)` is a single
limited recursion on notation over `v 0`: the recursion's own bit-selected step
functions do the branching, projecting out `v 1` or `v 2`, and the concatenation
of the two branches bounds the result. -/
theorem dispatch : Cobham fun v : Fin 3 → List Bool =>
    caseBit (v 0) (v 1) (v 2) := by
  -- On `b :: x` the step argument is `⟨x, rec, v 1, v 2⟩`, so the branches are
  -- projections 3 (bit `0`) and 2 (bit `1`).
  have hrec : ∀ (x : List Bool) (v : Fin 2 → List Bool),
      recNotation (fun _ : Fin 2 → List Bool => ([] : List Bool))
        (fun w : Fin 4 → List Bool => w 3) (fun w : Fin 4 → List Bool => w 2) x v
        = caseBit x (v 0) (v 1) := by
    intro x v
    cases x with
    | nil => rfl
    | cons b x => cases b <;> rfl
  -- The bound: the two branches concatenated.
  have hj : Cobham fun w : Fin 3 → List Bool => w 1 ++ w 2 :=
    (Cobham.comp Cobham.append fun i : Fin 2 => Cobham.proj i.succ).of_eq fun v => rfl
  refine (Cobham.boundedRec .empty (.proj 3) (.proj 2) hj ?_).of_eq fun v => ?_
  · intro x v
    rw [hrec]
    exact caseBit_length_le _ _ _
  · rw [hrec]
    rfl

/-- **Dropping a prefix of a given length is in the class.** `v 1` is advanced by
one `tail` per bit of the ruler `v 0`: the recursion applies `tail` to its own
recursive value, so the changing argument lives in the recursion's value rather
than in its parameters — which is what makes it expressible at all. -/
theorem dropPrefix :
    Cobham fun v : Fin 2 → List Bool => (v 1).drop (v 0).length := by
  have hrec : ∀ (r : List Bool) (u : Fin 1 → List Bool),
      recNotation (fun u : Fin 1 → List Bool => u 0)
        (fun w : Fin 3 → List Bool => (w 1).tail)
        (fun w : Fin 3 → List Bool => (w 1).tail) r u
        = (u 0).drop r.length := by
    intro r u
    induction r with
    | nil => rfl
    | cons b r ih => cases b <;> simp [ih, List.tail_drop]
  have hstep : Cobham fun w : Fin 3 → List Bool => (w 1).tail :=
    (Cobham.comp Cobham.tail fun _ : Fin 1 => Cobham.proj 1).of_eq fun v => rfl
  refine (Cobham.boundedRec (.proj 0) hstep hstep (.proj 1) ?_).of_eq fun v => ?_
  · intro r u
    rw [hrec, show (Fin.cons r u : Fin 2 → List Bool) 1 = u 0 from rfl]
    simp
  · rw [hrec]
    rfl

/-- One more bit of a prefix is the prefix plus the first bit of what remains. -/
private theorem take_succ_eq (x : List Bool) (n : ℕ) :
    x.take (n + 1) = x.take n ++ (x.drop n).take 1 := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      cases x with
      | nil => simp
      | cons a x => simpa using ih x

/-- **Taking a prefix of a given length is in the class.** Each bit of the ruler
`v 0` appends one more bit of `v 1`, read off by dispatching on the head of what
is still undropped — so `dropPrefix` and `dispatch` together give `take`. -/
theorem takePrefix :
    Cobham fun v : Fin 2 → List Bool => (v 1).take (v 0).length := by
  have hbit : ∀ z : List Bool, caseBit z [true] [false] = z.take 1 := by
    intro z; cases z with
    | nil => rfl
    | cons b z => cases b <;> rfl
  have hrec : ∀ (r : List Bool) (u : Fin 1 → List Bool),
      recNotation (fun _ : Fin 1 → List Bool => ([] : List Bool))
        (fun w : Fin 3 → List Bool =>
          w 1 ++ caseBit ((w 2).drop (w 0).length) [true] [false])
        (fun w : Fin 3 → List Bool =>
          w 1 ++ caseBit ((w 2).drop (w 0).length) [true] [false]) r u
        = (u 0).take r.length := by
    intro r u
    induction r with
    | nil => rfl
    | cons b r ih =>
        cases b <;>
          · show (recNotation _ _ _ r u) ++ caseBit _ _ _ = _
            rw [ih, hbit]
            exact (take_succ_eq (u 0) r.length).symm
  -- The step: append the next bit of `u 0`, located by dropping `|r|` bits.
  have hdrop : Cobham fun w : Fin 3 → List Bool => (w 2).drop (w 0).length :=
    (comp₂ dropPrefix (.proj 0) (.proj 2)).of_eq fun v => by simp
  have hbitFn : Cobham fun w : Fin 3 → List Bool =>
      caseBit ((w 2).drop (w 0).length) [true] [false] :=
    (comp₃ dispatch hdrop (Cobham.const [true]) (Cobham.const [false])).of_eq
      fun v => by simp
  have hstep : Cobham fun w : Fin 3 → List Bool =>
      w 1 ++ caseBit ((w 2).drop (w 0).length) [true] [false] :=
    appendFn (.proj 1) hbitFn
  refine (Cobham.boundedRec .empty hstep hstep (.proj 1) ?_).of_eq fun v => ?_
  · intro r u
    rw [hrec, show (Fin.cons r u : Fin 2 → List Bool) 1 = u 0 from rfl]
    simp
  · rw [hrec]
    rfl

/-- **Total bit dispatch is in the class.** Same recursion as `dispatch`, except
the base case returns the `false` branch instead of the empty string — so the
empty string reads as `false` and every flag is genuinely one bit. -/
theorem dispatch₀ : Cobham fun v : Fin 3 → List Bool =>
    caseBit₀ (v 0) (v 1) (v 2) := by
  have hrec : ∀ (x : List Bool) (v : Fin 2 → List Bool),
      recNotation (fun u : Fin 2 → List Bool => u 1)
        (fun w : Fin 4 → List Bool => w 3) (fun w : Fin 4 → List Bool => w 2) x v
        = caseBit₀ x (v 0) (v 1) := by
    intro x v
    cases x with
    | nil => rfl
    | cons b x => cases b <;> rfl
  have hj : Cobham fun w : Fin 3 → List Bool => w 1 ++ w 2 :=
    (Cobham.comp Cobham.append fun i : Fin 2 => Cobham.proj i.succ).of_eq fun v => rfl
  refine (Cobham.boundedRec (.proj 1) (.proj 3) (.proj 2) hj ?_).of_eq fun v => ?_
  · intro x v
    rw [hrec]
    exact caseBit₀_length_le _ _ _
  · rw [hrec]
    rfl

/-- Applying `tail` to a member of the class. -/
theorem tailFn {n : ℕ} {g : (Fin n → List Bool) → List Bool} (h : Cobham g) :
    Cobham fun v : Fin n → List Bool => (g v).tail :=
  (Cobham.comp Cobham.tail fun _ : Fin 1 => h).of_eq fun _ => rfl

/-- Total if-then-else on a flag is in the class. -/
theorem iteFn {n : ℕ} {gc gx gy : (Fin n → List Bool) → List Bool}
    (hc : Cobham gc) (hx : Cobham gx) (hy : Cobham gy) :
    Cobham fun v : Fin n → List Bool => caseBit₀ (gc v) (gx v) (gy v) :=
  (comp₃ dispatch₀ hc hx hy).of_eq fun v => by simp

/-- The flag connectives are in the class: each is one `dispatch₀`. -/
theorem andFn {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) :
    Cobham fun v : Fin n → List Bool => andBit (g₀ v) (g₁ v) :=
  iteFn h₀ (iteFn h₁ (Cobham.const [true]) (Cobham.const [false]))
    (Cobham.const [false])

/-- Disjunction of flags is in the class. -/
theorem orFn {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) :
    Cobham fun v : Fin n → List Bool => orBit (g₀ v) (g₁ v) :=
  iteFn h₀ (Cobham.const [true])
    (iteFn h₁ (Cobham.const [true]) (Cobham.const [false]))

/-- Negation of a flag is in the class. -/
theorem notFn {n : ℕ} {g : (Fin n → List Bool) → List Bool} (h : Cobham g) :
    Cobham fun v : Fin n → List Bool => notBit (g v) :=
  iteFn h (Cobham.const [false]) (Cobham.const [true])

/-- **Bit extraction is in the class**: drop to the marked position and dispatch
on what is left. -/
theorem bitAtFn : Cobham fun v : Fin 2 → List Bool => bitAt (v 0) (v 1) :=
  (comp₃ dispatch₀ dropPrefix (Cobham.const [true]) (Cobham.const [false])).of_eq
    fun v => by simp [bitAt]

/-- Extracting the leading bit of a member of the class, as a flag. -/
theorem headFlagFn {n : ℕ} {g : (Fin n → List Bool) → List Bool} (h : Cobham g) :
    Cobham fun v : Fin n → List Bool => bitAt [] (g v) :=
  (comp₂ bitAtFn (Cobham.const []) h).of_eq fun v => by simp

/-- **The nonemptiness flag is in the class.** This is the one consumer of the
*partial* dispatcher: both branches are `[true]`, so the flag is `[true]` exactly
when there is a bit to read and `[]` otherwise. -/
theorem nonemptyFn {n : ℕ} {g : (Fin n → List Bool) → List Bool} (h : Cobham g) :
    Cobham fun v : Fin n → List Bool => nonemptyFlag (g v) :=
  (comp₃ dispatch h (Cobham.const [true]) (Cobham.const [true])).of_eq
    fun v => by simp [nonemptyFlag]

/-- **Matching against a fixed constant is in the class.** For each constant the
test unfolds into finitely many bit comparisons joined by `andFn`, so this is a
finite composition — the meta-level induction is on the constant, not a
recursion inside the algebra. -/
theorem matchPrefixFn {n : ℕ} {g : (Fin n → List Bool) → List Bool} (h : Cobham g)
    (c : List Bool) :
    Cobham fun v : Fin n → List Bool => matchPrefix c (g v) := by
  induction c generalizing g with
  | nil => exact (Cobham.const [true]).of_eq fun v => rfl
  | cons b c ih =>
      have htail := ih (tailFn h)
      have hhead : Cobham fun v : Fin n → List Bool =>
          bif b then bitAt [] (g v) else notBit (bitAt [] (g v)) := by
        cases b
        · exact (notFn (headFlagFn h)).of_eq fun v => rfl
        · exact (headFlagFn h).of_eq fun v => rfl
      exact (andFn (nonemptyFn h) (andFn hhead htail)).of_eq fun v => rfl

/-- Taking a prefix of one member of the class at the width of another. -/
theorem takeFn {n : ℕ} {gr gx : (Fin n → List Bool) → List Bool}
    (hr : Cobham gr) (hx : Cobham gx) :
    Cobham fun v : Fin n → List Bool => (gx v).take (gr v).length :=
  (comp₂ takePrefix hr hx).of_eq fun v => by simp

/-- Dropping a prefix of one member of the class at the width of another. -/
theorem dropFn {n : ℕ} {gr gx : (Fin n → List Bool) → List Bool}
    (hr : Cobham gr) (hx : Cobham gx) :
    Cobham fun v : Fin n → List Bool => (gx v).drop (gr v).length :=
  (comp₂ dropPrefix hr hx).of_eq fun v => by simp

/-- A block of `|x|` zeros is in the class, by limited recursion on notation:
each peeled bit prepends one `0` to the recursive value, and the argument bounds
the result. -/
theorem lengthPad :
    Cobham fun v : Fin 1 → List Bool => List.replicate (v 0).length false := by
  have hrec : ∀ (x : List Bool) (v : Fin 0 → List Bool),
      recNotation (fun _ : Fin 0 → List Bool => ([] : List Bool))
        (fun w : Fin 2 → List Bool => false :: w 1)
        (fun w : Fin 2 → List Bool => false :: w 1) x v
        = List.replicate x.length false := by
    intro x v
    induction x with
    | nil => rfl
    | cons b x ih => cases b <;> simp [ih, List.replicate_succ]
  have hstep : Cobham fun w : Fin 2 → List Bool => false :: w 1 :=
    (Cobham.comp (.bit false) fun _ : Fin 1 => .proj 1).of_eq fun v => rfl
  refine (Cobham.boundedRec .empty hstep hstep (.proj 0) ?_).of_eq fun v => ?_
  · intro x v
    rw [hrec, Fin.cons_zero]
    simp
  · rw [hrec]

/-- A block of zeros as wide as a member of the class. -/
theorem zeroBlockFn {n : ℕ} {g : (Fin n → List Bool) → List Bool} (h : Cobham g) :
    Cobham fun v : Fin n → List Bool => List.replicate (g v).length false :=
  (Cobham.comp lengthPad fun _ : Fin 1 => h).of_eq fun _ => rfl

/-- Concatenating `i` copies of a member of the class — a finite composition, so
the induction is at the meta level. -/
theorem repeatFn {n : ℕ} {g : (Fin n → List Bool) → List Bool} (h : Cobham g) :
    ∀ i : ℕ, Cobham fun v : Fin n → List Bool => (List.replicate i (g v)).flatten
  | 0 => Cobham.empty.of_eq fun _ => rfl
  | i + 1 => (appendFn h (repeatFn h i)).of_eq fun _ => by
      simp [List.replicate_succ]

/-- **Block addressing is in the class.** With every field of a configuration
padded to the ruler's width, field `i` is `takeFn` after dropping `i` rulers —
and `i` is a fixed natural number, so the drop is a finite concatenation. -/
theorem blockFn {n : ℕ} {gr gx : (Fin n → List Bool) → List Bool}
    (hr : Cobham gr) (hx : Cobham gx) (i : ℕ) :
    Cobham fun v : Fin n → List Bool => blockAt (gr v) (gx v) i :=
  (takeFn hr (dropFn (repeatFn hr i) hx)).of_eq fun v => by
    rw [blockAt]
    congr 2
    simp

/-- **Fixed-width padding is in the class.** With every field of a simulated
configuration padded to one ruler's width, field `i` is recovered by dropping `i`
rulers and taking one — so no self-delimiting decoder is ever needed inside the
algebra. -/
theorem padFn {n : ℕ} {gr gx : (Fin n → List Bool) → List Bool}
    (hr : Cobham gr) (hx : Cobham gx) :
    Cobham fun v : Fin n → List Bool => padTo (gr v) (gx v) :=
  (takeFn hr (appendFn hx (zeroBlockFn hr))).of_eq fun _ => rfl

/-- **Finite table dispatch is in the class.** Matching a member of the class
against each of finitely many constant patterns in turn, taking the first
branch that fires and a default otherwise, is a finite chain of `iteFn`s.

This is exactly the shape of a Turing machine's transition function: the patterns
are the (state, symbols-read) combinations, of which there are finitely many for
a fixed machine, and the branches assemble the successor configuration. -/
theorem tableFn {n : ℕ} {g d : (Fin n → List Bool) → List Bool}
    (hg : Cobham g) (hd : Cobham d)
    (table : List (List Bool × ((Fin n → List Bool) → List Bool)))
    (hbranch : ∀ p ∈ table, Cobham p.2) :
    Cobham fun v : Fin n → List Bool =>
      table.foldr (fun p acc => caseBit₀ (matchPrefix p.1 (g v)) (p.2 v) acc)
        (d v) := by
  induction table with
  | nil => exact hd
  | cons p t ih =>
      exact iteFn (matchPrefixFn hg p.1) (hbranch p (by simp))
        (ih fun q hq => hbranch q (by simp [hq]))

/-- **A table of constant patterns is a case analysis.** If some entry's pattern
prefixes the key, and every entry whose pattern prefixes the key carries the same
value, then the fold returns that value — regardless of the order the entries
appear in.

Phrasing it as "all matching entries agree" rather than "exactly one matches"
avoids having to prove the patterns pairwise distinct: for a transition table the
patterns *are* distinct, but agreement is the weaker and more convenient
obligation. -/
theorem foldr_table_eq (g d val : List Bool) :
    ∀ table : List (List Bool × List Bool),
      (∃ p ∈ table, p.1 <+: g) →
      (∀ q ∈ table, q.1 <+: g → q.2 = val) →
      table.foldr (fun q acc => caseBit₀ (matchPrefix q.1 g) q.2 acc) d = val := by
  intro table
  induction table with
  | nil => rintro ⟨p, hp, -⟩ -; simp at hp
  | cons a rest ih =>
      rintro ⟨p, hp, hpre⟩ hall
      rcases Decidable.em (a.1 <+: g) with hm | hm
      · rw [List.foldr_cons, (matchPrefix_eq_true_iff a.1 g).mpr hm, caseBit₀_cons,
          Bool.cond_true]
        exact hall a (by simp) hm
      · have hmf : matchPrefix a.1 g = [false] := by
          rcases matchPrefix_flag a.1 g with h | h
          · exact absurd ((matchPrefix_eq_true_iff a.1 g).mp h) hm
          · exact h
        rw [List.foldr_cons, hmf, caseBit₀_cons, Bool.cond_false]
        refine ih ⟨p, ?_, hpre⟩ fun q hq => hall q (by simp [hq])
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact absurd hpre hm
        · exact hp'

/-! ### Clocked iteration

The engine of the completeness direction: a machine is simulated by iterating its
one-step transition function a polynomial number of times, and both halves of
that — the iteration and the polynomial clock — are cheap inside the algebra. -/

/-- **Bounded iteration is in the class.** Iterating a step function once per bit
of a clock string is a single limited recursion on notation: the recursion
ignores *which* bit it peels and simply applies the step to its own recursive
value, so `h₀ = h₁ = f ∘ Fin.tail`. The clock's length is the iteration count,
which is why polynomial clocks (`exists_pow_clock`) give polynomially many
steps. -/
theorem iterFn {n : ℕ} {e : (Fin n → List Bool) → List Bool}
    {f j : (Fin (n + 1) → List Bool) → List Bool}
    (he : Cobham e) (hf : Cobham f) (hj : Cobham j)
    (hbound : ∀ (c : List Bool) (v : Fin n → List Bool),
      ((fun s => f (Fin.cons s v))^[c.length] (e v)).length
        ≤ (j (Fin.cons c v)).length) :
    Cobham fun v : Fin (n + 1) → List Bool =>
      (fun s => f (Fin.cons s (Fin.tail v)))^[(v 0).length] (e (Fin.tail v)) := by
  have hstep : Cobham fun w : Fin (n + 1 + 1) → List Bool => f (Fin.tail w) :=
    (Cobham.comp hf fun i : Fin (n + 1) => Cobham.proj i.succ).of_eq fun w => rfl
  have hrec : ∀ (c : List Bool) (v : Fin n → List Bool),
      recNotation e (fun w : Fin (n + 1 + 1) → List Bool => f (Fin.tail w))
        (fun w : Fin (n + 1 + 1) → List Bool => f (Fin.tail w)) c v
        = (fun s => f (Fin.cons s v))^[c.length] (e v) := by
    intro c v
    induction c with
    | nil => rfl
    | cons b c ih =>
        rw [List.length_cons, Function.iterate_succ_apply', ← ih]
        cases b <;> simp [Fin.tail_cons]
  refine (Cobham.boundedRec he hstep hstep hj ?_).of_eq fun v => ?_
  · intro c v
    rw [hrec]
    exact hbound c v
  · rw [hrec]

/-- **Clocks.** For every constant `c` and exponent `d` there is a member of the
class whose value on `v` is at least `c · (|v 0| + 1) ^ d` bits long — built from
constants and `smash`, which is exactly what `smash` is for. -/
theorem exists_pow_clock (c d : ℕ) :
    ∃ f : (Fin 1 → List Bool) → List Bool, Cobham f ∧
      ∀ v : Fin 1 → List Bool, c * ((v 0).length + 1) ^ d ≤ (f v).length := by
  induction d with
  | zero =>
      exact ⟨fun _ => List.replicate c false, Cobham.const _, fun v => by simp⟩
  | succ d ih =>
      obtain ⟨f, hf, hlen⟩ := ih
      have hsucc : Cobham fun v : Fin 1 → List Bool => false :: v 0 :=
        (Cobham.comp (.bit false) fun _ : Fin 1 => .proj 0).of_eq fun v => rfl
      refine ⟨fun v => Complexity.smash (f v) (false :: v 0),
        (comp₂ Cobham.smash hf hsucc).of_eq fun v => by simp, fun v => ?_⟩
      have h1 := hlen v
      calc c * ((v 0).length + 1) ^ (d + 1)
          = (c * ((v 0).length + 1) ^ d) * ((v 0).length + 1) := by ring
        _ ≤ (f v).length * (false :: v 0).length := by
              exact Nat.mul_le_mul h1 (by simp)
        _ = _ := by simp

end Cobham

end Complexity
