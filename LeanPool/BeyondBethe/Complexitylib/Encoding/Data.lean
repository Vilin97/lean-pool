/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
public import Aesop.BuiltinRules
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Tactic.ToDual

/-!
# Main internal data type for the rose tree machine (RTM)

This file contains the main internal data structure for the RTM, `Data`, a rose tree.

## Main definitions and notations

- `Data` - the main data structure
- `Data.size` - the size of a `Data` object when encoded using parentheses, complexity results
  use this size as the main measure.
- `Data.toBits` - a parenthesized (balanced-bracket) serialization into `List Bool`, with length
  equal to `Data.size`, and injective (`Data.toBits_injective`).
- `Data.recL` - the main recursion principle for `Data`
- `Data.inductionL` - the main induction principle for `Data`

-/


public section

namespace Complexity

/-- Rose-tree data structure, it allows us to encode most of Lean's data structures in a
"natural" manner -/
inductive Data where
  | l : List Data → Data
deriving Repr

mutual
  /-- Decidable equality for `Data`, defined jointly with `Data.listDecEq`. -/
  def Data.decEq : ∀ (a b : Data), Decidable (a = b)
    | .l xs, .l ys =>
      match Data.listDecEq xs ys with
      | isTrue h => isTrue (congrArg Data.l h)
      | isFalse h => isFalse fun heq => h (Data.l.inj heq)
  /-- Decidable equality for `List Data`, defined jointly with `Data.decEq`. -/
  def Data.listDecEq : ∀ (xs ys : List Data), Decidable (xs = ys)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by simp)
    | _ :: _, [] => isFalse (by simp)
    | x :: xs, y :: ys =>
      match Data.decEq x y, Data.listDecEq xs ys with
      | isTrue hxy, isTrue hxys => isTrue (congrArg₂ List.cons hxy hxys)
      | isFalse hxy, _ => isFalse fun h => hxy (List.cons.inj h).1
      | _, isFalse hxys => isFalse fun h => hxys (List.cons.inj h).2
end

instance : DecidableEq Data := Data.decEq
instance : BEq Data := inferInstance
instance : LawfulBEq Data := inferInstance

/-- The empty `Data` node, `Data.l []`. -/
abbrev Data.empty := Data.l []


/-- The list of children of a `Data` node. -/
@[scoped grind =]
def Data.asList
  | Data.l xs => xs

@[scoped grind =]
lemma Data.asList_empty : Data.empty.asList = [] := by rfl

@[simp, scoped grind =]
lemma Data.asList_l (d : Data) : Data.l d.asList = d := by simp [Data.asList]; grind

@[simp, scoped grind =]
lemma Data.l_asList (xs : List Data) : (Data.l xs).asList = xs := by simp [Data.asList]

/-- The encoding length of `d`, relevant for complexity.
This is the encoded size assuming an encoding into parenthesized expressions. -/
def Data.size : Data → ℕ
  | Data.l xs => 2 + (xs.map Data.size |>.sum)

@[simp]
lemma Data.size_le {d : Data} : 0 < d.size := by
  obtain ⟨xs⟩ := d
  grind [Data.size]

@[simp, scoped grind =]
lemma Data.size_empty : Data.empty.size = 2 := by simp [Data.empty, Data.size]

@[simp, scoped grind =]
lemma Data.cons_size {h : Data} {t : List Data} :
    (Data.l (h :: t)).size = h.size + (Data.l t).size := by
  simp [Data.size]
  grind

lemma Data.size_lt_of_mem {c : Data} {xs : List Data} (hc : c ∈ xs) :
    c.size < (Data.l xs).size := by
  induction xs with
  | nil => simp at hc
  | cons a as ih =>
    rw [Data.cons_size]
    rcases List.mem_cons.1 hc with h | h
    · subst h; have := @Data.size_le (Data.l as); omega
    · have := ih h; omega

/-- Recursion principle for `Data`. -/
@[elab_as_elim]
def Data.recL {motive : Data → Sort*}
    (nil : motive (Data.l []))
    (cons : ∀ (x : Data) (xs : List Data),
      motive x → motive (Data.l xs) → motive (Data.l (x :: xs))) :
    ∀ d, motive d
  | .l [] => nil
  | .l (x :: xs) =>
      cons x xs (Data.recL nil cons x) (Data.recL nil cons (.l xs))

/-- Induction principle for `Data`, the `Prop`-valued companion to `Data.recL`. -/
@[elab_as_elim]
theorem Data.inductionL {motive : Data → Prop}
    (nil : motive (Data.l []))
    (cons : ∀ (x : Data) (xs : List Data),
      motive x → motive (Data.l xs) → motive (Data.l (x :: xs)))
    (d : Data) : motive d :=
  Data.recL nil cons d

/-! ## Bitstring serialization

`Data.toBits` serializes a `Data` value into a `List Bool` using a parenthesized
(balanced-bracket) encoding: `false` opens a node, its children are serialized in order, and
`true` closes the node. This matches `Data.size` exactly (`Data.length_toBits`) and is injective
(`Data.toBits_injective`), so any `DataEncode` instance yields an injective bitstring encoding
(see `Complexitylib.Encoding.DataEncode`). -/

/-- Serialize `Data` into a bitstring with a parenthesized (balanced-bracket) encoding: `false`
opens a node, the children are serialized in order, and `true` closes the node. -/
def Data.toBits : Data → List Bool
  | Data.l xs => false :: ((xs.map Data.toBits).flatten ++ [true])

lemma Data.toBits_l (xs : List Data) :
    (Data.l xs).toBits = false :: ((xs.map Data.toBits).flatten ++ [true]) := by
  rw [Data.toBits]

@[simp]
lemma Data.length_toBits (d : Data) : d.toBits.length = d.size := by
  induction d using Data.inductionL with
  | nil => simp [Data.toBits]
  | cons x xs ihx ihxs =>
    simp only [Data.toBits, Data.size, List.map_cons, List.flatten_cons, List.length_cons,
      List.length_append, List.length_flatten, List.map_map] at *
    grind

/-- One step of the stack-based `Data.fromBits` parser. The state is a stack of frames, each a
list of the sibling nodes completed so far at that nesting depth (outermost frame at the bottom).
Reading `false` opens a new (empty) frame; reading `true` closes the top frame into a `Data.l`
node and appends it to its parent. `none` is a permanent failure state (an unmatched `true`). -/
def Data.fromBitsStep : Option (List (List Data)) → Bool → Option (List (List Data))
  | none, _ => none
  | some stack, false => some ([] :: stack)
  | some stack, true =>
    match stack with
    | kids :: parent :: rest => some ((parent ++ [Data.l kids]) :: rest)
    | _ => none

/-- Decode a bitstring produced by `Data.toBits` back into a `Data` value, or `none` if it is not
a valid single serialization. This is a left inverse of `Data.toBits` (`Data.fromBits_toBits`). -/
def Data.fromBits (bits : List Bool) : Option Data :=
  match bits.foldl Data.fromBitsStep (some [[]]) with
  | some [[d]] => some d
  | _ => none

/-- Running `Data.fromBitsStep` over `d.toBits` appends the decoded `d` to the top frame of the
stack, leaving the rest of the stack untouched. This is the key lemma behind
`Data.fromBits_toBits`. -/
theorem Data.foldl_fromBitsStep_toBits :
    ∀ (d : Data) (top : List Data) (rest : List (List Data)),
      d.toBits.foldl Data.fromBitsStep (some (top :: rest)) = some ((top ++ [d]) :: rest) := by
  -- Strong induction on the size of `d`, so that each child (strictly smaller) can appeal to the
  -- inductive hypothesis while a plain list induction consumes the children in order.
  have key : ∀ (n : ℕ) (d : Data) (top : List Data) (rest : List (List Data)),
      d.size ≤ n →
      d.toBits.foldl Data.fromBitsStep (some (top :: rest)) = some ((top ++ [d]) :: rest) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n IH =>
      rintro ⟨xs⟩ top rest hsz
      -- Consuming the flattened children appends them, in order, to the current frame.
      have L : ∀ (xs : List Data) (cur : List Data) (rest : List (List Data)),
          (∀ c ∈ xs, c.size < n) →
          (xs.map Data.toBits).flatten.foldl Data.fromBitsStep (some (cur :: rest))
            = some ((cur ++ xs) :: rest) := by
        intro xs
        induction xs with
        | nil => intro cur rest _; simp
        | cons c cs ihcs =>
          intro cur rest hlt
          have hc : c.size < n := hlt c (List.mem_cons_self ..)
          simp only [List.map_cons, List.flatten_cons, List.foldl_append]
          rw [IH c.size hc c cur rest (Nat.le_refl _),
            ihcs (cur ++ [c]) rest (fun c' hc' => hlt c' (List.mem_cons_of_mem _ hc'))]
          simp
      rw [Data.toBits_l]
      simp only [List.foldl_cons, List.foldl_append, Data.fromBitsStep]
      rw [L xs [] (top :: rest) (fun c hc => Nat.lt_of_lt_of_le (Data.size_lt_of_mem hc) hsz)]
      simp
  intro d top rest
  exact key d.size d top rest (Nat.le_refl _)

/-- `Data.fromBits` recovers any value serialized by `Data.toBits`. -/
@[simp]
theorem Data.fromBits_toBits (d : Data) : Data.fromBits d.toBits = some d := by
  simp only [Data.fromBits, Data.foldl_fromBitsStep_toBits, List.nil_append]

/-- `Data.toBits` is injective: the parenthesized serialization determines the value. This follows
from `Data.fromBits` being a left inverse. -/
theorem Data.toBits_injective : Function.Injective Data.toBits := by
  intro a b h
  have := Data.fromBits_toBits a
  rw [h, Data.fromBits_toBits b] at this
  exact Option.some.inj this.symm

end Complexity
