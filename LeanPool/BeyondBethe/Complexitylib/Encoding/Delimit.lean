/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Init
public import Aesop.BuiltinRules
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Widget.Calc
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Self-delimiting blocks

To concatenate binary strings into a single binary string, each piece must announce its own
end. This file defines the library's single framing operation and its parsers:

- `delimit` frames a payload: each payload bit is doubled (`false ↦ [false, false]`,
  `true ↦ [true, true]`) and the block is terminated by the separator `[false, true]`,
  which no run of doubled bits can produce.
- `unpair?` parses one block off the front of the input, returning the payload and the
  remaining suffix (`none` on malformed input). It is named for its role in the pairing
  codec `Complexity.pair` (see `Complexitylib.Encoding.Pairing`), which is
  `pair x y = delimit x ++ y`.
- `undelimitBlock`, `takeFirstBlock`, `hasBlock`, `tagBlock`, and `undelimitBlocks` are the
  total helper functions machines compute when working with framed data.

This file deliberately has no dependency on the machine or complexity-class layers, so the
machine-input pairing codec (`Complexitylib.Encoding.Pairing`) can build on it without import
cycles.
-/


@[expose] public section

namespace Complexity

/-- Frame a binary string as a self-delimiting block: each payload bit is doubled
    (`false ↦ [false, false]`, `true ↦ [true, true]`) and the block is terminated by the
    separator `[false, true]`, which no run of doubled bits can produce. -/
def delimit (x : List Bool) : List Bool :=
  (x.flatMap fun b => [b, b]) ++ [false, true]

@[simp] theorem delimit_nil : delimit [] = [false, true] := rfl

@[simp] theorem delimit_cons (b : Bool) (l : List Bool) :
    delimit (b :: l) = b :: b :: delimit l := by
  simp [delimit]

@[simp] theorem delimit_length (l : List Bool) : (delimit l).length = 2 * l.length + 2 := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [delimit_cons, List.length_cons, ih]; omega

/-- Parse one self-delimiting block off the front of the input. It scans doubled bits until
    the first separator `[false, true]`, returning the decoded payload together with the
    remaining suffix. Invalid doubled prefixes return `none`. -/
def unpair? : List Bool → Option (List Bool × List Bool)
  | [] => none
  | false :: true :: y => some ([], y)
  | false :: false :: z =>
      Option.map (fun (xy : List Bool × List Bool) => (false :: xy.1, xy.2)) (unpair? z)
  | true :: true :: z =>
      Option.map (fun (xy : List Bool × List Bool) => (true :: xy.1, xy.2)) (unpair? z)
  | _ => none

/-- `unpair?` reads back the framing written by `delimit`: parsing one block off the front
    of any input recovers the payload and the remaining suffix. -/
@[simp] theorem unpair?_delimit_append (x y : List Bool) :
    unpair? (delimit x ++ y) = some (x, y) := by
  induction x with
  | nil => simp [unpair?]
  | cons b x ih => cases b <;> simp [unpair?, ih]

/-- Soundness of the parser: a successful parse decomposes the input as the parsed payload's
    framing followed by the leftover suffix. -/
theorem eq_delimit_append_of_unpair?_eq_some :
    ∀ {z x y : List Bool}, unpair? z = some (x, y) → z = delimit x ++ y
  | [], _, _, h => by simp [unpair?] at h
  | [b], _, _, h => by cases b <;> simp [unpair?] at h
  | false :: true :: rest, x, y, h => by
    simp only [unpair?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | false :: false :: rest, x, y, h => by
    simp only [unpair?, Option.map_eq_some_iff] at h
    obtain ⟨⟨p₁, p₂⟩, hp, heq⟩ := h
    obtain ⟨rfl, rfl⟩ : false :: p₁ = x ∧ p₂ = y := by simpa [Prod.ext_iff] using heq
    simp only [eq_delimit_append_of_unpair?_eq_some hp, delimit_cons, List.cons_append]
  | true :: true :: rest, x, y, h => by
    simp only [unpair?, Option.map_eq_some_iff] at h
    obtain ⟨⟨p₁, p₂⟩, hp, heq⟩ := h
    obtain ⟨rfl, rfl⟩ : true :: p₁ = x ∧ p₂ = y := by simpa [Prod.ext_iff] using heq
    simp only [eq_delimit_append_of_unpair?_eq_some hp, delimit_cons, List.cons_append]
  | true :: false :: rest, _, _, h => by simp [unpair?] at h

/- ## Total block helpers -/

/-- Strip the framing of a single self-delimiting block, returning its payload. On `delimit P`
this returns `P`. Unlike `unpair?`, this is total: it ignores any data trailing the first block
and maps malformed input to `[]`. -/
def undelimitBlock : List Bool → List Bool
  | false :: true :: _ => []
  | false :: false :: rest => false :: undelimitBlock rest
  | true :: _ :: rest => true :: undelimitBlock rest
  | _ => []

@[simp]
theorem undelimitBlock_delimit (P : List Bool) :
    undelimitBlock (delimit P) = P := by
  induction P with
  | nil => rfl
  | cons b P ih => cases b <;> simp [undelimitBlock, ih]

/-- Keep the leading self-delimiting block of a bitstring, dropping everything after it. On a
pair encoding `delimit x ++ w` this returns `delimit x`. -/
def takeFirstBlock : List Bool → List Bool
  | false :: true :: _ => [false, true]
  | false :: false :: rest => false :: false :: takeFirstBlock rest
  | true :: c :: rest => true :: c :: takeFirstBlock rest
  | l => l

@[simp]
theorem takeFirstBlock_delimit_append (P Q : List Bool) :
    takeFirstBlock (delimit P ++ Q) = delimit P := by
  induction P with
  | nil => rfl
  | cons b P ih => cases b <;> simp [takeFirstBlock, ih]

/-- Does the bitstring begin with a well-formed self-delimiting block? -/
def hasBlock : List Bool → Bool
  | false :: true :: _ => true
  | false :: false :: rest => hasBlock rest
  | true :: true :: rest => hasBlock rest
  | _ => false

theorem hasBlock_eq_isSome_unpair? :
    ∀ l : List Bool, hasBlock l = (unpair? l).isSome
  | [] => rfl
  | [b] => by cases b <;> rfl
  | false :: true :: _ => rfl
  | false :: false :: rest => by
    simp only [hasBlock, unpair?, hasBlock_eq_isSome_unpair? rest]
    cases unpair? rest <;> rfl
  | true :: true :: rest => by
    simp only [hasBlock, unpair?, hasBlock_eq_isSome_unpair? rest]
    cases unpair? rest <;> rfl
  | true :: false :: _ => rfl

/-- Tag a bitstring with a leading `true` if it begins with a well-formed self-delimiting
block, and return the empty bitstring otherwise. On pair encodings this computes
`encode ∘ decode`. -/
def tagBlock (l : List Bool) : List Bool :=
  bif hasBlock l then true :: l else []

/- ## Parsing a sequence of blocks -/

/-- Parse a sequence of self-delimiting blocks, using `fuel` to bound the number of blocks.

This is the auxiliary, fuel-carrying implementation of `undelimitBlocks`; since every block
is nonempty, `input.length` is always enough fuel. -/
def undelimitBlocksAux : ℕ → List Bool → Option (List (List Bool))
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, input => do
    let (block, rest) ← unpair? input
    let blocks ← undelimitBlocksAux fuel rest
    return block :: blocks

/-- Parse a sequence of self-delimiting blocks off the front of the input.

Since every block is nonempty, `input.length` bounds the number of blocks, so it always
suffices as fuel for `undelimitBlocksAux`. -/
def undelimitBlocks (input : List Bool) : Option (List (List Bool)) :=
  undelimitBlocksAux input.length input

theorem length_le_length_flatten_delimit (l : List (List Bool)) :
    l.length ≤ ((l.map delimit).flatten).length := by
  induction l with
  | nil => simp
  | cons b t ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
      delimit_length]
    omega

private theorem undelimitBlocksAux_flatten_delimit (l : List (List Bool)) :
    ∀ fuel, l.length ≤ fuel → undelimitBlocksAux fuel ((l.map delimit).flatten) = some l := by
  induction l with
  | nil => intro fuel _; cases fuel <;> rfl
  | cons b t ih =>
    intro fuel hfuel
    rw [List.length_cons] at hfuel
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨hd, tl, hcons⟩ : ∃ hd tl, delimit b ++ (t.map delimit).flatten = hd :: tl := by
      cases b <;> exact ⟨_, _, rfl⟩
    simp only [List.map_cons, List.flatten_cons, hcons, undelimitBlocksAux]
    rw [← hcons, unpair?_delimit_append]
    simp [ih fuel (by omega)]

theorem undelimitBlocks_flatten_delimit (l : List (List Bool)) :
    undelimitBlocks ((l.map delimit).flatten) = some l :=
  undelimitBlocksAux_flatten_delimit l _ (length_le_length_flatten_delimit l)

end Complexity
