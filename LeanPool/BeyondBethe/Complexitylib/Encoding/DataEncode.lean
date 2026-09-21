/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Encoding.Data
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.List.Basic

/-!
# Encodings into `Data`

This file defines the class that is used to encode arbitrary data structures into `Data`,
so that RTMs (rose tree machines) can operate on them.

Instances are provided for convenience for `Data` itself, `Bool`, `List α`, `Option α`, `α × β`,
and `ℕ` (binary encoding via `List Bool`)

Every `DataEncode` instance also yields a *bitstring* encoding `DataEncode.bitstringEncode`, by
serializing the target `Data` value with `Data.toBits`. Since both the `DataEncode` instance and
`Data.toBits` are injective, `bitstringEncode` is injective too
(`DataEncode.bitstringEncode_injective`).
-/


public section

namespace Complexity

/-- Encoding of types into `Data`. -/
class DataEncode (α : Type) where
  /-- Encode a value of `α` as `Data`. -/
  encode : α → Data
  /-- The encoding is injective, so distinct values never collide. -/
  h_inj : encode.Injective

instance : DataEncode Data where
  encode b := b
  h_inj := by intros a b h_eq; grind

@[simp, scoped grind =]
lemma DataEncode_encode_data (d : Data) : DataEncode.encode d = d := rfl

instance : DataEncode Bool where
  encode b := if b then Data.l [ Data.l [] ] else Data.l []
  h_inj := by intros a b h_eq; grind

instance (α : Type) [DataEncode α] : DataEncode (List α) where
  encode xs := Data.l (xs.map DataEncode.encode)
  h_inj := by
    intro a b h
    exact List.map_injective_iff.mpr DataEncode.h_inj (Data.l.inj h)

@[simp, scoped grind =]
lemma DataEncode_list_nil {α : Type} [DataEncode α] :
  DataEncode.encode ([] : List α) = Data.l [] := by
  simp [DataEncode.encode]

@[simp, scoped grind =]
lemma DataEncode_list_eq_nil_iff_nil {α : Type} [DataEncode α] (xs : List α) :
  DataEncode.encode xs = Data.empty ↔ xs = [] := by
  simp [DataEncode.encode]

@[simp, scoped grind =]
lemma DataEncode_list_tail {α : Type} [DataEncode α] (xs : List α) :
  (DataEncode.encode xs).asList.tail = (DataEncode.encode xs.tail).asList := by
  simp [DataEncode.encode]

instance (α : Type) [DataEncode α] : DataEncode (Option α) where
  encode := fun
    | none => Data.l []
    | some x => Data.l [DataEncode.encode x]
  h_inj := by
    intro a b h
    grind [DataEncode.h_inj]

@[simp]
lemma DataEncode_Option_empty {α : Type} [DataEncode α] (x : Option α) :
  (DataEncode.encode x == Data.empty) = x.isNone := by
  cases x <;> simp [DataEncode.encode, Data.empty]

instance (α β : Type) [DataEncode α] [DataEncode β] : DataEncode (α × β) where
  encode := fun (a, b) => Data.l [DataEncode.encode a, DataEncode.encode b]
  h_inj := by
    intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
    grind [DataEncode.h_inj]

lemma DataEncode_pair {α β : Type} [DataEncode α] [DataEncode β] (a : α) (b : β) :
  DataEncode.encode (a, b) = Data.l [DataEncode.encode a, DataEncode.encode b] := by
  simp [DataEncode.encode]

instance : DataEncode ℕ where
  encode x := DataEncode.encode (Nat.bits x)
  h_inj := by
    intro a b h
    have hb : a.bits = b.bits := DataEncode.h_inj h
    have hrec : ∀ n : ℕ, n.bits.foldr (fun b acc => Nat.bit b acc) 0 = n := by
      intro n
      induction n using Nat.binaryRec' with
      | zero => simp
      | bit b n hn ih => rw [Nat.bits_append_bit n b hn]; simp [ih]
    have := congrArg (List.foldr (fun b acc => Nat.bit b acc) 0) hb
    simpa [hrec] using this

/-- Encode a value into a bitstring (`List Bool`) by first encoding it into `Data` and then
serializing that with the parenthesized `Data.toBits`. This is the class-inferrable bitstring
encoding available for any type with a `DataEncode` instance. -/
@[expose] def DataEncode.bitstringEncode {α : Type} [DataEncode α] (a : α) : List Bool :=
  (DataEncode.encode a).toBits

lemma DataEncode.bitstringEncode_def {α : Type} [DataEncode α] (a : α) :
    DataEncode.bitstringEncode a = (DataEncode.encode a).toBits := rfl

/-- The bitstring encoding is injective: distinct values yield distinct bitstrings. This composes
the injectivity of the `DataEncode` instance with that of `Data.toBits`. -/
theorem DataEncode.bitstringEncode_injective {α : Type} [DataEncode α] :
    Function.Injective (DataEncode.bitstringEncode (α := α)) :=
  Data.toBits_injective.comp DataEncode.h_inj

end Complexity
