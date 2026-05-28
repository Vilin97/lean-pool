/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.Data.Fintype.CardEmbedding

import LeanPool.TwoColoringOneRound.LowerBound.N1000000AvailFrom
import LeanPool.TwoColoringOneRound.LowerBound.N1000000MaskAtFacts
import LeanPool.TwoColoringOneRound.LowerBound.N1000000OrbitalBasis
import LeanPool.TwoColoringOneRound.LowerBound.N1000000PairTransitivity
import LeanPool.TwoColoringOneRound.LowerBound.N1000000StructureConstants

namespace Distributed2Coloring.LowerBound

namespace N1000000OrbitCounting

open scoped BigOperators

open Distributed2Coloring.LowerBound.N1000000AvailFrom
open Distributed2Coloring.LowerBound.N1000000MaskAtFacts
open Distributed2Coloring.LowerBound.N1000000OrbitalBasis
open Distributed2Coloring.LowerBound.N1000000PairTransitivity
open Distributed2Coloring.LowerBound.N1000000StructureConstants

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev n : Nat := N1000000Data.n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev SymN := Sym n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev V := Vertex n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev DirIdx := N1000000StructureConstants.DirIdx

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev AvailFrom3 := AvailFrom (s := 3)

noncomputable instance : Fintype AvailFrom3 := by infer_instance

private lemma card_outside : Fintype.card AvailFrom3 = n - 3 := by
  simpa using (card_availFrom (s := 3))

private lemma base_i0 : (baseVertex.1 ⟨0, by decide⟩ : SymN) = ⟨0, by decide⟩ := by
  rfl

private lemma base_i1 : (baseVertex.1 ⟨1, by decide⟩ : SymN) = ⟨1, by decide⟩ := by
  rfl

private lemma base_i2 : (baseVertex.1 ⟨2, by decide⟩ : SymN) = ⟨2, by decide⟩ := by
  rfl

private lemma ge_three_of_ne_base (x : SymN)
    (h0 : x ≠ (baseVertex.1 ⟨0, by decide⟩))
    (h1 : x ≠ (baseVertex.1 ⟨1, by decide⟩))
    (h2 : x ≠ (baseVertex.1 ⟨2, by decide⟩)) : 3 ≤ x.1 := by
  by_contra hge
  have hlt : x.1 < 3 := Nat.lt_of_not_ge hge
  cases hx0 : x.1 with
  | zero =>
      have : x = (baseVertex.1 ⟨0, by decide⟩) := by
        apply Fin.ext
        simp [baseVertex, baseTuple, hx0]
      exact h0 this
  | succ m =>
      cases hm0 : m with
      | zero =>
          have hx1 : x.1 = 1 := by simp [hx0, hm0]
          have : x = (baseVertex.1 ⟨1, by decide⟩) := by
            apply Fin.ext
            simp [baseVertex, baseTuple, hx1]
          exact h1 this
      | succ m2 =>
          cases hm1 : m2 with
          | zero =>
              have hx2 : x.1 = 2 := by simp [hx0, hm0, hm1]
              have : x = (baseVertex.1 ⟨2, by decide⟩) := by
                apply Fin.ext
                simp [baseVertex, baseTuple, hx2]
              exact h2 this
            | succ m3 =>
                have hxge : 3 ≤ x.1 := by
                  -- `x.1 = m3 + 3` in this branch.
                  have hx : x.1 = m3.succ.succ.succ := by simp [hx0, hm0, hm1]
                  -- `3 ≤ succ (succ (succ m3))`.
                  rw [hx]
                  exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le m3)))
                exact (Nat.not_lt_of_ge hxge hlt).elim

/-- Free columns for a directed type `k`: coordinates not equal to any base symbol. -/
def FreeCol (k : DirIdx) : Type :=
  { j : Fin 3 // colMatch (maskAt k) j = none }

noncomputable instance (k : DirIdx) : Fintype (FreeCol k) := by
  dsimp [FreeCol]
  infer_instance

private lemma card_freeCol (k : DirIdx) : Fintype.card (FreeCol k) = freeCols (maskAt k) := by
  classical
  simpa [FreeCol, freeCols] using
    (Fintype.card_subtype (α := Fin 3) (p := fun j : Fin 3 => colMatch (maskAt k) j = none))

private theorem colMatch_unique' (k : DirIdx) :
    ∀ j₁ j₂ : Fin 3, ∀ i : Fin 3,
      colMatch (maskAt k) j₁ = some i → colMatch (maskAt k) j₂ = some i → j₁ = j₂ := by
  classical
  fin_cases k <;> decide

private lemma colMatch_unique (k : DirIdx) {j₁ j₂ : Fin 3} {i : Fin 3}
    (h₁ : colMatch (maskAt k) j₁ = some i) (h₂ : colMatch (maskAt k) j₂ = some i) : j₁ = j₂ :=
  colMatch_unique' (k := k) _ _ _ h₁ h₂

/-- Vertices in the orbit of the base vertex with directed type `k`. -/
def BaseOrbit (k : DirIdx) : Type :=
  { u : V // dirMask baseVertex u = maskAt k }

noncomputable instance (k : DirIdx) : Fintype (BaseOrbit k) := by
  dsimp [BaseOrbit]
  infer_instance

theorem baseOrbit_freeCoord_outside {k : DirIdx} (u : BaseOrbit k) (j : FreeCol k) :
    3 ≤ (u.1.1 j.1).1 := by
  have hcolNone : colMatch (maskAt k) j.1 = none := j.2
  -- For each base index `i`, the `(i,j)` bit is `false`, hence `base_i ≠ u_j`.
  have hne : ∀ i : Fin 3, u.1.1 j.1 ≠ baseVertex.1 i := by
    intro i
    have hm :
        (maskAt k).testBit (i.1 * 3 + j.1.1) = decide (colMatch (maskAt k) j.1 = some i) := by
      exact maskAt_testBit_eq_decide_colMatch (d := k) (i := i) (j := j.1)
    have hmFalse : (maskAt k).testBit (i.1 * 3 + j.1.1) = false := by
      -- `colMatch = none`, so it cannot be `some i`.
      have : decide (colMatch (maskAt k) j.1 = some i) = false := by simp [hcolNone]
      simp [hm, this]
    have hdFalse : (dirMask baseVertex u.1).testBit (i.1 * 3 + j.1.1) = false := by
      simpa [u.2] using hmFalse
    have hb :
        (dirMask baseVertex u.1).testBit (i.1 * 3 + j.1.1) =
          decide (baseVertex.1 i = u.1.1 j.1) := by
      exact dirMask_testBit (u := baseVertex) (v := u.1) (i := i) (j := j.1)
    have hDecFalse : decide (baseVertex.1 i = u.1.1 j.1) = false := by
      simpa [hb] using hdFalse
    have : ¬ baseVertex.1 i = u.1.1 j.1 := of_decide_eq_false hDecFalse
    simpa [eq_comm] using this
  exact
    ge_three_of_ne_base (x := u.1.1 j.1)
      (h0 := hne ⟨0, by decide⟩) (h1 := hne ⟨1, by decide⟩) (h2 := hne ⟨2, by decide⟩)

private def encodeBaseOrbit (k : DirIdx) (u : BaseOrbit k) : FreeCol k ↪ AvailFrom3 :=
  ⟨fun j => ⟨u.1.1 j.1, baseOrbit_freeCoord_outside (u := u) (j := j)⟩, by
    intro j₁ j₂ hEq
    have : u.1.1 j₁.1 = u.1.1 j₂.1 := by
      -- strip subtypes
      exact congrArg Subtype.val hEq
    exact Subtype.ext (u.1.2 this)⟩

private theorem base_val_lt_three (i : Fin 3) : (baseVertex.1 i).1 < 3 := by
  fin_cases i <;> decide

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def decodeTuple (k : DirIdx) (g : FreeCol k ↪ AvailFrom3) : Tuple 3 n :=
  fun j =>
    if hc : colMatch (maskAt k) j = none then
      (g ⟨j, hc⟩).1
    else
      -- `colMatch ≠ none`, so it must be `some i` for a unique `i`.
      baseVertex.1 (Classical.choose ((Option.ne_none_iff_exists').1 hc))

theorem decodeTuple_of_colMatch_none (k : DirIdx) (g : FreeCol k ↪ AvailFrom3) (j : Fin 3)
    (hc : colMatch (maskAt k) j = none) :
    decodeTuple (k := k) g j = (g ⟨j, hc⟩).1 := by
  simp [decodeTuple, hc]

theorem decodeTuple_of_colMatch_some (k : DirIdx) (g : FreeCol k ↪ AvailFrom3) (j i : Fin 3)
    (hc : colMatch (maskAt k) j = some i) :
    decodeTuple (k := k) g j = baseVertex.1 i := by
  classical
  simp [decodeTuple, hc]

private theorem decodeTuple_injective (k : DirIdx) (g : FreeCol k ↪ AvailFrom3) :
    Function.Injective (decodeTuple (k := k) g) := by
  classical
  intro j₁ j₂ hEq
  by_cases h₁ : colMatch (maskAt k) j₁ = none <;> by_cases h₂ : colMatch (maskAt k) j₂ = none
  · -- both free
    have hDec₁ : decodeTuple (k := k) g j₁ = (g ⟨j₁, h₁⟩).1 :=
      decodeTuple_of_colMatch_none (k := k) (g := g) (j := j₁) h₁
    have hDec₂ : decodeTuple (k := k) g j₂ = (g ⟨j₂, h₂⟩).1 :=
      decodeTuple_of_colMatch_none (k := k) (g := g) (j := j₂) h₂
    have : (g ⟨j₁, h₁⟩).1 = (g ⟨j₂, h₂⟩).1 := by
      simpa [hDec₁, hDec₂] using hEq
    have hg : (g ⟨j₁, h₁⟩) = (g ⟨j₂, h₂⟩) := by
      apply Subtype.ext
      exact this
    have : (⟨j₁, h₁⟩ : FreeCol k) = ⟨j₂, h₂⟩ := g.injective hg
    simpa using congrArg Subtype.val this
  · -- free vs fixed
    rcases (Option.ne_none_iff_exists').1 h₂ with ⟨i₂, hi₂⟩
    have hDec₁ : decodeTuple (k := k) g j₁ = (g ⟨j₁, h₁⟩).1 :=
      decodeTuple_of_colMatch_none (k := k) (g := g) (j := j₁) h₁
    have hDec₂ : decodeTuple (k := k) g j₂ = baseVertex.1 i₂ :=
      decodeTuple_of_colMatch_some (k := k) (g := g) (j := j₂) (i := i₂) hi₂
    have hval : (g ⟨j₁, h₁⟩).1 = baseVertex.1 i₂ := by
      simpa [hDec₁, hDec₂] using hEq
    have hge : 3 ≤ (g ⟨j₁, h₁⟩).1.1 := (g ⟨j₁, h₁⟩).2
    have hlt : (baseVertex.1 i₂).1 < 3 := base_val_lt_three (i := i₂)
    exact (Nat.not_lt_of_ge hge (by simpa [hval] using hlt)).elim
  · -- fixed vs free
    rcases (Option.ne_none_iff_exists').1 h₁ with ⟨i₁, hi₁⟩
    have hDec₁ : decodeTuple (k := k) g j₁ = baseVertex.1 i₁ :=
      decodeTuple_of_colMatch_some (k := k) (g := g) (j := j₁) (i := i₁) hi₁
    have hDec₂ : decodeTuple (k := k) g j₂ = (g ⟨j₂, h₂⟩).1 :=
      decodeTuple_of_colMatch_none (k := k) (g := g) (j := j₂) h₂
    have hval : baseVertex.1 i₁ = (g ⟨j₂, h₂⟩).1 := by
      simpa [hDec₁, hDec₂] using hEq
    have hge : 3 ≤ (g ⟨j₂, h₂⟩).1.1 := (g ⟨j₂, h₂⟩).2
    have hlt : (baseVertex.1 i₁).1 < 3 := base_val_lt_three (i := i₁)
    exact (Nat.not_lt_of_ge hge (by simpa [hval] using hlt)).elim
  · -- both fixed
    rcases (Option.ne_none_iff_exists').1 h₁ with ⟨i₁, hi₁⟩
    rcases (Option.ne_none_iff_exists').1 h₂ with ⟨i₂, hi₂⟩
    have hDec₁ : decodeTuple (k := k) g j₁ = baseVertex.1 i₁ :=
      decodeTuple_of_colMatch_some (k := k) (g := g) (j := j₁) (i := i₁) hi₁
    have hDec₂ : decodeTuple (k := k) g j₂ = baseVertex.1 i₂ :=
      decodeTuple_of_colMatch_some (k := k) (g := g) (j := j₂) (i := i₂) hi₂
    have : baseVertex.1 i₁ = baseVertex.1 i₂ := by
      simpa [hDec₁, hDec₂] using hEq
    have : i₁ = i₂ := baseVertex.2 this
    have : j₁ = j₂ :=
      colMatch_unique (k := k) (j₁ := j₁) (j₂ := j₂) (i := i₁) hi₁ (by simpa [this] using hi₂)
    simp [this]

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def decodeVertex (k : DirIdx) (g : FreeCol k ↪ AvailFrom3) : V :=
  ⟨decodeTuple (k := k) g, decodeTuple_injective (k := k) g⟩

private lemma decide_base_eq_decodeVertex_eq_decide_colMatch (k : DirIdx)
    (g : FreeCol k ↪ AvailFrom3)
    (i j : Fin 3) :
    decide (baseVertex.1 i = (decodeVertex (k := k) g).1 j) =
      decide (colMatch (maskAt k) j = some i) := by
  classical
  cases hc : colMatch (maskAt k) j with
  | none =>
      have hv : (decodeVertex (k := k) g).1 j = (g ⟨j, hc⟩).1 := by
        have h0 : (decodeVertex (k := k) g).1 j = decodeTuple (k := k) g j := rfl
        have h1 : decodeTuple (k := k) g j = (g ⟨j, hc⟩).1 :=
          decodeTuple_of_colMatch_none (k := k) (g := g) (j := j) hc
        simpa [h0] using h1
      have hge : 3 ≤ ((decodeVertex (k := k) g).1 j).1 := by
        simpa [hv] using (g ⟨j, hc⟩).2
      have hlt : (baseVertex.1 i).1 < 3 := base_val_lt_three (i := i)
      have hne : baseVertex.1 i ≠ (decodeVertex (k := k) g).1 j := by
        intro hEqSym
        have : (baseVertex.1 i).1 = ((decodeVertex (k := k) g).1 j).1 := by
          simpa using congrArg Fin.val hEqSym
        exact (Nat.not_lt_of_ge hge (by simpa [this] using hlt)).elim
      simp [hne]
  | some i0 =>
      have hv : (decodeVertex (k := k) g).1 j = baseVertex.1 i0 := by
        have h0 : (decodeVertex (k := k) g).1 j = decodeTuple (k := k) g j := rfl
        have h1 : decodeTuple (k := k) g j = baseVertex.1 i0 :=
          decodeTuple_of_colMatch_some (k := k) (g := g) (j := j) (i := i0) hc
        simpa [h0] using h1
      by_cases hEq : i = i0
      · subst hEq
        simp [hv]
      · have hne : baseVertex.1 i ≠ baseVertex.1 i0 := by
          intro hEqSym
          exact hEq (baseVertex.2 hEqSym)
        have hEq' : i0 ≠ i := by simpa [eq_comm] using hEq
        simp [hv, hne, hEq']

theorem decodeVertex_mask (k : DirIdx) (g : FreeCol k ↪ AvailFrom3) :
    dirMask baseVertex (decodeVertex (k := k) g) = maskAt k := by
  classical
  -- Use `eq_of_testBit_eq`, splitting into `t < 9` and `t ≥ 9`.
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < 9
  · -- Write `t = (t/3)*3 + (t%3)` and use `dirMask_testBit` / `maskAt_testBit_eq_decide_colMatch`.
    let iNat : Nat := t / 3
    let jNat : Nat := t % 3
    have hi : iNat < 3 := by
      have : t < 3 * 3 := by simpa using ht
      simpa [iNat] using (Nat.div_lt_of_lt_mul this)
    have hj : jNat < 3 := by
      have : 0 < 3 := by decide
      simpa [jNat] using (Nat.mod_lt t (y := 3) this)
    let i : Fin 3 := ⟨iNat, hi⟩
    let j : Fin 3 := ⟨jNat, hj⟩
    have htDecomp : i.1 * 3 + j.1 = t := by
      -- `Nat.div_add_mod` is `3*(t/3) + t%3 = t`.
      simpa [iNat, jNat, Nat.mul_comm] using (Nat.div_add_mod t 3)
    have :
        Nat.testBit (dirMask baseVertex (decodeVertex (k := k) g)) (i.1 * 3 + j.1) =
          Nat.testBit (maskAt k) (i.1 * 3 + j.1) := by
      simp [dirMask_testBit, maskAt_testBit_eq_decide_colMatch,
        decide_base_eq_decodeVertex_eq_decide_colMatch (k := k) (g := g) (i := i) (j := j)]
    simpa [htDecomp] using this
  · -- For `t ≥ 9`, both numbers are `< 2^9`, hence the `t`th bit is `false`.
    have h9t : 9 ≤ t := Nat.le_of_not_gt ht
    have hPow : (2 : Nat) ^ 9 ≤ (2 : Nat) ^ t :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) h9t
    have hDirLt9 : dirMask baseVertex (decodeVertex (k := k) g) < (2 : Nat) ^ 9 := by
      simpa [Nat.shiftLeft_eq] using (dirMask_lt (u := baseVertex) (v := decodeVertex (k := k) g))
    have hMaskLt9 : maskAt k < (2 : Nat) ^ 9 := by
      simpa [Nat.shiftLeft_eq] using (maskAt_lt_512 (d := k))
    have hDirLt : dirMask baseVertex (decodeVertex (k := k) g) < (2 : Nat) ^ t :=
      lt_of_lt_of_le hDirLt9 hPow
    have hMaskLt : maskAt k < (2 : Nat) ^ t :=
      lt_of_lt_of_le hMaskLt9 hPow
    simp [Nat.testBit_eq_false_of_lt hDirLt, Nat.testBit_eq_false_of_lt hMaskLt]

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def decodeBaseOrbit (k : DirIdx) (g : FreeCol k ↪ AvailFrom3) : BaseOrbit k :=
  ⟨decodeVertex (k := k) g, decodeVertex_mask (k := k) g⟩

theorem base_eq_of_colMatch {k : DirIdx} (u : BaseOrbit k) {j i : Fin 3}
    (h : colMatch (maskAt k) j = some i) : u.1.1 j = baseVertex.1 i := by
  -- Compare the `(i,j)` bit in the mask equality.
  have hm :
      (maskAt k).testBit (i.1 * 3 + j.1) = decide (colMatch (maskAt k) j = some i) := by
    exact maskAt_testBit_eq_decide_colMatch (d := k) (i := i) (j := j)
  have hm' : (maskAt k).testBit (i.1 * 3 + j.1) = true := by
    simp [hm, h]
  have hd' : (dirMask baseVertex u.1).testBit (i.1 * 3 + j.1) = true := by
    simpa [u.2] using hm'
  have hb :
      (dirMask baseVertex u.1).testBit (i.1 * 3 + j.1) = decide (baseVertex.1 i = u.1.1 j) := by
    exact dirMask_testBit (u := baseVertex) (v := u.1) (i := i) (j := j)
  have : decide (baseVertex.1 i = u.1.1 j) = true := by simpa [hb] using hd'
  have : baseVertex.1 i = u.1.1 j := of_decide_eq_true this
  simpa [eq_comm] using this

private theorem decode_encode_id (k : DirIdx) :
    ∀ u : BaseOrbit k, decodeBaseOrbit k (encodeBaseOrbit k u) = u := by
  intro u
  apply Subtype.ext
  apply Subtype.ext
  funext j
  classical
  cases hcol : colMatch (maskAt k) j with
  | none =>
      -- free coordinate
      have hcol' : colMatch (maskAt k) j = none := by simp [hcol]
      have h0 :
          (decodeBaseOrbit k (encodeBaseOrbit k u)).1.1 j
            = decodeTuple (k := k) (encodeBaseOrbit k u) j := rfl
      have h1 :
          decodeTuple (k := k) (encodeBaseOrbit k u) j = (encodeBaseOrbit k u ⟨j, hcol'⟩).1 := by
        simpa using
          (decodeTuple_of_colMatch_none (k := k) (g := encodeBaseOrbit k u) (j := j) hcol')
      have hDec :
          (decodeBaseOrbit k (encodeBaseOrbit k u)).1.1 j
            = (encodeBaseOrbit k u ⟨j, hcol'⟩).1 := by
        simpa [h0] using h1
      simpa [encodeBaseOrbit] using hDec
  | some i =>
      -- fixed coordinate
      have hi : colMatch (maskAt k) j = some i := by simp [hcol]
      have hUi : u.1.1 j = baseVertex.1 i := base_eq_of_colMatch (u := u) (j := j) (i := i) hi
      have h0 :
          (decodeBaseOrbit k (encodeBaseOrbit k u)).1.1 j
            = decodeTuple (k := k) (encodeBaseOrbit k u) j := rfl
      have h1 : decodeTuple (k := k) (encodeBaseOrbit k u) j = baseVertex.1 i := by
        simpa using
          (decodeTuple_of_colMatch_some (k := k) (g := encodeBaseOrbit k u) (j := j) (i := i) hi)
      have hDec : (decodeBaseOrbit k (encodeBaseOrbit k u)).1.1 j = baseVertex.1 i := by
        simpa [h0] using h1
      simpa [hUi] using hDec

private theorem encode_decode_id (k : DirIdx) :
    ∀ g : FreeCol k ↪ AvailFrom3, encodeBaseOrbit k (decodeBaseOrbit k g) = g := by
  intro g
  apply Function.Embedding.ext
  intro j
  apply Subtype.ext
  -- Both sides are equal as elements of `Fin n`.
  have h0 : (decodeBaseOrbit k g).1.1 j.1 = decodeTuple (k := k) g j.1 := rfl
  have h1 : decodeTuple (k := k) g j.1 = (g ⟨j.1, j.2⟩).1 :=
    decodeTuple_of_colMatch_none (k := k) (g := g) (j := j.1) j.2
  -- Unfold `encodeBaseOrbit` and use `h0,h1`.
  have : ((encodeBaseOrbit k (decodeBaseOrbit k g)) j).1 = (g ⟨j.1, j.2⟩).1 := by
    -- `encodeBaseOrbit` returns the underlying vertex value on its free columns.
    simpa [encodeBaseOrbit, h0] using congrArg id h1
  simpa using this

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def baseOrbit_equiv_embedding (k : DirIdx) :
    BaseOrbit k ≃ (FreeCol k ↪ AvailFrom3) where
  toFun := encodeBaseOrbit k
  invFun := decodeBaseOrbit k
  left_inv := decode_encode_id k
  right_inv := encode_decode_id k

theorem baseOrbit_card (k : DirIdx) : Fintype.card (BaseOrbit k) = baseTypeCount k := by
  classical
  -- Convert to embeddings of the free columns into the `n-3` outside symbols.
  have hEquiv : Fintype.card (BaseOrbit k) = Fintype.card (FreeCol k ↪ AvailFrom3) :=
    Fintype.card_congr (baseOrbit_equiv_embedding k)
  -- Count embeddings via falling factorial.
  have hEmb :
      Fintype.card (FreeCol k ↪ AvailFrom3)
        = (Fintype.card AvailFrom3).descFactorial (Fintype.card (FreeCol k)) := by
    exact Fintype.card_embedding_eq (α := FreeCol k) (β := AvailFrom3)
  -- Rewrite the RHS to match `baseTypeCount`.
  calc
    Fintype.card (BaseOrbit k)
        = Fintype.card (FreeCol k ↪ AvailFrom3) := hEquiv
    _ = (Fintype.card AvailFrom3).descFactorial (Fintype.card (FreeCol k)) := hEmb
    _ = (n - 3).descFactorial (freeCols (maskAt k)) := by
          simp [card_outside, card_freeCol]
    _ = baseTypeCount k := by
          simp [baseTypeCount]

end N1000000OrbitCounting

end Distributed2Coloring.LowerBound
