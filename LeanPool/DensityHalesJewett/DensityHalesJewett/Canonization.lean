/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.DensityHalesJewett.DensityHalesJewett.Subspace
import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.Finite.Sum

/-!
# Canonization of the constant letters

A word over the alphabet `Option α` is a word over `α` with variable positions marked by `none`;
its support is the set of variable positions.  Substituting such a word into a combinatorial
subspace gives `Subspace.wordMap`, which turns a subspace of dimension `ℓ` into a map from words
of length `ℓ` to words of length the ambient dimension.

The main result `exists_canonical` is the support canonization lemma of
`graham_rothschild_lines_from_mhj.tex`: after passing to a suitable `ℓ`-dimensional subspace, the
colour of a substituted word depends only on its support.  It is proved by induction on `ℓ`, one
application of the ordinary Hales--Jewett theorem per variable, each of them applied to the
profile of colours obtained by letting the remaining positions vary.
-/

@[expose] public section

open Finset
open Combinatorics

namespace DensityHalesJewett

/-- Two words over `Option α` have the same support when their variable positions agree. -/
def SameSupport {α ι : Type*} (x y : ι → Option α) : Prop := ∀ i, x i = none ↔ y i = none

namespace Line

variable {α ι : Type*}

/-- The word obtained from a line by substituting a letter, or the variable itself, at its
variable positions. -/
def fillOption (l : Combinatorics.Line α ι) (v : Option α) : ι → Option α :=
  fun i ↦ (l.idxFun i).elim v some

@[simp]
lemma fillOption_some (l : Combinatorics.Line α ι) (a : α) :
    fillOption l (some a) = some ∘ l a := by
  funext i
  cases h : l.idxFun i <;> simp [fillOption, Combinatorics.Line.coe_apply, h]

end Line

namespace Subspace

variable {α η θ ι : Type*}

/-- Substitute a word over `Option α` into a combinatorial subspace, marking variable positions
of the parameter word by `none`. -/
def wordMap (V : Combinatorics.Subspace η α ι) (x : η → Option α) : ι → Option α :=
  fun i ↦ Sum.elim some x (V.idxFun i)

lemma wordMap_compose (V : Combinatorics.Subspace η α ι) (W : Combinatorics.Subspace θ α η)
    (x : θ → Option α) : wordMap (compose V W) x = wordMap V (wordMap W x) := by
  funext i
  cases h : V.idxFun i <;> simp [wordMap, compose, h]

lemma composeLine_idxFun (V : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α η) :
    (composeLine V l).idxFun = wordMap V l.idxFun :=
  rfl

/-- Prepend a new variable direction, realized by a line on a fresh block of coordinates, to the
directions of a subspace. -/
def consLine {ℓ : ℕ} {B B' : Type*} (V : Combinatorics.Subspace (Fin ℓ) α B)
    (l : Combinatorics.Line α B') : Combinatorics.Subspace (Fin (ℓ + 1)) α (B ⊕ B') where
  idxFun := Sum.elim (fun b ↦ (V.idxFun b).map id Fin.succ)
    fun i ↦ (l.idxFun i).elim (Sum.inr 0) Sum.inl
  proper e := by
    induction e using Fin.cases with
    | zero =>
      obtain ⟨i, hi⟩ := l.proper
      exact ⟨Sum.inr i, by simp [hi]⟩
    | succ j =>
      obtain ⟨b, hb⟩ := V.proper j
      exact ⟨Sum.inl b, by simp [hb]⟩

lemma wordMap_consLine {ℓ : ℕ} {B B' : Type*} (V : Combinatorics.Subspace (Fin ℓ) α B)
    (l : Combinatorics.Line α B') (x : Fin (ℓ + 1) → Option α) :
    wordMap (consLine V l) x
      = Sum.elim (wordMap V fun i ↦ x i.succ) (Line.fillOption l (x 0)) := by
  funext i
  cases i with
  | inl b => cases h : V.idxFun b <;> simp [wordMap, consLine, h]
  | inr i => cases h : l.idxFun i <;> simp [wordMap, consLine, Line.fillOption, h]

/-- Embed the first `N` coordinates of a cube into a larger one, filling the remaining
coordinates with a fixed letter. -/
noncomputable def padInitial (α : Type*) [Nonempty α] {N n : ℕ} (h : N ≤ n) :
    Combinatorics.Subspace (Fin N) α (Fin n) where
  idxFun i := if hi : i.val < N then Sum.inr ⟨i.val, hi⟩ else Sum.inl (Classical.arbitrary α)
  proper e := ⟨Fin.castLE h e, by simp [Fin.castLE, e.isLt]⟩

end Subspace

namespace Canonization

variable {α : Type*}

open Subspace

/-- The inductive form of support canonization: for any block of positions preceding the
variables and any block of variable slots following them, there is a block of positions carrying
`ℓ` variables on which every colouring becomes a function of the support alone. -/
private lemma exists_canonical_aux (α : Type*) [Finite α] (C : Type*) [Finite C] (ℓ : ℕ) :
    ∀ (P S : Type) [Finite P] [Finite S], ∃ (B : Type) (_ : Finite B),
      ∀ χ : (P → Option α) → (B → Option α) → (S → Option α) → C,
        ∃ V : Combinatorics.Subspace (Fin ℓ) α B,
          ∀ (p : P → Option α) (s : S → Option α) (x y : Fin ℓ → Option α),
            SameSupport x y → χ p (wordMap V x) s = χ p (wordMap V y) s := by
  induction ℓ with
  | zero =>
    intro P S _ _
    refine ⟨PEmpty, inferInstance, ?_⟩
    intro χ
    refine ⟨⟨PEmpty.elim, ?_⟩, ?_⟩
    · intro e
      exact e.elim0
    · intro p s _ _ _
      exact congrArg (fun w ↦ χ p w s) (funext fun i ↦ i.elim)
  | succ ℓ ih =>
    intro P S _ _
    obtain ⟨B, _, hB⟩ := ih P (Unit ⊕ S)
    obtain ⟨B', _, hB'⟩ := Combinatorics.Line.exists_mono_in_high_dimension α
      ((P → Option α) → (B → Option α) → (S → Option α) → C)
    refine ⟨B ⊕ B', inferInstance, ?_⟩
    intro χ
    obtain ⟨l, prof, hprof⟩ := hB' fun u p b s ↦ χ p (Sum.elim b (some ∘ u)) s
    have hprof' : ∀ (a : α) (p : P → Option α) (b : B → Option α) (s : S → Option α),
        χ p (Sum.elim b (some ∘ l a)) s = prof p b s :=
      fun a p b s ↦ congrFun (congrFun (congrFun (hprof a) p) b) s
    obtain ⟨V, hV⟩ := hB fun p b q ↦
      χ p (Sum.elim b (Line.fillOption l (q (Sum.inl ())))) fun s ↦ q (Sum.inr s)
    refine ⟨consLine V l, ?_⟩
    intro p s x y hxy
    rw [wordMap_consLine, wordMap_consLine]
    apply Eq.trans (hV p (Sum.elim (fun _ ↦ x 0) s) (fun i ↦ x i.succ) (fun i ↦ y i.succ)
      fun i ↦ hxy i.succ)
    simp only [Sum.elim_inl, Sum.elim_inr]
    cases hx : x 0 with
    | none => rw [(hxy 0).1 hx]
    | some a =>
      cases hy : y 0 with
      | none => simp [(hxy 0).2 hy] at hx
      | some b =>
        rw [Line.fillOption_some, Line.fillOption_some, hprof' a, hprof' b]

/-- **Support canonization**: in a large enough cube every colouring of words over `Option α`
admits an `ℓ`-dimensional subspace on which the colour of a substituted word depends only on its
support. -/
lemma exists_canonical (α : Type*) [Finite α] (C : Type*) [Finite C] (ℓ : ℕ) :
    ∃ N : ℕ, ∀ χ : (Fin N → Option α) → C,
      ∃ V : Combinatorics.Subspace (Fin ℓ) α (Fin N),
        ∀ x y : Fin ℓ → Option α, SameSupport x y → χ (wordMap V x) = χ (wordMap V y) := by
  obtain ⟨B, _, hB⟩ := exists_canonical_aux α C ℓ PEmpty PEmpty
  have := Fintype.ofFinite B
  refine ⟨Fintype.card B, ?_⟩
  intro χ
  obtain ⟨V, hV⟩ := hB fun _ w _ ↦ χ (w ∘ (Fintype.equivFin B).symm)
  have hw (z : Fin ℓ → Option α) :
      wordMap (V.reindex (Equiv.refl _) (Equiv.refl _) (Fintype.equivFin B)) z
        = wordMap V z ∘ (Fintype.equivFin B).symm := by
    funext i
    cases h : V.idxFun ((Fintype.equivFin B).symm i) <;>
      simp [wordMap, Combinatorics.Subspace.reindex, h]
  refine ⟨V.reindex (Equiv.refl _) (Equiv.refl _) (Fintype.equivFin B), ?_⟩
  intro x y hxy
  rw [hw x, hw y]
  exact hV PEmpty.elim PEmpty.elim x y hxy

/-- Support canonization holds in every ambient dimension beyond the one it produces. -/
lemma exists_canonical_of_le (α : Type*) [Finite α] [Nonempty α] (C : Type*) [Finite C] (ℓ : ℕ) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ χ : (Fin n → Option α) → C,
      ∃ V : Combinatorics.Subspace (Fin ℓ) α (Fin n),
        ∀ x y : Fin ℓ → Option α, SameSupport x y → χ (wordMap V x) = χ (wordMap V y) := by
  obtain ⟨N, hN⟩ := exists_canonical α C ℓ
  refine ⟨N, ?_⟩
  intro n hn χ
  obtain ⟨V, hV⟩ := hN fun w ↦ χ (wordMap (padInitial α hn) w)
  refine ⟨compose (padInitial α hn) V, ?_⟩
  intro x y hxy
  rw [wordMap_compose, wordMap_compose]
  exact hV x y hxy

end Canonization
end DensityHalesJewett
