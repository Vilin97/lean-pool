/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.DensityHalesJewett.DensityHalesJewett.Word
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Combinatorial subspaces

Ranges, containment, relative density, alphabet restriction, and lines inside mathlib's
`Combinatorics.Subspace`.
-/

@[expose] public section

open Finset Function
open Combinatorics

namespace DensityHalesJewett
namespace Subspace

variable {η α ι : Type*}

/-- Evaluation by a fixed combinatorial subspace is injective. -/
lemma injective (V : Combinatorics.Subspace η α ι) :
    Function.Injective V := by
  intro x y hxy
  funext e
  obtain ⟨i, hi⟩ := V.proper e
  simpa only [V.apply_inr hi] using congrFun hxy i

/-- The finite range of a combinatorial subspace. -/
def range [Fintype (η → α)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) : Finset (ι → α) :=
  Finset.univ.image V

@[simp]
lemma mem_range [Fintype (η → α)] [DecidableEq (ι → α)]
    {V : Combinatorics.Subspace η α ι} {w : ι → α} :
    w ∈ range V ↔ ∃ x, V x = w := by
  simp [range]

/-- A subspace is contained in a finite word family when all its evaluations belong to it. -/
def IsContained (V : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) : Prop :=
  ∀ x, V x ∈ A

/-- Compose a parameter subspace with an ambient subspace. -/
def compose (V : Combinatorics.Subspace η α ι) (W : Combinatorics.Subspace θ α η) :
    Combinatorics.Subspace θ α ι where
  idxFun i := (V.idxFun i).elim Sum.inl W.idxFun
  proper e := by
    obtain ⟨j, hj⟩ := W.proper e
    obtain ⟨i, hi⟩ := V.proper j
    refine ⟨i, ?_⟩
    simp only [hi, Sum.elim_inr, hj]

@[simp]
lemma compose_apply (V : Combinatorics.Subspace η α ι) (W : Combinatorics.Subspace θ α η)
    (x : θ → α) : compose V W x = V (W x) := by
  funext i
  cases hi : V.idxFun i <;> simp [compose, Combinatorics.Subspace.coe_apply, hi]

/-- Repeat the first `m` parameter directions to fill a larger `M`-coordinate cube. -/
def repeatInitial {m M : ℕ} (α : Type*) (hm : 1 ≤ m) (hmM : m ≤ M) :
    Combinatorics.Subspace (Fin m) α (Fin M) where
  idxFun i := Sum.inr <|
    if hi : i.val < m then ⟨i.val, hi⟩ else ⟨0, Nat.zero_lt_of_lt hm⟩
  proper e := by
    refine ⟨Fin.castLE hmM e, ?_⟩
    simp only [Fin.castLE, e.isLt, ↓reduceDIte]

@[simp]
lemma repeatInitial_map {β : Type*} {m M : ℕ} (α : Type*) (hm : 1 ≤ m) (hmM : m ≤ M)
    (f : β → α) (x : Fin m → β) :
    repeatInitial α hm hmM (f ∘ x) = f ∘ repeatInitial β hm hmM x := by
  funext i
  simp only [Function.comp_apply, (repeatInitial α hm hmM).apply_inr rfl,
    (repeatInitial β hm hmM).apply_inr rfl]

/-- Concatenate subspaces on disjoint coordinate blocks. -/
def concat (V : Combinatorics.Subspace η α ι) (W : Combinatorics.Subspace θ α κ) :
    Combinatorics.Subspace (η ⊕ θ) α (ι ⊕ κ) where
  idxFun := Sum.elim
    (fun i ↦ (V.idxFun i).elim Sum.inl (fun e ↦ Sum.inr <| Sum.inl e))
    (fun i ↦ (W.idxFun i).elim Sum.inl (fun e ↦ Sum.inr <| Sum.inr e))
  proper e := by
    cases e with
    | inl e =>
      obtain ⟨i, hi⟩ := V.proper e
      refine ⟨Sum.inl i, ?_⟩
      simp only [hi, Sum.elim_inl, Sum.elim_inr]
    | inr e =>
      obtain ⟨i, hi⟩ := W.proper e
      refine ⟨Sum.inr i, ?_⟩
      simp only [hi, Sum.elim_inr]

@[simp]
lemma concat_apply (V : Combinatorics.Subspace η α ι) (W : Combinatorics.Subspace θ α κ)
    (x : η → α) (y : θ → α) : concat V W (Sum.elim x y) =
      Sum.elim (V x) (W y) := by
  funext i
  cases i with
  | inl i => cases hi : V.idxFun i <;> simp [concat, Combinatorics.Subspace.coe_apply, hi]
  | inr i => cases hi : W.idxFun i <;> simp [concat, Combinatorics.Subspace.coe_apply, hi]

/-- Regard a line as a one-dimensional subspace parameterized by `Fin 1`. -/
def lineToSubspaceFinOne (l : Combinatorics.Line α ι) :
    Combinatorics.Subspace (Fin 1) α ι :=
  l.toSubspaceUnit.reindex finOneEquiv.symm (Equiv.refl _) (Equiv.refl _)

@[simp]
lemma lineToSubspaceFinOne_apply (l : Combinatorics.Line α ι) (x : Fin 1 → α) :
    lineToSubspaceFinOne l x = l (x 0) := by
  funext i
  simp [lineToSubspaceFinOne, Fin.eq_zero]

/-- Relative density on a subspace, defined on its parameter cube. -/
def relativeDensity [Fintype (η → α)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) : ℚ≥0 :=
  (Finset.univ.filter fun x ↦ V x ∈ A).dens

/-- Ambient line structures whose evaluations are contained in a subspace. -/
def Lines [Fintype (η → α)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) :=
  {l : Combinatorics.Line α ι // ∀ a, l a ∈ range V}

/-- Compose a parameter-cube line with a combinatorial subspace. -/
def composeLine (V : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α η) :
    Combinatorics.Line α ι where
  idxFun i := (V.idxFun i).elim some l.idxFun
  proper := by
    obtain ⟨e, he⟩ := l.proper
    obtain ⟨i, hi⟩ := V.proper e
    refine ⟨i, ?_⟩
    simp only [hi, Sum.elim_inr, he]

@[simp]
lemma composeLine_apply (V : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α η)
    (a : α) : composeLine V l a = V (l a) := by
  funext i
  cases hi : V.idxFun i <;>
    simp [composeLine, Combinatorics.Line.coe_apply, Combinatorics.Subspace.coe_apply, hi]

/-- Regard the composite of a parameter line with a subspace as a line in that subspace. -/
def composeLineToLines [Fintype (η → α)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α η) : Lines V :=
  ⟨composeLine V l, fun a ↦ mem_range.mpr ⟨l a, (composeLine_apply V l a).symm⟩⟩

/-- The canonical parameter word representing a point of a line contained in a subspace. -/
noncomputable def parameterWord [Fintype (η → α)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) (q : Lines V) (a : α) : η → α :=
  Classical.choose <| mem_range.mp (q.2 a)

lemma parameterWord_apply [Fintype (η → α)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) (q : Lines V) (a : α) :
    V (parameterWord V q a) = q.1 a :=
  Classical.choose_spec <| mem_range.mp (q.2 a)

/-- A chosen coordinate on which a subspace realizes a given parameter direction. -/
noncomputable def properCoordinate (V : Combinatorics.Subspace η α ι) (e : η) : ι :=
  Classical.choose <| V.proper e

lemma properCoordinate_spec (V : Combinatorics.Subspace η α ι) (e : η) :
    V.idxFun (properCoordinate V e) = Sum.inr e :=
  Classical.choose_spec <| V.proper e

/-- Recover the parameter-cube line underlying an ambient line contained in a subspace. -/
noncomputable def uncomposeLine [Fintype (η → α)] [DecidableEq (ι → α)] [Nontrivial α]
    (V : Combinatorics.Subspace η α ι) (q : Lines V) : Combinatorics.Line α η where
  idxFun e := q.1.idxFun (properCoordinate V e)
  proper := by
    obtain ⟨j, hj⟩ := q.1.proper
    cases hVj : V.idxFun j with
    | inl b =>
      obtain ⟨a, hab⟩ := exists_ne b
      refine absurd ?_ hab
      rw [← q.1.apply_none a j hj, ← parameterWord_apply V q a]
      exact V.apply_inl hVj
    | inr e =>
      cases hq : q.1.idxFun (properCoordinate V e) with
      | none => exact ⟨e, hq⟩
      | some c =>
        obtain ⟨a, hac⟩ := exists_ne c
        exact absurd (by rw [← q.1.apply_none a j hj, ← q.1.apply_some hq,
          ← parameterWord_apply V q a, V.apply_inr (properCoordinate_spec V e),
          V.apply_inr hVj]) hac

lemma uncomposeLine_apply [Fintype (η → α)] [DecidableEq (ι → α)] [Nontrivial α]
    (V : Combinatorics.Subspace η α ι) (q : Lines V) (a : α) :
    V (uncomposeLine V q a) = q.1 a := by
  funext i
  cases hi : V.idxFun i with
  | inl b => rw [V.apply_inl hi, ← parameterWord_apply V q a, V.apply_inl hi]
  | inr e =>
    rw [V.apply_inr hi]
    change q.1 a (properCoordinate V e) = q.1 a i
    rw [← parameterWord_apply V q a, V.apply_inr (properCoordinate_spec V e), V.apply_inr hi]

/-- Composition with a subspace identifies parameter-cube lines with ambient lines contained in
the subspace. -/
noncomputable def linesEquiv [Fintype (η → α)] [DecidableEq (ι → α)]
    [Nontrivial α] (V : Combinatorics.Subspace η α ι) :
    Combinatorics.Line α η ≃ Lines V where
  toFun := composeLineToLines V
  invFun := uncomposeLine V
  left_inv := by
    intro l
    apply Combinatorics.Line.coe_injective
    funext a
    apply injective V
    rw [uncomposeLine_apply]
    exact composeLine_apply V l a
  right_inv := by
    intro q
    apply Subtype.ext
    change composeLine V (uncomposeLine V q) = q.1
    apply Combinatorics.Line.coe_injective
    funext a
    rw [composeLine_apply]
    exact uncomposeLine_apply V q a

/-- Map a parameter-cube line to the corresponding ambient line in a subspace. -/
def mapLine (V : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α η) :
    Combinatorics.Line α ι :=
  composeLine V l

lemma mapLine_eq_composeLine (V : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α η) :
    mapLine V l = composeLine V l :=
  rfl

@[simp]
lemma mapLine_apply (V : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α η)
    (a : α) : mapLine V l a = V (l a) :=
  composeLine_apply V l a

/-- Restrict the variable letters of a subspace along an alphabet embedding. -/
def restrictAlphabet {β : Type*} [Fintype (η → β)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) (e : β ↪ α) : Finset (ι → α) :=
  Finset.univ.image fun x ↦ V (e ∘ x)

end Subspace

/-- Fix the coordinates outside a designated block, keeping a subspace on the block. -/
def transportSubspace {α η ι ω ν : Type*} (e : ι ≃ ω ⊕ ν) (z : ω → α)
    (V : Combinatorics.Subspace η α ν) : Combinatorics.Subspace η α ι where
  idxFun c := Sum.elim (fun a ↦ Sum.inl (z a)) V.idxFun (e c)
  proper x := by
    obtain ⟨c, hc⟩ := V.proper x
    exact ⟨e.symm (Sum.inr c), by simp only [Equiv.apply_symm_apply, Sum.elim_inr, hc]⟩

@[simp]
lemma transportSubspace_apply {α η ι ω ν : Type*} (e : ι ≃ ω ⊕ ν) (z : ω → α)
    (V : Combinatorics.Subspace η α ν) (x : η → α) :
    transportSubspace e z V x = Sum.elim z (V x) ∘ e := by
  funext c
  simp only [Combinatorics.Subspace.coe_apply, transportSubspace, Function.comp_apply]
  cases e c <;> simp only [Sum.elim_inl, Sum.elim_inr, id_eq, Combinatorics.Subspace.coe_apply]

/-- The preimage of a word family in a subspace parameter cube. -/
noncomputable def parameterPreimage {η α ι : Type*} [Fintype (η → α)]
    (V : Combinatorics.Subspace η α ι) (D : Finset (ι → α)) : Finset (η → α) := by
  classical
  apply Finset.univ.filter
  intro x
  exact V x ∈ D

end DensityHalesJewett
