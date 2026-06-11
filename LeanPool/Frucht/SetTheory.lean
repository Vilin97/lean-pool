/-
Copyright (c) 2026 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
import Mathlib.Algebra.Order.Group.End
import Mathlib.Combinatorics.SimpleGraph.Maps
import LeanPool.Frucht.ClassicalReplacements

/-!
# Choice-free set theory on types

Develops the ZF-style membership, subset, transitive closure, and well-foundedness
structure on `Type u` (via the `collect`/`elements` axioms), together with the
`ConditionallyCompleteLattice` instance, providing the set-theoretic substrate for
the canonical pointed graphs used in the proof of Frucht's theorem.
-/

noncomputable section
universe u
open Relation

variable {x y z : Type u} {M : Set (Type u)}

@[classical] instance (priority := low) : CoeSort x (Type u) := ⟨elements (α := x)⟩

@[classical] instance : Membership (Type u) (Type u) where
  mem := fun y x => x ∈ Set.range ((↑) : y → Type u)

@[classical] instance : HasSubset (Type u) where
  Subset := fun x y => ∀ z ∈ x, z ∈ y

@[classical] instance : Membership M M where
  mem := fun y x => x.1 ∈ y.1

@[classical] lemma mem_class_iff {x y : M} : x ∈ y ↔ x.1 ∈ y.1 := Iff.rfl

section Definitions

variable (x y z M)

@[classical] def equivElements : x ≃ {y : Type u // y ∈ x} :=
  Equiv.ofInjective' (elements (α := x)) (elements_inj (α := x))

@[classical] def pairSet := collect <| fun
  | ULift.up false => x
  | ULift.up true => y

@[classical] def bigUnion := collect fun y : Sigma ((↑) : x → _) => elements y.2
@[classical] def powerset := collect fun y : Set x => collect fun z : y => (z : x)
@[classical] def separate (p : Type u → Prop) := collect fun y : {y : x | p y} => (y : x)
@[classical] def TransitiveClass := ∀ x ∈ M, ∀ y ∈ x, y ∈ M
@[classical] def IsTransitive := ∀ y ∈ x, ∀ z ∈ y, z ∈ x
@[classical] def IsTransitiveClosure :=
  x ∈ y ∧ IsTransitive y ∧ ∀ z, x ∈ z → IsTransitive z → y ⊆ z

end Definitions

@[classical] lemma mem_def : x ∈ y ↔ x ∈ Set.range ((↑) : y → Type u) := Iff.rfl
@[classical] lemma mem_iff : x ∈ y ↔ ∃ z : y, ↑z = x := Iff.rfl
@[classical] lemma subset_iff : x ⊆ y ↔ ∀ z ∈ x, z ∈ y := Iff.rfl

@[classical] lemma elements_mem (a : x) : ↑a ∈ x := by
  simp [mem_iff]

@[classical, simp]
lemma mem_collect {α} {f : α → Type u} : x ∈ collect f ↔ ∃ y : α, f y = x := by
  simp only [mem_iff]
  have := collect_elements (α := collect f)
  rw [collect_ext, Set.ext_iff] at this
  simpa using this x

@[classical] def castMem (h : x ∈ y) : y := (equivElements y).symm ⟨x, h⟩

@[classical] lemma range_elements_collect {α : Type u} (f : α → _) :
    Set.range ((↑) : collect f → _) = Set.range f := by
  rw [← collect_ext, collect_elements]

@[classical] def collectEquivRange {α : Type u} (f : α → _) : collect f ≃ Set.range f :=
  range_elements_collect f ▸ equivElements _

@[classical, simp] lemma elements_cast (h : x ∈ y) : ((castMem h : y) : Type u) = x := by
  simp only [castMem, equivElements, Equiv.ofInjective', Equiv.ofBijective', Equiv.symm_mk,
    Equiv.coe_fn_mk, Subtype.mk.injEq]
  generalize_proofs ex unique
  exact Exists.chooseUnique_spec ex unique

@[classical, simp] lemma cast_elements (a : x) : castMem (elements_mem a) = a := by
  apply elements_inj
  simp only [castMem, equivElements, Equiv.ofInjective', Equiv.ofBijective', Equiv.symm_mk,
    Equiv.coe_fn_mk, Subtype.mk.injEq]
  generalize_proofs ex unique
  exact Exists.chooseUnique_spec ex unique

@[classical] def moveSub (hy : y ⊆ x) (z : y) : x := castMem (hy _ (elements_mem z))

@[classical, simp]
lemma elements_moveSub (hy : y ⊆ x) (z : y) : ((moveSub hy z : x) : Type u) = z := by
  simp [moveSub]

@[classical] lemma ext_iff : x = y ↔ (∀ z, z ∈ x ↔ z ∈ y) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp [h]
  · simp only [← collect_elements (α := x), ← collect_elements (α := y),
      collect_ext, mem_collect] at h ⊢
    ext z
    exact h z

@[classical, ext] lemma ext : (∀ z, z ∈ x ↔ z ∈ y) → x = y := by
  simp [ext_iff]

@[classical] lemma mem_pair : z ∈ pairSet x y ↔ z = x ∨ z = y := by
  simp [pairSet]; tauto

@[classical, simp] lemma mem_bigUnion : y ∈ bigUnion x ↔ ∃ z ∈ x, y ∈ z := by
  simp only [bigUnion, mem_collect, Sigma.exists]
  refine ⟨fun ⟨a, b, h⟩ => ?_, fun ⟨z, hz, hz'⟩ => ?_⟩
  · use a
    simp [← h, elements_mem]
  · simp only [mem_iff] at hz hz'
    obtain ⟨a, ha⟩ := hz
    obtain ⟨b, hb⟩ := hz'
    cases ha
    cases hb
    use a, b

@[classical] lemma mem_powerset : y ∈ powerset x ↔ y ⊆ x := by
  simp only [powerset, mem_collect, subset_iff]
  refine ⟨fun ⟨z, hz⟩ w hw => ?_, fun w => ?_⟩
  · rw [← hz, mem_collect] at hw
    rw [mem_iff]
    obtain ⟨t, ht⟩ := hw
    use t.1
  · use {z : x | (z : Type u) ∈ y}
    ext z
    simp only [Set.coe_setOf, Set.mem_setOf_eq, mem_collect, Subtype.exists, exists_prop]
    refine ⟨fun ⟨a, ha, ha'⟩ => ?_, fun h => ?_⟩
    · rwa [← ha']
    · have h' := w _ h
      simp only [mem_iff] at h'
      obtain ⟨a, ha⟩ := h'
      exact ⟨a, by simpa [ha]⟩

@[classical] lemma mem_separate {p : Type u → Prop} : y ∈ separate x p ↔ y ∈ x ∧ p y := by
  simp only [separate, Set.coe_setOf, Set.mem_setOf_eq, mem_collect,
    Subtype.exists, exists_prop]
  refine ⟨fun ⟨a, ha, ha'⟩ => ?_, fun ⟨h, h'⟩ => ?_⟩
  · simp [← ha', ha, elements_mem]
  · rw [mem_iff] at h
    obtain ⟨a, ha⟩ := h
    exact ⟨a, by simpa [ha]⟩

@[classical] instance : EmptyCollection (Type u) where
  emptyCollection := collect PEmpty.elim
@[classical] instance : Singleton (Type u) (Type u) := ⟨fun x => pairSet x x⟩
@[classical] instance : Union (Type u) := ⟨fun x y => bigUnion (pairSet x y)⟩
@[classical] instance : Inter (Type u) := ⟨fun x y => separate x (fun z => z ∈ y)⟩

@[classical, simp] lemma mem_empty : x ∈ (∅ : Type u) ↔ False := by
  simp [EmptyCollection.emptyCollection]
@[classical, simp] lemma mem_singleton : y ∈ ({x} : Type u) ↔ y = x := by
  simp [Singleton.singleton, mem_pair]
@[classical] lemma union_eq_big_union : x ∪ y = bigUnion (pairSet x y) := rfl
@[classical] lemma inter_eq_separate : x ∩ y = separate x (fun z => z ∈ y) := rfl
@[classical, simp] lemma mem_union : z ∈ x ∪ y ↔ z ∈ x ∨ z ∈ y := by
  simp [union_eq_big_union, mem_bigUnion, mem_pair]
@[classical, simp] lemma mem_inter : z ∈ x ∩ y ↔ z ∈ x ∧ z ∈ y := by
  simp [inter_eq_separate, mem_separate]

@[classical] instance : IsPartialOrder (Type u) (· ⊆ ·) where
  refl := fun _ _ => by simp
  trans := fun a b c ha hb x hx => hb _ (ha _ hx)
  antisymm := by
    intro a b h h'
    ext x
    refine ⟨fun hx => h _ hx, fun hx => h' _ hx⟩

@[classical] instance : PartialOrder (Type u) where
  le := (· ⊆ ·)
  le_refl := subset_refl
  le_trans := fun a b c => subset_trans
  le_antisymm := fun a b => subset_antisymm

@[classical] lemma le_iff_subset : x ≤ y ↔ x ⊆ y := Iff.rfl

section collectSet

variable (S : Set (Type u)) [hS : Small.{u} S]

@[classical] def collectSet : Type u :=
  Exists.chooseUnique
    (show ∃ x, ∀ y, y ∈ x ↔ y ∈ S by
      obtain ⟨α, ⟨eq⟩⟩ := hS
      refine ⟨collect fun x : α => (eq.invFun x).1, fun y => ?_⟩
      simp only [Equiv.invFun_as_coe, mem_collect]
      refine ⟨fun ⟨a, ha⟩ => ?_, fun hy => ?_⟩
      · simp [← ha]
      · exact ⟨eq ⟨y, hy⟩, by simp⟩)
    (fun {a b} ha hb => by simp only [← hb] at ha; exact ext ha)

@[classical, simp] lemma mem_collectSet : x ∈ collectSet S ↔ x ∈ S := by
  simp only [collectSet]
  generalize_proofs h h'
  exact h.chooseUnique_spec h' x

open Classical in
@[classical] instance : SupSet (Type u) where
  sSup := fun S => if _ : Small.{u} S then bigUnion (collectSet S) else ∅

@[classical] lemma sSup_of_small : sSup S = bigUnion (collectSet S) := by
  simp [sSup, hS]

@[classical] lemma mem_sSup : x ∈ sSup S ↔ ∃ y ∈ S, x ∈ y := by
  simp [sSup_of_small, mem_collectSet]

@[classical] lemma sSup_mem_upperBounds' : sSup S ∈ upperBounds S := by
  intro α hα x hx
  simp only [mem_sSup]
  use α

end collectSet

@[classical] lemma bddAbove_iff {S : Set (Type u)} : BddAbove S ↔ Small.{u} S := by
  refine ⟨fun hS => ?_, fun hS => ?_⟩
  · obtain ⟨α, hα⟩ := hS
    simp only [upperBounds, le_iff_subset, ← mem_powerset, Set.mem_setOf_eq] at hα
    apply small_subset hα
  · refine ⟨sSup S, sSup_mem_upperBounds' S⟩

@[classical] lemma bddBelow_iff {S : Set (Type u)} : BddBelow S := by
  use ∅
  simp [lowerBounds, le_iff_subset, subset_iff, mem_empty]

@[classical] instance : ConditionallyCompleteLattice (Type u) :=
  conditionallyCompleteLatticeOfsSup (Type u)
    (by intro a b; rw [bddAbove_iff]; apply small_pair)
    (by intro a b; apply bddBelow_iff)
    (fun S hS ne => by
      rw [bddAbove_iff] at hS
      refine ⟨sSup_mem_upperBounds' S, ?_⟩
      intro x hx y hy
      simp only [sSup_of_small S, mem_bigUnion, mem_collectSet] at hy
      obtain ⟨z, hz, hy⟩ := hy
      exact hx hz _ hy)

@[classical] lemma mem_iSup {α : Type*} [Small.{u} α] (f : α → Type u) (x : Type u) :
    x ∈ iSup f ↔ ∃ i : α, x ∈ f i := by
  simp [iSup, sSup_of_small]

@[classical] lemma sup_eq : x ⊔ y = x ∪ y := by
  change sSup {x, y} = x ∪ y
  haveI : Small ({x, y} : Set _) := by apply small_pair
  rw [sSup_of_small]
  ext z
  simp

@[classical] lemma inf_eq : x ⊓ y = x ∩ y := by
  change sSup (lowerBounds {x, y}) = x ∩ y
  ext z
  haveI : Small (lowerBounds {x, y}) := by
    apply small_subset (s := Set.range ((↑) : powerset x → _))
    intro w hw
    simp only [lowerBounds_insert, lowerBounds_singleton] at hw
    change w ∈ powerset x
    rw [mem_powerset]
    exact hw.1
  rw [sSup_of_small]
  simp only [lowerBounds_insert, lowerBounds_singleton, mem_bigUnion, mem_collectSet, mem_inter]
  refine ⟨fun ⟨w, ⟨hx, hy⟩, hz⟩ => ?_, fun ⟨hx, hy⟩ => ?_⟩
  · exact ⟨hx _ hz, hy _ hz⟩
  · refine ⟨x ∩ y, ?_⟩
    simpa [le_iff_subset, subset_iff] using ⟨fun _ h _ => h, hx, hy⟩

@[classical] def trcl_step (x : Type u) : ℕ → Type u
  | 0 => x
  | n + 1 => bigUnion (trcl_step x n)

@[classical] def trcl (x : Type u) := ⨆ i : ℕ, trcl_step x i

@[classical] lemma mem_trcl_singleton_iff : y ∈ trcl {x} ↔ ReflTransGen (· ∈ ·) y x := by
  simp only [trcl, mem_iSup]
  refine ⟨fun ⟨i, hy⟩ => ?_, fun h => ?_⟩
  · induction i generalizing y with
    | zero =>
      simp only [trcl_step, mem_singleton] at hy
      simpa [hy] using .refl
    | succ i ih =>
      simp only [forall_exists_index] at ih
      simp only [trcl_step, mem_bigUnion] at hy
      obtain ⟨z, hz, hz'⟩ := hy
      exact .trans (.single hz') (ih _ hz hz)
  · induction h using ReflTransGen.head_induction_on with
    | refl => use 0; simp [trcl_step]
    | @head z w hz hw ih =>
      obtain ⟨i, ih⟩ := ih
      use i + 1
      simp only [trcl_step, mem_bigUnion]
      use w

@[classical] lemma sub_trcl_singleton : x ⊆ trcl {x} := by
  intro y hy
  rw [mem_trcl_singleton_iff]
  exact .single hy

@[classical] lemma sub_trcl : x ⊆ trcl x := by
  change trcl_step x 0 ≤ trcl x
  apply le_ciSup
  erw [bddAbove_iff]
  apply small_range

@[classical] lemma trcl_singleton_contains_self : x ∈ trcl {x} :=
  sub_trcl _ (by simp)

@[classical] lemma trcl_singleton_trans_of_mem (hxy : x ∈ y) (hax : y ∈ trcl {z}) :
    x ∈ trcl {z} := by
  rw [mem_trcl_singleton_iff] at hax ⊢
  exact .head hxy hax

@[classical] lemma trcl_singleton_trans (hxy : x ∈ trcl {y}) (hyz : y ∈ trcl {z}) :
    x ∈ trcl {z} := by
  rw [mem_trcl_singleton_iff] at hxy hyz ⊢
  exact .trans hxy hyz

@[classical] lemma isTransitiveClosure_trcl : IsTransitiveClosure x (trcl {x}) := by
  refine ⟨trcl_singleton_contains_self, ?_, ?_⟩
  · intro y hy z hz
    rw [mem_trcl_singleton_iff] at hy ⊢
    exact .head hz hy
  · intro y hy htrans z hz
    rw [mem_trcl_singleton_iff] at hz
    induction hz using ReflTransGen.head_induction_on with
    | refl => exact hy
    | @head z w hw _ hy => exact htrans _ hy _ hw

@[classical] lemma isTransitiveClosure_iff : IsTransitiveClosure x y ↔ y = trcl {x} := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' := isTransitiveClosure_trcl (x := x)
    exact le_antisymm (h.2.2 _ trcl_singleton_contains_self h'.2.1) (h'.2.2 _ h.1 h.2.1)
  · rw [h]
    apply isTransitiveClosure_trcl

@[classical] lemma mem_transitive
    {M : Set (Type u)} (htrans : TransitiveClass M) (hx : x ∈ M) (hy : y ∈ trcl {x}) :
    y ∈ M := by
  rw [mem_trcl_singleton_iff] at hy
  induction hy with
  | refl => assumption
  | @tail z x _ hz ih => exact ih (htrans _ hx _ hz)

@[classical] def WF : Set (Type u) := Acc (· ∈ ·)
@[classical] lemma well_founded_wf : IsWellFounded WF.{u} (· ∈ ·) :=
  ⟨Acc.wfRel.2⟩

@[classical] lemma transitive_wf : TransitiveClass WF := by
  intro x hx y hy
  induction hx with
  | @intro α hα _ => exact hα _ hy

lemma not_mem_self_wf {x : WF.{u}} : x ∉ x := by
  intro hx
  obtain ⟨y, hy, hmin⟩ := well_founded_wf.wf.has_min {x | x ∈ x} ⟨x, hx⟩
  exact hmin _ hy hy

@[classical] lemma heq_iff {α β} {a : α} {b : β} : HEq a b ↔ α = β ∧ (a : Type _) = b := by
  refine ⟨fun h => ?_, fun ⟨eq, h⟩ => ?_⟩
  · cases h
    simp
  · cases eq
    simpa using elements_inj h

@[classical] def FAFA₂ := ∀ (x y X Y : Type u),
  (hX : IsTransitiveClosure x X) → (hY : IsTransitiveClosure y Y) →
  (f : InvImage (· ∈ ·) ((↑) : X → Type u) ≃r InvImage (· ∈ ·) ((↑) : Y → Type u)) →
  (x' : X) → (hx : ↑x' = x) → (y' : Y) → (hx : ↑y' = y) →
  f x' = y' → x = y

@[classical] def Foundation := ∀ x : Type u, (∃ y, y ∈ x) → ∃ y, y ∈ x ∧ ∀ z ∈ x, z ∉ y

@[classical] def Frucht :=
  ∀ (Γ : Type u) [Group Γ], ∃ V : Type u, ∃ G : SimpleGraph V, Nonempty ((G ≃g G) ≃* Γ)
