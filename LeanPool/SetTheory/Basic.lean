/-
Copyright (c) 2026 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
import LeanPool.SetTheory.Realize
import Mathlib.SetTheory.ZFC.VonNeumann

/-!
# Basic theory of models of ZF set theory

This module develops the order-theoretic and membership structure on models of ZF,
including the von Neumann hierarchy and foundational lemmas used throughout the Kunen
inconsistency development.
-/

noncomputable section

variable {M N M₀ : Type _} [ZFStructure M] [ZFStructure N] [ZFStructure M₀]

open Subtype in
attribute [instance low] instLE instLT instLawfulOrderLT instMin instMax instReflLE instAntisymmLE
  instTotalLE Subtype.instTransLE instMinEqOr instLawfulOrderMin instMaxEqOr instLawfulOrderMax
  instIsPreorder instIsLinearPreorder instIsPartialOrder instIsLinearOrder preorder partialOrder
  decidableLE decidableLT

open Order ZFSet Function Cardinal

section FirstOrder

open FirstOrder Language

variable {v₁ : Fin 1 → M} {v₂ : Fin 2 → M}

/-- The `formula` declaration. -/
def Membership.mem.formula : ZFFormula 2 := #1 ∈ᶻ' #0
@[realize_simps, realize]
lemma Membership.mem.realize_iff : formula.Realize v₂ ↔ v₂ 1 ∈ v₂ 0 := by
  simp [formula, Formula.Realize, realize_simps]

/-- The `formula` declaration. -/
def Ne.formula : ZFFormula 2 := ∼(#0 =' #1)
@[realize_simps, realize]
lemma Ne.realize_iff : formula.Realize v₂ ↔ v₂ 0 ≠ v₂ 1 := by
  simp [formula, Formula.Realize]

/-- The `formula` declaration. -/
def Eq.formula : ZFFormula 2 := #0 =' #1
@[realize_simps, realize]
lemma Eq.realize_iff : formula.Realize v₂ ↔ v₂ 0 = v₂ 1 := by
  simp [formula, Formula.Realize, realize_simps]

/-- The `formula` declaration. -/
def HasSubset.Subset.formula : ZFFormula 2 := ∀' (&0 ∈ᶻ' #0 ⟹ &0 ∈ᶻ' #1)
@[realize_simps, realize]
lemma HasSubset.Subset.realize_iff : formula.Realize v₂ ↔ v₂ 0 ⊆ v₂ 1 := by
  simp [formula, Formula.Realize, realize_simps, Fin.snoc]
  rfl

variable [HasEmpty M]

@[simp] lemma EmptyCollection.emptyCollection.spec : ∀ x, x ∉ (∅ : M) :=
  HasEmpty.exists_empty.choose_spec.1

lemma EmptyCollection.emptyCollection.eq_iff (x : M) : (∅ : M) = x ↔ ∀ y, y ∉ x :=
  HasEmpty.exists_empty.choose_eq_iff

/-- The `formula` declaration. -/
def EmptyCollection.emptyCollection.formula : ZFFormula 1 := EqEmptyN 0

@[realize_simps] lemma EmptyCollection.emptyCollection.realize_iff :
    formula.Realize v₁ ↔ ∅ = v₁ 0 := by
  simp [formula, EqEmptyN.realize_iff]

@[realize] lemma EmptyCollection.emptyCollection.eu : ∃! x : M, ∀ y : M, y ∉ x :=
  HasEmpty.exists_empty

end FirstOrder

namespace SetTheory

/-- The von Neumann universe `V` carrier, wrapping a ground-model `ZFSet`. -/
structure V where
  /-- The underlying `ZFSet` of an element of `V`. -/
  val : ZFSet.{0}

@[ext] lemma V.ext (x y : V) : x.val = y.val → x = y := by cases x; cases y; simp

/-- The `ToV` type. -/
class ToV (α : Type*) where
  /-- The `toV` declaration. -/
  toV : α → V
open ToV

/-- The `toZFSet` declaration. -/
def toZFSet {α} [ToV α] (x : α) : ZFSet.{0} := (toV x).val

/-- The `↓_` notation. -/
prefix:max "↓" => toV
/-- The `⇓_` notation. -/
prefix:max "⇓" => toZFSet

instance : ToV ZFSet.{0} := ⟨fun x => ⟨x⟩⟩

instance structureZFSet {A : ZFSet.{0}} : 𝓛ZF.Structure A where
  RelMap | .mem => fun x => (x 0).1 ∈ (x 1).1

lemma mem_inside_ZFSet {A : ZFSet} {x y : A} : x ∈ y ↔ x.1 ∈ y.1 := Iff.rfl

instance structureV : 𝓛ZF.Structure V where
  RelMap | .mem => fun x => (x 0).1 ∈ (x 1).1

/-- The `IsVonNeumann` type. -/
@[class] inductive IsVonNeumann (α) [s : ZFStructure α]
  | vonNeumann (μ) (hμ : IsSuccLimit μ) (eq : Sigma.mk α s = ⟨V_ μ, structureZFSet⟩)
  | V (eq : Sigma.mk α s = ⟨V, structureV⟩)

open Ordinal in
/-- The `IsVonNeumannWithOmega` type. -/
@[class] inductive IsVonNeumannWithOmega (α) [s : ZFStructure α]
  | vonNeumann (μ) (hμ : IsSuccLimit μ)
    (omega_lt_μ : ω < μ) (eq : Sigma.mk α s = ⟨V_ μ, structureZFSet⟩)
  | V (eq : Sigma.mk α s = ⟨V, structureV⟩)

end SetTheory

open SetTheory

variable [hM : IsVonNeumann M] [hN : IsVonNeumann N] [hM₀ : IsVonNeumannWithOmega M₀]

/-- Case-split on the proof `h : IsVonNeumann M`, introducing `μ` and `hμ` in the
successor-limit case and discharging the `V` case, then registering the limit fact. -/
macro "split_vonNeumann" h:ident : tactic => do
  let μ := Lean.mkIdent `μ
  let hμ := Lean.mkIdent `hμ
  `(tactic | (rcases $h:ident with ⟨$μ, $hμ, ⟨_⟩⟩ | ⟨⟨_⟩⟩; haveI _ := Fact.mk $hμ))

/-- Like `split_vonNeumann`, but for `IsVonNeumannWithOmega M`, additionally
introducing the hypothesis `omega_lt_μ` that `ω < μ`. -/
macro "split_vonNeumann_omega" h:ident : tactic => do
  let μ := Lean.mkIdent `μ
  let hμ := Lean.mkIdent `hμ
  let omega_lt_μ := Lean.mkIdent `omega_lt_μ
  `(tactic | (rcases $h:ident with ⟨$μ, $hμ, $omega_lt_μ, ⟨_⟩⟩ | ⟨⟨_⟩⟩; haveI _ := Fact.mk $hμ))

namespace SetTheory

instance : IsVonNeumann M₀ := by
  split_vonNeumann_omega hM₀
  · exact .vonNeumann μ hμ rfl
  · exact .V rfl

instance {μ} [hμ : Fact (IsSuccLimit μ)] : IsVonNeumann (V_ μ) :=
  .vonNeumann μ hμ.out rfl

instance : IsVonNeumannWithOmega V := .V rfl

instance : ToV M where
  toV x := by
    split_vonNeumann hM
    · exact ⟨x.1⟩
    · exact x

namespace ToV

@[toV_simps] lemma reduce_mem {x y : M} : ↓x ∈ ↓y ↔ x ∈ y := by
  split_vonNeumann hM <;> exact Iff.rfl

@[toV_simps] lemma reduce_eq {x y : M} : ↓x = ↓y ↔ x = y := by
  split_vonNeumann hM
  · simp [toV]
  · exact Iff.rfl

@[toV_simps] lemma reduce_ne {x y : M} : ↓x ≠ ↓y ↔ x ≠ y := reduce_eq.not

@[toV_simps] lemma forall_mem_toV {x : M} {p : V → Prop} :
    (∀ y ∈ ↓x, p y) ↔ (∀ y ∈ x, p ↓y) := by
  split_vonNeumann hM
  · exact ⟨
      fun h _ hy => h _ hy,
      fun h y hy => h ⟨⇓y, isTransitive_vonNeumann _ _ x.2 hy⟩ hy
    ⟩
  · exact Iff.rfl

@[toV_simps] lemma reduce_subset {x y : M} : ↓x ⊆ ↓y ↔ x ⊆ y := by
  simp only [HasSubset.Subset, toV_simps]

@[toV_simps] lemma forall_mem_toV_iff
    {x : M} {p : V → Prop} (hp : ∀ y, p y → ∃ z : M, ↓z = y) :
    (∀ y, y ∈ ↓x ↔ p y) ↔ (∀ y, y ∈ x ↔ p ↓y) := by
  conv_rhs => enter [y]; rw [← reduce_mem]
  split_vonNeumann hM
  · refine ⟨
      fun h y => ⟨fun hy => (h _).mp hy, fun hy => (h _).mpr hy⟩,
      fun h y => ⟨fun hy => (h ⟨⇓y, isTransitive_vonNeumann _ _ x.2 hy⟩).mp hy, fun hy => ?_⟩
    ⟩
    obtain ⟨z, hz⟩ := hp _ hy
    exact hz ▸ (h z).mpr (hz ▸ hy)
  · exact Iff.rfl

@[toV_simps] lemma exists_mem_toV {x : M} {p : V → Prop} :
    (∃ y ∈ ↓x, p y) ↔ (∃ y ∈ x, p ↓y) := by
  simp only [← Classical.not_forall_not, not_and]
  congr! 1
  exact forall_mem_toV

end ToV

namespace ToZFSet

@[toZFSet_simps high] lemma toZFSet_toV {x : M} : ⇓↓x = ⇓x := rfl
@[toZFSet_simps] lemma toV_vonNeumann {μ} [Fact (IsSuccLimit μ)] {x : V_ μ} : ↓x = ⟨x.1⟩ := rfl
@[toZFSet_simps] lemma toV_V {x : V} : ↓x = ⟨x.1⟩ := rfl
@[toZFSet_simps] lemma toV_ZFSet {x : ZFSet} : ↓x = ⟨x⟩ := rfl
@[toZFSet_simps] lemma toZFSet_vonNeumann {μ} [Fact (IsSuccLimit μ)] {x : V_ μ} : ⇓x = x.1 := rfl
@[toZFSet_simps] lemma toZFSet_V {x : V} : ⇓x = x.1 := rfl
@[toZFSet_simps] lemma «forall» {p : V → Prop} : (∀ x, p x) ↔ ∀ x : ZFSet, p ↓x := by aesop
@[toZFSet_simps] lemma «exists» {p : V → Prop} : (∃ x, p x) ↔ ∃ x : ZFSet, p ↓x := by aesop

@[toZFSet_simps] lemma mem {x : M} {y : M} : x ∈ y ↔ ⇓x ∈ ⇓y := by
  split_vonNeumann hM <;> exact Iff.rfl

@[toZFSet_simps] lemma subset {x : M} {y : M} : x ⊆ y ↔ ⇓x ⊆ ⇓y := by
  rw [← ToV.reduce_subset]
  simp [Subset, ZFSet.Subset, toZFSet_simps]

@[toZFSet_simps] lemma eq {x y : M} : x = y ↔ ⇓x = ⇓y := by
  split_vonNeumann hM
  · exact Subtype.ext_iff
  · cases x; cases y; exact Iff.of_eq (V.mk.injEq _ _)

@[toZFSet_simps] lemma ne {x y : M} : x ≠ y ↔ ⇓x ≠ ⇓y := eq.not

end ToZFSet

instance : Std.Refl (α := M) (· ⊆ ·) := by constructor; simp [Subset]

@[ext] lemma ext {x y : M} (eq : ∀ z : M, z ∈ x ↔ z ∈ y) : x = y := by
  split_vonNeumann hM
  · rw [Subtype.ext_iff, ZFSet.ext_iff]
    convert_to ∀ z : V, z ∈ ↓x ↔ z ∈ ↓y
    · simp only [toZFSet_simps]
    · rwa [ToV.forall_mem_toV_iff]
      exact fun z hz => ⟨⟨⇓z, isTransitive_vonNeumann _ _ y.2 hz⟩, rfl⟩
  · revert x y eq
    simpa only [toZFSet_simps] using fun _ _ => ZFSet.ext

lemma ext_of_subset {X A B : M}
    (A_sub : A ⊆ X) (B_sub : B ⊆ X) (ext : ∀ x ∈ X, x ∈ A ↔ x ∈ B) : A = B := by
  ext x
  exact ⟨fun hx => (ext _ (A_sub hx)).mp hx, fun hx => (ext _ (B_sub hx)).mpr hx⟩

instance instSetLike : SetLike M M where
  coe := fun x => {y | y ∈ x}
  coe_injective := fun x y eq => by
    simp only [Set.ext_iff, Set.mem_setOf_eq] at eq
    exact ext eq

instance instPartialOrderM : PartialOrder M := PartialOrder.ofSetLike M M

lemma le_def {x y : M} : x ≤ y ↔ x ⊆ y := Iff.rfl
lemma le_iff {x y : M} : x ≤ y ↔ ∀ ⦃z : M⦄, z ∈ x → z ∈ y := Iff.rfl
lemma mem_of_le {x y z : M} (hsub : x ≤ y) (hz : z ∈ x) : z ∈ y := hsub hz
lemma mem_coe {x y : M} : x ∈ (y : Set M) ↔ x ∈ y := SetLike.mem_coe
lemma lt_iff_le_and_exists {x y : M} : x < y ↔ x ≤ y ∧ ∃ z ∈ y, z ∉ x :=
  SetLike.lt_iff_le_and_exists

@[toZFSet_simps] lemma ToZFSet.le (x y : M) : x ≤ y ↔ ⇓x ≤ ⇓y := by
  change x ⊆ y ↔ ⇓x ⊆ ⇓y
  simp only [toZFSet_simps]

@[toZFSet_simps] lemma ToZFSet.lt (x y : M) : x < y ↔ ⇓x < ⇓y := by
  simp only [lt_iff_le_and_ne, toZFSet_simps]

attribute [formula_builder_pre, formula_builder] Set.mem_setOf_eq
/-- The `IsSet` declaration. -/
@[formula_builder_pre] def IsSet (C : Set M) := ∃! x : M, ∀ y, y ∈ x ↔ y ∈ C

lemma isSet_iff_exists_set {C : Set M} : IsSet C ↔ ∃ x : M, ∀ y, y ∈ x ↔ y ∈ C := by
  refine ⟨fun | ⟨x, hx⟩ => ⟨x, hx.1⟩, fun | ⟨x, hx⟩ => ⟨x, hx, fun y hy => ?_⟩⟩
  ext z
  refine ⟨fun hz => ?_, fun hz => ?_⟩ <;> (
    simp only [hx, hy] at hz ⊢
    exact hz
  )

lemma not_mem_self {x : M} : x ∉ x := by
  simpa [toZFSet_simps] using mem_irrefl _

open Classical in
lemma exists_separate (x : M) (p : M → Prop) : IsSet {y | y ∈ x ∧ p y} := by
  rw [isSet_iff_exists_set]
  split_vonNeumann hM
  · refine ⟨⟨x.1.sep fun y => if hy : y ∈ V_ μ then p ⟨y, hy⟩ else True, ?_⟩, ?_⟩
    · exact mem_vonNeumann_of_subset sep_subset x.2
    · simp [toZFSet_simps]
  · revert x p
    simpa only [toZFSet_simps] using fun x p =>
      ⟨ZFSet.sep (fun x => p (↓x)) x, fun _ => ZFSet.mem_sep⟩

/-- The `separate` declaration. -/
def separate (x : M) (p : M → Prop) := (exists_separate x p).choose

@[simp] lemma mem_separate_iff {x : M} {p : M → Prop} : ∀ z, z ∈ separate x p ↔ z ∈ x ∧ p z :=
  (exists_separate x p).choose_spec.1

lemma separate_sub {x : M} {p : M → Prop} : separate x p ⊆ x := by
  simp [Subset]; tauto

lemma isSet_iff {C : Set M} : IsSet C ↔ (∃ x : M, ∀ y, y ∈ C → y ∈ x) := by
  simpa only [isSet_iff_exists_set] using ⟨
    fun | ⟨x, hx⟩ => ⟨x, fun y hy => (hx y).mpr hy⟩,
    fun | ⟨x, hx⟩ => ⟨separate x (· ∈ C), by simpa⟩
  ⟩

instance : HasEmpty M where
  exists_empty := by
    simp only [← iff_false]
    change IsSet {x | False}
    simp only [isSet_iff, Set.mem_setOf_eq, IsEmpty.forall_iff, implies_true,
      exists_const_iff, and_true]
    split_vonNeumann hM
    · refine ⟨∅, mem_vonNeumann.mpr ?_⟩
      simpa only [rank_empty, pos_iff_ne_zero] using (Ordinal.isSuccLimit_iff.mp hμ).1
    · exact ⟨↓(∅ : ZFSet)⟩

@[toV_simps] lemma empty.toV : ∅ = ↓(∅ : M) := by
  simpa only [EmptyCollection.emptyCollection.eq_iff, toV_simps]
    using EmptyCollection.emptyCollection.spec

@[toZFSet_simps] lemma empty.toZFSet : ⇓(∅ : M) = ∅ := by
  simp (config := {singlePass := true}) only [← ToZFSet.toZFSet_toV]
  simpa only [ZFSet.ext_iff, notMem_empty, iff_false, ← empty.toV, toZFSet_simps]
    using EmptyCollection.emptyCollection.spec (M := V)

lemma mem_vonNeumann_powerset {μ x} (hμ : IsSuccLimit μ) (hx : x ∈ V_ μ) :
    powerset x ∈ V_ μ := by
  simp only [mem_vonNeumann, rank_powerset] at hx ⊢
  exact hμ.add_one_lt hx

lemma mem_vonNeumann_singleton {μ x} (hμ : IsSuccLimit μ) (hx : x ∈ V_ μ) : {x} ∈ V_ μ := by
  refine mem_vonNeumann_of_subset (fun y hy => ?_) (mem_vonNeumann_powerset hμ hx)
  simp only [mem_singleton] at hy
  simp [hy]

lemma mem_vonNeumann_union {μ} {x y : ZFSet} (hx : x ∈ V_ μ) (hy : y ∈ V_ μ) : x ∪ y ∈ V_ μ := by
  simp only [mem_vonNeumann, rank_union] at hx hy ⊢
  simp [hx, hy]

@[realize] lemma powerset.eu (x : M) : IsSet {y | y ⊆ x} := by
  rw [isSet_iff]
  split_vonNeumann hM
  · exact ⟨⟨powerset x, mem_vonNeumann_powerset hμ x.2⟩, by simp [toZFSet_simps]⟩
  · revert x
    simpa only [toZFSet_simps] using fun x => ⟨x.powerset, by simp⟩

attribute [simp] powerset.spec
/-- The `𝓟_` declaration. -/
prefix:max "𝓟 " => powerset

@[toV_simps] lemma powerset.toV (x : M) : 𝓟 ↓x = ↓(𝓟 x) := by
  symm
  simp only [SetTheory.ext_iff, powerset.spec]
  rw [ToV.forall_mem_toV_iff]
  · simp [powerset.spec, toV_simps]
  · intro z hz
    split_vonNeumann hM
    · simp only [toZFSet_simps] at hz
      exact ⟨⟨_, mem_vonNeumann_of_subset hz x.2⟩, rfl⟩
    · exact ⟨z, rfl⟩

@[realize] lemma singleton.eu (x : M) : IsSet {y | y = x} := by
  rw [isSet_iff]
  split_vonNeumann hM
  · refine ⟨⟨{x.1}, mem_vonNeumann_singleton hμ x.2⟩, ?_⟩
    simp only [toZFSet_simps]
    simp
  · revert x
    simpa only [toZFSet_simps] using fun x => ⟨{x}, by simp⟩

@[realize] lemma insert.eu (x y : M) : IsSet {z | z = x ∨ z ∈ y} := by
  rw [isSet_iff]
  split_vonNeumann hM
  · refine ⟨⟨{x.1} ∪ y.1, mem_vonNeumann_union (mem_vonNeumann_singleton hμ x.2) y.2⟩, ?_⟩
    simp only [toZFSet_simps]
    simp
  · revert x y
    simpa only [toZFSet_simps] using fun x y => ⟨{x} ∪ y, by simp⟩

end SetTheory

section FirstOrder

open FirstOrder Language

/-- The `formula` declaration. -/
def LE.le.formula : ZFFormula 2 := ∀' (&0 ∈ᶻ' #0 ⟹ &1 ∈ᶻ' #1)
@[realize_simps, realize]
lemma LE.le.realize_iff {v : Fin 2 → M} : formula.Realize v ↔ v 0 ≤ v 1 := by
  simp [LE.le.formula, Formula.Realize, realize_simps, Fin.snoc]
  tauto

/-- The `formula` declaration. -/
def LT.lt.formula : ZFFormula 2 := ∀' (&0 ∈ᶻ' #0 ⟹ &1 ∈ᶻ' #1) ⊓ ∼(#0 =' #1)
@[realize_simps, realize]
lemma LT.lt.realize_iff {v : Fin 2 → M} : formula.Realize v ↔ v 0 < v 1 := by
  simp [LT.lt.formula, Formula.Realize, realize_simps, Fin.snoc, lt_iff_le_and_ne]
  tauto

instance instSingletonMM : Singleton M M where singleton := SetTheory.singleton
@[simp] lemma Singleton.singleton.spec (x y : M) : y ∈ ({x} : M) ↔ y = x :=
  SetTheory.singleton.spec ..
lemma Singleton.singleton.eq_iff (x y : M) : ({x} : M) = y ↔ ∀ z, z ∈ y ↔ z = x :=
  SetTheory.singleton.eq_iff ..
/-- The `formula` declaration. -/
def Singleton.singleton.formula := SetTheory.singleton.formula
@[realize_simps] lemma Singleton.singleton.realize_iff (v : Fin 2 → M) :
    formula.Realize v ↔ {v 0} = v 1 := SetTheory.singleton.realize_iff v
@[realize] lemma Singleton.singleton.eu (x : M) : IsSet {y | y = x} :=
  SetTheory.singleton.eu x

instance instInsertMM : Insert M M where insert := SetTheory.insert
@[simp] lemma Insert.insert.spec (x y z : M) : z ∈ insert x y ↔ z = x ∨ z ∈ y :=
  SetTheory.insert.spec ..
lemma Insert.insert.eq_iff (x y z : M) : Insert.insert x y = z ↔ ∀ w, w ∈ z ↔ w = x ∨ w ∈ y :=
  SetTheory.insert.eq_iff ..
/-- The `formula` declaration. -/
def Insert.insert.formula := SetTheory.insert.formula
@[realize_simps] lemma Insert.insert.realize_iff (v : Fin 3 → M) :
    formula.Realize v ↔ insert (v 0) (v 1) = v 2 := SetTheory.insert.realize_iff v
@[realize] lemma Insert.insert.eu (x y : M) : IsSet {z | z = x ∨ z ∈ y} :=
  SetTheory.insert.eu x y

end FirstOrder

namespace SetTheory

@[toV_simps] lemma singleton.toV {x} : {↓x} = ↓({x} : M) := by
  rw [Singleton.singleton.eq_iff, ToV.forall_mem_toV_iff]
  · simpa only [toV_simps] using Singleton.singleton.spec _
  · rintro z ⟨_⟩
    exact ⟨x, rfl⟩

@[toZFSet_simps] lemma singleton.toZFSet {x} : ⇓({x} : M) = {⇓x} := by
  simp (config := {singlePass := true}) only [← ToZFSet.toZFSet_toV]
  simpa only [ZFSet.ext_iff, mem_singleton, singleton.toV, toZFSet_simps]
    using Singleton.singleton.spec ↓x

lemma mem_singleton (x : M) : x ∈ ({x} : M) := by simp
lemma singleton_subset_iff (x y : M) : {x} ⊆ y ↔ x ∈ y := by simp [Subset]

lemma exists_toZFSet_of_mem {x : M} {y : ZFSet} (hy : y ∈ ⇓x) : ∃ z : M, ⇓z = y := by
  split_vonNeumann hM
  · exact ⟨⟨_, isTransitive_vonNeumann _ _ x.2 hy⟩, rfl⟩
  · exact ⟨↓y, rfl⟩

lemma exists_toV_of_mem {x : M} {y : V} (hy : y ∈ ↓x) : ∃ z : M, ↓z = y := by
  revert x
  simp only [toZFSet_simps]
  exact exists_toZFSet_of_mem

@[toV_simps] lemma insert.toV {x y : M} : Insert.insert ↓x ↓y = ↓(Insert.insert x y) := by
  rw [Insert.insert.eq_iff, ToV.forall_mem_toV_iff]
  · simpa only [toV_simps] using Insert.insert.spec _ _
  · rintro z (⟨⟨_⟩⟩ | hz)
    · exact ⟨x, rfl⟩
    · exact exists_toV_of_mem hz

@[toZFSet_simps] lemma insert.toZFSet {x y : M} : ⇓(Insert.insert x y) = Insert.insert ⇓x ⇓y := by
  simp (config := {singlePass := true}) only [← ToZFSet.toZFSet_toV]
  simpa only [ZFSet.ext_iff, mem_insert_iff, insert.toV, toZFSet_simps]
    using Insert.insert.spec ↓x ↓y

/-- The `ExistsUniqueAt` declaration. -/
def ExistsUniqueAt {α : Type*} (x : α) (p : α → Prop) := p x ∧ ∀ y, p y → y = x

@[formula_builder] lemma isGLB_iff {C : Set M} {x : M} :
    IsGLB C x ↔ ∀ y, y ∈ x ↔ ∀ t ∈ C, y ∈ t := by
  simp only [IsGLB, IsGreatest, lowerBounds, Set.mem_setOf_eq, upperBounds]
  exact ⟨
    fun | ⟨is_bound, greatest⟩, y => ⟨
      fun y t ht => is_bound ht y,
      fun hy => greatest (a := {y}) (by simpa [le_iff]) (Singleton.singleton.spec y y |>.mpr rfl)
    ⟩,
    fun h => ⟨
      fun t ht z hz => (h _).mp hz _ ht,
      fun y hy z hz => (h _).mpr fun t ht => hy ht hz
    ⟩
  ⟩

lemma isLUB_iff {C : Set M} {x : M} : IsLUB C x ↔ ∀ y, y ∈ x ↔ ∃ t ∈ C, y ∈ t := by
  simp only [IsLUB, IsLeast, upperBounds, Set.mem_setOf_eq, lowerBounds]
  refine ⟨
    fun | ⟨is_bound, least⟩, y => ⟨
      fun hy => ?_,
      fun | ⟨t, ht, hy⟩ => is_bound ht hy
    ⟩,
    fun hx => ⟨
      fun t ht y hy => (hx y).mpr ⟨_, ht, hy⟩,
      fun y hy z hz => ((hx z).mp hz).casesOn fun | t, ⟨ht, hz'⟩ => hy ht hz'
    ⟩
  ⟩
  by_contra! y_not_in_sUnion
  replace least := mem_of_le (least (a := separate x (· ≠ y)) ?_) hy
  · simp at least
  · simpa only [le_iff, mem_separate_iff]
      using fun t ht z hz => ⟨is_bound ht hz, fun eq => y_not_in_sUnion _ ht (eq ▸ hz)⟩

lemma exists_minimal {p : M → Prop} : (∃! x, IsGLB {x | p x} x) ↔ ∃ x : M, p x := by
  simp only [isGLB_iff]
  conv_lhs => change IsSet {x | ∀ (t : M), p t → x ∈ t}
  rw [isSet_iff]
  refine ⟨fun | ⟨x, hx⟩ => ?_, fun | ⟨t, ht⟩ => ?_⟩
  · by_contra h
    simp only [not_exists] at h
    specialize hx x
    simp [h, not_mem_self] at hx
  · refine ⟨_, fun y hy => hy _ ht⟩

/-- The `IsTransitive` declaration. -/
@[realize] def IsTransitive (X : M) := ∀ ⦃x⦄, x ∈ X → x ⊆ X

@[toV_simps] lemma IsTransitive.toV (α : M) : IsTransitive ↓α ↔ IsTransitive α := by
  simp only [IsTransitive, toV_simps]

@[toZFSet_simps] lemma IsTransitive.toZFSet (α : M) : IsTransitive α ↔ (⇓α).IsTransitive := by
  convert (IsTransitive.toV α).symm using 1
  simp only [IsTransitive, ZFSet.IsTransitive, toZFSet_simps]

/-- The `enoughTransitive` declaration. -/
def enoughTransitive (x : M) : {y : M // IsTransitive y ∧ x ⊆ y} := by
  split_vonNeumann hM
  · refine ⟨⟨V_ x.1.rank, vonNeumann_mem_of_lt (mem_vonNeumann.mp x.2)⟩, ?_⟩
    simpa only [IsTransitive.toZFSet, toZFSet_simps]
      using ⟨isTransitive_vonNeumann _, subset_vonNeumann.mpr le_rfl⟩
  · refine ⟨⟨V_ x.1.rank⟩, ?_⟩
    simpa only [IsTransitive.toZFSet, toZFSet_simps]
      using ⟨isTransitive_vonNeumann _, subset_vonNeumann.mpr le_rfl⟩

lemma toZFSet_enoughTransitive {x : M} : ⇓(enoughTransitive x).1 = V_ (⇓x).rank := by
  unfold enoughTransitive
  split_vonNeumann hM <;> rfl

@[realize] lemma trcl.eu (x : M) :
    ∃! y : M, IsGLB {t | IsTransitive t ∧ x ⊆ t} y := by
  simpa only [exists_minimal] using (enoughTransitive x).exists_of_subtype

lemma mem_trcl_iff {x y : M} : y ∈ trcl x ↔ ∀ t : M, IsTransitive t ∧ x ⊆ t → y ∈ t := by
  revert y
  change ∀ y : M, _
  simpa only [isGLB_iff, Set.mem_setOf_eq] using trcl.spec x

lemma isTransitive_trcl {x : M} : IsTransitive (trcl x) := by
  intro y hy z hz
  rw [mem_trcl_iff] at hy ⊢
  exact fun t ⟨ht, sub⟩ => ht (hy t ⟨ht, sub⟩) hz

lemma trcl_trans {x y z : M} (hz : z ∈ y) (hy : y ∈ trcl x) : z ∈ trcl x :=
  isTransitive_trcl hy hz

lemma sub_trcl {x : M} : x ⊆ trcl x := by
  intro y hy
  rw [mem_trcl_iff]
  exact fun t ⟨ht, sub⟩ => sub hy

lemma trcl_sub {x y : M} (hx : IsTransitive y) (sub : x ⊆ y) : trcl x ⊆ y :=
  fun _ hz => mem_trcl_iff.mp hz _ ⟨hx, sub⟩

@[realize] lemma union.eu (x y : M) : IsSet {z | z ∈ x ∨ z ∈ y} := by
  rw [isSet_iff]
  use trcl {x, y}
  rintro z (hz | hz) <;> exact trcl_trans hz <| sub_trcl (by simp)

@[realize] lemma inter.eu (x y : M) : IsSet {z | z ∈ x ∧ z ∈ y} := by
  rw [isSet_iff]
  exact ⟨y, by simp⟩

end SetTheory

instance instUnionM : Union M where union := SetTheory.union
@[simp] lemma Union.union.spec (x y z : M) : z ∈ x ∪ y ↔ z ∈ x ∨ z ∈ y := SetTheory.union.spec ..
lemma Union.union.eq_iff (x y z : M) : x ∪ y = z ↔ ∀ w, w ∈ z ↔ w ∈ x ∨ w ∈ y :=
  SetTheory.union.eq_iff ..
/-- The `formula` declaration. -/
def Union.union.formula := SetTheory.union.formula
@[realize_simps] lemma Union.union.realize_iff (v : Fin 3 → M) :
    formula.Realize v ↔ v 0 ∪ v 1 = v 2 := SetTheory.union.realize_iff v
@[realize] lemma Union.union.eu (x y : M) : IsSet {z | z ∈ x ∨ z ∈ y} :=
  SetTheory.union.eu x y

instance instInterM : Inter M where inter := SetTheory.inter
@[simp] lemma Inter.inter.spec (x y z : M) : z ∈ x ∩ y ↔ z ∈ x ∧ z ∈ y := SetTheory.inter.spec ..
lemma Inter.inter.eq_iff (x y z : M) : x ∩ y = z ↔ ∀ w, w ∈ z ↔ w ∈ x ∧ w ∈ y :=
  SetTheory.inter.eq_iff ..
/-- The `formula` declaration. -/
def Inter.inter.formula := SetTheory.inter.formula
@[realize_simps] lemma Inter.inter.realize_iff (v : Fin 3 → M) :
    formula.Realize v ↔ v 0 ∩ v 1 = v 2 := SetTheory.inter.realize_iff v
@[realize] lemma Inter.inter.eu (x y : M) : IsSet {z | z ∈ x ∧ z ∈ y} :=
  SetTheory.inter.eu x y

namespace SetTheory

@[toV_simps] lemma union.toV {x y : M} : ↓x ∪ ↓y = ↓(x ∪ y) := by
  rw [Union.union.eq_iff, ToV.forall_mem_toV_iff]
  · simpa only [toV_simps] using Union.union.spec _ _
  · rintro z (hz | hz) <;> exact exists_toV_of_mem hz

@[toZFSet_simps] lemma union.toZFSet {x y : M} : ⇓(x ∪ y) = ⇓x ∪ ⇓y := by
  simp (config := {singlePass := true}) only [← ToZFSet.toZFSet_toV]
  simpa only [ZFSet.ext_iff, ZFSet.mem_union, union.toV, toZFSet_simps]
    using Union.union.spec ↓x ↓y

open Classical in
instance instInfSetM : InfSet M where
  sInf s := if hs : s.Nonempty then separate hs.some fun x => ∀ t ∈ s, x ∈ t else ∅

instance instConditionallyCompleteLatticeM : ConditionallyCompleteLattice M :=
  conditionallyCompleteLatticeOfsInf M
    (fun x y => by use x ∪ y; simp [le_iff]; tauto)
    (fun x y => by use ∅; simp [toZFSet_simps])
    (fun s _ hs => by
      simp only [sInf, hs, ↓reduceDIte]
      conv_lhs => rw [show s = {x | x ∈ s} by simp]
      simpa only [isGLB_iff, Set.mem_setOf_eq, mem_separate_iff, and_iff_right_iff_imp]
        using fun y hy => hy _ hs.some_mem)

instance instOrderBotM : OrderBot M where
  bot := ∅
  bot_le := by simp [le_iff]

@[realize] lemma succ.eu (x : M) : ∃! y, y = Insert.insert x x := by simp

@[toV_simps] lemma succ.toV (α : M) : succ ↓α = ↓(succ α) := by
  simp only [succ.spec, toV_simps]

@[toZFSet_simps] lemma succ.toZFSet (α : M) : ⇓(succ α) = Insert.insert ⇓α ⇓α := by
  simp only [succ.spec, toZFSet_simps]

@[simp] lemma lt_succ {α : M} : α < succ α := by
  simpa only [
    lt_iff_le_and_exists, toZFSet_simps, ZFSet.le_def, subset_def, mem_insert_iff
  ] using ⟨by tauto, α, by simp, mem_irrefl _⟩

@[realize] lemma pair.eu (x y : M) : ∃! z, z = ({{x}, {x, y}} : M) := by simp
/-- The `⸨_,_⸩` notation. -/
notation "⸨"a ", " b "⸩" => pair a b

/-- The `IsPair` declaration. -/
@[realize] def IsPair (z : M) := ∃ x, ∃ y, z = ⸨x, y⸩

@[simp] lemma isPair_pair {x y : M} : IsPair ⸨x, y⸩ := by simp [IsPair]

lemma fst_aux {x y z : M} (hz : z = ⸨x, y⸩) : ExistsUniqueAt x fun x => ∀ w ∈ z, x ∈ w := by
  subst hz
  simp [ExistsUniqueAt, pair.spec]

@[realize] lemma fst.eu {z : M} (hz : IsPair z) : ∃! x, ∀ w ∈ z, x ∈ w := by
  rcases hz with ⟨x, y, h⟩
  exact ⟨_, fst_aux h⟩

@[simp] lemma fst_pair (x y : M) : fst ⸨x, y⸩ = x := by
  simpa only [fst.eq_iff (h₁ := ⟨x, y, rfl⟩)] using (fst_aux rfl).1

lemma pair_eq_singleton_iff {x y z : M} : {x, y} = ({z} : M) ↔ x = z ∧ y = z := by
  simp only [toZFSet_simps]
  exact ZFSet.pair_eq_singleton_iff

lemma snd_aux {x y z : M} (hz : z = ⸨x, y⸩) :
    ExistsUniqueAt y fun y => (∃ w ∈ z, y ∈ w) ∧ ((∀ w ∈ z, y ∈ w) → ∀ a ∈ z, ∀ b ∈ z, a = b) := by
  cases hz
  simp only [ExistsUniqueAt]
  by_cases h : y = x
  · simp [pair.spec, h, eq_comm, eq_comm.trans pair_eq_singleton_iff]
  · simp [pair.spec, h, pair_eq_singleton_iff]

@[realize] lemma snd.eu {z : M} (hz : IsPair z) :
    ∃! x, (∃ w ∈ z, x ∈ w) ∧ ((∀ w ∈ z, x ∈ w) → ∀ x ∈ z, ∀ y ∈ z, x = y) := by
  rcases hz with ⟨x, y, h⟩
  exact ⟨_, snd_aux h⟩

@[simp] lemma snd_pair (x y : M) : snd ⸨x, y⸩ = y := by
  simpa only [snd.eq_iff (h₁ := ⟨x, y, rfl⟩)] using (snd_aux rfl).1

@[simp] lemma pair_eta {z : M} (hz : IsPair z) : ⸨fst z, snd z⸩ = z := by
  rcases hz with ⟨x, y, ⟨_⟩⟩
  simp

lemma singleton_mem_pair (x y : M) : {x} ∈ ⸨x, y⸩ := by simp [pair.spec]
lemma unordered_pair_mem_pair (x y : M) : {x, y} ∈ ⸨x, y⸩ := by simp [pair.spec]

@[realize] lemma Pairs.eu (A B : M) : IsSet {x | IsPair x ∧ fst x ∈ A ∧ snd x ∈ B} := by
  rw [isSet_iff]
  use 𝓟 𝓟 (trcl {A, B})
  rintro _ ⟨⟨x, y, ⟨_⟩⟩, hx, hy⟩
  simp only [fst_pair, snd_pair] at hx hy
  simp only [pair.spec, powerset.spec, Subset, Insert.insert.spec, Singleton.singleton.spec]
  rintro z (⟨⟨_⟩⟩ | ⟨⟨_⟩⟩) <;>
    simp only [Insert.insert.spec, Singleton.singleton.spec]
  · rintro z ⟨_⟩
    exact trcl_trans hx <| sub_trcl (by simp)
  · rintro z (⟨⟨_⟩⟩ | ⟨⟨_⟩⟩)
    · exact trcl_trans hx <| sub_trcl (by simp)
    · exact trcl_trans hy <| sub_trcl (by simp)

attribute [simp] Pairs.spec

/-- The `IsRelation` declaration. -/
@[realize] def IsRelation (r : M) := ∀ ⦃x⦄, x ∈ r → IsPair x
/-- The `IsFunc` declaration. -/
@[realize] def IsFunc (f : M) := IsRelation f ∧ ∀ ⦃x y z⦄, ⸨x, y⸩ ∈ f → ⸨x, z⸩ ∈ f → y = z

@[realize] lemma Dom.eu (f : M) : IsSet {x | ∃ y, ⸨x, y⸩ ∈ f} := by
  rw [isSet_iff]
  use trcl f
  rintro x ⟨y, hy⟩
  exact trcl_trans (mem_singleton x) <|
    trcl_trans (singleton_mem_pair x y) <|
    sub_trcl hy

@[realize] lemma Ran.eu (f : M) : IsSet {y | ∃ x, ⸨x, y⸩ ∈ f} := by
  rw [isSet_iff]
  use trcl f
  rintro y ⟨x, hx⟩
  exact trcl_trans (show y ∈ {x, y} by simp) <|
    trcl_trans (unordered_pair_mem_pair x y) <|
    sub_trcl hx

lemma func_sub_pairs {A B f : M} (hf : IsFunc f ∧ Dom f = A ∧ Ran f ⊆ B) : f ⊆ Pairs A B := by
  intro x hx
  have eta := pair_eta (hf.1.1 hx)
  have fst_mem_dom : fst x ∈ Dom f := by
      simpa only [Dom.spec] using ⟨snd x, eta.symm ▸ hx⟩
  have fst_mem_A := hf.2.1 ▸ fst_mem_dom
  simp only [Pairs.spec, hf.1.1 hx, fst_mem_A, true_and]
  apply hf.2.2 ?_
  simpa only [Ran.spec] using ⟨fst x, eta.symm ▸ hx⟩

@[realize] lemma Func.eu (A B : M) : IsSet {f | IsFunc f ∧ Dom f = A ∧ Ran f ⊆ B} := by
  rw [isSet_iff]
  refine ⟨𝓟 (Pairs A B), fun f hf => ?_⟩
  simpa only [powerset.spec] using func_sub_pairs hf

@[realize] lemma apply.eu {f x : M} (hf : IsFunc f) (hx : x ∈ Dom f) : ∃! y, ⸨x, y⸩ ∈ f := by
  rw [Dom.spec] at hx
  rcases hx with ⟨y, hy⟩
  exact ⟨y, hy, fun z hz => (hf.2 hy hz).symm⟩

/-- The `PreserveMem` declaration. -/
@[realize] def PreserveMem (f : M) := ∀ x ∈ Dom f, ∀ y ∈ Dom f, x ∈ y → apply f x ∈ apply f y

/-- The `funcToSet` declaration. -/
def funcToSet {A B : M} (f : A → B) : M :=
  separate (Pairs A B) fun x => ∃ hx : fst x ∈ A, (f ⟨fst x, hx⟩).1 = snd x

@[simp] lemma isFunc_funcToSet {A B : M} {f : A → B} : IsFunc (funcToSet f) := by
  simpa only [
    IsFunc, IsRelation, funcToSet, mem_separate_iff, and_imp, forall_exists_index,
    fst_pair, snd_pair
  ] using ⟨
    fun x hx _ _ => ((Pairs.spec ..).mp hx).1,
    fun x y z _ _ eq_y _ _ eq_z => eq_y ▸ eq_z
  ⟩

@[simp] lemma dom_funcToSet {A B : M} {f : A → B} : Dom (funcToSet f) = A := by
  simp only [Dom.eq_iff]
  refine fun x => ⟨fun hx => ⟨(f ⟨x, hx⟩).1, ?_⟩, fun | ⟨y, hy⟩ => ?_⟩
  · simp only [funcToSet, mem_separate_iff, Pairs.spec, fst_pair, snd_pair]
    exact ⟨⟨isPair_pair, hx, (f ⟨x, hx⟩).2⟩, hx, trivial⟩
  · simp only [funcToSet, mem_separate_iff, Pairs.spec, fst_pair, snd_pair] at hy
    exact hy.2.1

lemma mem_Ran_funcToSet_iff {A B : M} {f : A → B} :
    ∀ y, y ∈ Ran (funcToSet f) ↔ ∃ x, ∃ hx : x ∈ A, (f ⟨x, hx⟩).1 = y := by
  simp only [funcToSet, Ran.spec, mem_separate_iff, Pairs.spec, fst_pair, snd_pair]
  intro y
  congr! 2 with x
  exact and_iff_right_iff_imp.mpr
    fun | ⟨hx, eq⟩ => ⟨isPair_pair, hx, eq ▸ (f ⟨x, hx⟩).2⟩

lemma ran_funcToSet_sub {A B : M} {f : A → B} : Ran (funcToSet f) ⊆ B := by
  simp only [Subset, mem_Ran_funcToSet_iff]
  rintro _ ⟨x, hx, ⟨_⟩⟩
  exact (f ⟨x, hx⟩).2

lemma funcToSet_mem_Func {A B : M} (f : A → B) : funcToSet f ∈ Func A B := by
  simpa only [Func.spec] using ⟨isFunc_funcToSet, dom_funcToSet, ran_funcToSet_sub⟩

lemma apply_mem_Ran {f x : M} (hf : IsFunc f) (hx : x ∈ Dom f) : apply f x ∈ Ran f := by
  simpa only [Ran.spec] using ⟨_, apply.spec f x hf hx⟩

/-- The `setToFunc` declaration. -/
def setToFunc {A B : M} (f : (Func A B : M)) : A → B := by
  have hf := f.2
  erw [Func.spec] at hf
  exact fun | ⟨x, hx⟩ => ⟨apply f x, hf.2.2 (apply_mem_Ran hf.1 (hf.2.1.symm ▸ hx))⟩

lemma apply_funcToSet {A B : M} (f : A → B) {x : M} (hx : x ∈ A) :
    apply (funcToSet f) x = (f ⟨x, hx⟩).1 := by
  rw [funcToSet, apply.eq_iff]
  · simp only [mem_separate_iff, Pairs.spec, fst_pair, snd_pair]
    exact ⟨⟨isPair_pair, hx, (f ⟨x, hx⟩).2⟩, hx, trivial⟩
  · exact isFunc_funcToSet
  · simpa [Dom.spec, hx] using ⟨_, (f ⟨x, hx⟩).2, rfl⟩

lemma apply_funcToSet_rev {A B : M} (f : A → B) {x : A} :
    (f x).1 = apply (funcToSet f) x.1 := by
  rw [apply_funcToSet]

lemma setToFunc_funcToSet {A B : M} {f : A → B} :
    setToFunc ⟨funcToSet f, funcToSet_mem_Func f⟩ = f := by
  ext1 x
  simp only [setToFunc, apply_funcToSet f x.2]

lemma funcToSet_setToFunc {A B : M} (f : (Func A B : M)) : funcToSet (setToFunc f) = f.1 := by
  ext x
  have hf := f.2
  erw [Func.spec] at hf
  simp only [funcToSet, setToFunc, mem_separate_iff] at ⊢
  refine ⟨fun | ⟨hx, hfst, hsnd⟩ => ?_, fun hx => ?_⟩
  · rw [Pairs.spec] at hx
    rwa [apply.eq_iff _ _ hf.1 (hf.2.1.symm ▸ hfst), pair_eta hx.1] at hsnd
  · simp only [func_sub_pairs hf hx, exists_prop]
    have eta := pair_eta (hf.1.1 hx)
    have fst_mem_dom : fst x ∈ Dom f.1 := by
        simpa only [Dom.spec] using ⟨snd x, eta.symm ▸ hx⟩
    have fst_mem_A := hf.2.1 ▸ fst_mem_dom
    simp only [fst_mem_A, apply.eq_iff _ _ hf.1 fst_mem_dom, eta, hx, and_true]

/-- The `funcEquiv` declaration. -/
def funcEquiv {A B : M} : (Func A B : M) ≃ (A → B) where
  toFun f := setToFunc f
  invFun f := ⟨funcToSet f, funcToSet_mem_Func f⟩
  left_inv := by simp [LeftInverse, funcToSet_setToFunc]
  right_inv := by simp [RightInverse, LeftInverse, setToFunc_funcToSet]

lemma forall_func {A B : M} {p : M → Prop} :
    (∀ f ∈ Func A B, p f) ↔ ∀ f : A → B, p (funcToSet f) := by
  rw [Subtype.forall']
  exact funcEquiv.forall_congr_left

lemma exists_func {A B : M} {p : M → Prop} :
    (∃ f ∈ Func A B, p f) ↔ ∃ f : A → B, p (funcToSet f) := by
  simp only [← Classical.not_forall_not, not_and]
  congr! 1
  exact forall_func

lemma subset_func {f g : M} (hf : IsFunc f) (hg : IsFunc g)
    (dom_sub : Dom f ⊆ Dom g) (ext : ∀ x ∈ Dom f, apply f x = apply g x) : f ⊆ g := by
  intro z hz
  obtain ⟨x, y, ⟨_⟩⟩ := hf.1 hz
  have x_mem_dom : x ∈ Dom f := by simpa [Dom.spec] using ⟨_, hz⟩
  specialize ext x x_mem_dom
  have : apply f x = y := by rwa [apply.eq_iff _ _ hf x_mem_dom]
  rwa [eq_comm, this, apply.eq_iff _ _ hg (dom_sub x_mem_dom)] at ext

lemma ext_func {f g : M} (hf : IsFunc f) (hg : IsFunc g)
    (dom_eq : Dom f = Dom g) (ext : ∀ x ∈ Dom f, apply f x = apply g x) : f = g :=
  le_antisymm
    (subset_func hf hg (le_of_eq dom_eq) ext)
    (subset_func hg hf (ge_of_eq dom_eq) fun x hx => (ext x (dom_eq ▸ hx)).symm)

@[simp] lemma sSup_empty : sSup (∅ : Set M) = ∅ := by
  simp only [SetTheory.ext_iff, EmptyCollection.emptyCollection.spec, iff_false]
  change ∀ x, x ∉ sInf (upperBounds ∅)
  simpa [sInf, upperBounds] using fun _ _ => ⟨_, not_mem_self⟩

@[simp] lemma sInf_empty : sInf (∅ : Set M) = ∅ := by
  simp [sInf]

/-- The `IsInjective` declaration. -/
@[realize] def IsInjective (f : M) :=
  IsFunc f ∧ ∀ x ∈ Dom f, ∀ y ∈ Dom f, apply f x = apply f y → x = y

@[simp] lemma isInjective_funcToSet {A B : M} {f : A → B} :
    IsInjective (funcToSet f) ↔ Injective f := by
  simp +contextual only [IsInjective, isFunc_funcToSet, true_and, dom_funcToSet, Injective,
    Subtype.forall, Subtype.mk.injEq, apply_funcToSet, Subtype.coe_inj]
  exact Iff.rfl

lemma nonempty_iff (x : M) : Nonempty x ↔ x ≠ ∅ := by
  simp only [nonempty_subtype, ne_eq]
  rw [eq_comm, EmptyCollection.emptyCollection.eq_iff]
  simp only [not_forall, not_not]
  exact Iff.rfl

/-- The `cardLE` declaration. -/
@[realize] def cardLE (x y : M) := ∃ f ∈ Func x y, IsInjective f
/-- The `cardEq` declaration. -/
@[realize] def cardEq (x y : M) := ∃ f ∈ Func x y, IsInjective f ∧ Ran f = y
/-- The `cardLT` declaration. -/
@[realize] def cardLT (x y : M) := cardLE x y ∧ ¬cardEq x y

lemma cardLE_iff (x y : M) : cardLE x y ↔ #x ≤ #y := by
  simpa only [cardLE, exists_func, isInjective_funcToSet, le_def]
    using ⟨fun | ⟨f, hf⟩ => ⟨⟨f, hf⟩⟩, fun | ⟨f⟩ => ⟨f.1, f.2⟩⟩

lemma ran_funcToSet_eq {A B : M} {f : A → B} : Ran (funcToSet f) = B ↔ Surjective f := by
  rw [SetTheory.ext_iff]
  simp only [mem_Ran_funcToSet_iff, Surjective]
  refine ⟨fun | h, ⟨y, hy⟩ => ?_, fun h y => ⟨fun | ⟨x, hx, eq⟩ => ?_, fun hy => ?_⟩⟩
  · obtain ⟨x, hx, ⟨_⟩⟩ := (h y).mpr hy
    exact ⟨⟨x, hx⟩, rfl⟩
  · subst eq
    exact Subtype.property _
  · obtain ⟨x, hx⟩ := h ⟨y, hy⟩
    exact ⟨x.1, x.2, by rw [hx]⟩

lemma cardEq_iff (x y : M) : cardEq x y ↔ #x = #y := by
  simpa only [cardEq, exists_func, isInjective_funcToSet, ran_funcToSet_eq, Cardinal.eq]
    using ⟨
      fun | ⟨f, hf₁, hf₂⟩ => ⟨Equiv.ofBijective f ⟨hf₁, hf₂⟩⟩,
      fun | ⟨f⟩ => ⟨f.1, f.injective, f.surjective⟩
    ⟩

lemma cardLT_iff (x y : M) : cardLT x y ↔ #x < #y := by
  rw [cardLT, cardLE_iff, cardEq_iff, lt_iff_le_and_ne]

@[realize] lemma iUnion.eu (f : M) : IsSet {y | ∃ x ∈ Ran f, y ∈ x} := by
  simpa only [isSet_iff, Ran.spec] using ⟨
    trcl f, fun
    | u, ⟨y, ⟨x, hxy⟩, hu⟩ =>
      trcl_trans hu <|
      trcl_trans (by simp) <|
      trcl_trans (unordered_pair_mem_pair x y) <|
      sub_trcl hxy
  ⟩

lemma mem_sSup_iff {C : Set M} {x : M} (hC : BddAbove C) : x ∈ sSup C ↔ ∃ t ∈ C, x ∈ t := by
  by_cases! C_cmp_empty : C.Nonempty
  · have := isLUB_csSup C_cmp_empty hC
    rw [isLUB_iff] at this
    rw [this]
  · simp [C_cmp_empty, sSup_empty]

lemma iUnion_funcToSet {A B : M} {f : A → B} : iUnion (funcToSet f) = ⨆ x : A, (f x).1 := by
  rw [iUnion.eq_iff]
  intro x
  erw [mem_sSup_iff]
  · simp only [Set.mem_range, Subtype.exists, mem_Ran_funcToSet_iff]; rfl
  · refine ⟨iUnion (funcToSet f), ?_⟩
    intro x
    simp only [Set.mem_range, Subtype.exists, forall_exists_index]
    rintro x hx rfl y hy
    erw [iUnion.spec]
    exact ⟨_, (mem_Ran_funcToSet_iff _).mpr ⟨x, hx, rfl⟩, hy⟩

end SetTheory
