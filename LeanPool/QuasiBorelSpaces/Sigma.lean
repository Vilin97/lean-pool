/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import LeanPool.QuasiBorelSpaces.MeasureTheory.Cases
import LeanPool.QuasiBorelSpaces.MeasureTheory.Sigma
import LeanPool.QuasiBorelSpaces.Prop
import LeanPool.QuasiBorelSpaces.Subtype
import Mathlib.Data.Sigma.Order
import LeanPool.QuasiBorelSpaces.Defs
import LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Sigma
import LeanPool.QuasiBorelSpaces.Prod


/-!
# Small Coproducts of Quasi-Borel Spaces

This file defines small coproducts of quasi-borel spaces by giving a
`QuasiBorelSpace` instance for the `Σ` type.

See [HeunenKSY17], Proposition 17.
-/

open scoped MeasureTheory

namespace QuasiBorelSpace.Sigma

variable
  {I : Type*} {P : I → Type*} [∀ i, QuasiBorelSpace (P i)]
  {J : Type*} {Q : J → Type*} [∀ j, QuasiBorelSpace (Q j)]
  {A B C : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B] [QuasiBorelSpace C]

/--
Represents a variable for a Σ-type. Intuitively, a variable in `Σi, P i` is a
gluing of a countable number of variables, each in some `P i`.
-/
structure Var (I : Type*) (P : I → Type*) [∀ i, QuasiBorelSpace (P i)] where
  /-- Each index represents some `I`. -/
  embed : ℕ → I
  /-- Obtains the index of the underlying variable, given the intended input. -/
  index : ℝ → ℕ
  /-- The family of variables. -/
  var : (i : ℕ) → ℝ → P (embed i)
  /-- Each variable is, in fact, a variable. -/
  isHom_var : ∀i, IsHom (var i)
  /-- The index function is measurable. -/
  measurable_index : Measurable[_, ⊤] index

namespace Var

attribute [fun_prop] measurable_index

/--
Since every `Var` represents a variable, each `Var` induces a function
`ℝ → Σi, P i`.
-/
@[simps]
def apply (x : Var I P) (r : ℝ) : Sigma P where
  fst := x.embed (x.index r)
  snd := x.var (x.index r) r

@[simp]
lemma apply_mk
    {f : ℕ → I} {i : ℝ → ℕ} {φ : (i : ℕ) → ℝ → P (f i)} {r : ℝ}
    (hφ : ∀ i, IsHom (φ i)) (hi : Measurable[_, ⊤] i)
    : apply ⟨f, i, φ, hφ, hi⟩ r = ⟨f (i r), φ (i r) r⟩ :=
  rfl

/-- A `Var` can be constructed from any `Encodable` index type. -/
def mk'
    (Index : Type*) [Encodable Index] (embed : Index → I) (index : ℝ → Index)
    (var : (i : Index) → ℝ → P (embed i)) (isHom_var : ∀ i, IsHom (var i))
    (measurable_index : Measurable[_, ⊤] index)
    : Var I P where
  embed n := embed ((Encodable.decode₂ Index n).getD (index 0))
  index r := Encodable.encode (index r)
  var _ r := var _ r
  isHom_var _ := isHom_var _
  measurable_index := Measurable.fun_comp measurable_from_top measurable_index

@[simp]
lemma apply_mk'
    {J : Type*} [Encodable J]
    {f : J → I} {i : ℝ → J} {φ : (i : J) → ℝ → P (f i)} {r : ℝ}
    (hφ : ∀ i, IsHom (φ i)) (hi : Measurable[_, ⊤] i)
    : apply (mk' J f i φ hφ hi) r = ⟨f (i r), φ (i r) r⟩ := by
  simp only [mk', apply_mk, Sigma.mk.injEq, Encodable.decode₂_encode, Option.getD_some, true_and]
  rw [Encodable.decode₂_encode]
  simp only [Option.getD_some, heq_eq_eq]

instance : CoeFun (Var I P) (fun _ ↦ ℝ → Sigma P) where
  coe := apply

/-- The constant variable. -/
def const (x : Sigma P) : Var I P := mk'
  (Index := Unit)
  (embed := fun _ ↦ x.1)
  (index := fun _ ↦ ())
  (var := fun _ _ ↦ x.2)
  (isHom_var := by simp only [isHom_const', implies_true])
  (measurable_index := measurable_const)

@[simp]
lemma const_apply (x : Sigma P) (r : ℝ) : const x r = x := by rfl

/-- Composition under measurable functions. -/
def comp {f : ℝ → ℝ} (hf : Measurable f) (x : Var I P) : Var I P where
  embed := x.embed
  index r := x.index (f r)
  var i r := x.var i (f r)
  isHom_var i := isHom_comp' (x.isHom_var i) (by simp only [isHom_ofMeasurableSpace, hf])
  measurable_index := Measurable.fun_comp x.measurable_index hf

@[simp]
lemma comp_apply
    {f : ℝ → ℝ} (hf : Measurable f)
    (x : Var I P) (r : ℝ)
    : comp hf x r = x (f r) := by
  rfl

/-- Gluing of a countable number of variables. -/
def cases {ix : ℝ → ℕ} (hix : Measurable ix) (φ : ℕ → Var I P) : Var I P := mk'
  (Index := ℕ × ℕ)
  (embed := fun x ↦ (φ x.1).embed x.2)
  (index := fun r ↦ ⟨ix r, (φ (ix r)).index r⟩)
  (var := fun i r ↦ (φ i.1).var i.2 r)
  (isHom_var := fun i ↦ (φ i.1).isHom_var i.2)
  (measurable_index := by
    let : MeasurableSpace (ℕ × ℕ) := ⊤
    apply MeasureTheory.measurable_cases (f := fun n r ↦
        (⟨n, (φ n).index r⟩ : ℕ × ℕ))
    · exact hix
    · intro i
      apply Measurable.fun_comp
      · apply measurable_from_top
      · apply measurable_index)

@[simp]
lemma cases_apply
    {ix : ℝ → ℕ} (hix : Measurable ix)
    (φ : ℕ → Var I P) (r : ℝ)
    : cases hix φ r = φ (ix r) r := by
  simp only [cases, apply_mk']
  rfl

/-- Normal `QuasiBorelSpace.Var`s can be pushed 'inside' a `Var`. -/
def distrib {φ₁ : ℝ → A} (hφ₁ : IsHom φ₁) (φ₂ : Var I P) : Var I (fun i ↦ A × P i) where
  embed := φ₂.embed
  index := φ₂.index
  var i r := (φ₁ r, φ₂.var i r)
  isHom_var i := by simp only [Prod.isHom_iff, hφ₁, φ₂.isHom_var i, and_self]
  measurable_index := φ₂.measurable_index

@[simp]
lemma distrib_apply
    {φ₁ : ℝ → A} (hφ₁ : IsHom φ₁) (φ₂ : Var I P) (r : ℝ)
    : apply (distrib hφ₁ φ₂) r = ⟨(φ₂ r).1, φ₁ r, (φ₂ r).2⟩ := by
  rfl

instance [∀ i, LE (P i)] : LE (Var I P) where
  le φ₁ φ₂ := ∀x, apply φ₁ x ≤ apply φ₂ x

instance [∀ i, Preorder (P i)] : Preorder (Var I P) where
  le_refl φ x := by simp only [le_refl]
  le_trans _ _ _ h₁ h₂ x := le_trans (h₁ x) (h₂ x)

open OmegaCompletePartialOrder

omit [∀ i, QuasiBorelSpace (P i)] in
private lemma cast_mono
    [∀ i, Preorder (P i)] {i j : I} (h : i = j)
    : Monotone (cast (congr_arg P h)) := by
  intro _ _ h'
  subst h
  exact h'

/-- Converts a `Chain` of `Var`s into a `Var` of `Chain`s. -/
noncomputable def chain [∀ i, Preorder (P i)] (φ : Chain (Var I P)) : Var I fun r ↦ Chain (P r) :=
  open Classical in
  have : Encodable (Set.range (Sigma.fst ∘ (φ 0).apply)) := by
    suffices Countable (Set.range (Sigma.fst ∘ (φ 0).apply)) by
      apply Encodable.ofCountable
    simp only [Set.countable_coe_iff]
    apply Set.Countable.mono
    · apply Set.range_comp_subset_range (g := (φ 0).embed)
    · apply Set.countable_range
  mk'
    (Index := Set.range (Sigma.fst ∘ (φ 0).apply))
    (embed := Subtype.val)
    (index := Set.rangeFactorization _)
    (var := fun i r ↦ {
      toFun n :=
        if h : i.val = ((φ n).apply r).fst then
          h ▸ (φ n).var ((φ n).index r) r
        else
          have : Nonempty (P i) := by
            rcases i with ⟨i, r, rfl⟩
            exact ⟨(φ 0).var ((φ 0).index r) r⟩
          this.some
      monotone' i₁ i₂ hi := by
        classical
        have h₀ := (OrderHomClass.mono φ) hi r
        simp only [Sigma.le_def, apply_fst, apply_snd] at h₀
        change (if h : (i : I) = ((φ i₁).apply r).fst then _ else _) ≤
               (if h : (i : I) = ((φ i₂).apply r).fst then _ else _)
        by_cases h₁ : (i : I) = ((φ i₁).apply r).fst
        · by_cases h₂ : (i : I) = ((φ i₂).apply r).fst
          · rw [dif_pos h₁, dif_pos h₂]
            rw [eqRec_eq_cast, eqRec_eq_cast]
            have hkey := cast_mono h₂.symm h₀.snd
            simp only [eqRec_eq_cast] at hkey
            convert hkey using 2
            exact (cast_heq _ _).symm
          · exfalso
            apply h₂
            simp only [apply_fst] at h₁ h₂ ⊢
            rw [← h₀.fst]; exact h₁
        · by_cases h₂ : (i : I) = ((φ i₂).apply r).fst
          · exfalso
            apply h₁
            simp only [apply_fst] at h₁ h₂ ⊢
            rw [h₀.fst]; exact h₂
          · simp only [h₁, h₂, ↓reduceDIte, le_refl]
    })
    (isHom_var := by
      simp only [
        apply_fst, Chain.isHom_iff, Subtype.forall, Set.mem_range,
        Function.comp_apply, forall_exists_index]
      intro i r h n
      classical
      apply Prop.isHom_dite
      · simp only [isHom_ofMeasurableSpace]
        let : MeasurableSpace I := ⊤
        apply Measurable.const_eq
        fun_prop
      · apply isHom_cases
          (A := { x // i = (φ n).embed ((φ n).index x) })
          (I := { j // (φ n).embed j = i })
          (B := P i)
          (ix := fun x : { x // i = (φ n).embed ((φ n).index x) } ↦
            ⟨(φ n).index x.val, x.property.symm⟩)
          (f := fun j x ↦ j.property ▸ (φ n).var j ↑x)
        · apply isHom_mono
          · fun_prop
          · intro ψ hψ
            simp only [isVar_iff_isHom, Subtype.isHom_def, isHom_ofMeasurableSpace] at ⊢ hψ
            apply Measurable.comp (g := id)
            · have hid :
                  @Measurable { j // (φ n).embed j = i } { j // (φ n).embed j = i }
                    inferInstance ⊤ id := by
                apply Measurable.le
                · rw [top_le_iff]
                  ext
                  simp only [MeasurableSpace.measurableSet_top, iff_true]
                  apply MeasurableSet.of_subtype_image
                  simp only [MeasurableSpace.measurableSet_top]
                · apply measurable_id
              exact hid
            · apply Measurable.subtype_mk hψ
        · rintro ⟨m, rfl⟩
          apply isHom_comp'
          · apply (φ n).isHom_var
          · apply Subtype.isHom_val
            exact isHom_id'
      · fun_prop)
    (measurable_index := by
      let : MeasurableSpace I := ⊤
      apply Measurable.mono
      · apply Measurable.rangeFactorization
        fun_prop
      · rfl
      · simp only [top_le_iff]
        ext
        simp only [MeasurableSpace.measurableSet_top, MeasurableSet.of_subtype_image])

@[simp]
lemma chain_apply [∀ i, Preorder (P i)] (φ : Chain (Var I P)) (r)
    : (chain φ).apply r = Chain.Sigma.distrib (φ.map ⟨fun φ ↦ φ r, fun _ _ h ↦ h r⟩) := by
  classical
  simp only [
    chain, apply_fst, apply_mk', Set.rangeFactorization_coe, Function.comp_apply,
    Chain.Sigma.distrib, Chain.coe_map, OrderHom.coe_mk, apply_snd, Sigma.mk.injEq,
    heq_eq_eq, true_and]
  apply Chain.ext
  funext n
  have hfst : (φ 0).embed ((φ 0).index r) = (φ n).embed ((φ n).index r) := by
    have := (OrderHomClass.mono φ) (Nat.zero_le n) r
    simp only [Sigma.le_def, apply_fst, apply_snd] at this
    exact this.fst
  change (if h : (φ 0).embed ((φ 0).index r) = (φ n).embed ((φ n).index r) then _ else _) = _
  rw [dif_pos hfst]
  rfl

end Var

instance : QuasiBorelSpace (Σ i : I, P i) where
  IsVar φ := ∃ (ψ : Var I P), ∀r, φ r = ψ r
  isVar_const x := by
    use Var.const x
    simp only [Var.const_apply, implies_true]
  isVar_comp hf hφ := by
    rcases hφ with ⟨ψ, hψ⟩
    use ψ.comp hf
    simp only [hψ, Var.comp_apply, implies_true]
  isVar_cases' hindex hφ := by
    choose ψ hψ using hφ
    use Var.cases hindex ψ
    simp only [hψ, Var.cases_apply, implies_true]

@[local simp]
lemma isHom_def (φ : ℝ → (i : I) × P i) : IsHom φ ↔ ∃ (ψ : Var I P), ∀r, φ r = ψ r := by
  rw [← isVar_iff_isHom]
  rfl

@[fun_prop, simp]
lemma isHom_mk (i) : IsHom (⟨i, ·⟩ : P i → Sigma P) := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [isHom_def]
  intro φ hφ
  use .mk'
    (Index := Unit)
    (embed := fun _ ↦ i)
    (index := fun _ ↦ ())
    (var := fun _ ↦ φ)
    (isHom_var := fun _ ↦ hφ)
    (measurable_index := by simp only [measurable_const])
  simp only [Var.apply_mk', implies_true]

@[fun_prop]
lemma isHom_mk' {i} {f : A → P i} (hf : IsHom f) : IsHom (fun x ↦ ⟨i, f x⟩ : A → Sigma P) := by
  fun_prop

lemma isHom_elim {f : Sigma P → A} (hf : ∀ i, IsHom (fun x ↦ f ⟨i, x⟩)) : IsHom f := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [isHom_def]
  intro φ hφ
  choose φ hφ₀ using hφ
  rcases φ with ⟨emb, ix, var, hvar, hix⟩
  simp only [Var.apply_mk] at hφ₀
  conv => enter [1, x]; rw [hφ₀]
  apply isHom_cases (ix := ix) (f := fun i x ↦ f ⟨emb i, var i x⟩)
  · simp only [isHom_ofMeasurableSpace, hix]
  · intro j
    apply isHom_comp' (hf (emb j)) (hvar j)

lemma isHom_elim'
    {f : ∀ i, P i → B} (hf : ∀ i, IsHom (f i))
    {g : A → (i : I) × P i} (hg : IsHom g)
    : IsHom (fun x ↦ f (g x).1 (g x).2) := by
  exact isHom_comp' (f := fun x : Sigma P ↦ (f x.1 x.2 : B)) (g := g) (isHom_elim hf) hg

@[fun_prop, simp]
lemma isHom_fst [QuasiBorelSpace I] : IsHom (Sigma.fst : Sigma P → I) := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [isHom_def, forall_exists_index]
  intro φ ψ hψ
  simp only [hψ]
  rcases ψ with ⟨embed, index, var, isHom_var, measurable_index⟩
  simp only [Var.apply_mk]
  apply isHom_cases (ix := index) (f := fun n r ↦ embed n)
  · simp only [isHom_ofMeasurableSpace, measurable_index]
  · simp only [isHom_const', implies_true]

@[fun_prop]
lemma isHom_snd : IsHom (Sigma.snd : (_ : I) × A → A) := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [isHom_def, forall_exists_index]
  intro φ ψ hψ
  simp only [hψ]
  rcases ψ with ⟨embed, index, var, isHom_var, measurable_index⟩
  simp only [Var.apply_mk]
  apply isHom_cases (ix := index) (f := fun n r ↦ var n r)
  · simp only [isHom_ofMeasurableSpace, measurable_index]
  · fun_prop

lemma isHom_distrib : IsHom (fun x : A × Sigma P ↦ (⟨x.2.1, x.1, x.2.2⟩ : (i : I) × A × P i)) := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [Prod.isHom_iff, isHom_def, and_imp, forall_exists_index]
  intro φ hφ ψ hψ
  exists Var.distrib hφ ψ
  intro r
  simp only [Var.distrib_apply]
  rw [hψ]

lemma isHom_distrib'
    {f : A × Sigma P → B} (hf : IsHom (fun x : (i : I) × A × P i ↦ f ⟨x.2.1, x.1, x.2.2⟩))
    : IsHom f := by
  exact isHom_comp'
      (f := fun x : (i : I) × A × P i ↦ f ⟨x.2.1, x.1, x.2.2⟩)
      (g := fun x : A × Sigma P ↦ ⟨x.2.1, x.1, x.2.2⟩)
      hf isHom_distrib

@[fun_prop]
lemma isHom_map
    {f : I → J}
    {g : ∀ i, P i → Q (f i)} (hg : ∀ i, IsHom (g i))
    : IsHom (Sigma.map f g) := by
  unfold Sigma.map
  apply isHom_elim
  intro i
  dsimp only
  fun_prop

instance
    [Countable I] [∀ i, MeasurableSpace (P i)] [∀ i, MeasurableQuasiBorelSpace (P i)]
    : MeasurableQuasiBorelSpace (Sigma P) where
  isHom_iff_measurable φ := by
    classical
    rw [isHom_def]
    apply Iff.intro
    · intro ⟨ψ, hψ⟩
      rw [←funext_iff] at hψ
      subst hψ
      apply MeasureTheory.measurable_cases
        (ix := ψ.index)
        (f := fun i r ↦ (⟨ψ.embed i, ψ.var i r⟩ : Sigma P))
      · fun_prop
      · intro i
        apply MeasureTheory.Sigma.measurable_mk'
        have := ψ.isHom_var i
        simp only [isHom_iff_measurable] at this
        exact this
    · intro h
      have := Encodable.ofCountable I
      have {i : {i : I // ∃r, (φ r).1 = i}} : Nonempty (P i.val) := by
        rcases i.property with ⟨r, hi⟩
        simp only [← hi]
        use (φ r).snd
      use .mk'
          {i : I // ∃r, (φ r).1 = i}
          Subtype.val
          (fun x ↦ ⟨(φ x).1, by grind⟩)
          (fun i r ↦ if h : (φ r).1 = i then h ▸ (φ r).2 else Classical.arbitrary _)
          ?_
          ?_
      · intro r
        rw [Var.apply_mk']
        simp only [↓reduceDIte]
      · intro ⟨i, hi⟩
        simp only [isHom_iff_measurable]
        apply MeasureTheory.measurable_dite
        · change Measurable fun x ↦ (φ x).fst ∈ ({i} : Set _)
          apply Measurable.fun_comp
          · simp only [measurable_mem]
            apply MeasurableSpace.measurableSet_top
          · fun_prop
        · apply MeasureTheory.Sigma.measurable_eq_rec
          simp only [Sigma.eta]
          fun_prop
        · fun_prop
      · intro _ _
        apply Measurable.subtype_mk
        · apply Measurable.fun_comp
          · simp only [MeasureTheory.Sigma.measurable_fst]
          · apply h
        · apply MeasurableSet.of_subtype_image
          apply MeasurableSpace.measurableSet_top

end QuasiBorelSpace.Sigma

namespace OmegaQuasiBorelSpace.Sigma

open OmegaCompletePartialOrder
open QuasiBorelSpace

variable {I : Type*} {P : I → Type*} [∀ i, OmegaQuasiBorelSpace (P i)]

private lemma heq_ext
    {i j} (f : Chain (P i)) (g : Chain (P j))
    (h : i = j) (h' : ∀ k, f k ≍ g k) : f ≍ g := by
  subst h
  simp_all only [heq_eq_eq]
  ext
  apply h'

@[fun_prop]
lemma isHom_chain_distrib : IsHom (Chain.Sigma.distrib (I := I) (P := P)) := by
  rw [isHom_def]
  simp only [Chain.isHom_iff, Sigma.isHom_def, Chain.Sigma.distrib]
  intro φ hφ
  choose ψ hψ using hφ
  use Sigma.Var.chain {
    toFun := ψ
    monotone' i₁ i₂ hi := by
      intro r
      simp only [← hψ]
      apply (OrderHomClass.mono (φ r)) hi
  }
  intro r
  simp only [
    Sigma.Var.chain_apply, Chain.Sigma.distrib, Chain.coe_map, OrderHom.coe_mk,
    Function.comp_apply, Sigma.Var.apply_fst, Sigma.Var.apply_snd, Sigma.mk.injEq]
  have hfst : ∀ k, ((φ r) k).fst = (ψ k).embed ((ψ k).index r) := by
    intro k
    rw [hψ k r]
    rfl
  refine ⟨hfst 0, ?_⟩
  apply heq_ext (P := P) (i := ((φ r) 0).fst) (j := (ψ 0).embed ((ψ 0).index r)) (h := hfst 0)
  intro k
  apply HEq.trans (eqRec_heq _ _)
  apply HEq.trans _ (eqRec_heq _ _).symm
  rw [hψ k r]
  rfl

instance : OmegaQuasiBorelSpace ((i : I) × P i) where
  isHom_ωSup := by
    simp only [ωSup]
    fun_prop

end OmegaQuasiBorelSpace.Sigma
