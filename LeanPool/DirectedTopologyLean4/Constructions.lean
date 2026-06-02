/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
import LeanPool.DirectedTopologyLean4.DirectedMap
import LeanPool.DirectedTopologyLean4.MonotonePath

/-!
# LeanPool.DirectedTopologyLean4.Constructions
-/

/-
  This file contains constructions of directed spaces such as:
  * The directed space induced by a preorder on a topological space.
  * The directed space induced by a continuous map from a topological space to a directed space.
  * The product of two directed spaces.

  This file also contains lemmas about directed maps from/to these spaces.
-/

open DirectedMap
open scoped unitInterval
universe u v

/-- Any space with a preorder can be equiped with a directedness, by allowing all monotone paths
  as directed paths
-/
@[reducible] def DirectedSpace.Preorder (α : Type u) [TopologicalSpace α] [Preorder α] :
    DirectedSpace α where
  IsDipath := fun {x y : α} γ => Monotone ↑γ
  isDipath_constant := fun x _ _ _ => le_refl x
  isDipath_concat := by
    intros x y z γ₁ γ₂ hγ₁ hγ₂ a b hab
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs with h₁ h₂ h₂
    · -- a ≤ 1/2 and b ≤ 1/2, so use monotonicity of γ₁
      apply hγ₁
      simp only [Subtype.mk_le_mk, Nat.ofNat_pos, mul_le_mul_iff_right₀, Subtype.coe_le_coe]
      exact hab
    · -- a ≤ 1/2 and b > 1/2, so use that γ₁ ≤ y ≤ γ₂
      exact le_trans (monotone_path_bounded hγ₁ _).2 (monotone_path_bounded hγ₂ _).1
    · -- Impossible, as 1/2 < a and b ≤ 1/2 and a ≤ b
      exact False.elim (h₁ (le_trans hab h₂))
    · -- a > 1/2 and b > 1/2, so use monotonicity of γ₂
      apply hγ₂
      simp only [Subtype.mk_le_mk, tsub_le_iff_right, sub_add_cancel, Nat.ofNat_pos,
        mul_le_mul_iff_right₀, Subtype.coe_le_coe]
      exact hab

  isDipath_reparam := fun {x y : α} γ t₀ t₁ f hf_mono hγ_mono a b hab => hγ_mono (hf_mono hab)

/-- A continuous map `f : α → β` with α an (undirected) topological space and β a directed
topological space
  creates a directed structure on α by pulling back paths.
-/
@[reducible] def DirectedSpace.Induced {α : Type u} {β : Type v} [TopologicalSpace α]
    [hβ : DirectedSpace β] {f : α → β} (hf : Continuous f) : DirectedSpace α where
  IsDipath := fun {x y : α} γ => IsDipath (γ.map hf)
  isDipath_constant := fun x => isDipath_constant (f x)
  isDipath_concat := by
    rintro x y z γ₁ γ₂ hγ₁ hγ₂
    rw [Path.map_trans γ₁ γ₂ hf]
    exact isDipath_concat hγ₁ hγ₂
  isDipath_reparam := fun {x y : α} γ t₀ t₁ φ hφ_mono hγ => by
    exact isDipath_reparam hφ_mono hγ

instance DirectedSubspace {α : Type u} {p : α → Prop} [DirectedSpace α] :
  DirectedSpace (Subtype p) :=
  DirectedSpace.Induced continuous_induced_dom

section subtype

lemma directed_induced {α : Type u} {β : Type v} [TopologicalSpace α] [hβ : DirectedSpace β]
  (f : C(α, β)) :
  @DirectedMap.Directed α β (DirectedSpace.Induced f.continuous_toFun) hβ f := fun _ _ _ hγ => hγ

/-- The inclusion of a subtype with the induced directed structure into the ambient space
is a directed map. -/
def DirectedSubtypeInclusion {α : Type u} (p : α → Prop) [DirectedSpace α] :
    D(Subtype p, α) where
  toFun := fun x => ↑x
  continuous_toFun := continuous_induced_dom
  directed_toFun := directed_induced _

/-- The inclusion of one subset into another, when both carry the induced directed structure,
is a directed map. -/
def DirectedSubsetInclusion {α : Type u} [t : DirectedSpace α] {X Y : Set α} (h : X ⊆ Y) : D(X,Y)
    where
  toFun := Set.inclusion h
  continuous_toFun := continuous_inclusion h
  directed_toFun := by
    intros x y γ γ_dipath
    have cont_X := @continuous_induced_dom {x // x ∈ X} α (fun p => ↑p)
    have cont_Y := @continuous_induced_dom {x // x ∈ Y} α (fun p => ↑p)
    have cont_X_Y : Continuous (Set.inclusion h) := continuous_inclusion h
    change IsDipath ((γ.map cont_X_Y).map cont_Y)
    have : (γ.map cont_X) = ((γ.map cont_X_Y).map cont_Y) := by { ext; rfl }
    rw [←this]
    exact γ_dipath

end subtype

instance DirectedProduct {α : Type u} {β : Type v} [t₁ : DirectedSpace α] [t₂ : DirectedSpace β] :
  DirectedSpace (α × β) where
  IsDipath := fun {x y : α × β}
      γ => (IsDipath (γ.map continuous_fst) ∧ IsDipath (γ.map continuous_snd))
  isDipath_constant := fun ⟨x₁, x₂⟩ => ⟨isDipath_constant x₁, isDipath_constant x₂⟩
  isDipath_concat := by
      rintro _ _ _ p q ⟨p₁_dipath, p₂_dipath⟩ ⟨q₁_dipath, q₂_dipath⟩
      convert (And.intro (isDipath_concat p₁_dipath q₁_dipath)
        (isDipath_concat p₂_dipath q₂_dipath))
      · rw [Path.map_trans]
      rw [Path.map_trans]
  isDipath_reparam := fun {a b : α × β} γ t₀ t₁ φ hφ_mono ⟨γ₁_dipath, γ₂_dipath⟩ =>
      ⟨isDipath_reparam hφ_mono γ₁_dipath, isDipath_reparam hφ_mono γ₂_dipath⟩

/-- The projection map `α × β → α` -/
def directedFst {α β : Type*} [DirectedSpace α] [DirectedSpace β] : D(α × β, α) where
  toFun := fun x => x.1
  directed_toFun := fun _ _ γ ⟨hγ₁, _⟩ => hγ₁

/-- The projection map `α × β → β` -/
def directedSnd {α β : Type*} [DirectedSpace α] [DirectedSpace β] : D(α × β, β) where
  toFun := fun x => x.2
  directed_toFun := fun _ _ γ ⟨_, hγ₂⟩ => hγ₂

section prod

variable {α β γ δ : Type*} [DirectedSpace α] [DirectedSpace β] [DirectedSpace γ] [DirectedSpace δ]

/-- Two directed maps `f : α → β` and `g : α → γ` can be turned into a directed map `α → β × γ` by
  mapping `a : α` to `(f a, g a)`.
-/
protected def DirectedMap.prodMapMk (f : D(α,β)) (g : D(α,γ)) : D(α, β × γ) where
  toFun := fun x => (f x, g x)
  directed_toFun := fun x y γ hγ => ⟨f.directed_toFun γ hγ, g.directed_toFun γ hγ⟩

/-- Two directed maps `f : α → γ` and `g : β → δ` can be turned into a directed map `α × β → β × γ`
by
  mapping `(a, b) : α × β` to `(f a, g b)`.
-/
protected def DirectedMap.prodMapMk' (f : D(α,γ)) (g : D(β,δ)) : D(α × β, γ × δ) where
  toFun := fun x => (f x.1, g x.2)
  directed_toFun := fun x y γ ⟨hγ₁, hγ₂⟩ => ⟨f.directed_toFun _ hγ₁, g.directed_toFun _ hγ₂⟩

/-- For every `t : α`, we can convert a directed map `F : α × β → γ` to a directed map `β → γ` by
  sending `b` to `F(t, b)`
-/
def DirectedMap.prodConstFst (F : D(α × β,γ)) (a : α) : D(β,γ) :=
  F.comp (DirectedMap.prodMapMk (DirectedMap.const β a) (DirectedMap.id β))

@[simp] lemma DirectedMap.prod_const_fst_apply (F : D(α × β,γ)) (a : α) (b : β) :
  DirectedMap.prodConstFst F a b = F (a, b) := rfl

/-- For every `t : β`, we can convert a directed map `F : α × β → γ` to a directed map `α → γ` by
  sending `a` to `F(a, t)`
-/
def DirectedMap.prodConstSnd (F : D(α × β,γ)) (t : β) : D(α,γ) :=
  F.comp (DirectedMap.prodMapMk (DirectedMap.id α) (DirectedMap.const α t))

@[simp] lemma DirectedMap.prod_const_snd_apply (F : D(α × β,γ)) (b : β) (a : α) :
  DirectedMap.prodConstSnd F b a = F (a, b) := rfl

end prod
