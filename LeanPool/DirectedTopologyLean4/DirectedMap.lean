/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
import LeanPool.DirectedTopologyLean4.DirectedSpace

/-!
# LeanPool.DirectedTopologyLean4.DirectedMap
-/

/-
  # Definition of directed maps
  This file defines the directed map between two directed spaces `X` and `Y` :
  it is a continuous map from `X` to `Y` that is also `Directed`, i.e. it maps any dipath in `X` to
  a dipath in `Y`.
  We give the definitions of:
  * Constant maps
  * Identities
  * Composition of directed maps
-/

namespace DirectedMap

/-- A continuous map between two directed spaces is `Directed` if it maps dipaths to dipaths. -/
def Directed {α β : Type*} [DirectedSpace α] [DirectedSpace β] (f : C(α, β)) : Prop :=
  ∀ ⦃x y : α⦄ (γ : Path x y), IsDipath γ → IsDipath (γ.map f.continuous_toFun)

end DirectedMap

/-- Define the type of a directed map -/
structure DirectedMap (α β : Type*) [DirectedSpace α] [DirectedSpace β]
    extends ContinuousMap α β where
  protected directed_toFun : DirectedMap.Directed toContinuousMap

/-- Notation `D(X,Y)` for directed maps from `X` to `Y` -/
notation "D("α","β")" => DirectedMap α β

section

/-- Type class for the bundled directed maps from `α` to `β`. -/
class DirectedMapClass (F : Type*) (α β : outParam <| Type*) [DirectedSpace α] [DirectedSpace β]
  [FunLike F α β] : Prop extends ContinuousMapClass F α β where
  /-- Each element of the class is directed when viewed as a continuous map. -/
  map_directed (f : F) : DirectedMap.Directed (f : C(α, β))

end

export DirectedMapClass (map_directed)

section DirectedMapClass

variable {F α β : Type*} [DirectedSpace α] [DirectedSpace β] [FunLike F α β]
    [hF : DirectedMapClass F α β]
/-- Coerce a member of a `DirectedMapClass` to the bundled directed map type `D(α, β)`. -/
@[coe] def toDirectedMap (f : F) : D(α,β) := ⟨f, map_directed f⟩
instance : CoeTC F D(α,β) := ⟨toDirectedMap⟩

end DirectedMapClass

variable {α β γ δ : Type*} [DirectedSpace α] [DirectedSpace β] [DirectedSpace γ] [DirectedSpace δ]

namespace DirectedMap

instance instFunLike : FunLike D(α,β) α β where
  coe := fun f => f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

instance toDirectedMapClass : DirectedMapClass D(α,β) α β where
  map_continuous := fun f => f.continuous_toFun
  map_directed := fun f => f.directed_toFun

/-- Helper instance for when there's too many metavariables to apply `FunLike.hasCoeToFun` directly.
-/
instance : CoeFun (D(α,β)) fun _ => α → β := DFunLike.toCoeFun

/-- A directed map can be coerced into a continuous map -/
instance : Coe D(α,β) C(α, β) := ⟨fun f => f.toContinuousMap⟩

@[simp] lemma toFun_eq_coe {f : D(α,β)} : f.toFun = (f : α → β) := rfl
@[simp] lemma coe_to_continuous_map (f : D(α,β)) : ⇑f.toContinuousMap = f := rfl
@[simp] protected lemma coe_coe {F : Type*} [FunLike F α β] [DirectedMapClass F α β] (f : F)
    : ⇑(f : D(α,β)) = f := rfl

@[ext] theorem ext {f g : D(α,β)} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

variable (α)

/-- The identity map is directed -/
protected def id : D(α,α) where
  toFun := id
  directed_toFun := fun x y γ γ_path => γ_path

@[simp] lemma coe_id : ⇑(DirectedMap.id α) = id := rfl

/-- Constant maps are directed -/
def const (b : β) : D(α,β) where
  toFun := fun _ : α => b
  directed_toFun := fun x y γ _ => isDipath_constant b

@[simp] lemma coe_const (b : β) : ⇑(const α b) = Function.const α b := rfl

variable {α}

/-- The composition of directed maps is directed -/
def comp (f : D(β,γ)) (g : D(α,β)) : D(α,γ) where
  toFun := f ∘ g
  directed_toFun := fun x y p hp => f.directed_toFun (p.map g.continuous_toFun)
      (g.directed_toFun p hp)


@[simp] lemma id_apply (a : α) : DirectedMap.id α a = a := rfl
@[simp] lemma const_apply (b : β) (a : α) : const α b a = b := rfl
@[simp] lemma coe_comp (f : D(β,γ)) (g : D(α,β)) : ⇑(f.comp g) = f ∘ g := rfl
@[simp] lemma comp_apply (f : D(β,γ)) (g : D(α,β)) (a : α) : f.comp g a = f (g a) := rfl
@[simp] lemma comp_assoc (f : D(γ,δ)) (g : D(β,γ)) (h : D(α,β)) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma id_comp (f : D(α,β)) : (DirectedMap.id β).comp f = f := ext fun _ => rfl
@[simp] lemma comp_id (f : D(α,β)) : f.comp (DirectedMap.id α) = f := ext fun _ => rfl
@[simp] lemma const_comp (c : γ) (f : D(α,β)) : (const β c).comp f = const α c
    := ext <| fun _ => rfl
@[simp] lemma comp_const (f : D(β,γ)) (b : β) : f.comp (const α b) = const α (f b)
    := ext <| fun _ => rfl

lemma coe_injective : @Function.Injective D(α,β) (α → β) (↑) :=
  fun f g h => by cases f; cases g; congr; exact ContinuousMap.ext (congrFun h)

end DirectedMap
