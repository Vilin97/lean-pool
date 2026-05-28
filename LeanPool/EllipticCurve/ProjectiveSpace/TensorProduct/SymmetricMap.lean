/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Symmetric Multilinear Maps

In this file we define symmetric multilinear maps bewteen modules as a module itself.

## Main definitions

* `SymmetricMap R M N ι`: the symmetric `R`-multilinear maps from `ι → M` to `N`.

-/

universe u u' u₁ u₂ u₃ v w w'

open Equiv MultilinearMap Function

section Semiring

variable (R : Type u) [Semiring R] (M : Type v) [AddCommMonoid M] [Module R M]
  (N : Type w) [AddCommMonoid N] [Module R N]
  (P : Type w') [AddCommMonoid P] [Module R P] (ι : Type u') (ι' : Type u₁) (ι'' : Type u₂)

/-- An symmetric map from `ι → M` to `N`, denoted `M [Σ^ι]→ₗ[R] N`,
is a multilinear map that stays the same when its arguments are permuted. -/
structure SymmetricMap extends MultilinearMap R (fun _ : ι => M) N where
  /-- The map is symmetric: if the arguments of `v` are permuted, the result does not change. -/
  map_perm_apply' (v : ι → M) (e : Perm ι) : (toFun fun i ↦ v (e i)) = toFun v

@[inherit_doc]
notation M:arg " [Σ^" ι "]→ₗ[" R "] " N:arg => SymmetricMap R M N ι

namespace SymmetricMap

variable {R M N P ι} (f f₁ f₂ g g₁ g₂ : M [Σ^ι]→ₗ[R] N) (v x y : ι → M)

instance : FunLike (M [Σ^ι]→ₗ[R] N) (ι → M) N where
  coe f := f.toFun
  coe_injective' f g h := by
    rcases f with ⟨⟨_, _, _⟩, _⟩
    rcases g with ⟨⟨_, _, _⟩, _⟩
    congr

initialize_simps_projections SymmetricMap (toFun → apply)

variable [DecidableEq ι] in
@[simp] protected lemma map_update_add (g : ι → M) (c : ι) (x y : M) :
    f (update g c (x + y)) = f (update g c x) + f (update g c y) :=
  f.1.map_update_add g c x y

variable [DecidableEq ι] in
@[simp] protected lemma map_update_smul (g : ι → M) (c : ι) (r : R) (x : M) :
    f (update g c (r • x)) = r • f (update g c x) :=
  f.1.map_update_smul g c r x

lemma map_coord_zero {g : ι → M} (c : ι) (h : g c = 0) :
    f g = 0 :=
  f.1.map_coord_zero c h

variable [DecidableEq ι] in
@[simp] lemma map_update_zero (g : ι → M) (c : ι) :
    f (update g c 0) = 0 :=
  f.1.map_update_zero g c

@[simp] lemma map_zero [Nonempty ι] : f 0 = 0 :=
  f.1.map_zero

variable {f g} in
protected theorem congrFun (h : f = g) (x : ι → M) : f x = g x :=
  congr_arg (fun h : M [Σ^ι]→ₗ[R] N => h x) h

variable {x y} in
protected theorem congrArg (h : x = y) : f x = f y :=
  congr_arg (fun x : ι → M => f x) h

theorem coe_injective : Injective ((↑) : M [Σ^ι]→ₗ[R] N → (ι → M) → N) :=
  DFunLike.coe_injective

variable {f g} in
@[norm_cast]
theorem coe_inj : (f : (ι → M) → N) = g ↔ f = g :=
  coe_injective.eq_iff

variable {f g} in
@[ext] lemma ext (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

attribute [coe] SymmetricMap.toMultilinearMap

instance : Coe (M [Σ^ι]→ₗ[R] N) (MultilinearMap R (fun _ : ι ↦ M) N) :=
  ⟨fun f ↦ f.toMultilinearMap⟩

lemma toMultilinearMap_injective :
    Function.Injective (toMultilinearMap : M [Σ^ι]→ₗ[R] N → MultilinearMap R (fun _ : ι ↦ M) N) :=
  fun _ _ h ↦ ext <| congr_fun h

@[simp, norm_cast] lemma coe_coe : ⇑(f : MultilinearMap R (fun _ : ι ↦ M) N) = f := rfl

@[simp] lemma coe_mk (f : MultilinearMap R (fun _ : ι ↦ M) N) (h) :
  ⇑(⟨f, h⟩ : M [Σ^ι]→ₗ[R] N) = f := rfl

@[simp] lemma map_perm_apply (e : Perm ι) (x : ι → M) : (f fun i ↦ x (e i)) = f x :=
  f.2 x e

@[simp] lemma comp_domDomCongr (e : Perm ι) : f.1.domDomCongr e = f :=
  MultilinearMap.ext (f.2 · e)

/-- Build a `SymmetricMap` from a multilinear map that is invariant under `domDomCongr`. -/
@[simp] def mk' (f : MultilinearMap R (fun _ : ι ↦ M) N) (h : ∀ e, f.domDomCongr e = f) :
    M [Σ^ι]→ₗ[R] N :=
  ⟨f, fun v e ↦ DFunLike.congr_fun (h e) v⟩

instance : Add (M [Σ^ι]→ₗ[R] N) :=
  ⟨fun f g ↦ ⟨f.1 + g.1, fun v e ↦ by simp⟩⟩

@[simp] theorem add_coe : ⇑(f + g) = f + g := rfl

@[norm_cast] theorem coe_add : (f + g : M [Σ^ι]→ₗ[R] N).1 = f + g := rfl

instance : Zero (M [Σ^ι]→ₗ[R] N) :=
  ⟨⟨0, fun _ _ ↦ rfl⟩⟩

@[simp] theorem zero_coe : ⇑(0 : M [Σ^ι]→ₗ[R] N) = 0 := rfl

@[norm_cast] theorem coe_zero : (0 : M [Σ^ι]→ₗ[R] N).1 = 0 := rfl

@[simp] theorem mk_zero (h) : mk (0 : MultilinearMap R (fun _ : ι ↦ M) N) h = 0 := rfl

variable {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]

instance : SMul S (M [Σ^ι]→ₗ[R] N) :=
  { smul := fun c f ↦ ⟨c • f.1, fun v e ↦ by simp⟩ }

@[simp] theorem smul_coe (c : S) : ⇑(c • f) = c • f :=
  rfl

@[norm_cast] theorem coe_smul (c : S) : ↑(c • f) = c • f.1 :=
  rfl

theorem coeFn_smul (c : S) (f : M [Σ^ι]→ₗ[R] N) : ⇑(c • f) = c • ⇑f :=
  rfl

instance instSMulCommClass {T : Type*} [Monoid T] [DistribMulAction T N] [SMulCommClass R T N]
    [SMulCommClass S T N] : SMulCommClass S T (M [Σ^ι]→ₗ[R] N) where
  smul_comm _ _ _ := ext fun _ ↦ smul_comm ..

instance instIsCentralScalar [DistribMulAction Sᵐᵒᵖ N] [IsCentralScalar S N] :
    IsCentralScalar S (M [Σ^ι]→ₗ[R] N) :=
  ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩

instance : AddCommMonoid (M [Σ^ι]→ₗ[R] N) := fast_instance%
  coe_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

instance instDistribMulAction : DistribMulAction S (M [Σ^ι]→ₗ[R] N) where
  one_smul _ := ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _
  smul_zero _ := ext fun _ => smul_zero _
  smul_add _ _ _ := ext fun _ => smul_add _ _ _

variable {S' : Type*} [Semiring S'] [Module S' N] [SMulCommClass R S' N]

/-- The space of multilinear maps over an algebra over `R` is a module over `R`, for the pointwise
addition and scalar multiplication. -/
instance : Module S' (M [Σ^ι]→ₗ[R] N) where
  add_smul _ _ _ := ext fun _ => add_smul _ _ _
  zero_smul _ := ext fun _ => zero_smul _ _

instance [NoZeroSMulDivisors S' N] :
    NoZeroSMulDivisors S' (M [Σ^ι]→ₗ[R] N) where
  eq_zero_or_eq_zero_of_smul_eq_zero {c f} h := by
    by_cases hc : c = 0
    · exact .inl hc
    · refine .inr (ext fun x ↦ ?_)
      have := congr(⇑$h x)
      rw [smul_coe, Pi.smul_apply, zero_coe, Pi.zero_apply] at this
      exact (eq_zero_or_eq_zero_of_smul_eq_zero this).resolve_left hc

/-- Embedding of symmetric maps into multilinear maps as a linear map. -/
@[simps]
def toMultilinearMapLM : (M [Σ^ι]→ₗ[R] N) →ₗ[S'] MultilinearMap R (fun _ : ι ↦ M) N where
  toFun := toMultilinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Composing a symmetric map with a linear map on the source, yielding a symmetric map. -/
def compLinearMap (f : N [Σ^ι]→ₗ[R] P) (g : M →ₗ[R] N) :
    M [Σ^ι]→ₗ[R] P :=
  ⟨f.1.compLinearMap fun _ ↦ g, fun x e ↦ f.map_perm_apply e (g ∘ x)⟩

@[simp] lemma compLinearMap_coe (f : N [Σ^ι]→ₗ[R] P) (g : M →ₗ[R] N) :
    ⇑(f.compLinearMap g) = ⇑f ∘ fun x i ↦ g (x i) := rfl

lemma compLinearMap_apply (f : N [Σ^ι]→ₗ[R] P) (g : M →ₗ[R] N) (x : ι → M) :
    f.compLinearMap g x = f (g ∘ x) := rfl

variable (P ι) in
/-- Precomposition with a fixed linear map on the source, as an additive monoid homomorphism on
symmetric maps. -/
def compLinearMapAddHom (f : M →ₗ[R] N) :
    (N [Σ^ι]→ₗ[R] P) →+ (M [Σ^ι]→ₗ[R] P) :=
  { toFun g := compLinearMap g f
    map_zero' := rfl
    map_add' _ _ := rfl }

@[simp] lemma compLinearMapAddHom_coe (f : M →ₗ[R] N) :
    ⇑(compLinearMapAddHom P ι f) = (compLinearMap · f) := rfl

lemma compLinearMapAddHom_apply (f : M →ₗ[R] N) (g : N [Σ^ι]→ₗ[R] P) :
    compLinearMapAddHom P ι f g = compLinearMap g f := rfl

lemma compLinearMap_add (f₁ f₂ : N [Σ^ι]→ₗ[R] P) (g : M →ₗ[R] N) :
    compLinearMap (f₁ + f₂) g = compLinearMap f₁ g + compLinearMap f₂ g := rfl

variable (P ι) (S'' : Type*) [Semiring S''] [Module S'' P] [SMulCommClass R S'' P] in
/-- Precomposition with a fixed linear map on the source, as a linear map on symmetric maps. -/
def compLinearMapₗ (f : M →ₗ[R] N) : (N [Σ^ι]→ₗ[R] P) →ₗ[S''] (M [Σ^ι]→ₗ[R] P) :=
  { __ := compLinearMapAddHom P ι f
    map_smul' _ _ := rfl }

variable (S'' : Type*) [Semiring S''] [Module S'' P] [SMulCommClass R S'' P] in
@[simp] lemma compLinearMapₗ_coe (f : M →ₗ[R] N) :
    ⇑(compLinearMapₗ P ι S'' f) = (compLinearMap · f) := rfl

variable (S'' : Type*) [Semiring S''] [Module S'' P] [SMulCommClass R S'' P] in
lemma compLinearMapₗ_apply (f : M →ₗ[R] N) (g : N [Σ^ι]→ₗ[R] P) :
    compLinearMapₗ P ι S'' f g = compLinearMap g f := rfl

end SymmetricMap

namespace LinearMap

variable {R M N P ι}

/-- Composing a linear map with a symmetric map on the target, yielding a symmetric map. -/
def compSymmetricMap
    (f : N →ₗ[R] P) (g : SymmetricMap R M N ι) : SymmetricMap R M P ι :=
  ⟨f.compMultilinearMap g, fun x e ↦ f.congr_arg <| g.map_perm_apply e x⟩

@[simp] lemma compSymmetricMap_coe
    (f : N →ₗ[R] P) (g : SymmetricMap R M N ι) :
    ⇑(f.compSymmetricMap g) = ⇑f ∘ ⇑g :=
  rfl

lemma compSymmetricMap_apply
    (f : N →ₗ[R] P) (g : SymmetricMap R M N ι) (x : ι → M) :
    f.compSymmetricMap g x = f (g x) :=
  rfl

variable (M ι) in
/-- Postcomposition with a fixed linear map on the target, as an additive monoid homomorphism on
symmetric maps. -/
def compSymmetricMapAddHom (f : N →ₗ[R] P) :
    SymmetricMap R M N ι →+ SymmetricMap R M P ι :=
  { toFun := compSymmetricMap f
    map_zero' := SymmetricMap.ext fun _ ↦ f.map_zero
    map_add' _ _ := SymmetricMap.ext fun _ ↦ f.map_add _ _ }

@[simp] lemma compSymmetricMapAddHom_coe (f : N →ₗ[R] P) :
    ⇑(compSymmetricMapAddHom M ι f) = compSymmetricMap f :=
  rfl

variable (S : Type*) [Semiring S] [Module S N] [SMulCommClass R S N]
  [Module S P] [SMulCommClass R S P] [CompatibleSMul N P S R] in
/-- Postcomposition with a fixed linear map on the target, as a linear map on symmetric maps. -/
def compSymmetricMapₗ (f : N →ₗ[R] P) : SymmetricMap R M N ι →ₗ[S] SymmetricMap R M P ι :=
  { __ := compSymmetricMapAddHom M ι f
    map_smul' c g := SymmetricMap.ext fun x ↦ map_smul_of_tower f c (g x) }

end LinearMap

namespace SymmetricMap

/-- A symmetric map out of an empty index type is the same as an element of the target. -/
@[simps] def ofIsEmpty [IsEmpty ι] : (M [Σ^ι]→ₗ[R] N) ≃+ N where
  toFun f := f isEmptyElim
  invFun n := { toFun _ := n
                map_update_add' _ := isEmptyElim
                map_update_smul' _ := isEmptyElim
                map_perm_apply' _ _ := rfl }
  map_add' _ _ := rfl
  left_inv f := ext fun _ ↦ congrArg f <| Subsingleton.elim _ _
  right_inv _ := rfl

variable {ι} in
/-- A symmetric map out of a subsingleton index type is the same as a linear map. -/
@[simps!] def ofSubsingleton [Subsingleton ι] (i : ι) : (M [Σ^ι]→ₗ[R] N) ≃+ (M →ₗ[R] N) where
  toFun f :=
  { toFun m := f (const ι m)
    map_add' m₁ m₂ := by
      convert f.map_update_add 0 i m₁ m₂ using 2 <;>
      simp [eq_const_of_subsingleton (update _ _ _) i]
    map_smul' c m := by
      convert f.map_update_smul 0 i c m using 2 <;>
      simp [eq_const_of_subsingleton (update _ _ _) i]}
  invFun f := ⟨MultilinearMap.ofSubsingleton R M N i f, fun v e ↦
    by simp [Perm.subsingleton_eq_refl]⟩
  map_add' f g := rfl
  left_inv f := ext fun v ↦ congrArg f (eq_const_of_subsingleton v i).symm
  right_inv f := rfl

/-- A symmetric map out of a unique index type is the same as a linear map. -/
@[simps!] def isUnique [Unique ι] : (M [Σ^ι]→ₗ[R] N) ≃+ (M →ₗ[R] N) :=
  ofSubsingleton R M N default

variable {R M N ι ι' ι''}

/-- Reinterpret a symmetric `R`-map as a symmetric `S`-map, given `IsScalarTower S R M` and
`IsScalarTower S R N`. -/
def restrictScalars (S : Type*) [Semiring S] [SMul S R] [Module S M] [Module S N]
    [IsScalarTower S R M] [IsScalarTower S R N]
    (f : M [Σ^ι]→ₗ[R] N) : M [Σ^ι]→ₗ[S] N :=
  ⟨f.1.restrictScalars S, fun v e ↦ f.2 v e⟩

/-- Reindex the arguments of a symmetric map along an equivalence of index types. -/
def domDomCongr (e : ι ≃ ι') (f : M [Σ^ι]→ₗ[R] N) : M [Σ^ι']→ₗ[R] N :=
  ⟨f.1.domDomCongr e, fun v e₁ ↦ calc
    (f fun i ↦ v (e₁ (e i)))
      = (f fun i ↦ v (e (e.permCongr.symm e₁ i))) := by simp
    _ = (f fun i ↦ v (e i)) := f.2 (v ∘ e) (e.permCongr.symm e₁)⟩

@[simp] lemma domDomCongr_apply (e : ι ≃ ι') (f : M [Σ^ι]→ₗ[R] N) (v : ι' → M) :
    domDomCongr e f v = f (fun i ↦ v (e i)) :=
  rfl

lemma domDomCongr_trans (e₁ : ι ≃ ι') (e₂ : ι' ≃ ι'') (f : M [Σ^ι]→ₗ[R] N) :
    domDomCongr (e₁.trans e₂) f = domDomCongr e₂ (domDomCongr e₁ f) :=
  rfl

@[simp] lemma domDomCongr_refl (f : M [Σ^ι]→ₗ[R] N) :
    domDomCongr (Equiv.refl ι) f = f :=
  rfl

variable (R M N) (S : Type*) [Semiring S] [Module S N] [SMulCommClass R S N] in
/-- Reindexing the arguments of a symmetric map along an equivalence of index types, packaged as a
linear equivalence. -/
def domDomCongrLinearEquiv (e : ι ≃ ι') : (M [Σ^ι]→ₗ[R] N) ≃ₗ[S] (M [Σ^ι']→ₗ[R] N) where
  toFun f := f.domDomCongr e
  invFun f := f.domDomCongr e.symm
  left_inv f := by simp [← domDomCongr_trans]
  right_inv f := by simp [← domDomCongr_trans]
  map_add' f₁ f₂ := ext fun v ↦ by simp
  map_smul' c f := ext fun v ↦ by simp

variable (S : Type*) [Semiring S] [Module S N] [SMulCommClass R S N] in
@[simp] lemma domDomCongrLinearEquiv_apply (e : ι ≃ ι') (f : M [Σ^ι]→ₗ[R] N) (v : ι' → M) :
    domDomCongrLinearEquiv R M N S e f v = f (fun i ↦ v (e i)) :=
  rfl

end SymmetricMap

end Semiring


section CommSemiring

variable {R : Type u} [CommSemiring R] {M : Type v} [AddCommMonoid M] [Module R M]
  {N : Type w} [AddCommMonoid N] [Module R N] {ι : Type u'}

lemma map_smul_univ [Fintype ι] (f : M [Σ^ι]→ₗ[R] N) (c : ι → R) (v : ι → M) :
    f (fun i ↦ c i • v i) = (∏ i, c i) • f v :=
  MultilinearMap.map_smul_univ f.1 c v

variable (R ι) (A : Type w') [CommSemiring A] [Algebra R A]

/-- The symmetric map sending `v : ι → A` to the product `∏ i, v i` in the `R`-algebra `A`. -/
def mkPiAlgebra [Fintype ι] : A [Σ^ι]→ₗ[R] A :=
  ⟨.mkPiAlgebra R ι A, fun v e ↦ by simp [Fintype.prod_equiv e]⟩

@[simp] lemma mkPiAlgebra_apply [Fintype ι] (v : ι → A) :
    mkPiAlgebra R ι A v = ∏ i, v i := rfl

end CommSemiring
