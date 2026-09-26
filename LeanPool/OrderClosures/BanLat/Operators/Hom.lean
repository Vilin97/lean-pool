/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

public import LeanPool.OrderClosures.BanLat.Operators.Positive
public import LeanPool.OrderClosures.BanLat.LLexpr
public import Mathlib.Analysis.Normed.Operator.LinearIsometry


/-!
# Morphisms of vector lattices

This file defines `VecLatHom`, the type of vector lattice homomorphisms — maps that are
simultaneously real-linear and lattice homomorphisms — together with the
proposition-valued predicate `IsVecLatHom` characterising such maps. Key results include
the characterisation of vector lattice homomorphisms by their behaviour on absolute
values (`VecLatHom.ofAbs`) and the fact that every vector lattice homomorphism is monotone.

The second section develops `VecLatEquiv`, the type of vector lattice isomorphisms. It
packages `Positive.extensionEquiv`, which extends an additive bijection between positive
cones to a vector lattice isomorphism, and `toContinuousLinearEquiv`, which turns a
vector lattice isomorphism between Banach lattices into a continuous linear equivalence.

The final section introduces `BanachLatEquiv`, the type of Banach lattice isometries:
real linear isometric equivalences that also preserve `⊔` and `⊓`.
-/

@[expose] public section

/-! ## Vector lattice homomorphisms -/

/-- A vector lattice homomorphism from `X` to `Y`: a real-linear map that also preserves
`⊔` and `⊓`. -/
structure VecLatHom (X : Type*) (Y : Type*) [AddCommGroup X] [AddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [VectorLattice X] [VectorLattice Y] extends X →ₗ[ℝ] Y, LatticeHom X Y

attribute [inherit_doc LatticeHom] VecLatHom.toLatticeHom

variable {X : Type*} {Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [VectorLattice X] [VectorLattice Y]

/-- Predicate form of `VecLatHom`: a map is a vector lattice homomorphism if it is linear
and preserves `⊔` and `⊓`. -/
structure IsVecLatHom (f : X → Y) extends IsLinearMap ℝ f where
  map_sup' : ∀ x y : X, f (x ⊔ y) = (f x) ⊔ (f y)
  map_inf' : ∀ x y : X, f (x ⊓ y) = (f x) ⊓ (f y)

namespace VecLatHom

/-- The canonical `FunLike` instance, making `VecLatHom X Y` a type of functions `X → Y`. -/
instance instFunLike : FunLike (VecLatHom X Y) X Y where
  coe f := f.toFun
  coe_injective f g h := by
    dsimp at h
    cases f
    cases g
    congr
    exact LinearMap.ext_iff.mpr (congrFun h)

/-- Every `VecLatHom` satisfies the `IsVecLatHom` predicate. -/
theorem isVecLatHom (f : VecLatHom X Y) : IsVecLatHom f where
  map_add := f.toLinearMap.map_add
  map_smul := f.toLinearMap.map_smul
  map_sup' := f.toLatticeHom.map_sup'
  map_inf' := f.toLatticeHom.map_inf'

/-- Construct a `VecLatHom` from a proof that a function satisfies `IsVecLatHom`. -/
def ofIsVecLatHom (f : X → Y) (h : IsVecLatHom f) : VecLatHom X Y where
  toFun := f
  map_add' := h.map_add
  map_smul' := h.map_smul
  map_sup' := h.map_sup'
  map_inf' := h.map_inf'

/-- `VecLatHom X Y` is a `LatticeHomClass`. -/
instance instLatticeHomClass : LatticeHomClass (VecLatHom X Y) X Y where
  map_inf := by
    intro f a b
    exact f.toLatticeHom.map_inf' a b
  map_sup := by
    intro f a b
    exact f.toLatticeHom.map_sup' a b

/-- `VecLatHom X Y` is a `LinearMapClass`. -/
instance instLinearMapClass : LinearMapClass (VecLatHom X Y) ℝ X Y where
  map_add := by
    intro f a b
    exact f.toLinearMap.map_add a b
  map_smulₛₗ := by
    intro f c x
    simp only [RingHom.id_apply]
    exact f.toLinearMap.map_smul c x

/-- The underlying function of a `VecLatHom` equals its coercion to `X → Y`. -/
theorem toFun_eq_coe {f : VecLatHom X Y} : f.toFun = (f : X → Y) := rfl

/-- A vector lattice homomorphism preserves absolute values. -/
theorem map_abs (f : VecLatHom X Y) (x : X) : f |x| = |f x| := by
  rw [abs, abs, map_sup, map_neg]

/-- Every vector lattice homomorphism is monotone. -/
theorem monotone (f : VecLatHom X Y) : Monotone f := by
  intro x y hxy
  have : x ⊔ y = y := by simp [hxy]
  rw [← sup_eq_right, ← map_sup f x y, this]

/-- A vector lattice homomorphism maps nonneg elements to nonneg elements. -/
theorem map_nonneg (f : VecLatHom X Y) {x : X} (hx : 0 ≤ x) : 0 ≤ f x := by
  have h := f.monotone hx; rwa [map_zero] at h

/-- An injective vector lattice homomorphism reflects the order: if `f a ≤ f b` then
`a ≤ b`. Together with `monotone`, an injective vector lattice homomorphism is an order
embedding. -/
theorem le_of_map_le (f : VecLatHom X Y) (hf : Function.Injective f) {a b : X}
    (hab : f a ≤ f b) : a ≤ b :=
  sup_eq_right.mp (hf (by rw [map_sup f a b]; exact sup_eq_right.mpr hab))

/-- A vector lattice homomorphism preserves positive parts: `f x⁺ = (f x)⁺`. -/
theorem map_posPart (f : VecLatHom X Y) (x : X) : f x⁺ = (f x)⁺ := by
  rw [posPart_def, map_sup, map_zero, posPart_def]

/-- A vector lattice homomorphism preserves negative parts: `f x⁻ = (f x)⁻`. -/
theorem map_negPart (f : VecLatHom X Y) (x : X) : f x⁻ = (f x)⁻ := by
  rw [negPart_def, map_sup, map_neg, map_zero, negPart_def]

/-- A vector lattice homomorphism preserves disjointness: `x ⊓ y = 0 → f x ⊓ f y = 0`. -/
theorem map_disjoint (f : VecLatHom X Y) {x y : X} (h : x ⊓ y = 0) : f x ⊓ f y = 0 := by
  rw [← map_inf, h, map_zero]

/-- The identity vector lattice homomorphism. -/
def id : VecLatHom X X :=
  { LinearMap.id with
    map_sup' := fun _ _ => rfl
    map_inf' := fun _ _ => rfl }

/-- Construct a `VecLatHom` from a linear map that preserves absolute values. -/
def ofAbs (f : X →ₗ[ℝ] Y) (abs : ∀ x : X, f |x| = |f x|) : VecLatHom X Y :=
  { f with
    map_sup' := fun a b => by
      change f (a ⊔ b) = f a ⊔ f b
      rw [sup_eq_half_smul_add_add_abs_sub' ℝ, map_smul, map_add, map_add,
          abs (b - a), map_sub, ← sup_eq_half_smul_add_add_abs_sub' ℝ]
    map_inf' := fun a b => by
      change f (a ⊓ b) = f a ⊓ f b
      rw [inf_eq_half_smul_add_sub_abs_sub' ℝ, map_smul, map_sub, map_add,
          abs (b - a), map_sub, ← inf_eq_half_smul_add_sub_abs_sub' ℝ] }

/-- Composition of two vector lattice homomorphisms. -/
def comp {Z : Type*} [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z]
  [VectorLattice Z] (g : VecLatHom Y Z) (f : VecLatHom X Y) :
  VecLatHom X Z :=
  {LinearMap.comp g.toLinearMap f.toLinearMap with
    map_sup' := by
      intro x y
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_comp,
        Function.comp_apply]
      change g ( f (x ⊔ y) ) = (g (f x)) ⊔ (g (f y))
      simp only [map_sup]
    map_inf' := by
      intro x y
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_comp,
        Function.comp_apply]
      change g ( f (x ⊓ y) ) = (g (f x)) ⊓ (g (f y))
      simp only [map_inf]
  }

/-- Evaluation of a composed `VecLatHom`. -/
theorem comp_apply {Z : Type*} [AddCommGroup Z] [Lattice Z]
  [IsOrderedAddMonoid Z] [VectorLattice Z] (g : VecLatHom Y Z)
  (f : VecLatHom X Y) (x : X) : g.comp f x = g (f x) := by
    rw [comp]
    change (LinearMap.comp g.toLinearMap f.toLinearMap) x = g (f x)
    simp
    rfl

/-- The inverse of a bijective vector lattice homomorphism is again a vector lattice
homomorphism. -/
noncomputable def symm (f : VecLatHom X Y) (h : Function.Bijective f) : VecLatHom Y X :=
  {(LinearEquiv.ofBijective f.toLinearMap h).symm with
    map_sup' := by
      intro a b
      change
        (LinearEquiv.ofBijective f.toLinearMap h).symm (a ⊔ b) =
        (LinearEquiv.ofBijective f.toLinearMap h).symm a ⊔
        (LinearEquiv.ofBijective f.toLinearMap h).symm b
      rw [LinearEquiv.symm_apply_eq]
      change
        a ⊔ b = f ( (LinearEquiv.ofBijective f.toLinearMap h).symm a ⊔
        (LinearEquiv.ofBijective f.toLinearMap h).symm b)
      rw [map_sup]
      change
        a ⊔ b = LinearEquiv.ofBijective f.toLinearMap h
                ((LinearEquiv.ofBijective f.toLinearMap h).symm a) ⊔
                LinearEquiv.ofBijective f.toLinearMap h
                ((LinearEquiv.ofBijective f.toLinearMap h).symm b)
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    map_inf' := by
      intro a b
      change
        (LinearEquiv.ofBijective f.toLinearMap h).symm (a ⊓ b) =
        (LinearEquiv.ofBijective f.toLinearMap h).symm a ⊓
        (LinearEquiv.ofBijective f.toLinearMap h).symm b
      rw [LinearEquiv.symm_apply_eq]
      change
        a ⊓ b = f ( (LinearEquiv.ofBijective f.toLinearMap h).symm a ⊓
        (LinearEquiv.ofBijective f.toLinearMap h).symm b)
      rw [map_inf]
      change
        a ⊓ b = LinearEquiv.ofBijective f.toLinearMap h
                ((LinearEquiv.ofBijective f.toLinearMap h).symm a) ⊓
                LinearEquiv.ofBijective f.toLinearMap h
                ((LinearEquiv.ofBijective f.toLinearMap h).symm b)
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  }

/-- The inverse bijection from `symm`: `(f.symm h) y = x ↔ y = f x`. -/
theorem symm_apply (f : VecLatHom X Y) (h : Function.Bijective f)
  (x : X) (y : Y) : (f.symm h) y = x ↔ y = f x := by
    let lineq := LinearEquiv.ofBijective f.toLinearMap h
    change lineq.symm y = x ↔ y = f x
    apply LinearEquiv.symm_apply_eq

end VecLatHom

namespace LLexpr

variable {n : ℕ}

/-- A vector lattice homomorphism commutes with evaluation of lattice-linear expressions. -/
theorem map_eval {Y Z : Type*}
    [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]
    [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z] [VectorLattice Z]
    (T : VecLatHom Y Z) (y : Fin n → Y) (e : LLexpr n) :
    T (eval y e) = eval (fun i => T (y i)) e := by
  induction e with
  | zero => simp [eval]
  | var i => simp [eval]
  | add e₁ e₂ h₁ h₂ => simp [eval, h₁, h₂]
  | smul r e h => simp [eval, h]
  | sup e₁ e₂ h₁ h₂ => simp [eval, h₁, h₂, map_sup]
  | inf e₁ e₂ h₁ h₂ => simp [eval, h₁, h₂, map_inf]

end LLexpr

namespace IsVecLatHom

/-- Bundle an `IsVecLatHom` proof into a `VecLatHom`. -/
def mk' (f : X → Y) (vlh : IsVecLatHom f) : VecLatHom X Y where
  toFun := f
  map_add' := vlh.map_add
  map_smul' := vlh.map_smul
  map_sup' := vlh.map_sup'
  map_inf' := vlh.map_inf'

/-- Evaluation of `mk'` agrees with the underlying function. -/
@[simp]
theorem mk'_apply {f : X → Y} (vlh : IsVecLatHom f) (x : X) :
    mk' f vlh x = f x := rfl

/-- A linear map that preserves absolute values satisfies `IsVecLatHom`. -/
theorem of_abs {f : X → Y} (lin : IsLinearMap ℝ f) (abs : ∀ x : X, f |x|
  = |f x|) : IsVecLatHom f :=
  VecLatHom.isVecLatHom (VecLatHom.ofAbs (IsLinearMap.mk' f lin) abs)

/-- A positive linear map that preserves disjointness is a vector lattice homomorphism. -/
theorem of_disjoint {f : X → Y} (lin : IsLinearMap ℝ f)
    (_pos : ∀ x : X, 0 ≤ x → 0 ≤ f x)
    (disj : ∀ x y : X, x ⊓ y = 0 → f x ⊓ f y = 0) : IsVecLatHom f := by
  have fNeg : ∀ x : X, f (-x) = -f x := fun x => by
    have h := lin.map_smul (-1 : ℝ) x; rwa [neg_one_smul, neg_one_smul] at h
  have fSub : ∀ x y : X, f (x - y) = f x - f y := fun x y => by
    rw [sub_eq_add_neg, lin.map_add, fNeg, ← sub_eq_add_neg]
  have fPosPart : ∀ c : X, f c⁺ = (f c)⁺ := fun c =>
    uniqueness_posPart (f c) (by rw [← fSub, posPart_sub_negPart])
      (disj c⁺ c⁻ (posPart_inf_negPart_eq_zero c))
  have fSup : ∀ a b : X, f (a ⊔ b) = f a ⊔ f b := fun a b => by
    rw [sup_eq_add_posPart_sub, lin.map_add, fPosPart, fSub, ← sup_eq_add_posPart_sub]
  exact { lin with
    map_sup' := fSup
    map_inf' := fun a b => by
      have h := fSup (-a) (-b)
      rw [← neg_inf] at h
      rw [fNeg, fNeg a, fNeg b, ← neg_inf] at h
      exact neg_inj.mp h }

end IsVecLatHom

/-! ## Vector lattice isomorphisms -/

/-- A vector lattice isomorphism: a real-linear equivalence that also preserves `⊔` and `⊓`. -/
structure VecLatEquiv (X : Type*) (Y : Type*) [AddCommGroup X] [AddCommGroup Y]
    [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
    [VectorLattice X] [VectorLattice Y] extends X ≃ₗ[ℝ] Y, LatticeHom X Y

attribute [inherit_doc LatticeHom] VecLatEquiv.toLatticeHom

namespace VecLatEquiv

/-- The canonical `FunLike` instance, making `VecLatEquiv X Y` a type of functions `X → Y`. -/
instance instFunLike : FunLike (VecLatEquiv X Y) X Y where
  coe e := e.toFun
  coe_injective := by
    intro f g h
    cases f; cases g
    congr 1
    exact LinearEquiv.ext (congrFun h)

/-- Coerce a `VecLatEquiv` to a `VecLatHom`. -/
def toVecLatHom (e : VecLatEquiv X Y) : VecLatHom X Y :=
  { e.toLinearMap with
    map_sup' := e.map_sup'
    map_inf' := e.map_inf' }

/-- The identity vector lattice isomorphism. -/
def refl : VecLatEquiv X X :=
  { LinearEquiv.refl ℝ X with
    map_sup' := fun _ _ => rfl
    map_inf' := fun _ _ => rfl }

/-- The inverse of a vector lattice isomorphism. -/
def symm (e : VecLatEquiv X Y) : VecLatEquiv Y X :=
  { e.toLinearEquiv.symm with
    map_sup' := fun a b => by
      have h := e.map_sup' (e.toLinearEquiv.symm a) (e.toLinearEquiv.symm b)
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] at h
      change e.toLinearEquiv.symm (a ⊔ b) = e.toLinearEquiv.symm a ⊔ e.toLinearEquiv.symm b
      exact e.toLinearEquiv.injective (by rw [LinearEquiv.apply_symm_apply]; exact h.symm)
    map_inf' := fun a b => by
      have h := e.map_inf' (e.toLinearEquiv.symm a) (e.toLinearEquiv.symm b)
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] at h
      change e.toLinearEquiv.symm (a ⊓ b) = e.toLinearEquiv.symm a ⊓ e.toLinearEquiv.symm b
      exact e.toLinearEquiv.injective (by rw [LinearEquiv.apply_symm_apply]; exact h.symm) }

/-- Composition of vector lattice isomorphisms. -/
def trans {Z : Type*} [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z] [VectorLattice Z]
    (e₁ : VecLatEquiv X Y) (e₂ : VecLatEquiv Y Z) : VecLatEquiv X Z :=
  { e₁.toLinearEquiv.trans e₂.toLinearEquiv with
    map_sup' := fun a b => by
      change e₂.toFun (e₁.toFun (a ⊔ b)) = e₂.toFun (e₁.toFun a) ⊔ e₂.toFun (e₁.toFun b)
      rw [e₁.map_sup', e₂.map_sup']
    map_inf' := fun a b => by
      change e₂.toFun (e₁.toFun (a ⊓ b)) = e₂.toFun (e₁.toFun a) ⊓ e₂.toFun (e₁.toFun b)
      rw [e₁.map_inf', e₂.map_inf'] }

end VecLatEquiv

/-! ### Extension from the positive cone -/

namespace Positive

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Lattice X] [Lattice Y]
  [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]
  [IsVLArchimedean Y] {τ : X → Y}
  (hτ_nn : ∀ x, 0 ≤ x → 0 ≤ τ x)
  (hτ_add : ∀ x y, 0 ≤ x → 0 ≤ y → τ (x + y) = τ x + τ y)

/-- An additive bijection between positive cones extends to a vector lattice
isomorphism when the codomain is Archimedean. -/
noncomputable def extensionEquiv
    (hτ_inj : ∀ x y, 0 ≤ x → 0 ≤ y → τ x = τ y → x = y)
    (hτ_surj : ∀ y, 0 ≤ y → ∃ x, 0 ≤ x ∧ τ x = y) :
    VecLatEquiv X Y := by
  set T := extension hτ_nn hτ_add
  have hT_inj : Function.Injective T := by
    intro a b hab
    have h : T (a - b) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr hab
    rw [extension_apply] at h
    have heq : (a - b)⁺ = (a - b)⁻ :=
      hτ_inj _ _ (posPart_nonneg _) (negPart_nonneg _) (sub_eq_zero.mp h)
    have hsub := posPart_sub_negPart (a - b)
    rw [heq, sub_self] at hsub
    exact sub_eq_zero.mp hsub.symm
  have hT_surj : Function.Surjective T := by
    intro y
    obtain ⟨a, ha, haτ⟩ := hτ_surj y⁺ (posPart_nonneg y)
    obtain ⟨b, hb, hbτ⟩ := hτ_surj y⁻ (negPart_nonneg y)
    exact ⟨a - b, by
      rw [map_sub, extension_nonneg hτ_nn hτ_add ha,
        extension_nonneg hτ_nn hτ_add hb, haτ, hbτ,
        posPart_sub_negPart]⟩
  -- T is order-reflecting: 0 ≤ Tx → 0 ≤ x
  have hT_bipos : ∀ x, 0 ≤ T x → 0 ≤ x := by
    intro x hTx
    rw [extension_apply] at hTx
    have hτle : τ x⁻ ≤ τ x⁺ := sub_nonneg.mp hTx
    obtain ⟨c, hc, hcτ⟩ := hτ_surj _ hTx
    have hsum : τ (x⁻ + c) = τ x⁺ := by
      rw [hτ_add _ _ (negPart_nonneg _) hc, hcτ, add_sub_cancel]
    have heq : x⁻ + c = x⁺ :=
      hτ_inj _ _ (add_nonneg (negPart_nonneg _) hc) (posPart_nonneg _) hsum
    have hle : x⁻ ≤ x⁺ := heq ▸ le_add_of_nonneg_right hc
    have : x⁻ = 0 := (inf_eq_left.mpr hle).symm.trans
      ((inf_comm x⁻ x⁺).trans (posPart_inf_negPart_eq_zero x))
    rw [← posPart_sub_negPart x, this, sub_zero]
    exact posPart_nonneg _
  -- T⁻¹ is monotone (from bipositivity + positivity)
  have hT_inv_mono : ∀ a b, T a ≤ T b → a ≤ b := by
    intro a b hab
    have : 0 ≤ T (b - a) := by rw [map_sub]; exact sub_nonneg.mpr hab
    exact sub_nonneg.mp (hT_bipos _ this)
  have hT_mono : Monotone T := monotone_iff.mpr (extension_positive hτ_nn hτ_add)
  -- T preserves ⊔
  have hT_sup : ∀ a b, T (a ⊔ b) = T a ⊔ T b := by
    intro a b
    apply le_antisymm
    · obtain ⟨c, hc⟩ := hT_surj (T a ⊔ T b)
      have hca : a ≤ c := hT_inv_mono _ _ (hc ▸ le_sup_left)
      have hcb : b ≤ c := hT_inv_mono _ _ (hc ▸ le_sup_right)
      rw [← hc]; exact hT_mono (sup_le hca hcb)
    · exact sup_le (hT_mono le_sup_left) (hT_mono le_sup_right)
  -- T preserves ⊓
  have hT_inf : ∀ a b, T (a ⊓ b) = T a ⊓ T b := by
    intro a b
    apply le_antisymm
    · exact le_inf (hT_mono inf_le_left) (hT_mono inf_le_right)
    · obtain ⟨c, hc⟩ := hT_surj (T a ⊓ T b)
      have hca : c ≤ a := hT_inv_mono _ _ (hc ▸ inf_le_left)
      have hcb : c ≤ b := hT_inv_mono _ _ (hc ▸ inf_le_right)
      rw [← hc]; exact hT_mono (le_inf hca hcb)
  exact
    { (LinearEquiv.ofBijective T ⟨hT_inj, hT_surj⟩) with
      map_sup' := hT_sup
      map_inf' := hT_inf }

end Positive

/-! ### Continuous linear equivalence between Banach lattices -/

namespace VecLatEquiv

variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [BanachLattice X] [BanachLattice Y]

/-- A vector lattice isomorphism between Banach lattices extends to a continuous linear
equivalence. -/
noncomputable def toContinuousLinearEquiv (e : VecLatEquiv X Y) : X ≃L[ℝ] Y :=
  ContinuousLinearEquiv.mk e.toLinearEquiv
    (Positive.continuous (Positive.monotone_iff.mp e.toVecLatHom.monotone))
    (Positive.continuous (Positive.monotone_iff.mp e.symm.toVecLatHom.monotone))

end VecLatEquiv

/-! ## Banach lattice isometries -/

/-- A **Banach lattice isometry** between two Banach lattices: a real linear
isometric equivalence that also preserves the lattice operations `⊔` and `⊓`.
Such a map is automatically an order isomorphism. -/
structure BanachLatEquiv (X Y : Type*)
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [Lattice X] [Lattice Y]
    [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
    [BanachLattice X] [BanachLattice Y]
    extends X ≃ₗᵢ[ℝ] Y, LatticeHom X Y

attribute [inherit_doc LatticeHom] BanachLatEquiv.toLatticeHom

namespace BanachLatEquiv

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [Lattice X] [Lattice Y]
  [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [BanachLattice X] [BanachLattice Y]

/-- The canonical `FunLike` instance, making `BanachLatEquiv X Y` a type of
functions `X → Y`. -/
instance instFunLike : FunLike (BanachLatEquiv X Y) X Y where
  coe e := e.toFun
  coe_injective := by
    intro f g h
    cases f; cases g
    congr 1
    exact LinearIsometryEquiv.toLinearEquiv_injective
      (LinearEquiv.toEquiv_injective (Equiv.coe_inj.mp h))

/-- Coerce a `BanachLatEquiv` to a continuous linear equivalence. -/
noncomputable def toContinuousLinearEquiv (e : BanachLatEquiv X Y) : X ≃L[ℝ] Y :=
  e.toLinearIsometryEquiv.toContinuousLinearEquiv

/-- Coerce a `BanachLatEquiv` to a `VecLatEquiv`. -/
def toVecLatEquiv (e : BanachLatEquiv X Y) : VecLatEquiv X Y :=
  { e.toLinearIsometryEquiv.toLinearEquiv with
    map_sup' := e.map_sup'
    map_inf' := e.map_inf' }

/-- The inverse of a Banach lattice isometry. -/
def symm (e : BanachLatEquiv X Y) : BanachLatEquiv Y X where
  toLinearIsometryEquiv := e.toLinearIsometryEquiv.symm
  map_sup' := e.toVecLatEquiv.symm.map_sup'
  map_inf' := e.toVecLatEquiv.symm.map_inf'

/-- The identity Banach lattice isometry. -/
def refl (X : Type*) [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [BanachLattice X] : BanachLatEquiv X X where
  toLinearIsometryEquiv := LinearIsometryEquiv.refl ℝ X
  map_sup' := fun _ _ => rfl
  map_inf' := fun _ _ => rfl

/-- The composition of two Banach lattice isometries. -/
def trans {Z : Type*} [NormedAddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z]
    [BanachLattice Z] (e₁ : BanachLatEquiv X Y) (e₂ : BanachLatEquiv Y Z) :
    BanachLatEquiv X Z where
  toLinearIsometryEquiv := e₁.toLinearIsometryEquiv.trans e₂.toLinearIsometryEquiv
  map_sup' := (e₁.toVecLatEquiv.trans e₂.toVecLatEquiv).map_sup'
  map_inf' := (e₁.toVecLatEquiv.trans e₂.toVecLatEquiv).map_inf'

end BanachLatEquiv

/-! ## Inclusion into the completion -/

section Completion

open UniformSpace

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]

/-- The canonical inclusion of a normed vector lattice into its completion, as a vector
lattice homomorphism. -/
noncomputable def toCompletionVecLatHom : VecLatHom X (Completion X) where
  toFun := ((↑) : X → Completion X)
  map_add' := Completion.coe_add
  map_smul' := Completion.coe_smul
  map_sup' := coe_sup_completion
  map_inf' := coe_inf_completion

@[simp]
theorem coe_toCompletionVecLatHom :
    ⇑(toCompletionVecLatHom : VecLatHom X (Completion X)) = ((↑) : X → Completion X) :=
  rfl

/-- The canonical inclusion of a normed vector lattice into its completion is an isometry;
together with `toCompletionVecLatHom` this exhibits the inclusion as a lattice isometry. -/
theorem isometry_toCompletionVecLatHom :
    Isometry (toCompletionVecLatHom : X → Completion X) := by
  rw [coe_toCompletionVecLatHom]
  exact isometry_coe_completion

/-- A norm-preserving vector lattice homomorphism `T : X → Y` with dense range into a Banach
lattice `Y` extends to a Banach lattice isometry from the completion of `X` onto `Y`. -/
noncomputable def banachLatEquivCompletionOfDenseIsometry
    {Y : Type*} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [BanachLattice Y]
    (T : VecLatHom X Y) (hT_norm : ∀ x, ‖T x‖ = ‖x‖) (hT_dense : DenseRange ⇑T) :
    BanachLatEquiv (Completion X) Y := by
  let Tli : X →ₗᵢ[ℝ] Y := { toLinearMap := T.toLinearMap, norm_map' := hT_norm }
  have huc : UniformContinuous ⇑Tli := Tli.isometry.uniformContinuous
  let Tc : Completion X →ₗᵢ[ℝ] Y :=
    { toFun := Completion.extension Tli
      map_add' := fun z w => by
        refine Completion.induction_on₂ z w (isClosed_eq ?_ ?_) (fun x y => ?_)
        · exact Completion.continuous_extension.comp continuous_add
        · exact (Completion.continuous_extension.comp continuous_fst).add
            (Completion.continuous_extension.comp continuous_snd)
        · rw [← Completion.coe_add, Completion.extension_coe huc, Completion.extension_coe huc,
            Completion.extension_coe huc, map_add]
      map_smul' := fun r z => by
        refine Completion.induction_on z (isClosed_eq ?_ ?_) (fun x => ?_)
        · exact Completion.continuous_extension.comp (continuous_const_smul r)
        · exact (continuous_const_smul r).comp Completion.continuous_extension
        · rw [← Completion.coe_smul, Completion.extension_coe huc, Completion.extension_coe huc,
            map_smul, RingHom.id_apply]
      norm_map' := fun z => by
        refine Completion.induction_on z (isClosed_eq ?_ ?_) (fun x => ?_)
        · exact continuous_norm.comp Completion.continuous_extension
        · exact continuous_norm
        · change ‖Completion.extension (⇑Tli) (x : Completion X)‖ = ‖(x : Completion X)‖
          rw [Completion.extension_coe huc, Tli.norm_map, Completion.norm_coe] }
  have hTc_coe : ∀ a : X, Tc (a : Completion X) = T a := fun a =>
    Completion.extension_coe huc a
  have hdense : DenseRange ⇑Tc := by
    refine hT_dense.mono ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨(x : Completion X), hTc_coe x⟩
  have hsurj : Function.Surjective ⇑Tc := by
    have hclosed : IsClosed (Set.range ⇑Tc) := Tc.isometry.isClosedEmbedding.isClosed_range
    rw [← Set.range_eq_univ, ← hclosed.closure_eq, hdense.closure_range]
  refine
    { toLinearIsometryEquiv := LinearIsometryEquiv.ofSurjective Tc hsurj
      map_sup' := fun z w => ?_
      map_inf' := fun z w => ?_ }
  · change Tc (z ⊔ w) = Tc z ⊔ Tc w
    refine Completion.induction_on₂ z w (isClosed_eq ?_ ?_) (fun x y => ?_)
    · exact Tc.continuous.comp ContinuousSup.continuous_sup
    · exact ContinuousSup.continuous_sup.comp
        ((Tc.continuous.comp continuous_fst).prodMk (Tc.continuous.comp continuous_snd))
    · rw [← coe_sup_completion, hTc_coe, hTc_coe, hTc_coe]
      exact T.map_sup' x y
  · change Tc (z ⊓ w) = Tc z ⊓ Tc w
    refine Completion.induction_on₂ z w (isClosed_eq ?_ ?_) (fun x y => ?_)
    · exact Tc.continuous.comp ContinuousInf.continuous_inf
    · exact ContinuousInf.continuous_inf.comp
        ((Tc.continuous.comp continuous_fst).prodMk (Tc.continuous.comp continuous_snd))
    · rw [← coe_inf_completion, hTc_coe, hTc_coe, hTc_coe]
      exact T.map_inf' x y

end Completion
