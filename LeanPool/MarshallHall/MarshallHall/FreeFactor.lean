/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
import LeanPool.MarshallHall.MarshallHall.Grushko
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
import Mathlib.Logic.Equiv.Set

universe u

noncomputable section

open Monoid.Coprod

namespace MarshallHall

/-!
## Inclusion-compatible free factors

The witness below records the actual inclusion of the displayed subgroup into
the ambient group.  This prevents an abstract isomorphism from being mistaken
for the free-factor conclusion: the left coproduct injection must be the
subgroup inclusion itself.
-/

structure FreeFactorWitness {K : Type u} [Group K] (H : Subgroup K) where
  complement : Type u
  [complementGroup : Group complement]
  equiv : H ∗ complement ≃* K
  inclusion : ∀ h : H, equiv (Monoid.Coprod.inl h) = H.subtype h

structure MarshallHallWitness {F : Type u} [Group F] (H : Subgroup F) where
  K : Subgroup F
  hHK : H ≤ K
  finiteIndex : K.index ≠ 0
  complement : Type u
  [complementGroup : Group complement]
  equiv : H ∗ complement ≃* K
  inclusion : ∀ h : H, equiv (Monoid.Coprod.inl h) = ⟨h.1, hHK h.2⟩

def subgroupComapEquiv {F : Type u} [Group F]
    (H K : Subgroup F) (hHK : H ≤ K) :
    H ≃* Subgroup.comap K.subtype H :=
  { toFun := fun h => ⟨⟨h.1, hHK h.2⟩, h.2⟩
    invFun := fun k => ⟨k.1, k.2⟩
    left_inv := by intro h; rfl
    right_inv := by intro k; rfl
    map_mul' := by intro x y; rfl }

def FreeFactorWitness.pullback
    {K L : Type u} [Group K] [Group L]
    {H : Subgroup K} {H' : Subgroup L}
    (e : K ≃* L) (h : H ≃* H') (w : FreeFactorWitness H')
    (hcompat : ∀ x : H, e x.1 = (h x).1) :
    FreeFactorWitness H :=
  letI : Group w.complement := w.complementGroup
  { complement := w.complement
    equiv := ((MulEquiv.coprodCongr h (MulEquiv.refl _)).trans w.equiv).trans e.symm
    inclusion := by
      intro x
      apply e.injective
      simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      change w.equiv (Monoid.Coprod.inl (h x)) = e x.1
      rw [w.inclusion]
      exact (hcompat x).symm }

def IsFreeFactor {K : Type u} [Group K] (H : Subgroup K) : Prop :=
  Nonempty (FreeFactorWitness H)

def generatedByBasis {X K : Type u} [Group K] (B : FreeGroupBasis X K) (Y : Set X) :
    Subgroup K :=
  Subgroup.closure (B '' Y)

def subsetBasisHom {X K : Type u} [Group K] (B : FreeGroupBasis X K) (Y : Set X) :
    FreeGroup Y →* generatedByBasis B Y :=
  FreeGroup.lift (fun y => ⟨B y, Subgroup.subset_closure ⟨y, y.2, rfl⟩⟩)

def basisRetraction {X : Type u} (Y : Set X) : FreeGroup X →* FreeGroup Y :=
  by
    classical
    exact FreeGroup.lift (fun x => if hx : x ∈ Y then FreeGroup.of ⟨x, hx⟩ else 1)

@[simp]
theorem basisRetraction_apply_of_mem {X : Type u} (Y : Set X) {x : X} (hx : x ∈ Y) :
    basisRetraction Y (FreeGroup.of x) = FreeGroup.of ⟨x, hx⟩ := by
  classical
  simp [basisRetraction, hx]

@[simp]
theorem basisRetraction_apply_of_not_mem {X : Type u} (Y : Set X) {x : X} (hx : x ∉ Y) :
    basisRetraction Y (FreeGroup.of x) = 1 := by
  classical
  simp [basisRetraction, hx]

@[simp]
theorem subsetBasisHom_apply_of {X K : Type u} [Group K]
    (B : FreeGroupBasis X K) (Y : Set X) (y : Y) :
    subsetBasisHom B Y (FreeGroup.of y) =
      ⟨B y, Subgroup.subset_closure ⟨y, y.2, rfl⟩⟩ := by
  classical
  simp [subsetBasisHom]

theorem subsetBasisHom_retraction_on_closure {X K : Type u} [Group K]
    (B : FreeGroupBasis X K) (Y : Set X) (x : generatedByBasis B Y) :
    ((subsetBasisHom B Y (basisRetraction Y (B.repr x.1))) : K) = x.1 := by
  classical
  refine Subgroup.closure_induction (p := fun y _ =>
    ((subsetBasisHom B Y (basisRetraction Y (B.repr y))) : K) = y) ?_ ?_ ?_ ?_ x.2
  · rintro y ⟨z, hz, rfl⟩
    rw [B.repr_apply_coe, basisRetraction_apply_of_mem Y hz,
      subsetBasisHom_apply_of]
  · simp [basisRetraction, subsetBasisHom]
  · intro y z _ _ hy hz
    change subsetBasisHom B Y (basisRetraction Y (B.repr (y * z))) = y * z
    rw [B.repr.map_mul, (basisRetraction Y).map_mul, (subsetBasisHom B Y).map_mul]
    change (subsetBasisHom B Y (basisRetraction Y (B.repr y)) : K) *
      (subsetBasisHom B Y (basisRetraction Y (B.repr z)) : K) = y * z
    rw [hy, hz]
  · intro y _ hy
    change subsetBasisHom B Y (basisRetraction Y (B.repr y⁻¹)) = y⁻¹
    rw [B.repr.map_inv, (basisRetraction Y).map_inv, (subsetBasisHom B Y).map_inv]
    change (subsetBasisHom B Y (basisRetraction Y (B.repr y)) : K)⁻¹ = y⁻¹
    rw [hy]

def subsetBasisRetraction {X K : Type u} [Group K]
    (B : FreeGroupBasis X K) (Y : Set X) :
    generatedByBasis B Y →* FreeGroup Y :=
  (basisRetraction Y).comp B.repr.toMonoidHom |>.comp (generatedByBasis B Y).subtype

theorem subsetBasisHom_comp_retraction {X K : Type u} [Group K]
    (B : FreeGroupBasis X K) (Y : Set X) :
    (subsetBasisHom B Y).comp (subsetBasisRetraction B Y) = MonoidHom.id _ := by
  ext x
  change ((subsetBasisHom B Y (subsetBasisRetraction B Y x)) : K) = x.1
  exact subsetBasisHom_retraction_on_closure B Y x

theorem subsetBasisRetraction_comp_hom {X K : Type u} [Group K]
    (B : FreeGroupBasis X K) (Y : Set X) :
    (subsetBasisRetraction B Y).comp (subsetBasisHom B Y) = MonoidHom.id _ := by
  apply FreeGroup.ext_hom
  intro y
  simp [subsetBasisRetraction, subsetBasisHom, B.repr_apply_coe]

def subsetBasisEquiv {X K : Type u} [Group K]
    (B : FreeGroupBasis X K) (Y : Set X) :
    generatedByBasis B Y ≃* FreeGroup Y :=
  MulEquiv.ofBijective (subsetBasisRetraction B Y) ⟨
    (fun x y h => by
      have hh := congrArg (fun z => subsetBasisHom B Y z) h
      have hc := subsetBasisHom_comp_retraction B Y
      calc
        x = subsetBasisHom B Y (subsetBasisRetraction B Y x) := by
          have hx := congrArg (fun f : generatedByBasis B Y →* generatedByBasis B Y => f x) hc
          exact hx.symm
        _ = subsetBasisHom B Y (subsetBasisRetraction B Y y) := hh
        _ = y := by
          have hy := congrArg (fun f : generatedByBasis B Y →* generatedByBasis B Y => f y) hc
          exact hy),
    (fun z => ⟨subsetBasisHom B Y z, by
      have hz := congrArg (fun f : FreeGroup Y →* FreeGroup Y => f z)
        (subsetBasisRetraction_comp_hom B Y)
      exact hz⟩)⟩

def basisSubsetFreeFactorEquiv {X K : Type u} [Group K]
    (B : FreeGroupBasis X K) (Y : Set X) :
    generatedByBasis B Y ∗ FreeGroup (Yᶜ : Set X) ≃* K :=
  by
    classical
    exact
      (((MulEquiv.coprodCongr (subsetBasisEquiv B Y)
        (MulEquiv.refl (FreeGroup (Yᶜ : Set X)))).trans
        (binaryFreeProductEquiv (α := Y) (β := (Yᶜ : Set X)))).trans
        (FreeGroup.freeGroupCongr (Equiv.Set.sumCompl Y))).trans B.repr.symm

theorem repr_subsetBasisHom {X K : Type u} [Group K]
    (B : FreeGroupBasis X K) (Y : Set X) (w : FreeGroup Y) :
    B.repr ((subsetBasisHom B Y w : generatedByBasis B Y) : K) =
      FreeGroup.map (fun y : Y => (y : X)) w := by
  refine FreeGroup.induction_on w ?_ ?_ ?_ ?_
  · simp [subsetBasisHom]
  · intro y
    simp [subsetBasisHom, B.repr_apply_coe]
  · intro y ih
    simp [subsetBasisHom, B.repr_apply_coe, ih]
  · intro x y ihx ihy
    rw [(subsetBasisHom B Y).map_mul]
    rw [show ((subsetBasisHom B Y x * subsetBasisHom B Y y :
        generatedByBasis B Y) : K) =
        (subsetBasisHom B Y x : K) * (subsetBasisHom B Y y : K) by rfl]
    rw [B.repr.map_mul]
    calc
      _ = (FreeGroup.map (fun y : Y => (y : X)) x) *
          (FreeGroup.map (fun y : Y => (y : X)) y) := congrArg₂ (fun a b => a * b) ihx ihy
      _ = FreeGroup.map (fun y : Y => (y : X)) (x * y) :=
        (FreeGroup.map_mul (fun y : Y => (y : X)) x y).symm

theorem repr_subsetBasisEquiv {X K : Type u} [Group K]
    (B : FreeGroupBasis X K) (Y : Set X) (h : generatedByBasis B Y) :
    FreeGroup.map (fun y : Y => (y : X)) (subsetBasisEquiv B Y h) = B.repr (h : K) := by
  have hh : subsetBasisHom B Y (subsetBasisEquiv B Y h) = h := by
    change subsetBasisHom B Y (subsetBasisRetraction B Y h) = h
    have hc := congrArg (fun f : generatedByBasis B Y →* generatedByBasis B Y => f h)
      (subsetBasisHom_comp_retraction B Y)
    simpa [MonoidHom.comp_apply] using hc
  calc
    FreeGroup.map (fun y : Y => (y : X)) (subsetBasisEquiv B Y h) =
        B.repr ((subsetBasisHom B Y (subsetBasisEquiv B Y h) : generatedByBasis B Y) : K) := by
          symm
          exact repr_subsetBasisHom B Y (subsetBasisEquiv B Y h)
    _ = B.repr (h : K) := by rw [hh]

theorem generatedByBasis_isFreeFactor {X K : Type u} [Group K]
    (B : FreeGroupBasis X K) (Y : Set X) :
    IsFreeFactor (generatedByBasis B Y) := by
  classical
  refine ⟨{
    complement := FreeGroup (Yᶜ : Set X)
    equiv := basisSubsetFreeFactorEquiv B Y
    inclusion := ?_ }⟩
  intro h
  apply B.repr.injective
  simp [basisSubsetFreeFactorEquiv, B.repr_apply_coe]
  rw [FreeGroup.map.comp]
  convert repr_subsetBasisEquiv B Y h using 1
  congr 1

theorem isFreeFactor_of_basis_support {X K : Type u} [Group K]
    (H : Subgroup K) (B : FreeGroupBasis X K) (Y : Set X)
    (hY : ∀ y : Y, B y ∈ H)
    (hH : ∀ h : H, ∃ w : FreeGroup Y,
      B.repr (h : K) = FreeGroup.map (fun y : Y => (y : X)) w) :
    IsFreeFactor H := by
  have hle : generatedByBasis B Y ≤ H := by
    apply (Subgroup.closure_le H).2
    rintro _ ⟨y, hy, rfl⟩
    exact hY ⟨y, hy⟩
  have hge : H ≤ generatedByBasis B Y := by
    intro h hh
    obtain ⟨w, hw⟩ := hH ⟨h, hh⟩
    let z : generatedByBasis B Y := subsetBasisHom B Y w
    have hz : (z : K) = h := by
      apply B.repr.injective
      rw [repr_subsetBasisHom, hw]
    rw [← hz]
    exact z.property
  have heq : H = generatedByBasis B Y := le_antisymm hge hle
  simpa [heq] using generatedByBasis_isFreeFactor B Y

end MarshallHall
