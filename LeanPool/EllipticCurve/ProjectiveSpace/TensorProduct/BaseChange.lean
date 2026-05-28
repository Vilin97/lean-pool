/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import LeanPool.EllipticCurve.Lemmas
import LeanPool.EllipticCurve.ProjectiveSpace.TensorProduct.SymmetricMap
import Mathlib.Data.Finite.Card
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Base Change for Symmetric Multilinear Maps

In this file we contruct the base change for symmetric multilinear maps.

## Main definitions

* `SymmetricMap.baseChange`: the base change of a symmetric multilinear map `M [Σ^ι]→ₗ[R] N` to
  `(A ⊗[R] M) [Σ^ι]→ₗ[A] (A ⊗[R] N)`.

-/

open TensorProduct Function Equiv Perm

variable {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
  {ι' : Type*} {M₁ : ι' → Type*} [∀ i, AddCommMonoid (M₁ i)] [∀ i, Module R (M₁ i)]
  {n : ℕ} {M₂ : Fin n → Type*} [∀ i, AddCommMonoid (M₂ i)] [∀ i, Module R (M₂ i)]
  {N : Type*} [AddCommMonoid N] [Module R N]
  {ι A : Type*} [CommSemiring A] [Algebra R A] {N' : Type*} [AddCommMonoid N'] [Module A N']

namespace MultilinearMap

@[ext] lemma baseChange_hom_ext [Finite ι']
    {f g : MultilinearMap A (fun i : ι' ↦ A ⊗[R] M₁ i) N'}
    (h : ∀ v : (i : ι') → M₁ i, f (fun i ↦ 1 ⊗ₜ v i) = g (fun i ↦ 1 ⊗ₜ v i)) :
    f = g :=
  hom_ext' M₁ (fun i ↦ TensorProduct.mk R A (M₁ i) 1) (fun _ ↦ span_mk_one_eq_top) h

/-- Restrict a multilinear map on `Fin (n + 1)` to a multilinear map on `Fin n` along a chosen
`p : M₁ (Fin.last n)`. -/
def restrictFin {n : ℕ} {M₁ : Fin (n + 1) → Type*}
    [∀ i, AddCommMonoid (M₁ i)] [∀ i, Module R (M₁ i)]
    (f : MultilinearMap R M₁ N) (p : M₁ (Fin.last n)) :
      MultilinearMap R (fun i : Fin n ↦ M₁ i.castSucc) N where
  toFun v := f (Fin.lastCases p v)
  map_update_add' v i x y := by simp
  map_update_smul' v i x y := by simp

/-- `restrictFin` as linear map. -/
def restrictFinₗ {n : ℕ} {M₁ : Fin (n + 1) → Type*}
    [∀ i, AddCommMonoid (M₁ i)] [∀ i, Module R (M₁ i)] (f : MultilinearMap R M₁ N) :
      M₁ (Fin.last n) →ₗ[R] MultilinearMap R (fun i : Fin n ↦ M₁ i.castSucc) N where
  toFun p := f.restrictFin p
  map_add' x y := ext fun v ↦ by simp [restrictFin, Fin.lastCases_update_left x 0,
    Fin.lastCases_update_left y 0, Fin.lastCases_update_left (x + y) 0]
  map_smul' r x := ext fun v ↦ by simp [restrictFin, Fin.lastCases_update_left x 0,
    Fin.lastCases_update_left (r • x) 0]

/-- `restrictFin` as a bilinear map. -/
def restrictFinₗₗ {n : ℕ} {M₁ : Fin (n + 1) → Type*}
    [∀ i, AddCommMonoid (M₁ i)] [∀ i, Module R (M₁ i)] :
      MultilinearMap R M₁ N →ₗ[R] M₁ (Fin.last n) →ₗ[R]
        MultilinearMap R (fun i : Fin n ↦ M₁ i.castSucc) N where
  toFun f := f.restrictFinₗ
  map_add' f g := by ext p v; simp [restrictFinₗ, restrictFin]
  map_smul' r f := by ext p v; simp [restrictFinₗ, restrictFin]

/-- The induction step. -/
def baseChangeFinAux {n : ℕ} {M₁ : Fin (n + 1) → Type*}
    [∀ i, AddCommMonoid (M₁ i)] [∀ i, Module R (M₁ i)]
    (ih : MultilinearMap R (fun i : Fin n ↦ M₁ i.castSucc) N →ₗ[R]
      MultilinearMap A (fun i : Fin n ↦ A ⊗[R] M₁ i.castSucc) (A ⊗[R] N))
    (f : MultilinearMap R M₁ N) (v : (i : Fin n) → A ⊗[R] M₁ i.castSucc) :
      M₁ (Fin.last n) →ₗ[R] (A ⊗[R] N) where
  toFun p := ih (f.restrictFinₗₗ p) v
  map_add' x y := by simp
  map_smul' r x := by simp

/-- The induction step as a multilinear map. -/
def baseChangeFinAuxMultilinear {n : ℕ} {M₁ : Fin (n + 1) → Type*}
    [∀ i, AddCommMonoid (M₁ i)] [∀ i, Module R (M₁ i)]
    (ih : MultilinearMap R (fun i : Fin n ↦ M₁ i.castSucc) N →ₗ[R]
      MultilinearMap A (fun i : Fin n ↦ A ⊗[R] M₁ i.castSucc) (A ⊗[R] N))
    (f : MultilinearMap R M₁ N) :
    MultilinearMap A (fun (i : Fin n) ↦ A ⊗[R] M₁ i.castSucc)
      (M₁ (Fin.last n) →ₗ[R] (A ⊗[R] N)) where
  toFun v := baseChangeFinAux ih f v
  map_update_add' v i x y := LinearMap.ext fun _ ↦ (ih _).map_update_add v i x y
  map_update_smul' v i x y := LinearMap.ext fun _ ↦ (ih _).map_update_smul v i x y

/-- The induction step as a linear map to multilinear maps. -/
def baseChangeFinAuxMultilinearₗ {n : ℕ} {M₁ : Fin (n + 1) → Type*}
    [∀ i, AddCommMonoid (M₁ i)] [∀ i, Module R (M₁ i)]
    (ih : MultilinearMap R (fun i : Fin n ↦ M₁ i.castSucc) N →ₗ[R]
      MultilinearMap A (fun i : Fin n ↦ A ⊗[R] M₁ i.castSucc) (A ⊗[R] N)) :
    MultilinearMap R M₁ N →ₗ[R]
      MultilinearMap A (fun (i : Fin n) ↦ A ⊗[R] M₁ i.castSucc)
        (M₁ (Fin.last n) →ₗ[R] (A ⊗[R] N)) where
  toFun f := baseChangeFinAuxMultilinear ih f
  map_add' f g := by ext v p; simp [baseChangeFinAuxMultilinear, baseChangeFinAux]
  map_smul' r x := by ext v p; simp [baseChangeFinAuxMultilinear, baseChangeFinAux]

variable (R N A) in
/-- Base change for multilinear maps with a finite indexing type. Here we use `Fin n` as a special
case so that we can define the map inductively. -/
noncomputable def baseChangeFin : ∀ (n : ℕ) (M₁ : Fin n → Type*)
    [∀ i, AddCommMonoid (M₁ i)] [∀ i, Module R (M₁ i)],
    MultilinearMap R M₁ N →ₗ[R] MultilinearMap A (fun i ↦ A ⊗[R] M₁ i) (A ⊗[R] N)
  | 0 => fun _ _ _ ↦
    { toFun f := constOfIsEmpty A _ (1 ⊗ₜ f default)
      map_add' _ _ := ext fun v ↦ by simp [tmul_add]
      map_smul' _ _ := ext fun v ↦ by simp }
  | (n+1) => fun M₁ _ _ ↦ by refine
    { toFun f :=
      { toFun v := LinearMap.liftBaseChangeEquiv A
          (baseChangeFinAuxMultilinearₗ (baseChangeFin n fun i ↦ M₁ i.castSucc) f
            fun i ↦ v i.castSucc)
          (v (Fin.last n))
        map_update_add' v i := i.lastCases (by simp) fun i x y ↦ by simp
        map_update_smul' v i := i.lastCases (by simp) fun i x y ↦ by simp }
      map_add' f g := ext fun v ↦ by simp
      map_smul' c f := ext fun v ↦ by
        simp only [map_smul, smul_apply, coe_mk, RingHom.id_apply]
        rw [LinearMapClass.map_smul_of_tower, LinearMap.smul_apply] }

lemma baseChangeFin_apply_one_tmul (f : MultilinearMap R M₂ N)
    (v : (i : Fin n) → M₂ i) :
    baseChangeFin R N A n M₂ f (fun i ↦ 1 ⊗ₜ v i) = 1 ⊗ₜ f v := by
  induction n with
  | zero => simp [baseChangeFin, Unique.uniq _ v]
  | succ n ih => simp [baseChangeFin, baseChangeFinAuxMultilinearₗ, baseChangeFinAuxMultilinear,
      baseChangeFinAux, ih, restrictFinₗₗ, restrictFinₗ, restrictFin]

@[simp] lemma baseChangeFin_apply_tmul (f : MultilinearMap R M₂ N)
    (c : Fin n → A) (v : (i : Fin n) → M₂ i) :
    baseChangeFin R N A n M₂ f (fun i ↦ c i ⊗ₜ v i) = (∏ i, c i) ⊗ₜ f v := calc
  _ = baseChangeFin R N A n M₂ f (fun i ↦ c i • (1 ⊗ₜ v i)) :=
        congrArg _ <| funext fun i ↦ tmul_eq_smul_one_tmul (c i) (v i)
  _ = (∏ i, c i) • baseChangeFin R N A n M₂ f (fun i ↦ 1 ⊗ₜ v i) := map_smul_univ _ _ _
  _ = (∏ i, c i) • (1 ⊗ₜ f v) := congrArg _ <| baseChangeFin_apply_one_tmul f v
  _ = (∏ i, c i) ⊗ₜ f v := (tmul_eq_smul_one_tmul (∏ i, c i) (f v)).symm

variable (R M₁ N A) in
/-- Base change for multilinear maps with a (finite) indexing type, with a chosen equiv `ι ≃ Fin n`.
-/
noncomputable def baseChangeOfEquiv (e : ι' ≃ Fin n) :
    (MultilinearMap R M₁ N) →ₗ[R] MultilinearMap A (fun i ↦ A ⊗[R] M₁ i) (A ⊗[R] N) :=
  (domDomCongrLinearEquiv' A R (fun i ↦ A ⊗[R] M₁ i) (A ⊗[R] N) e).symm.toLinearMap.comp <|
    (baseChangeFin R N A n (fun i ↦ M₁ (e.symm i))).comp
      (domDomCongrLinearEquiv' R R M₁ N e).toLinearMap

@[simp] lemma baseChangeOfEquiv_apply_tmul [Fintype ι'] (e : ι' ≃ Fin n)
    (f : MultilinearMap R M₁ N) (c : ι' → A) (v : (i : ι') → M₁ i) :
    baseChangeOfEquiv R M₁ N A e f (fun i ↦ c i ⊗ₜ v i) = (∏ i, c i) ⊗ₜ f v := calc
  _ = baseChangeFin R N A n (fun i ↦ M₁ (e.symm i)) (domDomCongrLinearEquiv' R R M₁ N e f) fun x ↦
        c (e.symm x) ⊗ₜ[R] v (e.symm x) := rfl
  _ = (∏ i, c (e.symm i)) ⊗ₜ[R] (f fun x ↦ e.symm_apply_apply x ▸ v (e.symm (e x))) :=
        baseChangeFin_apply_tmul _ _ _
  _ = (∏ i, c (e.symm i)) ⊗ₜ[R] (f fun x ↦ v x) := by
        congr; ext x; generalize_proofs h; generalize e.symm (e x) = y at h; subst h; rfl
  _ = (∏ i, c i) ⊗ₜ[R] f v := congrArg₂ _ (e.symm.prod_comp c) rfl

/-- `baseChangeOfEquiv` is actually independent of the `Equiv` chosen. -/
lemma baseChangeOfEquiv_eq (e₁ e₂ : ι' ≃ Fin n) :
    baseChangeOfEquiv R M₁ N A e₁ = baseChangeOfEquiv R M₁ N A e₂ :=
  have : Fintype ι' := .ofEquiv _ e₁.symm
  LinearMap.ext fun f ↦ baseChange_hom_ext fun v ↦ by simp

variable (R M₁ N A) in
/-- Base change for multilinear maps indexed by a finite type, given by a term of
`Trunc (ι ≃ Fin n)`. -/
noncomputable def baseChangeOfTrunc (e : Trunc (ι' ≃ Fin n)) :
    MultilinearMap R M₁ N →ₗ[R] MultilinearMap A (fun i ↦ A ⊗[R] M₁ i) (A ⊗[R] N) :=
  e.lift (baseChangeOfEquiv R M₁ N A) baseChangeOfEquiv_eq

variable (R M₁ N A) in
/-- Base change for multilinear maps indexed by a finite type. -/
noncomputable def baseChange [Finite ι'] :
    MultilinearMap R M₁ N →ₗ[R] MultilinearMap A (fun i ↦ A ⊗[R] M₁ i) (A ⊗[R] N) :=
  baseChangeOfTrunc R M₁ N A <| .mk <| Finite.equivFin ι'

@[simp] lemma baseChange_apply_tmul [Fintype ι'] (f : MultilinearMap R M₁ N)
    (c : ι' → A) (v : (i : ι') → M₁ i) :
    baseChange R M₁ N A f (fun i ↦ c i ⊗ₜ v i) = (∏ i, c i) ⊗ₜ f v :=
  baseChangeOfEquiv_apply_tmul _ f c v

@[simp] lemma baseChange_apply_one_tmul [Finite ι']
    (f : MultilinearMap R M₁ N) (v : (i : ι') → M₁ i) :
    baseChange R M₁ N A f (fun i ↦ 1 ⊗ₜ v i) = 1 ⊗ₜ f v := by
  cases nonempty_fintype ι'
  convert baseChange_apply_tmul f 1 v
  simp

end MultilinearMap


namespace SymmetricMap

open MultilinearMap

@[ext] lemma baseChange_hom_ext [Finite ι]
    {f g : (A ⊗[R] M) [Σ^ι]→ₗ[A] N'}
    (h : ∀ v : ι → M, f (fun i ↦ 1 ⊗ₜ v i) = g (fun i ↦ 1 ⊗ₜ v i)) :
    f = g :=
  toMultilinearMap_injective <| MultilinearMap.baseChange_hom_ext h

variable (R M N ι A) in
/-- Base change for symmetric maps with a finite indexing type. -/
noncomputable def baseChange [Finite ι] :
    (M [Σ^ι]→ₗ[R] N) →ₗ[R] (A ⊗[R] M) [Σ^ι]→ₗ[A] (A ⊗[R] N) where
  toFun f := .mk' (f.1.baseChange _ _ _ _) fun e ↦ MultilinearMap.baseChange_hom_ext fun v ↦ by simp
  map_add' f g := baseChange_hom_ext fun v ↦ by simp [tmul_add]
  map_smul' c f := baseChange_hom_ext fun v ↦ by simp

@[simp] lemma baseChange_apply_tmul [Fintype ι] (f : M [Σ^ι]→ₗ[R] N) (c : ι → A) (v : ι → M) :
    baseChange R M N ι A f (fun i ↦ c i ⊗ₜ v i) = (∏ i, c i) ⊗ₜ f v :=
  MultilinearMap.baseChange_apply_tmul f.1 c v

@[simp] lemma baseChange_apply_one_tmul [Finite ι] (f : M [Σ^ι]→ₗ[R] N) (v : ι → M) :
    baseChange R M N ι A f (fun i ↦ 1 ⊗ₜ v i) = 1 ⊗ₜ f v :=
  MultilinearMap.baseChange_apply_one_tmul f.1 v

end SymmetricMap
