/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import LeanPool.Monlib4.LinearAlgebra.QuantumSet.Basic
import LeanPool.Monlib4.LinearAlgebra.QuantumSet.TensorProduct
import LeanPool.Monlib4.LinearAlgebra.QuantumSet.SchurMul

/-!
# LeanPool.Monlib4.LinearAlgebra.QuantumSet.Subset

Imported Lean Pool material for `LeanPool.Monlib4.LinearAlgebra.QuantumSet.Subset`.
-/

/-- Type synonym for a quantum set with its modular exponent shifted to `k`. -/
def QuantumSet.toSubset (k : ℝ) (A : Type*) : Type _ :=
  let _ : ℝ := k
  A

/-- The tautological equivalence from a type to its shifted quantum-set synonym. -/
def QuantumSet.toSubsetEquiv (k : ℝ) {A : Type*} :
  A ≃ QuantumSet.toSubset k A := Equiv.refl _

/-- Abbreviation for the shifted quantum-set type synonym. -/
abbrev QuantumSet.subset (k : ℝ) (A : Type*) : Type _ := QuantumSet.toSubset k A

variable {new_k : ℝ}
instance (A : Type*) [h : Inhabited A] : Inhabited (QuantumSet.subset new_k A) := h
instance {A : Type*} [h : Ring A] : Ring (QuantumSet.subset new_k A) := h
instance {A : Type*} [Ring A] [h : Algebra ℂ A] : Algebra ℂ (QuantumSet.subset new_k A) := h
instance {A : Type*} [h : Star A] : Star (QuantumSet.subset new_k A) := h
instance {A : Type*} [h : SMul ℂ A] : SMul ℂ (QuantumSet.subset new_k A) := h
instance {A : Type*} [Ring A] [h : StarRing A] : StarRing (QuantumSet.subset new_k A) := h
instance {A : Type*} [Star A] [SMul ℂ A] [h : StarModule ℂ A] :
    StarModule ℂ (QuantumSet.subset new_k A) := h

/-- The tautological algebra equivalence from a type to its shifted quantum-set synonym. -/
def QuantumSet.toSubsetAlgEquiv (k : ℝ) {A : Type*} [Ring A] [Algebra ℂ A] :
    A ≃ₐ[ℂ] QuantumSet.subset k A :=
  AlgEquiv.refl
lemma QuantumSet.toSubsetAlgEquiv_eq_toSubsetEquiv {A : Type*} [Ring A] [Algebra ℂ A]
  (x : A) :
  QuantumSet.toSubsetAlgEquiv new_k x = QuantumSet.toSubsetEquiv new_k x := rfl
lemma QuantumSet.toSubsetAlgEquiv_symm_eq_toSubsetEquiv {A : Type*} [Ring A] [Algebra ℂ A]
  (x : QuantumSet.subset new_k A) :
  (toSubsetAlgEquiv new_k).symm x = (toSubsetEquiv new_k).symm x := rfl

variable {A : Type*} [ha : starAlgebra A]

instance QuantumSet.subsetStarAlgebra (k : ℝ) :
    _root_.starAlgebra (QuantumSet.subset k A) where
  modAut r := (toSubsetAlgEquiv k).symm.trans ((ha.modAut r).trans (toSubsetAlgEquiv k))
  modAut_trans := ha.modAut_trans
  modAut_star := ha.modAut_star

lemma QuantumSet.subsetStarAlgebra_modAut_apply (r : ℝ) (x : QuantumSet.subset new_k A) :
  (QuantumSet.subsetStarAlgebra new_k).modAut r x =
    (toSubsetEquiv new_k) (ha.modAut r ((toSubsetEquiv new_k).symm x)) := rfl
lemma QuantumSet.subsetStarAlgebra_modAut_apply' (r : ℝ) (x : A) :
    (QuantumSet.subsetStarAlgebra new_k).modAut r (toSubsetEquiv new_k x) =
      (toSubsetEquiv new_k) (ha.modAut r x) :=
  rfl
lemma QuantumSet.subsetStarAlgebra_modAut_apply'' (r : ℝ) (x : QuantumSet.subset new_k A) :
  ((toSubsetEquiv new_k).symm
    (((QuantumSet.subsetStarAlgebra new_k).modAut r
      : subset new_k A ≃ₐ[ℂ] subset new_k A) x : subset new_k A) : A) =
    ((ha.modAut r ((toSubsetEquiv new_k).symm x : A)) : A) := rfl

/-- The normed additive group structure induced by shifting the quantum-set inner product. -/
@[reducible]
noncomputable def QuantumSet.subsetNormedAddCommGroup [hA : QuantumSet A]
  (new_k : ℝ) :
    letI : starAlgebra (QuantumSet.subset new_k A) := QuantumSet.subsetStarAlgebra new_k
    NormedAddCommGroup (QuantumSet.subset new_k A) :=
  letI : starAlgebra (subset new_k A) := QuantumSet.subsetStarAlgebra new_k
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (subset new_k A) _ _ _
  { inner := fun x y =>
      hA.inner ((toSubsetEquiv new_k).symm x)
        (ha.modAut (new_k + -hA.k) ((toSubsetEquiv new_k).symm y))
    conj_inner_symm := fun _ _ => by simp only [inner_conj_symm, QuantumSet.modAut_isSymmetric]
    re_inner_nonneg := fun _ => by
      rw [← add_halves (new_k + -k A), ← QuantumSet.modAut_apply_modAut,
        ← QuantumSet.modAut_isSymmetric, ← norm_sq_eq_re_inner]
      exact sq_nonneg _
    definite := fun _ => by
      rw [← add_halves (new_k + -k A), ← QuantumSet.modAut_apply_modAut,
        ← QuantumSet.modAut_isSymmetric, inner_self_eq_zero,
        AlgEquiv.map_eq_zero_iff]
      exact fun h => h
    add_left := fun _ _ _ => by simp only [← inner_add_left]; rfl
    smul_left := fun _ _ _ => by simp only [← inner_smul_left]; rfl }
/-- The inner product space structure induced by shifting the quantum-set inner product. -/
@[reducible]
noncomputable def QuantumSet.subsetInnerProductSpace (hA : QuantumSet A) (new_k : ℝ) :
  letI := hA.subsetNormedAddCommGroup new_k
  InnerProductSpace ℂ (subset new_k A) :=
letI : starAlgebra (subset new_k A) := QuantumSet.subsetStarAlgebra new_k
InnerProductSpace.ofCore _

-- theorem GNS.normedAddCommGroup.norm_eq [hA : QuantumSet A] (x : qS_GNS A) :
--   GNS.normedAddCommGroup.norm (x : qS_GNS A) = ‖modAut (- (hA.k / 2)) (x : A)‖ :=
-- rfl

/-- The inner product algebra structure induced by shifting the quantum-set inner product. -/
@[reducible]
noncomputable def QuantumSet.subsetInnerProductAlgebra (hA : QuantumSet A)
  (new_k : ℝ) :
  letI : starAlgebra (subset new_k A) := QuantumSet.subsetStarAlgebra new_k
  InnerProductAlgebra (subset new_k A) :=
letI : starAlgebra (subset new_k A) := QuantumSet.subsetStarAlgebra new_k
letI := hA.subsetNormedAddCommGroup new_k
letI := hA.subsetInnerProductSpace new_k
{ norm_sq_eq_inner := fun _ => by
    simp only [← norm_sq_eq_re_inner]
  norm_smul_le := fun c x =>
    NormedSpace.norm_smul_le (𝕜 := ℂ) (E := subset new_k A) c x
  conj_symm := inner_conj_symm
  add_left := inner_add_left
  smul_left := inner_smul_left }

lemma QuantumSet.subset_inner_eq [hA : QuantumSet A] (new_k : ℝ) (x y : subset new_k A) :
  letI : starAlgebra (subset new_k A) := QuantumSet.subsetStarAlgebra new_k
  (hA.subsetInnerProductAlgebra new_k).inner x y
    = hA.inner ((toSubsetEquiv new_k).symm x : A)
      (ha.modAut (new_k + -hA.k) ((toSubsetEquiv new_k).symm y)) :=
rfl
lemma QuantumSet.inner_eq_subset_inner [hA : QuantumSet A] (new_k : ℝ) (x y : A) :
  letI : starAlgebra (subset new_k A) := QuantumSet.subsetStarAlgebra _
  hA.inner x y
  = (hA.subsetInnerProductAlgebra new_k).inner
    (toSubsetEquiv new_k x) (toSubsetEquiv new_k (ha.modAut (hA.k + -new_k) y)) :=
by
  rw [subset_inner_eq]
  simp_rw [Equiv.symm_apply_apply, QuantumSet.modAut_apply_modAut]
  ring_nf
  rw [starAlgebra.modAut_zero]; rfl

open scoped InnerProductSpace
/-- A shifted quantum-set synonym inherits a quantum-set structure with exponent `new_k`. -/
@[reducible]
noncomputable def QuantumSet.instSubset (hA : QuantumSet A) (new_k : ℝ) :
    letI : starAlgebra (subset new_k A) := QuantumSet.subsetStarAlgebra _
    QuantumSet (subset new_k A) :=
letI st : starAlgebra (subset new_k A) := QuantumSet.subsetStarAlgebra _
letI gns := hA.subsetInnerProductAlgebra new_k
let to_ := @toSubsetEquiv new_k A
{ modAut_isSymmetric := fun r x y => by
    calc gns.inner (st.modAut r x) y
          = hA.inner (to_.symm (st.modAut r x))
          (ha.modAut (new_k + -hA.k) (to_.symm y)) := rfl
      _ = hA.inner (ha.modAut r (to_.symm x))
        (ha.modAut (new_k + -hA.k) (to_.symm y)) := rfl
      _ = hA.inner (to_.symm x)
        (ha.modAut (new_k + -hA.k) (ha.modAut r (to_.symm y))) := by
          simp_rw [modAut_isSymmetric, modAut_apply_modAut, add_comm]
      _ = hA.inner (to_.symm x)
        (ha.modAut (new_k + -hA.k) (to_.symm (st.modAut r y))) := rfl
      _ = gns.inner x (st.modAut r y) := rfl
  k := new_k
  inner_star_left := fun x y z =>
  by
    calc gns.inner (x * y) z
        = hA.inner (to_.symm (x * y))
          (ha.modAut (new_k + -hA.k) (to_.symm z)) := rfl
      _ = hA.inner (to_.symm x * to_.symm y)
          (ha.modAut (new_k + -hA.k) (to_.symm z)) := by rfl
      _ = hA.inner (to_.symm y)
          (ha.modAut (-hA.k) (to_.symm (star x) * ha.modAut new_k (to_.symm z))) := by
            rw [inner_star_left, add_comm, map_mul, modAut_apply_modAut]; rfl
      _ = hA.inner (to_.symm y)
          (ha.modAut (new_k + -hA.k)
          (ha.modAut (-new_k) (to_.symm (star x))
            * to_.symm z)) := by
            simp_rw [map_mul, modAut_apply_modAut, add_comm, neg_add_cancel_left]
      _ = gns.inner y (st.modAut (- new_k) (star x) * z) := rfl
  inner_conj_left := fun x y z =>
  calc gns.inner (x * y) z
      = hA.inner (to_.symm x * to_.symm y)
        (ha.modAut (new_k + -hA.k) (to_.symm z)) := rfl
    _ = hA.inner (to_.symm x)
      (ha.modAut (new_k + -hA.k) ((to_.symm z)
        * ha.modAut (-new_k + -1) (to_.symm (star y)))) := by
          simp_rw [inner_conj_left, map_mul, modAut_apply_modAut]
          ring_nf
          rfl
    _ = gns.inner x (z * st.modAut (-new_k + -1) (star y)) := rfl
  n := n A
  nIsFintype := QuantumSet.nIsFintype
  nIsDecidableEq := QuantumSet.nIsDecidableEq
  onb := by
    let b :=
      (toSubsetAlgEquiv new_k).toLinearEquiv.symm.trans
        ((modAut ((new_k / 2) + - (k A / 2))).toLinearEquiv.trans
          (hA.onb.repr).toLinearEquiv)
    refine Module.Basis.toOrthonormalBasis
      (Module.Basis.ofEquivFun
        (b.trans (WithLp.linearEquiv 2 ℂ (n A → ℂ)))) ?_
    rw [orthonormal_iff_ite]
    intro i j
    rw [subset_inner_eq, ← add_halves (new_k + -k A), ← QuantumSet.modAut_apply_modAut,
      ← QuantumSet.modAut_isSymmetric]
    simp_rw [b, Module.Basis.coe_ofEquivFun]
    simp only [WithLp.coe_symm_linearEquiv, PiLp.toLp_single, LinearEquiv.trans_symm,
      LinearEquiv.trans_apply, ← AlgEquiv.toLinearEquiv_symm,
      AlgEquiv.toLinearEquiv_apply, AlgEquiv.symm_symm, toSubsetAlgEquiv_eq_toSubsetEquiv,
      Equiv.symm_apply_apply, add_div, neg_div, AlgEquiv.apply_symm_apply]
    calc
      ⟪hA.onb.repr.symm (EuclideanSpace.single i (1 : ℂ)),
        hA.onb.repr.symm (EuclideanSpace.single j (1 : ℂ))⟫_ℂ
        = if i = j then (1 : ℂ) else 0 := by
        simp only [OrthonormalBasis.repr_symm_single, orthonormal_iff_ite.mp hA.onb.orthonormal] }

open QuantumSet in
/-- Transport a linear map between quantum sets to shifted quantum-set synonyms. -/
noncomputable abbrev LinearMap.toSubsetQuantumSet {B : Type*} [starAlgebra B]
  [QuantumSet A] [QuantumSet B] (f : A →ₗ[ℂ] B) (sk₁ sk₂ : ℝ) :
    subset sk₁ A →ₗ[ℂ] subset sk₂ B :=
  (toSubsetAlgEquiv sk₂).toLinearMap ∘ₗ f ∘ₗ
    (toSubsetAlgEquiv sk₁).symm.toLinearMap
open QuantumSet in
/-- Transport a shifted linear map back to the original quantum sets. -/
noncomputable abbrev LinearMap.ofSubsetQuantumSet {B : Type*} [starAlgebra B]
  [QuantumSet A] [QuantumSet B] (sk₁ sk₂ : ℝ)
  (f : subset sk₁ A →ₗ[ℂ] subset sk₂ B) :
    A →ₗ[ℂ] B :=
  (toSubsetAlgEquiv sk₂).symm.toLinearMap ∘ₗ f ∘ₗ
    (toSubsetAlgEquiv sk₁).toLinearMap

theorem QuantumSet.toSubsetAlgEquiv_adjoint [hA : QuantumSet A] (sk₁ : ℝ) :
  letI := hA.instSubset sk₁
  LinearMap.adjoint (toSubsetAlgEquiv sk₁ : A ≃ₐ[ℂ] subset sk₁ A).toLinearMap
    = (ha.modAut (sk₁ + -k A)).toLinearMap ∘ₗ (toSubsetAlgEquiv sk₁).symm.toLinearMap :=
by
  ext1 x
  apply ext_inner_left ℂ
  intro y
  simp_rw [LinearMap.adjoint_inner_right, AlgEquiv.toLinearMap_apply]
  rw [subset_inner_eq]
  rfl
theorem QuantumSet.toSubsetAlgEquiv_symm_adjoint [hA : QuantumSet A] (sk₁ : ℝ) :
  letI := hA.instSubset sk₁
  LinearMap.adjoint (toSubsetAlgEquiv sk₁ : A ≃ₐ[ℂ] subset sk₁ A).symm.toLinearMap
    = (toSubsetAlgEquiv sk₁).toLinearMap ∘ₗ (ha.modAut (-sk₁ + k A)).toLinearMap :=
by
  ext1 x
  letI := hA.instSubset sk₁
  apply ext_inner_left ℂ
  intro y
  simp_rw [LinearMap.adjoint_inner_right, AlgEquiv.toLinearMap_apply]
  rw [subset_inner_eq]
  simp_rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    toSubsetAlgEquiv_eq_toSubsetEquiv, Equiv.symm_apply_apply,
    modAut_apply_modAut]
  ring_nf
  simp only [starAlgebra.modAut_zero, AlgEquiv.one_apply]; rfl

open QuantumSet in
lemma LinearMap.toSubsetQuantumSet_apply {B : Type*} [starAlgebra B]
  [QuantumSet A] [QuantumSet B] (f : A →ₗ[ℂ] B) (sk₁ sk₂ : ℝ) (x : subset sk₁ A) :
  f.toSubsetQuantumSet sk₁ sk₂ x = toSubsetEquiv sk₂ (f ((toSubsetEquiv sk₁).symm x)) := rfl

open QuantumSet in
theorem LinearMap.toSubsetQuantumSet_adjoint_apply {B : Type*} [hb : starAlgebra B]
  [hA : QuantumSet A] [hB : QuantumSet B]
  (f : A →ₗ[ℂ] B) (sk₁ sk₂ : ℝ) :
  letI := hA.instSubset sk₁
  letI := hB.instSubset sk₂
  (LinearMap.adjoint (f.toSubsetQuantumSet sk₁ sk₂)) =
    ((ha.modAut (-sk₁ + hA.k)).toLinearMap
      ∘ₗ (LinearMap.adjoint f)
      ∘ₗ (hb.modAut (sk₂ + -hB.k)).toLinearMap).toSubsetQuantumSet sk₂ sk₁ :=
by
  simp_rw [toSubsetQuantumSet, LinearMap.adjoint_comp,
    toSubsetAlgEquiv_symm_adjoint, toSubsetAlgEquiv_adjoint,
    LinearMap.comp_assoc]

open QuantumSet in
theorem LinearMap.ofSubsetQuantumSet_adjoint_apply {B : Type*} [hb : starAlgebra B]
  [hA : QuantumSet A] [hB : QuantumSet B]
  (sk₁ sk₂ : ℝ) (f : subset sk₁ A →ₗ[ℂ] subset sk₂ B) :
  letI := hA.instSubset sk₁
  letI := hB.instSubset sk₂
  (LinearMap.adjoint (f.ofSubsetQuantumSet sk₁ sk₂)) =
    (ha.modAut (sk₁ + -hA.k)).toLinearMap
      ∘ₗ (LinearMap.adjoint f).ofSubsetQuantumSet sk₂ sk₁
      ∘ₗ (hb.modAut (-sk₂ + hB.k)).toLinearMap :=
by
  letI := hA.instSubset sk₁
  letI := hB.instSubset sk₂
  simp_rw [ofSubsetQuantumSet, LinearMap.adjoint_comp,
    toSubsetAlgEquiv_symm_adjoint, toSubsetAlgEquiv_adjoint,
    LinearMap.comp_assoc]

theorem rankOne_toSubsetQuantumSet {B : Type*} [hb : starAlgebra B]
  [hA : QuantumSet A] [hB : QuantumSet B]
  (sk₁ sk₂ : ℝ) (a : B) (b : A) :
  letI := hA.instSubset sk₁
  letI := hB.instSubset sk₂
  (rankOne ℂ a b).toLinearMap.toSubsetQuantumSet sk₁ sk₂
    = (rankOne ℂ (QuantumSet.toSubsetEquiv sk₂ a)
      (QuantumSet.toSubsetEquiv sk₁ (ha.modAut (-sk₁ + k A) b))).toLinearMap :=
by
  letI := hA.instSubset sk₁
  letI := hB.instSubset sk₂
  rw [LinearMap.toSubsetQuantumSet, LinearMap.rankOne_comp,
    LinearMap.comp_rankOne, QuantumSet.toSubsetAlgEquiv_symm_adjoint]
  simp_rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply]
  rfl

open QuantumSet in
theorem rankOne_ofSubsetQuantumSet {B : Type*} [starAlgebra B]
  [hA : QuantumSet A] [hB : QuantumSet B] (sk₁ sk₂ : ℝ)
  (a : subset sk₂ B) (b : subset sk₁ A) :
  letI := hA.instSubset sk₁
  letI := hB.instSubset sk₂
  (rankOne ℂ a b).ofSubsetQuantumSet sk₁ sk₂
    = (rankOne ℂ ((toSubsetEquiv sk₂).symm a)
      (ha.modAut (sk₁ + -k A) ((toSubsetEquiv sk₁).symm b))).toLinearMap :=
by
  letI := hA.instSubset sk₁
  letI := hB.instSubset sk₂
  rw [LinearMap.ofSubsetQuantumSet, LinearMap.rankOne_comp,
    LinearMap.comp_rankOne, QuantumSet.toSubsetAlgEquiv_adjoint]
  simp_rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply]
  rfl

@[simp]
theorem QuantumSet.subset_k {A : Type*} [starAlgebra A] [h : QuantumSet A] (r : ℝ) :
  letI := QuantumSet.instSubset h r
  k (QuantumSet.subset r A) = r :=
rfl

@[simp]
theorem QuantumSet.subset_n {A : Type*} [starAlgebra A] [h : QuantumSet A] (r : ℝ) :
  letI := QuantumSet.instSubset h r
  n (QuantumSet.subset r A) = n A :=
rfl

open scoped TensorProduct
/-- The tautological algebra equivalence between tensor products of shifted synonyms. -/
noncomputable def QuantumSet.subsetTensorAlgEquiv {A B : Type*} [starAlgebra A]
    [starAlgebra B] (r : ℝ) :
    (QuantumSet.subset r A ⊗[ℂ] QuantumSet.subset r B) ≃ₐ[ℂ]
      QuantumSet.subset r (A ⊗[ℂ] B) :=
  (AlgEquiv.TensorProduct.map
    (QuantumSet.toSubsetAlgEquiv r).symm
    (QuantumSet.toSubsetAlgEquiv r).symm).trans (QuantumSet.toSubsetAlgEquiv r)
theorem QuantumSet.subsetTensorAlgEquiv_tmul {A B : Type*} [starAlgebra A] [starAlgebra B]
  (r : ℝ) (x : QuantumSet.subset r A) (y : QuantumSet.subset r B) :
  QuantumSet.subsetTensorAlgEquiv r (x ⊗ₜ[ℂ] y)
    = QuantumSet.toSubsetAlgEquiv r
      ((QuantumSet.toSubsetAlgEquiv r).symm x ⊗ₜ[ℂ] (QuantumSet.toSubsetAlgEquiv r).symm y) :=
rfl
theorem QuantumSet.subsetTensorAlgEquiv_symm_tmul {A B : Type*} [starAlgebra A] [starAlgebra B]
  (r : ℝ) (a : A) (b : B) :
  (QuantumSet.subsetTensorAlgEquiv r).symm (QuantumSet.toSubsetAlgEquiv r (a ⊗ₜ[ℂ] b))
    = (QuantumSet.toSubsetAlgEquiv r)
      ((QuantumSet.toSubsetAlgEquiv r a) ⊗ₜ[ℂ] (QuantumSet.toSubsetAlgEquiv r b)) :=
rfl

theorem LinearMap.mul'_quantumSet_subset_eq {A : Type*} [starAlgebra A] [QuantumSet A]
    (r : ℝ) :
  LinearMap.mul' ℂ (QuantumSet.subset r A) = (QuantumSet.toSubsetAlgEquiv r).toLinearMap
      ∘ₗ (LinearMap.mul' ℂ A)
      ∘ₗ (TensorProduct.map
        (QuantumSet.toSubsetAlgEquiv r).symm.toLinearMap
        (QuantumSet.toSubsetAlgEquiv r).symm.toLinearMap) :=
by
  ext x y
  simp [AlgEquiv.toLinearMap_apply]

theorem QuantumSet.subsetTensorAlgEquiv_adjoint
  {A B : Type*} [starAlgebra A] [starAlgebra B] [QuantumSet A] [QuantumSet B]
  [h : Fact (k A = k B)] (r : ℝ) :
  letI h1 := QuantumSet.instSubset (A := A) (by infer_instance) r;
  letI h2 := QuantumSet.instSubset (A := B) (by infer_instance) r;
  letI h3 := QuantumSet.tensorProduct (h := h);
  letI := QuantumSet.tensorProduct (hA := h1) (hB := h2) (h := Fact.mk rfl);
  letI := QuantumSet.instSubset (A := A ⊗[ℂ] B) h3 r;
    LinearMap.adjoint (QuantumSet.subsetTensorAlgEquiv (A := A) (B := B) r).toLinearMap
    = (QuantumSet.subsetTensorAlgEquiv r).symm.toLinearMap :=
by
  simp only [QuantumSet.subsetTensorAlgEquiv, AlgEquiv.trans_toLinearMap,
    AlgEquiv.TensorProduct.map_toLinearMap]
  letI h1 := QuantumSet.instSubset (A := A) (by infer_instance) r
  letI h2 := QuantumSet.instSubset (A := B) (by infer_instance) r
  letI h3 := QuantumSet.tensorProduct (h := h)
  letI := QuantumSet.tensorProduct (hA := h1) (hB := h2) (h := Fact.mk rfl)
  letI := QuantumSet.instSubset (A := A ⊗[ℂ] B) h3 r
  refine (LinearMap.adjoint_comp
    (QuantumSet.toSubsetAlgEquiv r : A ⊗[ℂ] B ≃ₐ[ℂ] subset r (A ⊗[ℂ] B)).toLinearMap
    (TensorProduct.map (QuantumSet.toSubsetAlgEquiv r).symm.toLinearMap
      (QuantumSet.toSubsetAlgEquiv r).symm.toLinearMap)).trans ?_
  simp only [TensorProduct.map_adjoint, QuantumSet.toSubsetAlgEquiv_symm_adjoint,
    QuantumSet.toSubsetAlgEquiv_adjoint r, modAut_tensor, QuantumSet.tensorProduct.k_eq₁,
    ← h.out, AlgEquiv.TensorProduct.map_toLinearMap]
  change (TensorProduct.map
    ((QuantumSet.toSubsetAlgEquiv r).toLinearMap ∘ₗ (modAut (-r + k A)).toLinearMap)
    ((QuantumSet.toSubsetAlgEquiv r).toLinearMap ∘ₗ (modAut (-r + k A)).toLinearMap) ∘ₗ
      TensorProduct.map (modAut (r + -k A)).toLinearMap
        (modAut (r + -k A)).toLinearMap) ∘ₗ
      (QuantumSet.toSubsetAlgEquiv r).symm.toLinearMap = _
  rw [← TensorProduct.map_comp]
  simp only [AlgEquiv.coe_comp (e := modAut _)]
  have hmodA :
      (modAut (A := A) (r + -k A)).trans
          ((modAut (A := A) (-r + k A)).trans (QuantumSet.toSubsetAlgEquiv r)) =
        QuantumSet.toSubsetAlgEquiv r := by
    ext x
    simp only [AlgEquiv.trans_apply, QuantumSet.modAut_apply_modAut]
    ring_nf
    simp only [starAlgebra.modAut_zero, AlgEquiv.one_apply]
  have hmodB :
      (modAut (A := B) (r + -k A)).trans
          ((modAut (A := B) (-r + k A)).trans (QuantumSet.toSubsetAlgEquiv r)) =
        QuantumSet.toSubsetAlgEquiv r := by
    ext x
    simp only [AlgEquiv.trans_apply, QuantumSet.modAut_apply_modAut]
    ring_nf
    simp only [starAlgebra.modAut_zero, AlgEquiv.one_apply]
  simp only [hmodA, hmodB]
  rfl

theorem QuantumSet.comul_subset_eq {A : Type*} [starAlgebra A] [QuantumSet A] (r : ℝ) :
  letI := QuantumSet.instSubset (A := A) (by infer_instance) r
  letI : Fact (k A = k A) := Fact.mk rfl
  Coalgebra.comul (R := ℂ) (A := QuantumSet.subset r A)
    = (TensorProduct.map (QuantumSet.toSubsetAlgEquiv r).toLinearMap
        (QuantumSet.toSubsetAlgEquiv r).toLinearMap)
      ∘ₗ
    (Coalgebra.comul (R := ℂ) (A := A))
       ∘ₗ (toSubsetAlgEquiv r).symm.toLinearMap  :=
by
  letI := QuantumSet.instSubset (A := A) (by infer_instance) r
  letI : Fact (k A = k A) := Fact.mk rfl
  letI hh := QuantumSet.tensorProduct (A := A) (B := A) (h := Fact.mk rfl)
  letI := QuantumSet.instSubset (A := A ⊗[ℂ] A) (by infer_instance) r
  simp only [Coalgebra.comul_eq_mul_adjoint, LinearMap.mul'_quantumSet_subset_eq]
  simp only [LinearMap.adjoint_comp, TensorProduct.map_adjoint,
    toSubsetAlgEquiv_symm_adjoint, toSubsetAlgEquiv_adjoint]
  simp only [← LinearMap.comp_assoc]
  congr 1
  simp only [LinearMap.comp_assoc, ← Coalgebra.comul_eq_mul_adjoint,
    ← (QuantumSet.modAut_isCoalgHom _).2, TensorProduct.map_comp,
    ← AlgEquiv.TensorProduct.map_toLinearMap, ← modAut_tensor]
  congr 1
  rw [← LinearMap.comp_assoc]
  rw [AlgEquiv.coe_comp, starAlgebra.modAut_trans]
  ring_nf
  simp only [starAlgebra.modAut_zero, AlgEquiv.one_toLinearMap, LinearMap.one_comp]

theorem schurMul_toSubsetQuantumSet {A B : Type*} [starAlgebra A] [starAlgebra B]
    [QuantumSet A] [QuantumSet B]
    {f : A →ₗ[ℂ] B} (r₁ r₂ : ℝ) :
  letI := QuantumSet.instSubset (A := A) (by infer_instance) r₁;
  letI := QuantumSet.instSubset (A := B) (by infer_instance) r₂;
  (f.toSubsetQuantumSet r₁ r₂ •ₛ f.toSubsetQuantumSet r₁ r₂) =
    (f •ₛ f).toSubsetQuantumSet r₁ r₂ :=
by
  simp only [schurMul_apply_apply]
  simp only [QuantumSet.comul_subset_eq]
  nth_rw 2 [← LinearMap.comp_assoc]
  rw [← TensorProduct.map_comp, LinearMap.mul'_quantumSet_subset_eq]
  simp only [LinearMap.toSubsetQuantumSet, LinearMap.comp_assoc]
  simp only [← LinearMap.comp_assoc, ← TensorProduct.map_comp, AlgEquiv.symm_comp_toLinearMap,
    LinearMap.id_comp, LinearMap.comp_id]

theorem LinearMap.toSubsetQuantumSet_inj
  {A B : Type*} [starAlgebra A] [starAlgebra B] [QuantumSet A] [QuantumSet B]
  {f g : A →ₗ[ℂ] B} (r₁ r₂ : ℝ) :
  f.toSubsetQuantumSet r₁ r₂ = g.toSubsetQuantumSet r₁ r₂ ↔ f = g :=
by rfl

theorem QuantumSet.toSubsetEquiv_isReal {A : Type*} [Star A] (r : ℝ) :
  LinearMap.IsReal (QuantumSet.toSubsetEquiv r (A := A)) :=
fun _ => rfl
theorem QuantumSet.toSubsetEquiv_symm_isReal {A : Type*} [Star A] (r : ℝ) :
  LinearMap.IsReal (QuantumSet.toSubsetEquiv r (A := A)).symm :=
fun _ => rfl

theorem LinearMap.toSubsetQuantumSet_isReal_iff
  {A B : Type*} [starAlgebra A] [starAlgebra B] [QuantumSet A] [QuantumSet B]
  {f : A →ₗ[ℂ] B} (r₁ r₂ : ℝ) :
  letI := QuantumSet.instSubset (A := A) (by infer_instance) r₁;
  letI := QuantumSet.instSubset (A := B) (by infer_instance) r₂;
    LinearMap.IsReal (f.toSubsetQuantumSet r₁ r₂) ↔ LinearMap.IsReal f :=
by
  simp only [LinearMap.IsReal, LinearMap.toSubsetQuantumSet_apply,
    ← QuantumSet.toSubsetEquiv_isReal (A := B) r₂ _,
    QuantumSet.toSubsetEquiv_symm_isReal (A := _) r₁ _]
  rfl

variable {A : Type*} [starAlgebra A] [hA : QuantumSet A]

theorem QuantumSet.toSubset_onb (r : ℝ) (i : n A) :
  letI := hA.instSubset r;
  this.onb i =
    toSubsetAlgEquiv r (modAut ((k A / 2) + -(r / 2)) (hA.onb i)) :=
by
  letI := hA.instSubset r
  simp [onb]

lemma QuantumSet.comul_of_subset (r : ℝ) :
  letI := hA.instSubset r;
  Coalgebra.comul (R := ℂ) (A := A) =
    (TensorProduct.map (toSubsetAlgEquiv r).symm.toLinearMap
      (toSubsetAlgEquiv r).symm.toLinearMap)
    ∘ₗ Coalgebra.comul (R := ℂ)
    ∘ₗ (toSubsetAlgEquiv r).toLinearMap :=
by
  rw [← AlgEquiv.TensorProduct.map_toLinearMap,
    ← AlgEquiv.TensorProduct.map_symm, ← AlgEquiv.comp_linearMap_eq_iff,
    eq_comm, AlgEquiv.linearMap_comp_eq_iff, AlgEquiv.TensorProduct.map_toLinearMap,
    LinearMap.comp_assoc]
  exact comul_subset_eq r

theorem QuantumSet.toSubsetAlgEquiv_isReal
  {A : Type*} [Ring A] [Algebra ℂ A] [Star A] (r : ℝ) :
  LinearMap.IsReal (QuantumSet.toSubsetAlgEquiv r (A := A)) :=
fun _ => rfl

theorem QuantumSet.innerOne_map_one_toSubset_eq
  {A B : Type*} [starAlgebra A] [starAlgebra B] [QuantumSet A] [QuantumSet B]
  (r₁ r₂ : ℝ) {f : A →ₗ[ℂ] B} :
  letI := QuantumSet.instSubset (A := B) (by infer_instance) r₂
  ⟪1, f 1⟫_ℂ = ⟪1, (f.toSubsetQuantumSet r₁ r₂) 1⟫_ℂ :=
by
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply, map_one]
  rw [← AlgEquiv.toLinearMap_apply]
  letI := QuantumSet.instSubset (A := B) (by infer_instance) r₂
  nth_rw 2 [← LinearMap.adjoint_inner_left]
  rw [toSubsetAlgEquiv_adjoint, LinearMap.comp_apply]
  simp only [AlgEquiv.toLinearMap_apply, map_one]

instance {A : Type*} [hA : PartialOrder A] (r : ℝ) :
    PartialOrder (QuantumSet.subset r A) :=
hA
instance {A : Type*} [hA : NonUnitalNonAssocSemiring A] (r : ℝ) :
  NonUnitalNonAssocSemiring (QuantumSet.subset r A) :=
hA
instance {A : Type*} [hA : NonUnitalSemiring A] (r : ℝ) :
  NonUnitalSemiring (QuantumSet.subset r A) :=
hA
instance {A : Type*} [NonUnitalNonAssocSemiring A] [hA : StarRing A] (r : ℝ) :
  StarRing (QuantumSet.subset r A) :=
hA
instance {A : Type*} [NonUnitalSemiring A] [PartialOrder A] [StarRing A]
    [hA : StarOrderedRing A] (r : ℝ) :
  StarOrderedRing (QuantumSet.subset r A) :=
hA
instance {A : Type*} [hA : Nontrivial A] (r : ℝ) :
  Nontrivial (QuantumSet.subset r A) :=
hA

theorem QuantumSet.normOne_toSubset {A : Type*} [starAlgebra A] [QuantumSet A] (r : ℝ) :
  letI := QuantumSet.instSubset (A := A) (by infer_instance) r
  ‖(1 : A)‖ = ‖(1 : QuantumSet.subset r A)‖ :=
by
  letI := QuantumSet.instSubset (A := A) (by infer_instance) r
  simp_rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), QuantumSet.subset_inner_eq,
    ← QuantumSet.toSubsetAlgEquiv_symm_eq_toSubsetEquiv, map_one]

instance {A : Type*} [h : AddCommMonoid A] (r : ℝ) :
    AddCommMonoid (QuantumSet.subset r A) :=
  h

instance {A : Type*} [AddCommMonoid A] [h : Module ℂ A] (r : ℝ) :
    Module ℂ (QuantumSet.subset r A) :=
  h

theorem LinearMap.toSubsetQuantumSet_eq_iff {A B : Type*} [ha : starAlgebra A]
  [starAlgebra B] [hA : QuantumSet A] [hB : QuantumSet B] (sk₁ : ℝ) (sk₂ : ℝ)
  (f : A →ₗ[ℂ] B) :
  letI := hA.instSubset sk₁
  letI := hB.instSubset sk₂
  ∀ g : QuantumSet.subset sk₁ A →ₗ[ℂ] QuantumSet.subset sk₂ B,
    f.toSubsetQuantumSet sk₁ sk₂ = g ↔ f = g.ofSubsetQuantumSet sk₁ sk₂ :=
by
  letI := hA.instSubset sk₁
  letI := hB.instSubset sk₂
  intro g
  rfl
