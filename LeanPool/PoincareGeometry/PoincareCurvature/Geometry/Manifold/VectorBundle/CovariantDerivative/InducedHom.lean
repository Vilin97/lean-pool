/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.HomBundleComp

/-!
# Covariant derivatives on trivial and hom bundles

This file constructs the two induced connections needed for covariant tensor
calculus without assuming an external tensor-connection API.

* `trivialCovariantDerivative` is ordinary differentiation on a trivial real
  vector bundle.
* `inducedHomCovariantDerivative` is the connection on `Hom(V₁,V₂)` induced by
  connections on `V₁` and `V₂`.

The definition of a Mathlib `CovariantDerivative` must return a continuous
linear map even for a completely arbitrary (possibly nondifferentiable)
section.  Accordingly the hom connection uses its geometric formula when the
hom section is differentiable at the point and returns zero otherwise.  The
covariant-derivative laws only constrain differentiable sections, and the
exported computation theorem removes this implementation branch there.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff

namespace CovariantDerivative

section Trivial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Ordinary differentiation as the flat connection on a trivial real vector
bundle. -/
def trivialCovariantDerivative (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    CovariantDerivative I F (Bundle.Trivial M F) where
  toFun := fun σ x => mvfderiv (I := I) σ x
  isCovariantDerivativeOnUniv := by
    refine
      { add := ?_
        leibniz := ?_ }
    · intro σ τ x hσ hτ _hx
      have hσ' : MDiffAt
          (fun y : M => (Bundle.Trivial.trivialization M F (T% σ y)).2) x := by
        have h := ((trivializationAt F (Bundle.Trivial M F) x).mdifferentiableAt_section_iff
          I σ (FiberBundle.mem_baseSet_trivializationAt' x)).mp hσ
        simpa [Bundle.Trivial.eq_trivialization M F] using h
      have hτ' : MDiffAt
          (fun y : M => (Bundle.Trivial.trivialization M F (T% τ y)).2) x := by
        have h := ((trivializationAt F (Bundle.Trivial M F) x).mdifferentiableAt_section_iff
          I τ (FiberBundle.mem_baseSet_trivializationAt' x)).mp hτ
        simpa [Bundle.Trivial.eq_trivialization M F] using h
      simpa [Bundle.Trivial.trivialization_apply] using mvfderiv_add (I := I) hσ' hτ'
    · intro σ g x hσ hg _hx
      have hσ' : MDiffAt
          (fun y : M => (Bundle.Trivial.trivialization M F (T% σ y)).2) x := by
        have h := ((trivializationAt F (Bundle.Trivial M F) x).mdifferentiableAt_section_iff
          I σ (FiberBundle.mem_baseSet_trivializationAt' x)).mp hσ
        simpa [Bundle.Trivial.eq_trivialization M F] using h
      simpa [Bundle.Trivial.trivialization_apply] using mvfderiv_smul (I := I) hg hσ'

@[simp]
theorem trivialCovariantDerivative_apply
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (σ : M → F) (x : M) :
    trivialCovariantDerivative (I := I) F σ x = mvfderiv (I := I) σ x :=
  rfl

end Trivial

section InducedHom

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {V₁ V₂ : M → Type*}
  [TopologicalSpace (TotalSpace F₁ V₁)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, NormedSpace ℝ (V₁ x)]
  [∀ x, FiniteDimensional ℝ (V₁ x)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, NormedSpace ℝ (V₂ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [ContMDiffVectorBundle 2 F₁ V₁ I] [ContMDiffVectorBundle 1 F₂ V₂ I]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "Hom₁₂" => (fun x : M => V₁ x →L[ℝ] V₂ x)

/-- The geometric hom-connection formula at a point where the hom section is
differentiable.  The auxiliary section extending the input fibre vector is
canonical and linear in that input. -/
def inducedHomAtOfMDiff
    (cov₁ : CovariantDerivative I F₁ V₁)
    (cov₂ : CovariantDerivative I F₂ V₂)
    (φ : ∀ x : M, Hom₁₂ x) (x : M)
    (hφ : MDiffAt
      (fun y => TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := Hom₁₂) y (φ y)) x) :
    TM x →L[ℝ] Hom₁₂ x := by
  let D : V₁ x →ₗ[ℝ] (TM x →L[ℝ] V₂ x) :=
    { toFun := fun v =>
        cov₂ (fun y => φ y (smoothExtend (I := I) (F := F₁) (V := V₁) x v y)) x -
          (φ x).comp (cov₁ (smoothExtend (I := I) (F := F₁) (V := V₁) x v) x)
      map_add' := by
        intro v w
        have hextv : MDiffAt
            (T% (smoothExtend (I := I) (F := F₁) (V := V₁) x v)) x :=
          ((smoothExtend_contMDiff_two (I := I) (F := F₁) (V := V₁) x v).of_le
            (by simp) x).mdifferentiableAt one_ne_zero
        have hextw : MDiffAt
            (T% (smoothExtend (I := I) (F := F₁) (V := V₁) x w)) x :=
          ((smoothExtend_contMDiff_two (I := I) (F := F₁) (V := V₁) x w).of_le
            (by simp) x).mdifferentiableAt one_ne_zero
        have hv : MDiffAt
            (T% (fun y => φ y
              (smoothExtend (I := I) (F := F₁) (V := V₁) x v y))) x :=
          hφ.clm_bundle_apply hextv
        have hw : MDiffAt
            (T% (fun y => φ y
              (smoothExtend (I := I) (F := F₁) (V := V₁) x w y))) x :=
          hφ.clm_bundle_apply hextw
        rw [smoothExtend_add]
        have happ :
            (fun y => φ y ((smoothExtend (I := I) (F := F₁) (V := V₁) x v +
              smoothExtend (I := I) (F := F₁) (V := V₁) x w) y)) =
              (fun y => φ y (smoothExtend (I := I) (F := F₁) (V := V₁) x v y)) +
              (fun y => φ y (smoothExtend (I := I) (F := F₁) (V := V₁) x w y)) := by
          funext y
          simp
        rw [happ]
        rw [cov₂.isCovariantDerivativeOn.add hv hw]
        rw [cov₁.isCovariantDerivativeOn.add hextv hextw]
        ext u
        simp only [sub_apply, add_apply,
          ContinuousLinearMap.comp_apply, map_add]
        module
      map_smul' := by
        intro c v
        have hextv : MDiffAt
            (T% (smoothExtend (I := I) (F := F₁) (V := V₁) x v)) x :=
          ((smoothExtend_contMDiff_two (I := I) (F := F₁) (V := V₁) x v).of_le
            (by simp) x).mdifferentiableAt one_ne_zero
        have hv : MDiffAt
            (T% (fun y => φ y
              (smoothExtend (I := I) (F := F₁) (V := V₁) x v y))) x :=
          hφ.clm_bundle_apply hextv
        rw [smoothExtend_smul]
        have happ :
            (fun y => φ y ((c •
              smoothExtend (I := I) (F := F₁) (V := V₁) x v) y)) =
              c • (fun y => φ y
                (smoothExtend (I := I) (F := F₁) (V := V₁) x v y)) := by
          funext y
          simp
        rw [happ]
        rw [cov₂.isCovariantDerivativeOn.smul_const c hv]
        rw [cov₁.isCovariantDerivativeOn.smul_const c hextv]
        ext u
        simp only [sub_apply, smul_apply,
          ContinuousLinearMap.comp_apply, map_smul]
        simp only [RingHom.id_apply]
        module }
  let Dc : V₁ x →L[ℝ] (TM x →L[ℝ] V₂ x) :=
    LinearMap.toContinuousLinearMap D
  exact (ContinuousLinearMap.flipₗᵢ ℝ (V₁ x) (TM x) (V₂ x)) Dc

@[simp]
theorem inducedHomAtOfMDiff_apply
    (cov₁ : CovariantDerivative I F₁ V₁)
    (cov₂ : CovariantDerivative I F₂ V₂)
    (φ : ∀ x : M, Hom₁₂ x) (x : M)
    (hφ : MDiffAt
      (fun y => TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := Hom₁₂) y (φ y)) x)
    (u : TM x) (v : V₁ x) :
    inducedHomAtOfMDiff cov₁ cov₂ φ x hφ u v =
      cov₂ (fun y => φ y (smoothExtend (I := I) (F := F₁) (V := V₁) x v y)) x u -
        φ x (cov₁ (smoothExtend (I := I) (F := F₁) (V := V₁) x v) x u) := by
  rfl

/-- The connection induced on a hom bundle by source and target connections. -/
def inducedHomCovariantDerivative
    (cov₁ : CovariantDerivative I F₁ V₁)
    (cov₂ : CovariantDerivative I F₂ V₂) :
    CovariantDerivative I (F₁ →L[ℝ] F₂) Hom₁₂ where
  toFun := fun φ x => by
    classical
    exact if hφ : MDiffAt
          (fun y => TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := Hom₁₂) y (φ y)) x then
        inducedHomAtOfMDiff cov₁ cov₂ φ x hφ
      else 0
  isCovariantDerivativeOnUniv := by
    classical
    refine
      { add := ?_
        leibniz := ?_ }
    · intro φ ψ x hφ hψ _hx
      have hadd := mdifferentiableAt_add_section hφ hψ
      simp only [dif_pos hφ, dif_pos hψ, dif_pos hadd]
      ext u v
      simp only [inducedHomAtOfMDiff_apply, add_apply]
      have hext : MDiffAt
          (T% (smoothExtend (I := I) (F := F₁) (V := V₁) x v)) x :=
        ((smoothExtend_contMDiff_two (I := I) (F := F₁) (V := V₁) x v).of_le
          (by simp) x).mdifferentiableAt one_ne_zero
      have hφv : MDiffAt
          (T% (fun y => φ y
            (smoothExtend (I := I) (F := F₁) (V := V₁) x v y))) x :=
        hφ.clm_bundle_apply hext
      have hψv : MDiffAt
          (T% (fun y => ψ y
            (smoothExtend (I := I) (F := F₁) (V := V₁) x v y))) x :=
        hψ.clm_bundle_apply hext
      have happ :
          (fun y => (φ + ψ) y
            (smoothExtend (I := I) (F := F₁) (V := V₁) x v y)) =
            (fun y => φ y
              (smoothExtend (I := I) (F := F₁) (V := V₁) x v y)) +
            (fun y => ψ y
              (smoothExtend (I := I) (F := F₁) (V := V₁) x v y)) := by
        funext y
        simp
      rw [happ, cov₂.isCovariantDerivativeOn.add hφv hψv]
      simp only [Pi.add_apply, add_apply]
      module
    · intro φ g x hφ hg _hx
      have hsmul := hg.smul_section hφ
      simp only [dif_pos hφ, dif_pos hsmul]
      ext u v
      simp only [inducedHomAtOfMDiff_apply]
      have hext : MDiffAt
          (T% (smoothExtend (I := I) (F := F₁) (V := V₁) x v)) x :=
        ((smoothExtend_contMDiff_two (I := I) (F := F₁) (V := V₁) x v).of_le
          (by simp) x).mdifferentiableAt one_ne_zero
      have hφv : MDiffAt
          (T% (fun y => φ y
            (smoothExtend (I := I) (F := F₁) (V := V₁) x v y))) x :=
        hφ.clm_bundle_apply hext
      have happ :
          (fun y => (g • φ) y
            (smoothExtend (I := I) (F := F₁) (V := V₁) x v y)) =
            g • (fun y => φ y
              (smoothExtend (I := I) (F := F₁) (V := V₁) x v y)) := by
        funext y
        simp
      rw [happ, cov₂.isCovariantDerivativeOn.leibniz hφv hg]
      simp only [Pi.smul_apply', smul_apply,
        add_apply, ContinuousLinearMap.smulRight_apply,
        smoothExtend_apply, inducedHomAtOfMDiff_apply]
      module

theorem inducedHomCovariantDerivative_apply_of_mdifferentiableAt
    (cov₁ : CovariantDerivative I F₁ V₁)
    (cov₂ : CovariantDerivative I F₂ V₂)
    {φ : ∀ x : M, Hom₁₂ x} {x : M}
    (hφ : MDiffAt
      (fun y => TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := Hom₁₂) y (φ y)) x) :
    inducedHomCovariantDerivative cov₁ cov₂ φ x =
      inducedHomAtOfMDiff cov₁ cov₂ φ x hφ := by
  classical
  simp [inducedHomCovariantDerivative, hφ]

end InducedHom

end CovariantDerivative
