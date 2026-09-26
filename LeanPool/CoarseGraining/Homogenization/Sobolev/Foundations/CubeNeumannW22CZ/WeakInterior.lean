/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.VectorFieldAndApex
public import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.Translation

/-! # Weak Interior -/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

/-!
# Weak interior interface for the cube Neumann CZ discharge

This file starts the difference-quotient route for the cube Neumann `W2,2` /
Calderon-Zygmund estimate.  The reusable interior theorem consumes a weak
Poisson equation for an `H1Function`; the first bridge below packages the
already-proved reflected-block weak equation in exactly that form.
-/

/-- Weak equation `-Delta u = f` on an open set, tested against smooth compactly
supported functions whose topological support lies in the set. -/
def WeakPoissonEquationOn {d : ℕ} (U : Set (Vec d))
    (u : H1Function U) (f : Vec d → ℝ) : Prop :=
  ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ U →
      ∫ x in U, vecDot (u.grad x) (euclideanGradient φ x) ∂MeasureTheory.volume =
        ∫ x in U, f x * φ x ∂MeasureTheory.volume

/-- A weak `L²` Hessian witness for an `H¹` function on `U`.

The second derivative convention is: `hess i j` is the weak `j`th derivative
of the `i`th gradient coordinate. -/
structure HasWeakHessianOn {d : ℕ} (U : Set (Vec d)) (u : H1Function U) where
  hess : Fin d → Fin d → Vec d → ℝ
  hess_memL2 : ∀ i j, MemScalarL2 U (hess i j)
  weak_second :
    ∀ i j, HasWeakPartialDerivOn U j (fun x => u.grad x i) (hess i j)

namespace HasWeakHessianOn

variable {d : ℕ} {U : Set (Vec d)} {u : H1Function U}

/-- Unpack the weak second-derivative identity for one Hessian coordinate. -/
theorem coord (H : HasWeakHessianOn U u) (i j : Fin d) :
    HasWeakPartialDerivOn U j (fun x => u.grad x i) (H.hess i j) :=
  H.weak_second i j

/-- The `L²(U)` realization of one Hessian coordinate. -/
noncomputable def hessCoordToScalarL2 (H : HasWeakHessianOn U u)
    (i j : Fin d) : ScalarL2 U :=
  Homogenization.toScalarL2 (H.hess_memL2 i j)

/-- Sum of scalar `L²` norms over all Hessian coordinates. This is the
quantity the interior estimate should bound. -/
noncomputable def hessianCoordL2NormSum (H : HasWeakHessianOn U u) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, ‖H.hessCoordToScalarL2 i j‖

theorem hessianCoordL2NormSum_nonneg (H : HasWeakHessianOn U u) :
    0 ≤ H.hessianCoordL2NormSum := by
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- Restrict a weak Hessian witness to a smaller open set. -/
noncomputable def restrict (H : HasWeakHessianOn U u)
    {V : Set (Vec d)} (hVopen : IsOpen V) (hVU : V ⊆ U) :
    HasWeakHessianOn V (u.restrict hVopen hVU) where
  hess := H.hess
  hess_memL2 := by
    intro i j
    exact (H.hess_memL2 i j).mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hVU)
  weak_second := by
    intro i j
    simpa [H1Function.restrict] using
      (H.weak_second i j).restrict hVopen hVU

end HasWeakHessianOn

/-- Smooth compactly supported functions carry the classical Hessian as a weak
`L²` Hessian witness. This fixes the sign and coordinate convention for the
future nonsmooth interior theorem. -/
noncomputable def hasWeakHessianOn_ofContDiff {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfs : HasCompactSupport f) :
    HasWeakHessianOn U
      (H1Function.ofContDiff hU (hf.of_le (by simp)) hfs) := by
  refine
    { hess := fun i j => euclideanCoordSecondDeriv i j f
      hess_memL2 := ?_
      weak_second := ?_ }
  · intro i j
    have hcont : Continuous (euclideanCoordSecondDeriv i j f) :=
      (contDiff_euclideanCoordSecondDeriv hf i j).continuous
    have hs : HasCompactSupport (euclideanCoordSecondDeriv i j f) :=
      hasCompactSupport_euclideanCoordSecondDeriv hfs i j
    simpa [MemScalarL2, volumeMeasureOn] using
      (hcont.memLp_of_hasCompactSupport hs).restrict U
  · intro i j
    have hweak :
        HasWeakPartialDerivOn U j (euclideanCoordDeriv i f)
          (euclideanCoordSecondDeriv i j f) := by
      simpa [euclideanCoordSecondDeriv] using!
        (HasWeakPartialDerivOn.of_contDiff
          (U := U) (i := j) (f := euclideanCoordDeriv i f)
          ((contDiff_euclideanCoordDeriv hf i).of_le (by simp)))
    simpa [H1Function.ofContDiff, euclideanCoordDeriv] using! hweak

namespace WeakPoissonEquationOn

variable {d : ℕ} {U : Set (Vec d)}
variable {u : H1Function U} {f : Vec d → ℝ}

/-- Unpack a weak Poisson equation at a smooth compactly supported test. -/
theorem test (h : WeakPoissonEquationOn U u f)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ U) :
    ∫ x in U, vecDot (u.grad x) (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ x in U, f x * φ x ∂MeasureTheory.volume :=
  h φ hφ hφs hφ_sub

/-- Restrict a weak Poisson equation to a smaller open set. -/
theorem restrict (h : WeakPoissonEquationOn U u f)
    {V : Set (Vec d)} (hVopen : IsOpen V) (hVU : V ⊆ U) :
    WeakPoissonEquationOn V (u.restrict hVopen hVU) f := by
  intro φ hφ hφs hφ_sub
  have hφ_subU : tsupport φ ⊆ U := hφ_sub.trans hVU
  have htest := h.test φ hφ hφs hφ_subU
  have hzeroLeftV :
      ∀ x, x ∉ V →
        vecDot (u.grad x) (euclideanGradient φ x) = 0 := by
    intro x hx
    have hx_notin : x ∉ tsupport φ := fun hx' => hx (hφ_sub hx')
    simp [euclideanGradient_eq_zero_of_notMem_tsupport hx_notin, vecDot_zero_right]
  have hzeroLeftU :
      ∀ x, x ∉ U →
        vecDot (u.grad x) (euclideanGradient φ x) = 0 := by
    intro x hx
    exact hzeroLeftV x (fun hxV => hx (hVU hxV))
  have hzeroRightV :
      ∀ x, x ∉ V → f x * φ x = 0 := by
    intro x hx
    have hx_notin : x ∉ tsupport φ := fun hx' => hx (hφ_sub hx')
    simp [image_eq_zero_of_notMem_tsupport hx_notin]
  have hzeroRightU :
      ∀ x, x ∉ U → f x * φ x = 0 := by
    intro x hx
    exact hzeroRightV x (fun hxV => hx (hVU hxV))
  have hleft :
      ∫ x in V, vecDot (u.grad x) (euclideanGradient φ x) ∂MeasureTheory.volume =
        ∫ x in U, vecDot (u.grad x) (euclideanGradient φ x) ∂MeasureTheory.volume := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzeroLeftV,
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzeroLeftU]
  have hright :
      ∫ x in V, f x * φ x ∂MeasureTheory.volume =
        ∫ x in U, f x * φ x ∂MeasureTheory.volume := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzeroRightV,
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzeroRightU]
  simpa [H1Function.restrict, hleft, hright] using htest

/-- Translate a weak Poisson equation. -/
theorem translate (h : WeakPoissonEquationOn U u f) (z : Vec d) :
    WeakPoissonEquationOn (translateSet z U) (u.translate z) (fun x => f (x - z)) := by
  intro φ hφ hφs hφ_sub
  let ψ : Vec d → ℝ := fun x => φ (x + z)
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    simpa [ψ] using! hφ.comp (contDiff_id.add contDiff_const)
  have hψ_supp : HasCompactSupport ψ := by
    show HasCompactSupport (φ ∘ Homeomorph.addRight z)
    simpa [ψ, Function.comp] using hφs.comp_homeomorph (Homeomorph.addRight z)
  have hψ_sub : tsupport ψ ⊆ U := by
    intro x hx
    have hx' : x + z ∈ tsupport φ := by
      rw [show ψ = φ ∘ Homeomorph.addRight z by rfl,
        tsupport_comp_eq_preimage φ (Homeomorph.addRight z)] at hx
      exact hx
    have hxV : x + z ∈ translateSet z U := hφ_sub hx'
    simpa [mem_translateSet_iff_sub_mem, sub_eq_add_neg, add_assoc] using hxV
  have htest := h.test ψ hψ_smooth hψ_supp hψ_sub
  have hgradψ :
      ∀ x, euclideanGradient ψ x = euclideanGradient φ (x + z) := by
    intro x
    ext i
    unfold euclideanGradient euclideanCoordDeriv
    have hderiv :
        fderiv ℝ (fun y : Vec d => φ (y + z)) x =
          fderiv ℝ φ (x + z) := by
      simpa using (fderiv_comp_add_right (𝕜 := ℝ) (f := φ) (x := x) z)
    simp [ψ, hderiv]
  have hleft_change :
      ∫ x in translateSet z U,
          vecDot ((u.translate z).grad x) (euclideanGradient φ x)
            ∂MeasureTheory.volume =
        ∫ x in U, vecDot (u.grad x) (euclideanGradient φ (x + z))
            ∂MeasureTheory.volume := by
    symm
    simpa [H1Function.translate, sub_eq_add_neg, add_assoc] using
      (setIntegral_comp_addRight_translateSet (d := d) (E := ℝ) z U
        (fun x => vecDot ((u.translate z).grad x) (euclideanGradient φ x)))
  have hright_change :
      ∫ x in translateSet z U, f (x - z) * φ x ∂MeasureTheory.volume =
        ∫ x in U, f x * φ (x + z) ∂MeasureTheory.volume := by
    symm
    simpa [sub_eq_add_neg, add_assoc] using
      (setIntegral_comp_addRight_translateSet (d := d) (E := ℝ) z U
        (fun x => f (x - z) * φ x))
  calc
    ∫ x in translateSet z U,
        vecDot ((u.translate z).grad x) (euclideanGradient φ x)
          ∂MeasureTheory.volume
        = ∫ x in U, vecDot (u.grad x) (euclideanGradient φ (x + z))
            ∂MeasureTheory.volume := hleft_change
    _ = ∫ x in U, vecDot (u.grad x) (euclideanGradient ψ x)
            ∂MeasureTheory.volume := by
          congr with x
          rw [hgradψ x]
    _ = ∫ x in U, f x * ψ x ∂MeasureTheory.volume := htest
    _ = ∫ x in U, f x * φ (x + z) ∂MeasureTheory.volume := by rfl
    _ = ∫ x in translateSet z U, f (x - z) * φ x ∂MeasureTheory.volume :=
          hright_change.symm

/-- Scale a weak Poisson equation by a real constant. -/
theorem smul (h : WeakPoissonEquationOn U u f) (c : ℝ) :
    WeakPoissonEquationOn U (c • u) (fun x => c * f x) := by
  intro φ hφ hφs hφ_sub
  have htest := h.test φ hφ hφs hφ_sub
  calc
    ∫ x in U, vecDot ((c • u).grad x) (euclideanGradient φ x)
        ∂MeasureTheory.volume
        = ∫ x in U, c * vecDot (u.grad x) (euclideanGradient φ x)
            ∂MeasureTheory.volume := by
          congr with x
          simp [H1Function.smul_grad, vecDot_smul_left]
    _ = c * ∫ x in U, vecDot (u.grad x) (euclideanGradient φ x)
            ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_const_mul]
    _ = c * ∫ x in U, f x * φ x ∂MeasureTheory.volume := by
          rw [htest]
    _ = ∫ x in U, c * (f x * φ x) ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_const_mul]
    _ = ∫ x in U, (c * f x) * φ x ∂MeasureTheory.volume := by
          congr with x
          ring

/-- Extend a weak Poisson equation from smooth compactly supported tests to
all `H¹₀` tests. This is the legal-testing bridge needed by the
difference-quotient interior estimate. -/
theorem h10 (h : WeakPoissonEquationOn U u f)
    (hU : IsOpen U) (hf : MemScalarL2 U f) :
    ∀ φ : H10Function U,
      ∫ x in U, vecDot (u.grad x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume =
        ∫ x in U, f x * φ.toH1Function x ∂MeasureTheory.volume :=
  h10WeakEquationOn_of_contDiff_tests hU u.grad_memVectorL2 hf
    (fun ψ hψ hψs hψ_sub => h.test ψ hψ hψs hψ_sub)

end WeakPoissonEquationOn

namespace MeanZeroNeumannPoissonSolution

variable {d : ℕ} {Q : TriadicCube d} {F : Vec d → ℝ}

/-- The original cube Neumann solution is a weak Poisson solution on the cube,
packaged in the `WeakPoissonEquationOn` interface used by the difference
quotient interior estimates. -/
theorem weakPoissonEquationOnCube
    (W : MeanZeroNeumannPoissonSolution Q F)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    WeakPoissonEquationOn (openCubeSet Q) W.w.toH1Function F := by
  intro φ hφ hφs _hφ_sub
  exact
    W.weakEquationOnCube_of_compactSupport_of_memLp_normalizedCubeMeasure
      hφ hφs hmean hF

/-- The all-coordinate even reflection of a cube Neumann solution is a weak
Poisson solution on the full reflection block.

This is the first bridge needed by the difference-quotient proof: the hard
future theorem should consume `WeakPoissonEquationOn`; the reflection stack
already proves the same identity in reflected-vector-field notation. -/
theorem cubeFaceReflectionBlockFold_weakPoissonEquationOn
    (W : MeanZeroNeumannPoissonSolution Q F)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    WeakPoissonEquationOn (cubeFaceReflectionBlockSet Q)
      W.w.toH1Function.cubeFaceReflectionBlockFold
      (cubeCoordinateFoldReflectedScalar Q F) := by
  intro φ hφ hφs _hφ_sub
  simpa [WeakPoissonEquationOn] using
    W.cubeFaceReflectionBlock_reflectedVectorField_weakEquationOnBlock_of_compactSupport_of_memLp_normalizedCubeMeasure
      hφ hφs hmean hF

end MeanZeroNeumannPoissonSolution

end

end Homogenization
