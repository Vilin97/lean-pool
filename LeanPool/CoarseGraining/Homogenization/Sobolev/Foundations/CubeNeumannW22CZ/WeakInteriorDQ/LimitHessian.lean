/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.QuotientHessianRiesz

/-! # Limit Hessian -/

@[expose] public section

namespace Homogenization

open scoped Manifold
open scoped ENNReal Topology

noncomputable section

namespace WeakPoissonEquationOn

variable {d : ℕ} {V : Set (Vec d)}

/-!
# Limiting Hessian functional

This file isolates the final compactness/limit handoff for the interior
difference-quotient proof.  The hypothesis is deliberately narrow: for a
small-step sequence, the already-built quotient Hessian pairings converge on
smooth tests to the desired pairing against `uQ.grad`.  From that hypothesis
and the uniform quotient estimate, we build the bounded limiting functional.
-/

/-- The concrete fixed-step quotient-Hessian pairing on a smooth open-inner
test. -/
def openCubeInnerOpenCubeQuotientHessianPairing
    {Q : TriadicCube d} (uQ : H1Function (openCubeSet Q))
    (V : Set (Vec d)) (step : ℝ) (i j : Fin d) {ρ₁ : ℝ}
    (φ : H1WeakTestFunction (scaledOpenCubeSet Q ρ₁)) : ℝ :=
  -∫ x in V,
    euclideanForwardDifferenceQuotient step i uQ.toFun x *
      (fderiv ℝ (φ : Vec d → ℝ) x) (basisVec j) ∂MeasureTheory.volume

/-- The limiting Hessian pairing on a smooth open-inner test. -/
def openCubeInnerOpenCubeLimitHessianPairing
    {Q : TriadicCube d} (uQ : H1Function (openCubeSet Q))
    (V : Set (Vec d)) (i j : Fin d) {ρ₁ : ℝ}
    (φ : H1WeakTestFunction (scaledOpenCubeSet Q ρ₁)) : ℝ :=
  -∫ x in V,
    uQ.grad x i *
      (fderiv ℝ (φ : Vec d → ℝ) x) (basisVec j) ∂MeasureTheory.volume

/-- Smooth-test convergence hypothesis for a fixed sequence of legal
difference-quotient steps. -/
def OpenCubeInnerHessianPairingTendsto
    {Q : TriadicCube d} (uQ : H1Function (openCubeSet Q))
    (V : Set (Vec d)) (stepSeq : ℕ → ℝ) (i j : Fin d) {ρ₁ : ℝ} : Prop :=
  ∀ φ : H1WeakTestFunction (scaledOpenCubeSet Q ρ₁),
    Filter.Tendsto
      (fun n : ℕ =>
        openCubeInnerOpenCubeQuotientHessianPairing uQ V (stepSeq n) i j φ)
      Filter.atTop
      (nhds (openCubeInnerOpenCubeLimitHessianPairing uQ V i j φ))

private theorem support_fderiv_apply_basisVec_subset_of_tsupport_subset
    {U : Set (Vec d)} {φ : Vec d → ℝ} (j : Fin d) (hφ_sub : tsupport φ ⊆ U) :
    Function.support (fun x => (fderiv ℝ φ x) (basisVec j)) ⊆ U := by
  intro x hx
  exact hφ_sub <|
    (support_fderiv_subset (𝕜 := ℝ) (f := φ)) <| by
      change fderiv ℝ φ x ≠ 0
      intro hzero
      apply hx
      simp [hzero]

private theorem support_mul_fderiv_apply_basisVec_subset_of_tsupport_subset
    {U : Set (Vec d)} {w φ : Vec d → ℝ} (j : Fin d) (hφ_sub : tsupport φ ⊆ U) :
    Function.support (fun x => w x * (fderiv ℝ φ x) (basisVec j)) ⊆ U := by
  intro x hx
  have hderiv_ne : (fderiv ℝ φ x) (basisVec j) ≠ 0 := by
    intro hzero
    apply hx
    simp [hzero]
  exact support_fderiv_apply_basisVec_subset_of_tsupport_subset j hφ_sub hderiv_ne

private theorem openCubeInnerOpenCubeLimitHessianPairing_eq_of_toScalarL2_eq
    {Q : TriadicCube d} {uQ : H1Function (openCubeSet Q)} {f : Vec d → ℝ}
    (h : WeakPoissonEquationOn (openCubeSet Q) uQ f)
    (hf : MemScalarL2 (openCubeSet Q) f)
    (hV : IsOpenBoundedConvexDomain V)
    (stepSeq : ℕ → ℝ) (hstep : ∀ n, stepSeq n ≠ 0) (i j : Fin d)
    {ρ₁ ρ₂ σ₁ σ₂ ν : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V)
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂)
    (hVν : V ⊆ scaledClosedCubeSet Q ν)
    (hν_nonneg : 0 ≤ ν)
    (hνσ : ν ≤ σ₁)
    (hσ₁_lt_one : σ₁ < 1)
    (hσ₂_nonneg : 0 ≤ σ₂)
    (hσ₂_lt_one : σ₂ < 1)
    (hstep_abs : ∀ n, |stepSeq n| ≤ (σ₁ - ν) * cubeRadius Q)
    (hlim : OpenCubeInnerHessianPairingTendsto
      (ρ₁ := ρ₁) uQ V stepSeq i j)
    (φ ψ : H1WeakTestFunction (scaledOpenCubeSet Q ρ₁))
    (hφψ : φ.toScalarL2 = ψ.toScalarL2) :
    openCubeInnerOpenCubeLimitHessianPairing uQ V i j φ =
      openCubeInnerOpenCubeLimitHessianPairing uQ V i j ψ := by
  have hseq :
      (fun n : ℕ =>
          openCubeInnerOpenCubeQuotientHessianPairing uQ V (stepSeq n) i j φ) =
        fun n : ℕ =>
          openCubeInnerOpenCubeQuotientHessianPairing uQ V (stepSeq n) i j ψ := by
    funext n
    exact
      h.neg_integral_forwardDifferenceQuotient_mul_fderiv_openCube_innerOpenCube_eq_of_h1WeakTest_toScalarL2_eq_of_step_abs_le
        hf hV (hstep n) i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
        hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one (hstep_abs n) φ ψ hφψ
  exact tendsto_nhds_unique (hlim φ) (by simpa [hseq] using hlim ψ)

private theorem openCubeInnerOpenCubeLimitHessianPairing_add
    {Q : TriadicCube d} {uQ : H1Function (openCubeSet Q)}
    (hV : IsOpenBoundedConvexDomain V)
    (stepSeq : ℕ → ℝ) (i j : Fin d)
    {ρ₁ σ₁ ν : ℝ}
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V)
    (hVν : V ⊆ scaledClosedCubeSet Q ν)
    (hν_nonneg : 0 ≤ ν)
    (hνσ : ν ≤ σ₁)
    (hσ₁_lt_one : σ₁ < 1)
    (hstep_abs : ∀ n, |stepSeq n| ≤ (σ₁ - ν) * cubeRadius Q)
    (hlim : OpenCubeInnerHessianPairingTendsto
      (ρ₁ := ρ₁) uQ V stepSeq i j)
    (φ ψ : H1WeakTestFunction (scaledOpenCubeSet Q ρ₁)) :
    openCubeInnerOpenCubeLimitHessianPairing uQ V i j (φ.add ψ) =
      openCubeInnerOpenCubeLimitHessianPairing uQ V i j φ +
        openCubeInnerOpenCubeLimitHessianPairing uQ V i j ψ := by
  have hVU : V ⊆ openCubeSet Q := by
    intro x hx
    exact
      scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one Q hν_nonneg
        (lt_of_le_of_lt hνσ hσ₁_lt_one) (hVν hx)
  have hVshift :
      ∀ n, V ⊆ translateSet ((-stepSeq n) • basisVec i) (openCubeSet Q) := by
    intro n x hx
    rw [mem_translateSet_iff_sub_mem]
    have hσ₁_nonneg : 0 ≤ σ₁ := hν_nonneg.trans hνσ
    have hxshift :
        euclideanCoordShift (stepSeq n) i x ∈ scaledClosedCubeSet Q σ₁ :=
      euclideanCoordShift_mem_scaledClosedCubeSet_of_mem_scaledClosedCubeSet
        Q hνσ (hstep_abs n) i (hVν hx)
    have hxopen : euclideanCoordShift (stepSeq n) i x ∈ openCubeSet Q :=
      scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one
        Q hσ₁_nonneg hσ₁_lt_one hxshift
    simpa [euclideanCoordShift, sub_eq_add_neg, neg_smul] using hxopen
  have hSV : scaledOpenCubeSet Q ρ₁ ⊆ V :=
    (scaledOpenCubeSet_subset_scaledClosedCubeSet Q ρ₁).trans hinnerV
  have hseq :
      (fun n : ℕ =>
          openCubeInnerOpenCubeQuotientHessianPairing uQ V (stepSeq n) i j
            (φ.add ψ)) =
        fun n : ℕ =>
          openCubeInnerOpenCubeQuotientHessianPairing uQ V (stepSeq n) i j φ +
            openCubeInnerOpenCubeQuotientHessianPairing uQ V (stepSeq n) i j ψ := by
    funext n
    simpa [openCubeInnerOpenCubeQuotientHessianPairing] using
      neg_integral_forwardDifferenceQuotient_mul_fderiv_h1WeakTest_add
        (U := openCubeSet Q) (V := V) uQ hV hVU
        (step := stepSeq n) i j (hVshift n)
        (S := scaledOpenCubeSet Q ρ₁) hSV φ ψ
  have hsum :
      Filter.Tendsto
        (fun n : ℕ =>
          openCubeInnerOpenCubeQuotientHessianPairing uQ V (stepSeq n) i j
            (φ.add ψ))
        Filter.atTop
        (nhds
          (openCubeInnerOpenCubeLimitHessianPairing uQ V i j φ +
            openCubeInnerOpenCubeLimitHessianPairing uQ V i j ψ)) := by
    simpa [hseq] using (hlim φ).add (hlim ψ)
  exact tendsto_nhds_unique (hlim (φ.add ψ)) hsum

private theorem openCubeInnerOpenCubeLimitHessianPairing_smul
    {Q : TriadicCube d} {uQ : H1Function (openCubeSet Q)}
    (hV : IsOpenBoundedConvexDomain V)
    (stepSeq : ℕ → ℝ) (i j : Fin d)
    {ρ₁ σ₁ ν : ℝ}
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V)
    (hVν : V ⊆ scaledClosedCubeSet Q ν)
    (hν_nonneg : 0 ≤ ν)
    (hνσ : ν ≤ σ₁)
    (hσ₁_lt_one : σ₁ < 1)
    (hstep_abs : ∀ n, |stepSeq n| ≤ (σ₁ - ν) * cubeRadius Q)
    (hlim : OpenCubeInnerHessianPairingTendsto
      (ρ₁ := ρ₁) uQ V stepSeq i j)
    (c : ℝ) (φ : H1WeakTestFunction (scaledOpenCubeSet Q ρ₁)) :
    openCubeInnerOpenCubeLimitHessianPairing uQ V i j (φ.smul c) =
      c * openCubeInnerOpenCubeLimitHessianPairing uQ V i j φ := by
  have hVU : V ⊆ openCubeSet Q := by
    intro x hx
    exact
      scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one Q hν_nonneg
        (lt_of_le_of_lt hνσ hσ₁_lt_one) (hVν hx)
  have hVshift :
      ∀ n, V ⊆ translateSet ((-stepSeq n) • basisVec i) (openCubeSet Q) := by
    intro n x hx
    rw [mem_translateSet_iff_sub_mem]
    have hσ₁_nonneg : 0 ≤ σ₁ := hν_nonneg.trans hνσ
    have hxshift :
        euclideanCoordShift (stepSeq n) i x ∈ scaledClosedCubeSet Q σ₁ :=
      euclideanCoordShift_mem_scaledClosedCubeSet_of_mem_scaledClosedCubeSet
        Q hνσ (hstep_abs n) i (hVν hx)
    have hxopen : euclideanCoordShift (stepSeq n) i x ∈ openCubeSet Q :=
      scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one
        Q hσ₁_nonneg hσ₁_lt_one hxshift
    simpa [euclideanCoordShift, sub_eq_add_neg, neg_smul] using hxopen
  have hSV : scaledOpenCubeSet Q ρ₁ ⊆ V :=
    (scaledOpenCubeSet_subset_scaledClosedCubeSet Q ρ₁).trans hinnerV
  have hseq :
      (fun n : ℕ =>
          openCubeInnerOpenCubeQuotientHessianPairing uQ V (stepSeq n) i j
            (φ.smul c)) =
        fun n : ℕ =>
          c * openCubeInnerOpenCubeQuotientHessianPairing uQ V (stepSeq n) i j φ := by
    funext n
    simpa [openCubeInnerOpenCubeQuotientHessianPairing] using
      neg_integral_forwardDifferenceQuotient_mul_fderiv_h1WeakTest_smul
        (U := openCubeSet Q) (V := V) uQ hV hVU
        (step := stepSeq n) i j (hVshift n)
        (S := scaledOpenCubeSet Q ρ₁) hSV c φ
  have hmul :
      Filter.Tendsto
        (fun n : ℕ =>
          openCubeInnerOpenCubeQuotientHessianPairing uQ V (stepSeq n) i j
            (φ.smul c))
        Filter.atTop
        (nhds (c * openCubeInnerOpenCubeLimitHessianPairing uQ V i j φ)) := by
    simpa [hseq] using tendsto_const_nhds.mul (hlim φ)
  exact tendsto_nhds_unique (hlim (φ.smul c)) hmul

/-- The limiting Hessian pairing as a linear functional on the dense
smooth-test scalar `L²` submodule. -/
noncomputable def openCubeInnerOpenCubeLimitHessianSmoothTestFunctional
    {Q : TriadicCube d} {uQ : H1Function (openCubeSet Q)} {f : Vec d → ℝ}
    (h : WeakPoissonEquationOn (openCubeSet Q) uQ f)
    (hf : MemScalarL2 (openCubeSet Q) f)
    (hV : IsOpenBoundedConvexDomain V)
    (stepSeq : ℕ → ℝ) (hstep : ∀ n, stepSeq n ≠ 0) (i j : Fin d)
    {ρ₁ ρ₂ σ₁ σ₂ ν : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V)
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂)
    (hVν : V ⊆ scaledClosedCubeSet Q ν)
    (hν_nonneg : 0 ≤ ν)
    (hνσ : ν ≤ σ₁)
    (hσ₁_lt_one : σ₁ < 1)
    (hσ₂_nonneg : 0 ≤ σ₂)
    (hσ₂_lt_one : σ₂ < 1)
    (hstep_abs : ∀ n, |stepSeq n| ≤ (σ₁ - ν) * cubeRadius Q)
    (hlim : OpenCubeInnerHessianPairingTendsto
      (ρ₁ := ρ₁) uQ V stepSeq i j) :
    h1WeakTestScalarL2Submodule (d := d) (scaledOpenCubeSet Q ρ₁) →ₗ[ℝ] ℝ := by
  let S : Set (Vec d) := scaledOpenCubeSet Q ρ₁
  let rep :
      h1WeakTestScalarL2Submodule (d := d) S → H1WeakTestFunction S :=
    h1WeakTestScalarL2Representative
  refine
    { toFun := fun x => openCubeInnerOpenCubeLimitHessianPairing uQ V i j (rep x)
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    have hrep_add_eq :
        openCubeInnerOpenCubeLimitHessianPairing uQ V i j (rep (x + y)) =
          openCubeInnerOpenCubeLimitHessianPairing uQ V i j ((rep x).add (rep y)) :=
      openCubeInnerOpenCubeLimitHessianPairing_eq_of_toScalarL2_eq
        h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
        hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim
        (rep (x + y)) ((rep x).add (rep y)) (by
          rw [h1WeakTestScalarL2Representative_toScalarL2,
            H1WeakTestFunction.toScalarL2_add,
            h1WeakTestScalarL2Representative_toScalarL2,
            h1WeakTestScalarL2Representative_toScalarL2]
          rfl)
    have hpair_add :
        openCubeInnerOpenCubeLimitHessianPairing uQ V i j ((rep x).add (rep y)) =
          openCubeInnerOpenCubeLimitHessianPairing uQ V i j (rep x) +
            openCubeInnerOpenCubeLimitHessianPairing uQ V i j (rep y) :=
      openCubeInnerOpenCubeLimitHessianPairing_add
        (ρ₁ := ρ₁) (σ₁ := σ₁) (ν := ν) hV stepSeq i j hinnerV
        hVν hν_nonneg hνσ hσ₁_lt_one hstep_abs hlim (rep x) (rep y)
    exact hrep_add_eq.trans hpair_add
  · intro c x
    have hrep_smul_eq :
        openCubeInnerOpenCubeLimitHessianPairing uQ V i j (rep (c • x)) =
          openCubeInnerOpenCubeLimitHessianPairing uQ V i j ((rep x).smul c) :=
      openCubeInnerOpenCubeLimitHessianPairing_eq_of_toScalarL2_eq
        h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
        hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim
        (rep (c • x)) ((rep x).smul c) (by
          rw [h1WeakTestScalarL2Representative_toScalarL2,
            H1WeakTestFunction.toScalarL2_smul,
            h1WeakTestScalarL2Representative_toScalarL2]
          rfl)
    have hpair_smul :
        openCubeInnerOpenCubeLimitHessianPairing uQ V i j ((rep x).smul c) =
          c * openCubeInnerOpenCubeLimitHessianPairing uQ V i j (rep x) :=
      openCubeInnerOpenCubeLimitHessianPairing_smul
        (ρ₁ := ρ₁) (σ₁ := σ₁) (ν := ν) hV stepSeq i j hinnerV
        hVν hν_nonneg hνσ hσ₁_lt_one hstep_abs hlim c (rep x)
    calc
      openCubeInnerOpenCubeLimitHessianPairing uQ V i j (rep (c • x)) =
          openCubeInnerOpenCubeLimitHessianPairing uQ V i j ((rep x).smul c) :=
        hrep_smul_eq
      _ = c * openCubeInnerOpenCubeLimitHessianPairing uQ V i j (rep x) :=
        hpair_smul
      _ = c • openCubeInnerOpenCubeLimitHessianPairing uQ V i j (rep x) := by
        rfl

/-- The limiting smooth-test functional inherits the uniform quotient-Hessian
bound. -/
theorem norm_openCubeInnerOpenCubeLimitHessianSmoothTestFunctional_apply_le
    {Q : TriadicCube d} {uQ : H1Function (openCubeSet Q)} {f : Vec d → ℝ}
    (h : WeakPoissonEquationOn (openCubeSet Q) uQ f)
    (hf : MemScalarL2 (openCubeSet Q) f)
    (hV : IsOpenBoundedConvexDomain V)
    (stepSeq : ℕ → ℝ) (hstep : ∀ n, stepSeq n ≠ 0) (i j : Fin d)
    {ρ₁ ρ₂ σ₁ σ₂ ν : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V)
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂)
    (hVν : V ⊆ scaledClosedCubeSet Q ν)
    (hν_nonneg : 0 ≤ ν)
    (hνσ : ν ≤ σ₁)
    (hσ₁_lt_one : σ₁ < 1)
    (hσ₂_nonneg : 0 ≤ σ₂)
    (hσ₂_lt_one : σ₂ < 1)
    (hstep_abs : ∀ n, |stepSeq n| ≤ (σ₁ - ν) * cubeRadius Q)
    (hlim : OpenCubeInnerHessianPairingTendsto
      (ρ₁ := ρ₁) uQ V stepSeq i j)
    (x : h1WeakTestScalarL2Submodule (d := d) (scaledOpenCubeSet Q ρ₁)) :
    ‖openCubeInnerOpenCubeLimitHessianSmoothTestFunctional
        h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
        hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim x‖ ≤
      openCubeInnerQuotientHessianSmoothTestBound (ρ₁ := ρ₁) (ρ₂ := ρ₂) uQ f i θ *
        ‖((h1WeakTestScalarL2Submodule (d := d) (scaledOpenCubeSet Q ρ₁)).subtype x)‖ := by
  let φ : H1WeakTestFunction (scaledOpenCubeSet Q ρ₁) :=
    h1WeakTestScalarL2Representative x
  let C : ℝ := openCubeInnerQuotientHessianSmoothTestBound
    (ρ₁ := ρ₁) (ρ₂ := ρ₂) uQ f i θ
  let N : ℝ :=
    ‖((h1WeakTestScalarL2Submodule (d := d) (scaledOpenCubeSet Q ρ₁)).subtype x)‖
  have hbound_seq :
      ∀ n : ℕ,
        |openCubeInnerOpenCubeQuotientHessianPairing uQ V (stepSeq n) i j φ| ≤
          C * N := by
    intro n
    have hbound :=
      norm_openCubeInnerOpenCubeQuotientHessianSmoothTestFunctional_apply_le
        h hf hV (hstep n) i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
        hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one (hstep_abs n) x
    simpa [openCubeInnerOpenCubeQuotientHessianSmoothTestFunctional,
      openCubeInnerOpenCubeQuotientHessianPairing, φ, C, N, Real.norm_eq_abs]
      using hbound
  have hlim_abs :
      Filter.Tendsto
        (fun n : ℕ =>
          |openCubeInnerOpenCubeQuotientHessianPairing uQ V (stepSeq n) i j φ|)
        Filter.atTop
        (nhds |openCubeInnerOpenCubeLimitHessianPairing uQ V i j φ|) :=
    (hlim φ).abs
  have habs :
      |openCubeInnerOpenCubeLimitHessianPairing uQ V i j φ| ≤ C * N :=
    le_of_tendsto hlim_abs (Filter.Eventually.of_forall hbound_seq)
  simpa [openCubeInnerOpenCubeLimitHessianSmoothTestFunctional, φ, C, N,
    Real.norm_eq_abs] using habs

/-- Continuous extension of the limiting Hessian functional to all scalar
`L²` fields on the open inner cube. -/
noncomputable def openCubeInnerOpenCubeLimitHessianFunctional
    {Q : TriadicCube d} {uQ : H1Function (openCubeSet Q)} {f : Vec d → ℝ}
    (h : WeakPoissonEquationOn (openCubeSet Q) uQ f)
    (hf : MemScalarL2 (openCubeSet Q) f)
    (hV : IsOpenBoundedConvexDomain V)
    (stepSeq : ℕ → ℝ) (hstep : ∀ n, stepSeq n ≠ 0) (i j : Fin d)
    {ρ₁ ρ₂ σ₁ σ₂ ν : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V)
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂)
    (hVν : V ⊆ scaledClosedCubeSet Q ν)
    (hν_nonneg : 0 ≤ ν)
    (hνσ : ν ≤ σ₁)
    (hσ₁_lt_one : σ₁ < 1)
    (hσ₂_nonneg : 0 ≤ σ₂)
    (hσ₂_lt_one : σ₂ < 1)
    (hstep_abs : ∀ n, |stepSeq n| ≤ (σ₁ - ν) * cubeRadius Q)
    (hlim : OpenCubeInnerHessianPairingTendsto
      (ρ₁ := ρ₁) uQ V stepSeq i j) :
    ScalarL2 (scaledOpenCubeSet Q ρ₁) →L[ℝ] ℝ :=
  extendH1WeakTestScalarL2Functional
    (d := d) (U := scaledOpenCubeSet Q ρ₁)
    (openCubeInnerOpenCubeLimitHessianSmoothTestFunctional
      h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
      hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim)

/-- The limiting continuous functional inherits the uniform quotient bound. -/
theorem norm_openCubeInnerOpenCubeLimitHessianFunctional_apply_le
    {Q : TriadicCube d} {uQ : H1Function (openCubeSet Q)} {f : Vec d → ℝ}
    (h : WeakPoissonEquationOn (openCubeSet Q) uQ f)
    (hf : MemScalarL2 (openCubeSet Q) f)
    (hV : IsOpenBoundedConvexDomain V)
    (stepSeq : ℕ → ℝ) (hstep : ∀ n, stepSeq n ≠ 0) (i j : Fin d)
    {ρ₁ ρ₂ σ₁ σ₂ ν : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V)
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂)
    (hVν : V ⊆ scaledClosedCubeSet Q ν)
    (hν_nonneg : 0 ≤ ν)
    (hνσ : ν ≤ σ₁)
    (hσ₁_lt_one : σ₁ < 1)
    (hσ₂_nonneg : 0 ≤ σ₂)
    (hσ₂_lt_one : σ₂ < 1)
    (hstep_abs : ∀ n, |stepSeq n| ≤ (σ₁ - ν) * cubeRadius Q)
    (hlim : OpenCubeInnerHessianPairingTendsto
      (ρ₁ := ρ₁) uQ V stepSeq i j)
    (hρ₁_nonneg : 0 ≤ ρ₁)
    (x : ScalarL2 (scaledOpenCubeSet Q ρ₁)) :
    ‖openCubeInnerOpenCubeLimitHessianFunctional
        h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
        hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim x‖ ≤
      openCubeInnerQuotientHessianSmoothTestBound (ρ₁ := ρ₁) (ρ₂ := ρ₂) uQ f i θ *
        ‖x‖ := by
  exact
    norm_extendH1WeakTestScalarL2Functional_apply_le
      (d := d) (U := scaledOpenCubeSet Q ρ₁)
      (isOpen_scaledOpenCubeSet Q ρ₁)
      (volume_scaledOpenCubeSet_ne_top_of_nonneg Q hρ₁_nonneg)
      (openCubeInnerQuotientHessianSmoothTestBound (ρ₁ := ρ₁) (ρ₂ := ρ₂) uQ f i θ)
      (openCubeInnerOpenCubeLimitHessianSmoothTestFunctional
        h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
        hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim)
      (norm_openCubeInnerOpenCubeLimitHessianSmoothTestFunctional_apply_le
        h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
        hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim)
      x

/-- Riesz representative of the limiting open-inner Hessian functional. -/
noncomputable def openCubeInnerOpenCubeLimitHessianRieszRep
    {Q : TriadicCube d} {uQ : H1Function (openCubeSet Q)} {f : Vec d → ℝ}
    (h : WeakPoissonEquationOn (openCubeSet Q) uQ f)
    (hf : MemScalarL2 (openCubeSet Q) f)
    (hV : IsOpenBoundedConvexDomain V)
    (stepSeq : ℕ → ℝ) (hstep : ∀ n, stepSeq n ≠ 0) (i j : Fin d)
    {ρ₁ ρ₂ σ₁ σ₂ ν : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V)
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂)
    (hVν : V ⊆ scaledClosedCubeSet Q ν)
    (hν_nonneg : 0 ≤ ν)
    (hνσ : ν ≤ σ₁)
    (hσ₁_lt_one : σ₁ < 1)
    (hσ₂_nonneg : 0 ≤ σ₂)
    (hσ₂_lt_one : σ₂ < 1)
    (hstep_abs : ∀ n, |stepSeq n| ≤ (σ₁ - ν) * cubeRadius Q)
    (hlim : OpenCubeInnerHessianPairingTendsto
      (ρ₁ := ρ₁) uQ V stepSeq i j) :
    ScalarL2 (scaledOpenCubeSet Q ρ₁) :=
  (InnerProductSpace.toDual ℝ (ScalarL2 (scaledOpenCubeSet Q ρ₁))).symm
    (openCubeInnerOpenCubeLimitHessianFunctional
      h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
      hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim)

/-- Riesz evaluation theorem for the limiting Hessian representative. -/
theorem inner_openCubeInnerOpenCubeLimitHessianRieszRep_eq_functional
    {Q : TriadicCube d} {uQ : H1Function (openCubeSet Q)} {f : Vec d → ℝ}
    (h : WeakPoissonEquationOn (openCubeSet Q) uQ f)
    (hf : MemScalarL2 (openCubeSet Q) f)
    (hV : IsOpenBoundedConvexDomain V)
    (stepSeq : ℕ → ℝ) (hstep : ∀ n, stepSeq n ≠ 0) (i j : Fin d)
    {ρ₁ ρ₂ σ₁ σ₂ ν : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V)
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂)
    (hVν : V ⊆ scaledClosedCubeSet Q ν)
    (hν_nonneg : 0 ≤ ν)
    (hνσ : ν ≤ σ₁)
    (hσ₁_lt_one : σ₁ < 1)
    (hσ₂_nonneg : 0 ≤ σ₂)
    (hσ₂_lt_one : σ₂ < 1)
    (hstep_abs : ∀ n, |stepSeq n| ≤ (σ₁ - ν) * cubeRadius Q)
    (hlim : OpenCubeInnerHessianPairingTendsto
      (ρ₁ := ρ₁) uQ V stepSeq i j)
    (x : ScalarL2 (scaledOpenCubeSet Q ρ₁)) :
    inner ℝ
        (openCubeInnerOpenCubeLimitHessianRieszRep
          h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
          hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim)
        x =
      openCubeInnerOpenCubeLimitHessianFunctional
        h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
        hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim x := by
  change inner ℝ
      (((InnerProductSpace.toDual ℝ (ScalarL2 (scaledOpenCubeSet Q ρ₁))).symm)
        (openCubeInnerOpenCubeLimitHessianFunctional
          h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
          hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim))
      x =
    openCubeInnerOpenCubeLimitHessianFunctional
      h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
      hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim x
  exact
    InnerProductSpace.toDual_symm_apply
      (𝕜 := ℝ)
      (E := ScalarL2 (scaledOpenCubeSet Q ρ₁))
      (x := x)
      (y :=
        (openCubeInnerOpenCubeLimitHessianFunctional
          h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
          hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim :
          StrongDual ℝ (ScalarL2 (scaledOpenCubeSet Q ρ₁))))

/-- The continuous limiting functional agrees with the concrete smooth-test
functional on the dense submodule. -/
theorem openCubeInnerOpenCubeLimitHessianFunctional_apply_subtype
    {Q : TriadicCube d} {uQ : H1Function (openCubeSet Q)} {f : Vec d → ℝ}
    (h : WeakPoissonEquationOn (openCubeSet Q) uQ f)
    (hf : MemScalarL2 (openCubeSet Q) f)
    (hV : IsOpenBoundedConvexDomain V)
    (stepSeq : ℕ → ℝ) (hstep : ∀ n, stepSeq n ≠ 0) (i j : Fin d)
    {ρ₁ ρ₂ σ₁ σ₂ ν : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V)
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂)
    (hVν : V ⊆ scaledClosedCubeSet Q ν)
    (hν_nonneg : 0 ≤ ν)
    (hνσ : ν ≤ σ₁)
    (hσ₁_lt_one : σ₁ < 1)
    (hσ₂_nonneg : 0 ≤ σ₂)
    (hσ₂_lt_one : σ₂ < 1)
    (hstep_abs : ∀ n, |stepSeq n| ≤ (σ₁ - ν) * cubeRadius Q)
    (hlim : OpenCubeInnerHessianPairingTendsto
      (ρ₁ := ρ₁) uQ V stepSeq i j)
    (hρ₁_nonneg : 0 ≤ ρ₁)
    (x : h1WeakTestScalarL2Submodule (d := d) (scaledOpenCubeSet Q ρ₁)) :
    openCubeInnerOpenCubeLimitHessianFunctional
        h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
        hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim
        ((h1WeakTestScalarL2Submodule (d := d) (scaledOpenCubeSet Q ρ₁)).subtype x) =
      openCubeInnerOpenCubeLimitHessianSmoothTestFunctional
        h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
        hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim x := by
  exact
    extendH1WeakTestScalarL2Functional_apply_subtype
      (d := d) (U := scaledOpenCubeSet Q ρ₁)
      (isOpen_scaledOpenCubeSet Q ρ₁)
      (volume_scaledOpenCubeSet_ne_top_of_nonneg Q hρ₁_nonneg)
      (openCubeInnerQuotientHessianSmoothTestBound (ρ₁ := ρ₁) (ρ₂ := ρ₂) uQ f i θ)
      (openCubeInnerOpenCubeLimitHessianSmoothTestFunctional
        h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
        hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim)
      (norm_openCubeInnerOpenCubeLimitHessianSmoothTestFunctional_apply_le
        h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
        hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim)
      x

/-- The limiting Riesz representative has the same explicit norm bound as the
fixed-step quotient representatives. -/
theorem norm_openCubeInnerOpenCubeLimitHessianRieszRep_le
    {Q : TriadicCube d} {uQ : H1Function (openCubeSet Q)} {f : Vec d → ℝ}
    (h : WeakPoissonEquationOn (openCubeSet Q) uQ f)
    (hf : MemScalarL2 (openCubeSet Q) f)
    (hV : IsOpenBoundedConvexDomain V)
    (stepSeq : ℕ → ℝ) (hstep : ∀ n, stepSeq n ≠ 0) (i j : Fin d)
    {ρ₁ ρ₂ σ₁ σ₂ ν : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V)
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂)
    (hVν : V ⊆ scaledClosedCubeSet Q ν)
    (hν_nonneg : 0 ≤ ν)
    (hνσ : ν ≤ σ₁)
    (hσ₁_lt_one : σ₁ < 1)
    (hσ₂_nonneg : 0 ≤ σ₂)
    (hσ₂_lt_one : σ₂ < 1)
    (hstep_abs : ∀ n, |stepSeq n| ≤ (σ₁ - ν) * cubeRadius Q)
    (hlim : OpenCubeInnerHessianPairingTendsto
      (ρ₁ := ρ₁) uQ V stepSeq i j)
    (hρ₁_nonneg : 0 ≤ ρ₁) :
    ‖openCubeInnerOpenCubeLimitHessianRieszRep
        h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
        hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim‖ ≤
      openCubeInnerQuotientHessianSmoothTestBound (ρ₁ := ρ₁) (ρ₂ := ρ₂) uQ f i θ := by
  let L : ScalarL2 (scaledOpenCubeSet Q ρ₁) →L[ℝ] ℝ :=
    openCubeInnerOpenCubeLimitHessianFunctional
      h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
      hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim
  let C : ℝ :=
    openCubeInnerQuotientHessianSmoothTestBound (ρ₁ := ρ₁) (ρ₂ := ρ₂) uQ f i θ
  have hL_bound : ∀ x, ‖L x‖ ≤ C * ‖x‖ := by
    intro x
    simpa [L, C] using
      norm_openCubeInnerOpenCubeLimitHessianFunctional_apply_le
        h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
        hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim hρ₁_nonneg x
  have hL_op : ‖L‖ ≤ C :=
    L.opNorm_le_bound
      (by
        simpa [C] using
          openCubeInnerQuotientHessianSmoothTestBound_nonneg
            (ρ₁ := ρ₁) (ρ₂ := ρ₂) uQ f i θ)
      hL_bound
  have hnorm_eq :
      ‖openCubeInnerOpenCubeLimitHessianRieszRep
        h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
        hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim‖ = ‖L‖ := by
    change
      ‖((InnerProductSpace.toDual ℝ (ScalarL2 (scaledOpenCubeSet Q ρ₁))).symm) L‖ = ‖L‖
    exact ((InnerProductSpace.toDual ℝ (ScalarL2 (scaledOpenCubeSet Q ρ₁))).symm.norm_map L)
  exact hnorm_eq.trans_le hL_op

/-- Under the smooth-test pairing convergence hypothesis, the limiting Riesz
representative is the weak `j`-derivative of the `i`th weak-gradient
coordinate on the open inner cube. -/
theorem openCubeInnerOpenCubeLimitHessianRieszRep_hasWeakPartialDerivOn_grad
    {Q : TriadicCube d} {uQ : H1Function (openCubeSet Q)} {f : Vec d → ℝ}
    (h : WeakPoissonEquationOn (openCubeSet Q) uQ f)
    (hf : MemScalarL2 (openCubeSet Q) f)
    (hV : IsOpenBoundedConvexDomain V)
    (stepSeq : ℕ → ℝ) (hstep : ∀ n, stepSeq n ≠ 0) (i j : Fin d)
    {ρ₁ ρ₂ σ₁ σ₂ ν : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V)
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂)
    (hVν : V ⊆ scaledClosedCubeSet Q ν)
    (hν_nonneg : 0 ≤ ν)
    (hνσ : ν ≤ σ₁)
    (hσ₁_lt_one : σ₁ < 1)
    (hσ₂_nonneg : 0 ≤ σ₂)
    (hσ₂_lt_one : σ₂ < 1)
    (hstep_abs : ∀ n, |stepSeq n| ≤ (σ₁ - ν) * cubeRadius Q)
    (hlim : OpenCubeInnerHessianPairingTendsto
      (ρ₁ := ρ₁) uQ V stepSeq i j)
    (hρ₁_nonneg : 0 ≤ ρ₁) :
    HasWeakPartialDerivOn (scaledOpenCubeSet Q ρ₁) j
      (fun x => uQ.grad x i)
      (fun x =>
        openCubeInnerOpenCubeLimitHessianRieszRep
          h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
          hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim x) := by
  intro φ hφ hφs hφ_sub
  let S : Set (Vec d) := scaledOpenCubeSet Q ρ₁
  let φTest : H1WeakTestFunction S :=
    { toFun := φ
      smooth := hφ
      compactSupport := hφs
      support_subset := by simpa [S] using hφ_sub }
  let xsub : h1WeakTestScalarL2Submodule (d := d) S :=
    ⟨φTest.toScalarL2, by exact ⟨φTest, rfl⟩⟩
  let rep : ScalarL2 S :=
    openCubeInnerOpenCubeLimitHessianRieszRep
      h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
      hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim
  have hinner_functional :
      inner ℝ rep φTest.toScalarL2 =
        openCubeInnerOpenCubeLimitHessianFunctional
          h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
          hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim φTest.toScalarL2 := by
    simpa [rep, S] using
      inner_openCubeInnerOpenCubeLimitHessianRieszRep_eq_functional
        h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
        hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim φTest.toScalarL2
  have hfunctional_smooth :
      openCubeInnerOpenCubeLimitHessianFunctional
          h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
          hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim φTest.toScalarL2 =
        openCubeInnerOpenCubeLimitHessianSmoothTestFunctional
          h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
          hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim xsub := by
    simpa [xsub, S, Submodule.subtype] using
      openCubeInnerOpenCubeLimitHessianFunctional_apply_subtype
        h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
        hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim hρ₁_nonneg xsub
  have hsmooth_pairing :
      openCubeInnerOpenCubeLimitHessianSmoothTestFunctional
          h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
          hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim xsub =
        -∫ y in V,
          uQ.grad y i *
            (fderiv ℝ φ y) (basisVec j) ∂MeasureTheory.volume := by
    let ψ : H1WeakTestFunction S := h1WeakTestScalarL2Representative xsub
    have hψ_eq : ψ.toScalarL2 = φTest.toScalarL2 := by
      simpa [ψ, xsub, S, Submodule.subtype] using
        h1WeakTestScalarL2Representative_toScalarL2 xsub
    have hpair :=
      openCubeInnerOpenCubeLimitHessianPairing_eq_of_toScalarL2_eq
        h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
        hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim ψ φTest hψ_eq
    change
      openCubeInnerOpenCubeLimitHessianPairing uQ V i j ψ =
        -∫ y in V,
          uQ.grad y i *
            (fderiv ℝ φ y) (basisVec j) ∂MeasureTheory.volume
    simpa [openCubeInnerOpenCubeLimitHessianPairing, φTest] using hpair
  have hinner_integral :
      inner ℝ rep φTest.toScalarL2 =
        ∫ x in S, rep x * φ x ∂MeasureTheory.volume := by
    rw [scalarInner_eq_integral]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [φTest.coeFn_toScalarL2] with x hφ_l2
    rw [hφ_l2]
  have hrep_integral :
      ∫ x in S, rep x * φ x ∂MeasureTheory.volume =
        -∫ y in V,
          uQ.grad y i *
            (fderiv ℝ φ y) (basisVec j) ∂MeasureTheory.volume :=
    hinner_integral.symm.trans
      (hinner_functional.trans (hfunctional_smooth.trans hsmooth_pairing))
  have hSV : S ⊆ V := by
    simpa [S] using
      (scaledOpenCubeSet_subset_scaledClosedCubeSet Q ρ₁).trans hinnerV
  have hderiv_support :
      Function.support
        (fun x =>
          uQ.grad x i *
            (fderiv ℝ φ x) (basisVec j)) ⊆ S :=
    support_mul_fderiv_apply_basisVec_subset_of_tsupport_subset j (by simpa [S] using hφ_sub)
  have hV_eq_S :
      ∫ y in V,
          uQ.grad y i *
            (fderiv ℝ φ y) (basisVec j) ∂MeasureTheory.volume =
        ∫ y in S,
          uQ.grad y i *
            (fderiv ℝ φ y) (basisVec j) ∂MeasureTheory.volume :=
    integral_subset_of_support_subset (U := V) (V := S) hSV hderiv_support
  have hV_pair :
      ∫ y in V,
          uQ.grad y i *
            (fderiv ℝ φ y) (basisVec j) ∂MeasureTheory.volume =
        -∫ x in S, rep x * φ x ∂MeasureTheory.volume := by
    rw [hrep_integral, neg_neg]
  calc
    ∫ y in scaledOpenCubeSet Q ρ₁,
        (fun x => uQ.grad x i) y *
          (fderiv ℝ φ y) (basisVec j) ∂MeasureTheory.volume =
        ∫ y in S,
          uQ.grad y i *
            (fderiv ℝ φ y) (basisVec j) ∂MeasureTheory.volume := by
          rfl
    _ = ∫ y in V,
          uQ.grad y i *
            (fderiv ℝ φ y) (basisVec j) ∂MeasureTheory.volume := hV_eq_S.symm
    _ = -∫ x in S, rep x * φ x ∂MeasureTheory.volume := hV_pair
    _ = -∫ x in scaledOpenCubeSet Q ρ₁,
        (fun y =>
          openCubeInnerOpenCubeLimitHessianRieszRep
            h hf hV stepSeq hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ
            hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hstep_abs hlim y) x *
          φ x ∂MeasureTheory.volume := by
          rfl

end WeakPoissonEquationOn

end

end Homogenization
