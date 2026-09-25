/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.HilbertMinimization
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.Topology.Instances.Matrix

/-! # Hilbert Minimization Measurability -/

@[expose] public section

namespace Homogenization

noncomputable section

open ContinuousLinearMap
open Filter
open MeasureTheory
open TopologicalSpace
open scoped Topology

/-!
# Measurability primitives for Hilbert minimizers

This file contains generic measurable-operator facts needed to prove
measurable dependence of the Hilbert minimizer maps used in the doubled `Mu`
problem.  These are upstream primitives, not Chapter 5 wrappers.
-/

section Inverse

variable {Ω E F : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Inversion of continuous linear maps is continuous on the subtype of
invertible maps. -/
theorem continuous_clm_inverse_isInvertible :
    Continuous fun T : {T : E →L[ℝ] F // T.IsInvertible} =>
      ContinuousLinearMap.inverse T.1 := by
  rw [continuous_iff_continuousAt]
  intro T
  exact
    (T.2.contDiffAt_map_inverse (𝕜 := ℝ) (n := 0)).continuousAt.comp
      continuous_subtype_val.continuousAt

/-- A measurable family of invertible continuous linear maps has a measurable
family of inverses. -/
theorem _root_.Measurable.clm_inverse_of_isInvertible
    {L : Ω → E →L[ℝ] F} (hL : Measurable L)
    (hInv : ∀ ω, (L ω).IsInvertible) :
    Measurable fun ω => ContinuousLinearMap.inverse (L ω) := by
  let Lsub : Ω → {T : E →L[ℝ] F // T.IsInvertible} := fun ω => ⟨L ω, hInv ω⟩
  have hLsub : Measurable Lsub := hL.subtype_mk
  exact continuous_clm_inverse_isInvertible.measurable.comp hLsub

end Inverse

section Apply

variable {Ω E F : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [MeasurableSpace F] [BorelSpace F]

/-- Joint measurability of applying a measurable family of continuous linear
maps to a measurable family of vectors. -/
theorem _root_.Measurable.clm_apply {L : Ω → E →L[ℝ] F} {x : Ω → E}
    [OpensMeasurableSpace ((E →L[ℝ] F) × E)]
    (hL : Measurable L) (hx : Measurable x) :
    Measurable fun ω => L ω (x ω) := by
  have hEval : Measurable fun p : (E →L[ℝ] F) × E => p.1 p.2 :=
    (Continuous.clm_apply continuous_fst continuous_snd).measurable
  exact hEval.comp (hL.prodMk hx)

end Apply

section Matrix

/-- Entries of the total matrix inverse are measurable functions of the matrix
entries.  This is a finite-dimensional primitive used by Galerkin
approximations; invertibility is not needed for measurability because Lean's
matrix inverse is total. -/
theorem measurable_matrix_inv_entry {d : ℕ} {α : Type*} [MeasurableSpace α]
    {A : α → Fin d → Fin d → ℝ} (hA : Measurable A) (i j : Fin d) :
    Measurable fun x =>
      (((A x : Matrix (Fin d) (Fin d) ℝ)⁻¹ : Matrix (Fin d) (Fin d) ℝ) i j) := by
  have hdetMap : Measurable fun M : Fin d → Fin d → ℝ => Matrix.det M := by
    let f : (Fin d → Fin d → ℝ) → ℝ := fun M => Matrix.det M
    have hf : Continuous f := by
      simpa [f] using! (continuous_id.matrix_det : Continuous f)
    exact hf.measurable
  have hdet : Measurable fun x => Matrix.det (A x) := hdetMap.comp hA
  have hadjMap : Measurable fun M : Fin d → Fin d → ℝ => Matrix.adjugate M i j := by
    let g : (Fin d → Fin d → ℝ) → ℝ := fun M => Matrix.adjugate M i j
    have hg : Continuous g := by
      simpa [g] using! (((continuous_id.matrix_adjugate).matrix_elem i j) : Continuous g)
    exact hg.measurable
  have hadj : Measurable fun x => Matrix.adjugate (A x) i j := hadjMap.comp hA
  have hEq : ∀ x, (((A x : Matrix (Fin d) (Fin d) ℝ)⁻¹ : Matrix (Fin d) (Fin d) ℝ) i j)
      = (Matrix.det (A x))⁻¹ * Matrix.adjugate (A x) i j := fun x => by
    have := congrFun (congrFun (Matrix.inv_def (A x : Matrix (Fin d) (Fin d) ℝ)) i) j
    simpa [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv'] using this
  simp only [hEq]
  exact hdet.inv.mul hadj

end Matrix

section Galerkin

variable {Ω V : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {n : ℕ}

/-- The finite Galerkin Gram matrix for the bilinear form `B` on a selected
finite family of correction vectors. -/
noncomputable def galerkinMatrix (B : V →L[ℝ] V →L[ℝ] ℝ) (e : Fin n → V) :
    Fin n → Fin n → ℝ :=
  fun i j => B (e j) (e i)

/-- The finite Galerkin right-hand side for the affine shift `x`. -/
noncomputable def galerkinRhs (B : V →L[ℝ] V →L[ℝ] ℝ) (x : V) (e : Fin n → V) :
    Fin n → ℝ :=
  fun i => -B x (e i)

/-- The coordinate vector obtained from the total inverse of the finite
Galerkin Gram matrix.  Coercivity later identifies this total inverse with the
honest finite-dimensional inverse. -/
noncomputable def galerkinCoeff (B : V →L[ℝ] V →L[ℝ] ℝ) (x : V) (e : Fin n → V) :
    Fin n → ℝ :=
  fun j => ∑ i : Fin n,
    (((galerkinMatrix B e : Matrix (Fin n) (Fin n) ℝ)⁻¹ :
      Matrix (Fin n) (Fin n) ℝ) j i) *
    galerkinRhs B x e i

/-- The finite Galerkin correction vector assembled from its measurable
coordinate vector. -/
noncomputable def galerkinCorrection (B : V →L[ℝ] V →L[ℝ] ℝ) (x : V)
    (e : Fin n → V) : V :=
  ∑ j : Fin n, galerkinCoeff B x e j • e j

/-- The finite Galerkin affine minimizer. -/
noncomputable def galerkinAffineMinimizer (B : V →L[ℝ] V →L[ℝ] ℝ) (x : V)
    (e : Fin n → V) : V :=
  x + galerkinCorrection B x e

/-- Measurability of the finite Galerkin Gram matrix from scalar probe
measurability of the bilinear form. -/
theorem measurable_galerkinMatrix
    {B : Ω → V →L[ℝ] V →L[ℝ] ℝ} {e : Fin n → V}
    (hB : ∀ i j, Measurable fun ω => B ω (e j) (e i)) :
    Measurable fun ω => galerkinMatrix (B ω) e := by
  refine measurable_pi_iff.2 ?_
  intro i
  refine measurable_pi_iff.2 ?_
  intro j
  simpa [galerkinMatrix] using hB i j

/-- Measurability of the finite Galerkin right-hand side from scalar probe
measurability. -/
theorem measurable_galerkinRhs
    {B : Ω → V →L[ℝ] V →L[ℝ] ℝ} {x : Ω → V} {e : Fin n → V}
    (hBx : ∀ i, Measurable fun ω => B ω (x ω) (e i)) :
    Measurable fun ω => galerkinRhs (B ω) (x ω) e := by
  refine measurable_pi_iff.2 ?_
  intro i
  have hEq : ∀ ω, galerkinRhs (B ω) (x ω) e i = -(B ω (x ω) (e i)) :=
    fun ω => neg_apply (B ω (x ω)) (e i)
  simp only [hEq]
  exact (hBx i).neg

/-- Measurability of the finite Galerkin coefficient vector. -/
theorem measurable_galerkinCoeff
    {B : Ω → V →L[ℝ] V →L[ℝ] ℝ} {x : Ω → V} {e : Fin n → V}
    (hB : ∀ i j, Measurable fun ω => B ω (e j) (e i))
    (hBx : ∀ i, Measurable fun ω => B ω (x ω) (e i)) :
    Measurable fun ω => galerkinCoeff (B ω) (x ω) e := by
  classical
  have hMat : Measurable fun ω => galerkinMatrix (B ω) e :=
    measurable_galerkinMatrix hB
  have hRhs : Measurable fun ω => galerkinRhs (B ω) (x ω) e :=
    measurable_galerkinRhs hBx
  refine measurable_pi_iff.2 ?_
  intro j
  refine Finset.measurable_sum Finset.univ ?_
  intro i _hi
  have hInvEntry :
      Measurable fun ω =>
        (((galerkinMatrix (B ω) e : Matrix (Fin n) (Fin n) ℝ)⁻¹ :
          Matrix (Fin n) (Fin n) ℝ) j i) :=
    measurable_matrix_inv_entry hMat j i
  have hRhsEntry : Measurable fun ω => galerkinRhs (B ω) (x ω) e i :=
    measurable_pi_iff.1 hRhs i
  simpa [galerkinCoeff] using! hInvEntry.mul hRhsEntry

/-- Measurability of each finite Galerkin correction. -/
theorem measurable_galerkinCorrection
    [MeasurableSpace V] [MeasurableAdd₂ V] [MeasurableSMul ℝ V]
    {B : Ω → V →L[ℝ] V →L[ℝ] ℝ} {x : Ω → V} {e : Fin n → V}
    (hB : ∀ i j, Measurable fun ω => B ω (e j) (e i))
    (hBx : ∀ i, Measurable fun ω => B ω (x ω) (e i)) :
    Measurable fun ω => galerkinCorrection (B ω) (x ω) e := by
  classical
  have hCoeff : Measurable fun ω => galerkinCoeff (B ω) (x ω) e :=
    measurable_galerkinCoeff hB hBx
  unfold galerkinCorrection
  refine Finset.measurable_sum Finset.univ ?_
  intro j _hj
  have hj : Measurable fun ω => galerkinCoeff (B ω) (x ω) e j :=
    measurable_pi_iff.1 hCoeff j
  exact hj.smul_const (e j)

/-- Measurability of each finite Galerkin affine minimizer. -/
theorem measurable_galerkinAffineMinimizer
    [MeasurableSpace V] [MeasurableAdd₂ V] [MeasurableSMul ℝ V]
    {B : Ω → V →L[ℝ] V →L[ℝ] ℝ} {x : Ω → V} {e : Fin n → V}
    (hx : Measurable x)
    (hB : ∀ i j, Measurable fun ω => B ω (e j) (e i))
    (hBx : ∀ i, Measurable fun ω => B ω (x ω) (e i)) :
    Measurable fun ω => galerkinAffineMinimizer (B ω) (x ω) e := by
  have hCorr : Measurable fun ω => galerkinCorrection (B ω) (x ω) e :=
    measurable_galerkinCorrection hB hBx
  simpa [galerkinAffineMinimizer] using! hx.add hCorr

/-- Strong measurability of each finite Galerkin affine minimizer from scalar
Gram/RHS probe measurability.  Unlike `measurable_galerkinAffineMinimizer`,
this theorem does not require a second-countable target space; it assembles the
finite-dimensional correction from strongly measurable real coordinates. -/
theorem stronglyMeasurable_galerkinAffineMinimizer_of_scalar_probes
    [MeasurableSpace V]
    {B : Ω → V →L[ℝ] V →L[ℝ] ℝ} {x : Ω → V} {e : Fin n → V}
    (hx : StronglyMeasurable x)
    (hB : ∀ i j, Measurable fun ω => B ω (e j) (e i))
    (hBx : ∀ i, Measurable fun ω => B ω (x ω) (e i)) :
    StronglyMeasurable fun ω => galerkinAffineMinimizer (B ω) (x ω) e := by
  classical
  have hCoeff : Measurable fun ω => galerkinCoeff (B ω) (x ω) e :=
    measurable_galerkinCoeff hB hBx
  have hCorr : StronglyMeasurable fun ω => galerkinCorrection (B ω) (x ω) e := by
    unfold galerkinCorrection
    have hsum : StronglyMeasurable
        (∑ j : Fin n, fun ω => galerkinCoeff (B ω) (x ω) e j • e j) := by
      refine Finset.stronglyMeasurable_sum Finset.univ ?_
      intro j _hj
      have hj : Measurable fun ω => galerkinCoeff (B ω) (x ω) e j :=
        measurable_pi_iff.1 hCoeff j
      exact hj.stronglyMeasurable.smul_const (e j)
    convert hsum using 1
    ext ω
    simp [Finset.sum_apply]
  simpa [galerkinAffineMinimizer] using! hx.add hCorr

/-- A pointwise limit of finite Galerkin affine minimizers is strongly
measurable.  This is the generic measurability bridge for selected Hilbert
solutions once convergence of the Galerkin scheme has been proved. -/
theorem stronglyMeasurable_of_tendsto_galerkinAffineMinimizer
    [MeasurableSpace V] [SecondCountableTopology V] [OpensMeasurableSpace V]
    [MeasurableAdd₂ V] [MeasurableSMul ℝ V]
    {B : Ω → V →L[ℝ] V →L[ℝ] ℝ} {x : Ω → V}
    {e : (m : ℕ) → Fin m → V} {u : Ω → V}
    (hx : Measurable x)
    (hB : ∀ m, ∀ i j : Fin m, Measurable fun ω => B ω (e m j) (e m i))
    (hBx : ∀ m, ∀ i : Fin m, Measurable fun ω => B ω (x ω) (e m i))
    (hlim :
      Tendsto
        (fun m : ℕ => fun ω => galerkinAffineMinimizer (B ω) (x ω) (e m))
        atTop (𝓝 u)) :
    StronglyMeasurable u := by
  refine stronglyMeasurable_of_tendsto atTop ?_ hlim
  intro m
  exact (measurable_galerkinAffineMinimizer hx (hB m) (hBx m)).stronglyMeasurable

/-- A pointwise limit of finite Galerkin affine minimizers is strongly
measurable, using the finite-dimensional strong-measurability theorem and
therefore avoiding any second-countability assumption on the Hilbert target. -/
theorem stronglyMeasurable_of_tendsto_galerkinAffineMinimizer_of_scalar_probes
    [MeasurableSpace V]
    {B : Ω → V →L[ℝ] V →L[ℝ] ℝ} {x : Ω → V}
    {e : (m : ℕ) → Fin m → V} {u : Ω → V}
    (hx : StronglyMeasurable x)
    (hB : ∀ m, ∀ i j : Fin m, Measurable fun ω => B ω (e m j) (e m i))
    (hBx : ∀ m, ∀ i : Fin m, Measurable fun ω => B ω (x ω) (e m i))
    (hlim :
      Tendsto
        (fun m : ℕ => fun ω => galerkinAffineMinimizer (B ω) (x ω) (e m))
        atTop (𝓝 u)) :
    StronglyMeasurable u := by
  refine stronglyMeasurable_of_tendsto atTop ?_ hlim
  intro m
  exact stronglyMeasurable_galerkinAffineMinimizer_of_scalar_probes
    hx (hB m) (hBx m)

/-- An a.e. pointwise limit of finite Galerkin affine minimizers is
a.e.-strongly measurable. -/
theorem aestronglyMeasurable_of_tendsto_ae_galerkinAffineMinimizer
    [MeasurableSpace V] [SecondCountableTopology V] [OpensMeasurableSpace V]
    [MeasurableAdd₂ V] [MeasurableSMul ℝ V]
    {μ : Measure Ω} {B : Ω → V →L[ℝ] V →L[ℝ] ℝ} {x : Ω → V}
    {e : (m : ℕ) → Fin m → V} {u : Ω → V}
    (hx : Measurable x)
    (hB : ∀ m, ∀ i j : Fin m, Measurable fun ω => B ω (e m j) (e m i))
    (hBx : ∀ m, ∀ i : Fin m, Measurable fun ω => B ω (x ω) (e m i))
    (hlim :
      ∀ᵐ ω ∂μ,
        Tendsto (fun m : ℕ => galerkinAffineMinimizer (B ω) (x ω) (e m))
          atTop (𝓝 (u ω))) :
    AEStronglyMeasurable u μ := by
  refine aestronglyMeasurable_of_tendsto_ae atTop ?_ hlim
  intro m
  exact (measurable_galerkinAffineMinimizer hx (hB m) (hBx m)).stronglyMeasurable.aestronglyMeasurable

end Galerkin

section HilbertGalerkinLimit

variable {Ω V : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The selected affine Hilbert minimizer is strongly measurable once finite
Galerkin minimizers satisfy the deterministic energy-comparison convergence
hypotheses.  This is the generic "finite Galerkin convergence implies
measurable maximizer/minimizer" bridge. -/
theorem stronglyMeasurable_of_galerkin_energy_approximants
    [MeasurableSpace V] (K : ClosedSubmodule ℝ V)
    {B : Ω → V →L[ℝ] V →L[ℝ] ℝ} {hB : ∀ ω, IsCoercive (B ω)}
    (h_symm : ∀ ω, ∀ u v : V, B ω u v = B ω v u)
    {x : Ω → V} {e : (m : ℕ) → Fin m → V} {v : Ω → ℕ → V}
    (hx : StronglyMeasurable x)
    (hB_meas : ∀ m, ∀ i j : Fin m, Measurable fun ω => B ω (e m j) (e m i))
    (hBx_meas : ∀ m, ∀ i : Fin m, Measurable fun ω => B ω (x ω) (e m i))
    (hGalerkin_mem :
      ∀ ω m, galerkinAffineMinimizer (B ω) (x ω) (e m) - x ω ∈ K)
    (hv_mem : ∀ ω m, v ω m - x ω ∈ K)
    (hEnergy :
      ∀ ω m,
        quadraticEnergy (B ω) (galerkinAffineMinimizer (B ω) (x ω) (e m)) ≤
          quadraticEnergy (B ω) (v ω m))
    (hv_tendsto :
      ∀ ω,
        Tendsto (fun m : ℕ => v ω m) atTop
          (𝓝 (affineMinimizerMap K (B ω) (hB ω) (x ω)))) :
    StronglyMeasurable fun ω => affineMinimizerMap K (B ω) (hB ω) (x ω) := by
  have hlim :
      Tendsto
        (fun m : ℕ => fun ω =>
          galerkinAffineMinimizer (B ω) (x ω) (e m))
        atTop
        (𝓝 fun ω => affineMinimizerMap K (B ω) (hB ω) (x ω)) := by
    rw [tendsto_pi_nhds]
    intro ω
    exact tendsto_galerkin_of_quadraticEnergy_le_approximants
      K (hB ω) (h_symm ω) (x ω)
      (fun m => hGalerkin_mem ω m)
      (fun m => hv_mem ω m)
      (fun m => hEnergy ω m)
      (hv_tendsto ω)
  exact stronglyMeasurable_of_tendsto_galerkinAffineMinimizer_of_scalar_probes
    hx hB_meas hBx_meas hlim

/-- A.e.-strong measurability version of
`stronglyMeasurable_of_galerkin_energy_approximants`. -/
theorem aestronglyMeasurable_of_galerkin_energy_approximants
    [MeasurableSpace V] {μ : Measure Ω} (K : ClosedSubmodule ℝ V)
    {B : Ω → V →L[ℝ] V →L[ℝ] ℝ} {hB : ∀ ω, IsCoercive (B ω)}
    (h_symm : ∀ ω, ∀ u v : V, B ω u v = B ω v u)
    {x : Ω → V} {e : (m : ℕ) → Fin m → V} {v : Ω → ℕ → V}
    (hx : StronglyMeasurable x)
    (hB_meas : ∀ m, ∀ i j : Fin m, Measurable fun ω => B ω (e m j) (e m i))
    (hBx_meas : ∀ m, ∀ i : Fin m, Measurable fun ω => B ω (x ω) (e m i))
    (hGalerkin_mem :
      ∀ ω m, galerkinAffineMinimizer (B ω) (x ω) (e m) - x ω ∈ K)
    (hv_mem : ∀ ω m, v ω m - x ω ∈ K)
    (hEnergy :
      ∀ ω m,
        quadraticEnergy (B ω) (galerkinAffineMinimizer (B ω) (x ω) (e m)) ≤
          quadraticEnergy (B ω) (v ω m))
    (hv_tendsto :
      ∀ ω,
        Tendsto (fun m : ℕ => v ω m) atTop
          (𝓝 (affineMinimizerMap K (B ω) (hB ω) (x ω)))) :
    AEStronglyMeasurable (fun ω => affineMinimizerMap K (B ω) (hB ω) (x ω)) μ :=
  (stronglyMeasurable_of_galerkin_energy_approximants
    K h_symm hx hB_meas hBx_meas hGalerkin_mem hv_mem hEnergy
    hv_tendsto).aestronglyMeasurable

end HilbertGalerkinLimit

section CorrectionMap

variable {Ω V : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The Hilbert correction map is the inverse of the Lax-Milgram operator on
the restricted correction subspace, applied to the affine right-hand side. -/
theorem correctionMap_eq_clm_inverse_restrictBilin
    (K : ClosedSubmodule ℝ V) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (x : V) :
    correctionMap K B hB x =
      ContinuousLinearMap.inverse
        (InnerProductSpace.continuousLinearMapOfBilin (restrictBilin K B))
        (subspaceRhs K B x) := by
  rw [correctionMap]
  rw [← ContinuousLinearMap.inverse_equiv
    ((isCoercive_restrictBilin K hB).continuousLinearEquivOfBilin)]
  rfl

/-- Measurability of the Hilbert correction map follows from measurability of
the restricted Lax-Milgram operator and the affine right-hand side. -/
theorem _root_.Measurable.correctionMap_apply
    [MeasurableSpace V]
    (K : ClosedSubmodule ℝ V)
    [BorelSpace K.toSubmodule]
    [OpensMeasurableSpace ((K.toSubmodule →L[ℝ] K.toSubmodule) × K.toSubmodule)]
    {B : Ω → V →L[ℝ] V →L[ℝ] ℝ} {hB : ∀ ω, IsCoercive (B ω)}
    {x : Ω → V}
    (hSharp :
      Measurable fun ω =>
        InnerProductSpace.continuousLinearMapOfBilin (restrictBilin K (B ω)))
    (hRhs : Measurable fun ω => subspaceRhs K (B ω) (x ω)) :
    Measurable fun ω => correctionMap K (B ω) (hB ω) (x ω) := by
  have hInv :
      ∀ ω,
        (InnerProductSpace.continuousLinearMapOfBilin (restrictBilin K (B ω))).IsInvertible := by
    intro ω
    exact ⟨(isCoercive_restrictBilin K (hB ω)).continuousLinearEquivOfBilin, rfl⟩
  have hInverse :
      Measurable fun ω =>
        ContinuousLinearMap.inverse
          (InnerProductSpace.continuousLinearMapOfBilin (restrictBilin K (B ω))) :=
    hSharp.clm_inverse_of_isInvertible hInv
  have hApply :
      Measurable fun ω =>
        ContinuousLinearMap.inverse
          (InnerProductSpace.continuousLinearMapOfBilin (restrictBilin K (B ω)))
          (subspaceRhs K (B ω) (x ω)) :=
    hInverse.clm_apply hRhs
  simpa [correctionMap_eq_clm_inverse_restrictBilin] using hApply

/-- Measurability of the affine Hilbert minimizer follows from measurability
of the affine shift, the restricted Lax-Milgram operator, and the affine
right-hand side. -/
theorem _root_.Measurable.affineMinimizerMap_apply
    [MeasurableSpace V] [BorelSpace V] [MeasurableAdd₂ V]
    (K : ClosedSubmodule ℝ V)
    [BorelSpace K.toSubmodule]
    [OpensMeasurableSpace ((K.toSubmodule →L[ℝ] K.toSubmodule) × K.toSubmodule)]
    {B : Ω → V →L[ℝ] V →L[ℝ] ℝ} {hB : ∀ ω, IsCoercive (B ω)}
    {x : Ω → V} (hx : Measurable x)
    (hSharp :
      Measurable fun ω =>
        InnerProductSpace.continuousLinearMapOfBilin (restrictBilin K (B ω)))
    (hRhs : Measurable fun ω => subspaceRhs K (B ω) (x ω)) :
    Measurable fun ω => affineMinimizerMap K (B ω) (hB ω) (x ω) := by
  have hCorr : Measurable fun ω => correctionMap K (B ω) (hB ω) (x ω) :=
    Measurable.correctionMap_apply K hSharp hRhs
  have hCorrV : Measurable fun ω => (correctionMap K (B ω) (hB ω) (x ω) : V) :=
    measurable_subtype_coe.comp hCorr
  simpa [affineMinimizerMap] using! hx.add hCorrV

/-- Measurability of the parameterized affine Hilbert minimizer. -/
theorem _root_.Measurable.parameterAffineMinimizerMap_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace V] [BorelSpace V] [MeasurableAdd₂ V]
    (K : ClosedSubmodule ℝ V)
    [BorelSpace K.toSubmodule]
    [OpensMeasurableSpace ((K.toSubmodule →L[ℝ] K.toSubmodule) × K.toSubmodule)]
    {B : Ω → V →L[ℝ] V →L[ℝ] ℝ} {hB : ∀ ω, IsCoercive (B ω)}
    (ι : E →L[ℝ] V) {p : Ω → E} (hp : Measurable p)
    (hSharp :
      Measurable fun ω =>
        InnerProductSpace.continuousLinearMapOfBilin (restrictBilin K (B ω)))
    (hRhs : Measurable fun ω => subspaceRhs K (B ω) (ι (p ω))) :
    Measurable fun ω => parameterAffineMinimizerMap K (B ω) (hB ω) ι (p ω) := by
  have hx : Measurable fun ω => ι (p ω) :=
    ι.measurable_comp hp
  simpa [parameterAffineMinimizerMap] using
    (Measurable.affineMinimizerMap_apply K hx hSharp hRhs)

end CorrectionMap

end

end Homogenization
