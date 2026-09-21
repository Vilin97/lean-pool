/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.BonnetMyers.Connection

/-!
# The actual curvature/Ricci bridge

The comparison theorem consumes the curvature of the connection selected by the
metric.  This file only packages the audited curvature tensor into the
continuous-linear-map shape used by the public statement and proves the local
commutator computation.  No diameter or compactness fact is hidden here.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal Topology

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

private noncomputable def curvMiddle
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (x : M) (u : TM x) :
    TM x →L[ℝ] TM x →L[ℝ] TM x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => LinearMap.toContinuousLinearMap
        (CovariantDerivative.curvatureTensor (cov := cov) x u v)
      map_add' := by
        intro v v'
        ext z
        simp only [LinearMap.coe_toContinuousLinearMap']
        exact congrArg (fun L : TM x →ₗ[ℝ] TM x => L z)
          ((CovariantDerivative.curvatureTensor (cov := cov) x u).map_add v v')
      map_smul' := by
        intro c v
        ext z
        simp only [LinearMap.coe_toContinuousLinearMap']
        exact congrArg (fun L : TM x →ₗ[ℝ] TM x => L z)
          ((CovariantDerivative.curvatureTensor (cov := cov) x u).map_smul c v) }

private noncomputable def curvOuter
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (x : M) :
    TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => curvMiddle (cov := cov) x u
      map_add' := by
        intro u u'
        ext v z
        simp only [curvMiddle, LinearMap.coe_toContinuousLinearMap']
        exact congrArg (fun L : TM x →ₗ[ℝ] TM x →ₗ[ℝ] TM x => L v z)
          ((CovariantDerivative.curvatureTensor (cov := cov) x).map_add u u')
      map_smul' := by
        intro c u
        ext v z
        simp only [curvMiddle, LinearMap.coe_toContinuousLinearMap']
        exact congrArg (fun L : TM x →ₗ[ℝ] TM x →ₗ[ℝ] TM x => L v z)
          ((CovariantDerivative.curvatureTensor (cov := cov) x).map_smul c u) }

/-- The actual curvature tensor, in the nested continuous-linear-map shape of
the independent statement. -/
noncomputable def curvature
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (x : M) :
    TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x :=
  curvOuter (cov := cov) x

@[simp] theorem curvature_apply
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (x : M) (u v z : TM x) :
    curvature (cov := cov) x u v z =
      CovariantDerivative.curvatureTensor (cov := cov) x u v z := by
  simp [curvature, curvOuter, curvMiddle]

theorem curvature_self
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (x : M) (a : TM x) :
    curvature (cov := cov) x a a a = 0 := by
  rw [curvature_apply]
  exact CovariantDerivative.curvatureTensor_self (cov := cov) x a a

/-- Compute curvature from representatives with exactly the regularity used
by the raw commutator: `C¹` in the tangent slots and `C²` in the section
slot. -/
theorem curvature_apply_contMDiff
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (X Y Z : Π x : M, TM x)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y ↦ TotalSpace.mk' E y (Z y))) (x : M) :
    curvature (cov := cov) x (X x) (Y x) (Z x) =
      cov (fun y => cov Z y (Y y)) x (X x) -
        cov (fun y => cov Z y (X y)) x (Y x) -
        cov Z x (VectorField.mlieBracket I X Y x) := by
  let e := trivializationAt E TM x
  let φ : SmoothBumpFunction I x :=
    CovariantDerivative.smoothExtendBump (I := I) (F := E) (V := TM) x
  let τ : Π y : M, TM y :=
    CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x (Z x)
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  let σs : Fin (Module.finrank ℝ E) → Π y : M, TM y := fun i ↦
    CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x
      (e.localFrame b i x)
  let f : Fin (Module.finrank ℝ E) → M → ℝ := fun i y ↦
    (φ : M → ℝ) y * e.localFrameCoeff I b i y (Z y)
  let g : Fin (Module.finrank ℝ E) → M → ℝ := fun i y ↦
    (φ : M → ℝ) y * e.localFrameCoeff I b i y (τ y)
  have hφsupp : tsupport (φ : M → ℝ) ⊆ e.baseSet := by
    simpa [φ, e] using
      (CovariantDerivative.tsupport_smoothExtendBump_subset
        (I := I) (F := E) (V := TM) x)
  have hf : ∀ i : Fin (Module.finrank ℝ E), ContMDiff I 𝓘(ℝ) 2 (f i) := by
    intro i
    apply contMDiff_of_tsupport
    intro y hy
    have hyφ : y ∈ tsupport (φ : M → ℝ) :=
      (tsupport_smul_subset_left (φ : M → ℝ)
        (fun z ↦ e.localFrameCoeff I b i z (Z z))) hy
    have hybase : y ∈ e.baseSet := hφsupp hyφ
    have hcoeff : ContMDiffAt I 𝓘(ℝ) 2
        (fun z ↦ e.localFrameCoeff I b i z (Z z)) y := by
      have hz := contMDiffAt_localFrameCoeff (I := I) b hybase hZ.contMDiffAt i
      simpa only [LinearMap.piApply_apply] using hz
    convert ((φ.contMDiffAt.of_le (by exact ENat.LEInfty.out)).smul hcoeff) using 1
    ext z
    simp [f, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  have hτ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y ↦ TotalSpace.mk' E y (τ y)) := by
    simpa [τ] using CovariantDerivative.smoothExtend_contMDiff_two
      (I := I) (F := E) (V := TM) x (Z x)
  have hg : ∀ i : Fin (Module.finrank ℝ E), ContMDiff I 𝓘(ℝ) 2 (g i) := by
    intro i
    apply contMDiff_of_tsupport
    intro y hy
    have hyφ : y ∈ tsupport (φ : M → ℝ) :=
      (tsupport_smul_subset_left (φ : M → ℝ)
        (fun z ↦ e.localFrameCoeff I b i z (τ z))) hy
    have hybase : y ∈ e.baseSet := hφsupp hyφ
    have hτ' : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun z ↦ TotalSpace.mk' E z (τ z)) := hτ
    have hcoeff : ContMDiffAt I 𝓘(ℝ) 2
        (fun z ↦ e.localFrameCoeff I b i z (τ z)) y := by
      have hz := contMDiffAt_localFrameCoeff (I := I) b hybase hτ'.contMDiffAt i
      simpa only [LinearMap.piApply_apply] using hz
    convert ((φ.contMDiffAt.of_le (by exact ENat.LEInfty.out)).smul hcoeff) using 1
    ext z
    simp [g, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  have hσs : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (σs i y)) := by
    intro i
    simpa [σs, e] using CovariantDerivative.smoothExtend_contMDiff_two
      (I := I) (F := E) (V := TM) x (e.localFrame b i x)
  have hσsum : ∀ᶠ y in nhds x, Z y = ∑ i, f i y • σs i y := by
    have hsum := CovariantDerivative.eventually_eq_sum_smoothExtend_trivializationAt_localFrameCoeff_smul
      (I := I) (F := E) (V := TM) b Z x
    filter_upwards [φ.eventuallyEq_one, hsum] with y hyφ hy
    calc
      Z y = ∑ i, e.localFrameCoeff I b i y (Z y) • σs i y := by
        simpa [σs, e] using hy
      _ = ∑ i, f i y • σs i y := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [f, hyφ]
  have hτsum : ∀ᶠ y in nhds x, τ y = ∑ i, g i y • σs i y := by
    have hsum := CovariantDerivative.eventually_eq_sum_smoothExtend_trivializationAt_localFrameCoeff_smul
      (I := I) (F := E) (V := TM) b τ x
    filter_upwards [φ.eventuallyEq_one, hsum] with y hyφ hy
    calc
      τ y = ∑ i, e.localFrameCoeff I b i y (τ y) • σs i y := by
        simpa [σs, e] using hy
      _ = ∑ i, g i y • σs i y := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [g, hyφ]
  have hfg : ∀ i, f i x = g i x := by
    intro i
    have hτx : τ x = Z x := by
      simpa [τ] using
        (CovariantDerivative.smoothExtend_apply
          (I := I) (F := E) (V := TM) x (Z x))
    simp only [f, g, Pi.smul_apply, smul_eq_mul]
    rw [hτx]
  have hcomp := (CovariantDerivative.curvatureAux_eq_of_finite_sum_eq_right_apply
    (cov := cov) (X := X) (Y := Y) (σ := Z) (τ := τ)
    (f := f) (g := g) (σs := σs) (x := x)
    hX hY hZ hτ hf hg hσs hσsum hτsum hfg)
  have htensor :=
    CovariantDerivative.curvatureAux_eq_curvatureTensor_apply_of_eq_left_middle_eventuallyEq_right
      (cov := cov) (X := X) (Y := Y) (σ := τ) (x := x)
      hX hY hτ rfl rfl (by filter_upwards [] with y; rfl)
  rw [curvature_apply]
  exact htensor.symm.trans hcomp.symm

theorem curvature_apply_smooth
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (X Y Z : Π x : M, TM x)
    (hX : ContMDiff I I.tangent ∞ (T% X))
    (hY : ContMDiff I I.tangent ∞ (T% Y))
    (hZ : ContMDiff I I.tangent ∞ (T% Z)) (x : M) :
    curvature (cov := cov) x (X x) (Y x) (Z x) =
      cov (fun y => cov Z y (Y y)) x (X x) -
        cov (fun y => cov Z y (X y)) x (Y x) -
        cov Z x (VectorField.mlieBracket I X Y x) := by
  apply curvature_apply_contMDiff cov X Y Z
  · simpa only [ModelWithCorners.tangent] using
      hX.of_le (by simp : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  · simpa only [ModelWithCorners.tangent] using
      hY.of_le (by simp : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  · simpa only [ModelWithCorners.tangent] using
      hZ.of_le (by exact ENat.LEInfty.out)

/-- For the local connection, the Ricci contraction in the target is the
curvature-library contraction.  This is an identity of scalar traces, not an
extra Ricci hypothesis. -/
theorem ricci_trace_eq
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    [RiemannianBundle TM] (x : M) (a : TM x) :
    LinearMap.trace ℝ (TM x)
        { toFun := fun z => curvature (cov := cov) x z a a
          map_add' := by intro z z'; simp
          map_smul' := by intro c z; simp } =
      CovariantDerivative.ricciCurvature (cov := cov) x a a := by
  rw [CovariantDerivative.ricciCurvature_apply]
  congr 1

end BonnetMyersEntry
