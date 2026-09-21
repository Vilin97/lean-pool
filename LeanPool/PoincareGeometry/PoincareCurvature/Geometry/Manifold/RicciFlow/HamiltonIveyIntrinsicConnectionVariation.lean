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

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyMetricMixedRegularity
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.MetricInverseVariation
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyIntrinsicVariation
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurckCorrectionRegularity

/-!
# Intrinsic Ricci-flow connection variation from joint metric regularity

The slicewise `IsRicciFlowOn` predicate supplies the actual metric velocity, but
it does not by itself commute a time derivative with a spatial derivative.  The
generic Koszul variation API therefore exposes those commutations explicitly.
This file specializes that API to Ricci flow and proves the specialization
without retaining three opaque `HasDerivAt` premises: joint spacetime
regularity of the actual metric pairings supplies them through the mixed
derivative theorem, and the velocity is identified with the genuine intrinsic
Ricci tensor by the Ricci-flow equation.

The result is deliberately a fixed-field theorem.  The stronger moving-section
rule needed to differentiate the nested curvature commutator is a separate
layer; this file closes the scalar-to-vector Levi--Civita variation step that
feeds that layer.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative.TimeDependentRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]
  [CompactSpace M] [Nonempty M]

local notation "TM" => (TangentSpace I : M → Type _)
/-- The cyclic connection-variation formula for an actual Ricci flow.

The conclusion is the genuine derivative of the chosen Levi--Civita family on
fixed smooth fields.  The three time/space commutations are derived from the
joint spacetime metric pairings and the spatial regularity of the corresponding
intrinsic Ricci pairings.  No connection-variation tensor and no curvature
evolution equation is assumed here.
-/
theorem exists_hasDerivAt_along_const_with_cyclic_metricVariation_of_intrinsicRicciFlow
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s)
    {X Y : Π y : M, TM y} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hjointXYZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (Y p.2) (Z p.2)))
    (hRicciSpaceXYZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      MDiffAt
        (fun y ↦ RicciFlow.intrinsicRicciBilinearAt
          (I := I) (M := M) g t y (Y y) (Z y)) x)
    (hjointYXZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (X p.2) (Z p.2)))
    (hRicciSpaceYXZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      MDiffAt
        (fun y ↦ RicciFlow.intrinsicRicciBilinearAt
          (I := I) (M := M) g t y (X y) (Z y)) x)
    (hjointZXY : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (X p.2) (Y p.2)))
    (hRicciSpaceZXY : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      MDiffAt
        (fun y ↦ RicciFlow.intrinsicRicciBilinearAt
          (I := I) (M := M) g t y (X y) (Y y)) x) :
    ∃ Axy : TM x,
      HasDerivAt (fun τ : ℝ => (cov τ).along X Y x) Axy t ∧
      ∀ (Z : Π y : M, TM y),
        ContMDiff I (I.prod 𝓘(ℝ, E)) 2
          (fun y ↦ TotalSpace.mk' E y (Z y)) →
        2 * (g t).inner x Axy (Z x) =
          -2 * (metricVelocityCovariantDerivativeAlong
            (I := I) (M := M) cov
            (RicciFlow.intrinsicRicciBilinearAt (I := I) (M := M) g t)
            t X Y Z x +
          metricVelocityCovariantDerivativeAlong
            (I := I) (M := M) cov
            (RicciFlow.intrinsicRicciBilinearAt (I := I) (M := M) g t)
            t Y X Z x -
          metricVelocityCovariantDerivativeAlong
            (I := I) (M := M) cov
            (RicciFlow.intrinsicRicciBilinearAt (I := I) (M := M) g t)
            t Z X Y x) := by
  let ricci : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ :=
    RicciFlow.intrinsicRicciBilinearAt (I := I) (M := M) g t
  let hdot : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ :=
    fun y => (-2 : ℝ) • ricci y
  have hRicciTensor : RicciFlow.intrinsicRicciTensor (I := I) (M := M) g =
      RicciFlow.ricciTensor (I := I) (M := M) g cov hcov :=
    RicciFlow.intrinsicRicciTensor_eq_ricciTensor_of_isLeviCivita
      (I := I) (M := M) g hcov hLevi
  have hricciEq (y : M) (u v : TM y) :
      ricci y u v = g.ricciCurvature cov hcov t y u v := by
    have hpoint := congrArg (fun q => q t y u v) hRicciTensor
    simpa [ricci, RicciFlow.intrinsicRicciBilinearAt_apply,
      RicciFlow.ricciTensor] using hpoint
  have hmetric : ∀ (y : M) (u v : TM y),
      HasDerivAt (fun τ : ℝ => (g τ).inner y u v) (hdot y u v) t := by
    intro y u v
    have hmetric₀ := hflow.2.1 ht y u v
    have hmetricEq := hflow.2.2 ht y u v
    change HasDerivAt (fun τ : ℝ => (g τ).inner y u v) (gdot t y u v) t at hmetric₀
    rw [hmetricEq] at hmetric₀
    have hmetricRicci : HasDerivAt (fun τ : ℝ => (g τ).inner y u v)
        ((-2 : ℝ) * g.ricciCurvature cov hcov t y u v) t := by
      simpa [RicciFlow.ricciFlowRHS, RicciFlow.ricciTensor] using hmetric₀
    simpa [hdot, ricci, hricciEq y u v, smul_eq_mul] using hmetricRicci
  have hdotSpaceXYZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      MDiffAt (fun y ↦ hdot y (Y y) (Z y)) x := by
    intro Z hZ
    have h := (mdifferentiableAt_const : MDiffAt (fun _ : M => (-2 : ℝ)) x).smul
      (hRicciSpaceXYZ Z hZ)
    convert h using 1 <;> simp [hdot, ricci, smul_eq_mul] <;> funext y <;>
      simp [Pi.mul_apply] <;> ring
  have hdotSpaceYXZ : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      MDiffAt (fun y ↦ hdot y (X y) (Z y)) x := by
    intro Z hZ
    have h := (mdifferentiableAt_const : MDiffAt (fun _ : M => (-2 : ℝ)) x).smul
      (hRicciSpaceYXZ Z hZ)
    convert h using 1 <;> simp [hdot, ricci, smul_eq_mul] <;> funext y <;>
      simp [Pi.mul_apply] <;> ring
  have hdotSpaceZXY : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      MDiffAt (fun y ↦ hdot y (X y) (Y y)) x := by
    intro Z hZ
    have h := (mdifferentiableAt_const : MDiffAt (fun _ : M => (-2 : ℝ)) x).smul
      (hRicciSpaceZXY Z hZ)
    convert h using 1 <;> simp [hdot, ricci, smul_eq_mul] <;> funext y <;>
      simp [Pi.mul_apply] <;> ring
  have hgeneric :=
    exists_hasDerivAt_along_const_with_cyclic_metricVariation_of_jointMetricPairingRegularity
      (I := I) (M := M) g cov hcov hLevi hdot (t := t) hmetric
      (X := X) (Y := Y) (x := x)
      (hX.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))
      (hY.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))
      (fun Z hZ => hjointXYZ Z hZ) hdotSpaceXYZ
      (fun Z hZ => hjointYXZ Z hZ) hdotSpaceYXZ
      (fun Z hZ => hjointZXY Z hZ) hdotSpaceZXY
  rcases hgeneric with ⟨Axy, hAxy, hcyclic⟩
  refine ⟨Axy, hAxy, ?_⟩
  intro Z hZ
  have hZ₁ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% Z) :=
    hZ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have h := hcyclic Z hZ
  have hscaleXYZ := metricVelocityCovariantDerivativeAlong_smul
    (I := I) (M := M) cov ricci (-2 : ℝ) t X Y Z x (hRicciSpaceXYZ Z hZ₁)
  have hscaleYXZ := metricVelocityCovariantDerivativeAlong_smul
    (I := I) (M := M) cov ricci (-2 : ℝ) t Y X Z x (hRicciSpaceYXZ Z hZ₁)
  have hscaleZXY := metricVelocityCovariantDerivativeAlong_smul
    (I := I) (M := M) cov ricci (-2 : ℝ) t Z X Y x (hRicciSpaceZXY Z hZ₁)
  rw [hscaleXYZ, hscaleYXZ, hscaleZXY] at h
  have h' :
      2 * (g t).inner x Axy (Z x) =
        (-2 : ℝ) * metricVelocityCovariantDerivativeAlong
            (I := I) (M := M) cov ricci t X Y Z x +
          (-2 : ℝ) * metricVelocityCovariantDerivativeAlong
            (I := I) (M := M) cov ricci t Y X Z x -
          (-2 : ℝ) * metricVelocityCovariantDerivativeAlong
            (I := I) (M := M) cov ricci t Z X Y x := by
    simpa [hdot, ricci] using h
  calc
    2 * (g t).inner x Axy (Z x) =
        (-2 : ℝ) * metricVelocityCovariantDerivativeAlong
            (I := I) (M := M) cov ricci t X Y Z x +
          (-2 : ℝ) * metricVelocityCovariantDerivativeAlong
            (I := I) (M := M) cov ricci t Y X Z x -
          (-2 : ℝ) * metricVelocityCovariantDerivativeAlong
            (I := I) (M := M) cov ricci t Z X Y x := h'
    _ = -2 * (metricVelocityCovariantDerivativeAlong
          (I := I) (M := M) cov ricci t X Y Z x +
        metricVelocityCovariantDerivativeAlong
          (I := I) (M := M) cov ricci t Y X Z x -
        metricVelocityCovariantDerivativeAlong
          (I := I) (M := M) cov ricci t Z X Y x) := by ring

/-! The preceding fixed-field bridge can be used directly at the older
intrinsic-variation interface.  This wrapper removes the three raw mixed
`HasDerivAt` premises from that interface: they are obtained from the actual
joint metric pairings and the spatial regularity of the intrinsic Ricci
pairings.  The connection-variation hypothesis remains explicit because the
moving-section curvature commutator needs the stronger time-dependent rule. -/
theorem metricVelocityCovariantDerivative_connectionVariation_formula_intrinsicRicci_of_jointMetricPairingRegularity
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s)
    (A : ∀ x : M, TM x → TM x → TM x)
    (hvariation : TimeDependentCovariantDerivative.HasConnectionTimeVariationAt
      (I := I) (M := M) cov A t)
    {X Y Z : Π x : M, TM x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Y y)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Z y)))
    (hjointXYZ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
      (fun p : ℝ × M => (g p.1).inner p.2 (Y p.2) (Z p.2)))
    (hRicciYZ : MDiffAt
      (fun y ↦ RicciFlow.intrinsicRicciBilinearAt
        (I := I) (M := M) g t y (Y y) (Z y)) x)
    (hjointYXZ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
      (fun p : ℝ × M => (g p.1).inner p.2 (X p.2) (Z p.2)))
    (hRicciXZ : MDiffAt
      (fun y ↦ RicciFlow.intrinsicRicciBilinearAt
        (I := I) (M := M) g t y (X y) (Z y)) x)
    (hjointZXY : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
      (fun p : ℝ × M => (g p.1).inner p.2 (X p.2) (Y p.2)))
    (hRicciXY : MDiffAt
      (fun y ↦ RicciFlow.intrinsicRicciBilinearAt
        (I := I) (M := M) g t y (X y) (Y y)) x) :
    2 * (g t).inner x (A x (X x) (Y x)) (Z x) =
      -2 * (metricVelocityCovariantDerivativeAlong
          (I := I) (M := M) cov
          (RicciFlow.intrinsicRicciBilinearAt (I := I) (M := M) g t)
          t X Y Z x +
        metricVelocityCovariantDerivativeAlong
          (I := I) (M := M) cov
          (RicciFlow.intrinsicRicciBilinearAt (I := I) (M := M) g t)
          t Y X Z x -
        metricVelocityCovariantDerivativeAlong
          (I := I) (M := M) cov
          (RicciFlow.intrinsicRicciBilinearAt (I := I) (M := M) g t)
          t Z X Y x) := by
  let ricci : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ :=
    RicciFlow.intrinsicRicciBilinearAt (I := I) (M := M) g t
  let hdot : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ :=
    fun y => (-2 : ℝ) • ricci y
  have hRicciTensor : RicciFlow.intrinsicRicciTensor (I := I) (M := M) g =
      RicciFlow.ricciTensor (I := I) (M := M) g cov hcov :=
    RicciFlow.intrinsicRicciTensor_eq_ricciTensor_of_isLeviCivita
      (I := I) (M := M) g hcov hLevi
  have hricciEq (y : M) (u v : TM y) :
      ricci y u v = g.ricciCurvature cov hcov t y u v := by
    have hpoint := congrArg (fun q => q t y u v) hRicciTensor
    simpa [ricci, RicciFlow.intrinsicRicciBilinearAt_apply,
      RicciFlow.ricciTensor] using hpoint
  have hmetric : ∀ (y : M) (u v : TM y),
      HasDerivAt (fun τ : ℝ => (g τ).inner y u v) (hdot y u v) t := by
    intro y u v
    have hmetric₀ := hflow.2.1 ht y u v
    have hmetricEq := hflow.2.2 ht y u v
    change HasDerivAt (fun τ : ℝ => (g τ).inner y u v) (gdot t y u v) t at hmetric₀
    rw [hmetricEq] at hmetric₀
    have hmetricRicci : HasDerivAt (fun τ : ℝ => (g τ).inner y u v)
        ((-2 : ℝ) * g.ricciCurvature cov hcov t y u v) t := by
      simpa [RicciFlow.ricciFlowRHS, RicciFlow.ricciTensor] using hmetric₀
    simpa [hdot, ricci, hricciEq y u v, smul_eq_mul] using hmetricRicci
  have hmixedXYZ : HasDerivAt
      (fun τ : ℝ =>
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (Y y) (Z y)) x (X x))
      (mvfderiv (I := I)
        (fun y ↦ ((-2 : ℝ) • RicciFlow.intrinsicRicciBilinearAt
           (I := I) (M := M) g t y) (Y y) (Z y)) x (X x)) t := by
    have hdotYZ : MDiffAt (fun y ↦ hdot y (Y y) (Z y)) x := by
      have h := (mdifferentiableAt_const : MDiffAt (fun _ : M => (-2 : ℝ)) x).smul
        hRicciYZ
      convert h using 1 <;> simp [hdot, ricci, smul_eq_mul] <;> funext y <;>
        simp [Pi.mul_apply] <;> ring
    have h := hasDerivAt_metricPairing_mvfderiv_of_jointContMDiff
      (I := I) (M := M) g hdot (t := t) hmetric
      (X := X) (Y := Y) (Z := Z) x hjointXYZ hdotYZ
    simpa [hdot, ricci] using h
  have hmixedYXZ : HasDerivAt
      (fun τ : ℝ =>
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (X y) (Z y)) x (Y x))
      (mvfderiv (I := I)
        (fun y ↦ ((-2 : ℝ) • RicciFlow.intrinsicRicciBilinearAt
           (I := I) (M := M) g t y) (X y) (Z y)) x (Y x)) t := by
    have hdotXZ : MDiffAt (fun y ↦ hdot y (X y) (Z y)) x := by
      have h := (mdifferentiableAt_const : MDiffAt (fun _ : M => (-2 : ℝ)) x).smul
        hRicciXZ
      convert h using 1 <;> simp [hdot, ricci, smul_eq_mul] <;> funext y <;>
        simp [Pi.mul_apply] <;> ring
    have h := hasDerivAt_metricPairing_mvfderiv_of_jointContMDiff
      (I := I) (M := M) g hdot (t := t) hmetric
      (X := Y) (Y := X) (Z := Z) x hjointYXZ hdotXZ
    simpa [hdot, ricci] using h
  have hmixedZXY : HasDerivAt
      (fun τ : ℝ =>
        mvfderiv (I := I) (fun y ↦ (g τ).inner y (X y) (Y y)) x (Z x))
      (mvfderiv (I := I)
        (fun y ↦ ((-2 : ℝ) • RicciFlow.intrinsicRicciBilinearAt
           (I := I) (M := M) g t y) (X y) (Y y)) x (Z x)) t := by
    have hdotXY : MDiffAt (fun y ↦ hdot y (X y) (Y y)) x := by
      have h := (mdifferentiableAt_const : MDiffAt (fun _ : M => (-2 : ℝ)) x).smul
        hRicciXY
      convert h using 1 <;> simp [hdot, ricci, smul_eq_mul] <;> funext y <;>
        simp [Pi.mul_apply] <;> ring
    have h := hasDerivAt_metricPairing_mvfderiv_of_jointContMDiff
      (I := I) (M := M) g hdot (t := t) hmetric
      (X := Z) (Y := X) (Z := Y) x hjointZXY hdotXY
    simpa [hdot, ricci] using h
  exact metricVelocityCovariantDerivative_connectionVariation_formula_intrinsicRicci
    (I := I) (M := M) g cov hcov hLevi gdot s hflow ht A hvariation
    hX hY hZ hRicciYZ hRicciXZ hRicciXY hmixedXYZ hmixedYXZ hmixedZXY

/-! The spatial Ricci-pairing regularity used above is a consequence of the
actual curvature of a sufficiently regular Levi--Civita slice.  This keeps
that requirement from becoming a free Ricci differentiability assumption. -/
theorem intrinsicRicciPairing_mdifferentiableAt_of_covariantDerivative_two
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative (cov τ) 1)
    (hLevi : g.IsLeviCivita cov) (t : ℝ)
    (hcovTwo : ContMDiffCovariantDerivative (cov t) 2)
    {U V : Π y : M, TM y}
    (hU : ∀ y, MDiffAt (T% U) y)
    (hV : ∀ y, MDiffAt (T% V) y) (x : M) :
    MDiffAt
      (fun y => RicciFlow.intrinsicRicciBilinearAt
        (I := I) (M := M) g t y (U y) (V y)) x := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  letI : ContMDiffCovariantDerivative (cov t) 2 := hcovTwo
  have hRicciTensor :=
    CovariantDerivative.ricciCovariantTwoTensorMDiffAt_of_raisedRicciEndomorphismMDiffAt
      (I := I) (E := E) (M := M) (cov t) x
      (RicciFlow.raisedRicciEndomorphismMDiffAt_of_curvature
        (I := I) (M := M) (cov t) x)
  have hRicciU := hRicciTensor.clm_bundle_apply (hU x)
  have htotal := hRicciU.clm_bundle_apply (hV x)
  let r : M → ℝ := fun y =>
    CovariantDerivative.ricciCurvature (cov := cov t) y (U y) (V y)
  have hr : MDiffAt r x := by
    have ht :=
      ((trivializationAt ℝ (Bundle.Trivial M ℝ) x).mdifferentiableAt_section_iff
        I r (FiberBundle.mem_baseSet_trivializationAt' x)).mp htotal
    simpa [Bundle.Trivial.eq_trivialization M ℝ, r,
      CovariantDerivative.ricciCovariantTwoTensor_apply] using ht
  have hRicciEq (y : M) :
      RicciFlow.intrinsicRicciBilinearAt
          (I := I) (M := M) g t y (U y) (V y) = r y := by
    rw [RicciFlow.intrinsicRicciBilinearAt_apply]
    have hpoint := congrArg (fun q => q t y (U y) (V y))
      (RicciFlow.intrinsicRicciTensor_eq_ricciTensor_of_isLeviCivita
        (I := I) (M := M) g hcov hLevi)
    simpa [RicciFlow.ricciTensor, r] using hpoint
  have hfun :
      (fun y => RicciFlow.intrinsicRicciBilinearAt
        (I := I) (M := M) g t y (U y) (V y)) = r := by
    funext y
    exact hRicciEq y
  rw [hfun]
  exact hr

end CovariantDerivative.TimeDependentRiemannianMetric
