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

public import LeanPool.PoincareGeometry.AlmostSchur.LocalCurvatureExtensions

/-! # Local raw-to-tensor curvature

These are new local bridges over the attributed curvature core. In particular,
global chart-coefficient regularity is constructed by a cutoff, not required
of the original field. No equality on nondifferentiable junk sections is used.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set Filter
open scoped Manifold ContDiff Topology
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
local notation "TM" => (TangentSpace I : M → Type _)

/-- Covariant differentiation alongAlmostSchur fields respects regular section germs. -/
theorem along_eventuallyEq_of_contMDiffAt
    (cov : CovariantDerivative I E TM)
    {X X' Z Z' : Π y, TM y} {x : M}
    (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 (T% Z) x)
    (hZ' : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 (T% Z') x)
    (hXeq : X =ᶠ[𝓝 x] X') (hZeq : Z =ᶠ[𝓝 x] Z') :
    cov.alongAlmostSchur X Z =ᶠ[𝓝 x] cov.alongAlmostSchur X' Z' := by
  filter_upwards [hXeq, hZeq.eventuallyEq_nhds,
    (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hZ,
    (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hZ'] with y hXy he hZy hZ'y
  have hc := IsCovariantDerivativeOn.congr_of_eventuallyEq
    (hcov := cov.isCovariantDerivativeOnUniv)
    (hZy.mdifferentiableAt (by norm_num)) (hZ'y.mdifferentiableAt (by norm_num))
    (by simp) he
  simp only [CovariantDerivative.along_applyAlmostSchur, hc, hXy]
  rfl

/-- Comparing a local raw commutator with globally regular representatives. -/
theorem curvatureAux_eq_of_local_germs
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    {X Y Z X' Y' Z' : Π y, TM y} {x : M}
    (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 (T% Z) x)
    (hX' : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% X'))
    (hY' : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% Y'))
    (hZ' : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% Z'))
    (hXeq : X =ᶠ[𝓝 x] X') (hYeq : Y =ᶠ[𝓝 x] Y') (hZeq : Z =ᶠ[𝓝 x] Z') :
    cov.curvatureAuxAlmostSchur X Y Z x = cov.curvatureAuxAlmostSchur X' Y' Z' x := by
  have heY := along_eventuallyEq_of_contMDiffAt cov hZ (hZ' x) hYeq hZeq
  have heX := along_eventuallyEq_of_contMDiffAt cov hZ (hZ' x) hXeq hZeq
  have hYd : MDiffAt (T% (cov.alongAlmostSchur Y' Z')) x :=
    (cov.contMDiff_alongAlmostSchur (n := 1) hY' hZ' x).mdifferentiableAt (by norm_num)
  have hXd : MDiffAt (T% (cov.alongAlmostSchur X' Z')) x :=
    (cov.contMDiff_alongAlmostSchur (n := 1) hX' hZ' x).mdifferentiableAt (by norm_num)
  have hYd0 : MDiffAt (T% (cov.alongAlmostSchur Y Z)) x := by
    apply hYd.congr_of_eventuallyEq
    filter_upwards [heY] with y hy
    exact congrArg (TotalSpace.mk' E y) hy
  have hXd0 : MDiffAt (T% (cov.alongAlmostSchur X Z)) x := by
    apply hXd.congr_of_eventuallyEq
    filter_upwards [heX] with y hy
    exact congrArg (TotalSpace.mk' E y) hy
  have hcY := IsCovariantDerivativeOn.congr_of_eventuallyEq
    (hcov := cov.isCovariantDerivativeOnUniv) hYd0 hYd (by simp) heY
  have hcX := IsCovariantDerivativeOn.congr_of_eventuallyEq
    (hcov := cov.isCovariantDerivativeOnUniv) hXd0 hXd (by simp) heX
  have hcZ := IsCovariantDerivativeOn.congr_of_eventuallyEq
    (hcov := cov.isCovariantDerivativeOnUniv)
    (hZ.mdifferentiableAt (by norm_num)) ((hZ' x).mdifferentiableAt (by norm_num))
    (by simp) hZeq
  simp only [CovariantDerivative.curvatureAux_applyAlmostSchur, CovariantDerivative.along_applyAlmostSchur,
    hcY, hcX, hcZ, hXeq.self_of_nhds, hYeq.self_of_nhds,
    hXeq.mlieBracket_vectorField_eq (I := I) hYeq]

/-- The bundled curvature evaluates to the raw commutator on arbitrary locally
C² fields. All cutoff and global coefficient hypotheses have been discharged. -/
theorem curvatureAux_eq_curvatureTensor_of_contMDiffAt
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    {X Y Z : Π y, TM y} {x : M}
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 (T% Y) x)
    (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 (T% Z) x) :
    cov.curvatureAuxAlmostSchur X Y Z x = cov.curvatureTensorAlmostSchur x (X x) (Y x) (Z x) := by
  classical
  let b := Module.finBasis ℝ E
  obtain ⟨X', hX', heX, _⟩ := exists_contMDiff_section_germ_with_coefficients 2 b hX
  obtain ⟨Y', hY', heY, _⟩ := exists_contMDiff_section_germ_with_coefficients 2 b hY
  obtain ⟨Z', hZ', heZ, hZcoeff⟩ := exists_contMDiff_section_germ_with_coefficients 2 b hZ
  have hX1 := hX'.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)
  have hY1 := hY'.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)
  rw [curvatureAux_eq_of_local_germs cov hZ hX1 hY1 hZ' heX.symm heY.symm heZ.symm]
  exact cov.curvatureAux_eq_curvatureTensor_apply_of_eq_left_middle_localFrameCoeff_rightAlmostSchur
    b hX1 hY1 hZ' heX.self_of_nhds heY.self_of_nhds hZcoeff
    (fun i ↦ congrArg ((trivializationAt E TM x).localFrameCoeff I b i x) heZ.self_of_nhds)

end AlmostSchur
