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

public import LeanPool.PoincareGeometry.AlmostSchur.AlmostSchurAlgebra
public import LeanPool.PoincareGeometry.AlmostSchur.BundledRicciBochner
public import LeanPool.PoincareGeometry.AlmostSchur.IntegratedTraceFreeHessian
public import LeanPool.PoincareGeometry.AlmostSchur.LeviCivitaIntegratedBochner

/-!
# Bochner reduction under nonnegative Ricci curvature

This file discharges the complete Bochner half of the almost-Schur estimate for
the constructed Levi--Civita connection.  The remaining input to the final
inequality is the contracted-Bianchi pairing with the Poisson solution.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  [Nonempty M] [LindelofSpace M] [T2Space M] [CompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "LC" => (leviCivitaConnection (I := I) (M := M))

/-- Integrated Bochner with the genuine bundled Ricci contraction. -/
theorem leviCivita_integratedBundledRicciBochner
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f) :
    (∫ x, hessianNormSq LC f x ∂riemannianVolume (I := I)) +
      (∫ x, CovariantDerivative.ricciCurvatureAlmostSchur (cov := LC) x (gradient (I := I) f x)
        (gradient (I := I) f x) ∂riemannianVolume (I := I)) =
      ∫ x, (laplacian LC f x) ^ 2 ∂riemannianVolume (I := I) := by
  rw [← leviCivita_integratedRawBochner hf]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  exact (rawRicciGradient_eq_ricciCurvature LC (hf x)).symm

/-- Pointwise nonnegative Ricci curvature makes its integrated gradient
contraction nonnegative. -/
theorem integral_ricciGradient_nonneg
    (hRic : ∀ (x : M) (v : TM x),
      0 ≤ CovariantDerivative.ricciCurvatureAlmostSchur (cov := LC) x v v)
    (f : M → ℝ) :
    0 ≤ ∫ x, CovariantDerivative.ricciCurvatureAlmostSchur (cov := LC) x (gradient (I := I) f x)
      (gradient (I := I) f x) ∂riemannianVolume (I := I) :=
  integral_nonneg fun x => hRic x (gradient (I := I) f x)

/-- The exact trace-free Hessian estimate supplied by Bochner and
nonnegative Ricci curvature. -/
theorem leviCivita_traceFreeHessian_integral_bound
    (hRic : ∀ (x : M) (v : TM x),
      0 ≤ CovariantDerivative.ricciCurvatureAlmostSchur (cov := LC) x v v)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f)
    (hdim : Module.finrank ℝ E ≠ 0) :
    (Module.finrank ℝ E : ℝ) *
        (∫ x, traceFreeHessianNormSq LC f x ∂riemannianVolume (I := I)) ≤
      ((Module.finrank ℝ E : ℝ) - 1) *
        (∫ x, (laplacian LC f x) ^ 2 ∂riemannianVolume (I := I)) := by
  exact almostSchur_bochner_reduction (Nat.cast_nonneg _)
    (leviCivita_integratedBundledRicciBochner hf)
    (integral_ricciGradient_nonneg hRic f)
    (finrank_mul_integral_traceFreeHessianNormSq LC
      leviCivitaConnection_metricCompatible leviCivitaConnection_torsion hf hdim)

end AlmostSchur
