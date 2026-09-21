/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.LeviCivitaBochner
public import LeanPool.PoincareGeometry.AlmostSchur.IntegratedRawBochner

/-! # Integrated Bochner identity for the constructed Levi-Civita connection

This specializes the proved raw integrated identity to the explicitly
constructed regular metric-compatible torsion-free connection.  Identification
of the raw contraction with the Ricci tensor remains a separate theorem.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set MeasureTheory
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
local notation "LC" => (leviCivitaConnection (I := I) (M := M))

/-- The raw integrated Bochner identity with every connection premise discharged
by the constructed Levi-Civita connection. -/
theorem leviCivita_integratedRawBochner
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f) :
    (∫ x, hessianNormSq LC f x ∂riemannianVolume (I := I)) +
      (∫ x, rawRicciGradient LC f x ∂riemannianVolume (I := I)) =
      ∫ x, (laplacian LC f x) ^ 2 ∂riemannianVolume (I := I) :=
  integratedRawBochner LC leviCivitaConnection_metricCompatible
    leviCivitaConnection_torsion hf

end AlmostSchur
