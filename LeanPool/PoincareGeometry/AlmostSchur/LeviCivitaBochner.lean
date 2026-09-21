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

public import LeanPool.PoincareGeometry.AlmostSchur.LeviCivitaRegularity
public import LeanPool.PoincareGeometry.AlmostSchur.RawBochnerFlux

/-! # Bochner flux for the constructed regular Levi–Civita connection

No connection, compatibility, torsion, or connection-regularity hypothesis is
supplied by the caller. The contraction here is the actual raw commutator
contraction, not an assumed or separately bundled Ricci tensor.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff
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
local notation "TM" => (TangentSpace I : M → Type _)
local notation "LC" => (leviCivitaConnection (I := I) (M := M))

/-- The constructed connection's raw curvature is the corrected commutator. -/
theorem leviCivita_rawCurvature_eq_corrected_commutator
    (X Y Z : Π x, TM x) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    rawCurvature LC X Y Z x =
      (covariantAlong LC X (covariantAlong LC Y Z) x -
        LC Z x (covariantAlong LC X Y x)) -
      (covariantAlong LC Y (covariantAlong LC X Z) x -
        LC Z x (covariantAlong LC Y X x)) :=
  rawCurvature_eq_corrected_commutator LC X Y Z x
    (congrFun leviCivitaConnection_torsion x) hX hY

/-- The raw gradient contraction of the constructed connection is frame-independent. -/
theorem leviCivita_rawRicciGradient_eq_chart
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f)
    {ι : Type} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E) (x : M) (hx : x ∈ e.baseSet) :
    rawRicciGradient LC f x = chartRawRicciGradient LC f e b x :=
  rawRicciGradient_eq_chart LC leviCivitaConnection_metricCompatible
    leviCivitaConnection_torsion hf e b x hx

/-- Bochner's flux identity, now for an explicitly constructed regular connection. -/
theorem leviCivita_divergence_bochnerFlux
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f) (x : M) :
    divergence LC (bochnerFlux LC f) x = (laplacian LC f x) ^ 2 -
      hessianNormSq LC f x - rawRicciGradient LC f x :=
  divergence_bochnerFlux LC leviCivitaConnection_metricCompatible
    leviCivitaConnection_torsion hf x

end AlmostSchur
