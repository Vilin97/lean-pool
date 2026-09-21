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

public import LeanPool.PoincareGeometry.AlmostSchur.NonnegativeRicciBochner
public import LeanPool.PoincareGeometry.AlmostSchur.ContractedBianchiActual
public import LeanPool.PoincareGeometry.AlmostSchur.AlmostSchurAlgebra
public import LeanPool.PoincareGeometry.AlmostSchur.HilbertSchmidtPairing

/-!
# The geometric almost-Schur endpoint

This module assembles the already proved curvature, Green, Bochner, and finite
dimensional algebra.  The Poisson representative is kept as an explicit
hypothesis until the local elliptic bootstrap supplies it; no solver or
regularity theorem is hidden in this endpoint.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory
open scoped Manifold ContDiff Topology BigOperators

namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 3 E (TangentSpace I : M → Type _)]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  [Nonempty M] [LindelofSpace M] [T2Space M] [CompactSpace M]
  [PreconnectedSpace M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "LC" => (leviCivitaConnection (I := I) (M := M))

local instance almostSchurMetric0 :
    IsContMDiffRiemannianBundle I (↑(0 : ℕ)) E TM :=
  IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)

local instance almostSchurMetricOne :
    IsContMDiffRiemannianBundle I (↑(1 : ℕ)) E TM :=
  IsContMDiffRiemannianBundle.of_le (n := 2) (by norm_num)

local instance almostSchurContinuousMetric :
    IsContinuousRiemannianBundle E TM :=
  continuousRiemannianBundle_of_contMDiff (I := I)

local instance almostSchurFiniteMeasure :
    IsFiniteMeasure (riemannianVolume (I := I) (M := M)) :=
  ⟨(riemannianVolume_finite_positive (I := I)).2⟩

local instance almostSchurFiberFiniteDimensional (x : M) :
    FiniteDimensional ℝ (TM x) :=
  VectorBundle.finiteDimensional ℝ E TM x

/-- The Riesz-raised Hessian endomorphism. -/
noncomputable def hessianRaisedEndomorphism (f : M → ℝ) (x : M) :
    TM x →L[ℝ] TM x :=
  InnerProductSpace.continuousLinearMapOfBilin (hessian LC f x)

theorem inner_hessianRaisedEndomorphism (f : M → ℝ) (x : M)
    (u v : TM x) :
    inner ℝ (hessianRaisedEndomorphism (I := I) f x u) v =
      hessian LC f x u v := by
  unfold hessianRaisedEndomorphism
  rw [InnerProductSpace.continuousLinearMapOfBilin_apply]

theorem trace_hessianRaisedEndomorphism (f : M → ℝ) (x : M) :
    LinearMap.trace ℝ (TM x)
        (hessianRaisedEndomorphism (I := I) f x).toLinearMap =
      laplacian LC f x := by
  calc
    _ = ∑ i, inner ℝ
        ((hessianRaisedEndomorphism (I := I) f x)
          ((stdOrthonormalBasis ℝ (TM x)) i))
        ((stdOrthonormalBasis ℝ (TM x)) i) :=
      by
        rw [LinearMap.trace_eq_sum_inner
          (hessianRaisedEndomorphism (I := I) f x).toLinearMap
          (stdOrthonormalBasis ℝ (TM x))]
        apply Finset.sum_congr rfl
        intro i _
        exact real_inner_comm _ _
    _ = ∑ i, hessian LC f x
        ((stdOrthonormalBasis ℝ (TM x)) i)
        ((stdOrthonormalBasis ℝ (TM x)) i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact inner_hessianRaisedEndomorphism f x _ _
    _ = laplacian LC f x :=
      (laplacian_eq_sum_hessian LC f x
        (stdOrthonormalBasis ℝ (TM x))).symm

theorem hessianRaisedEndomorphism_traceFree_pair
    (f : M → ℝ) (x : M) (hdim : Module.finrank ℝ E ≠ 0) :
    hilbertSchmidtSq (traceFree (hessianRaisedEndomorphism (I := I) f x)) =
      hilbertSchmidtSq (hessianRaisedEndomorphism (I := I) f x) -
        (laplacian LC f x) ^ 2 / Module.finrank ℝ E := by
  have hrank := VectorBundle.finrank_eq ℝ E TM x
  have hx : Module.finrank ℝ (TM x) ≠ 0 := by rwa [hrank]
  have h := hilbertSchmidtSq_traceFree
    (hessianRaisedEndomorphism (I := I) f x) hx
  simpa only [trace_hessianRaisedEndomorphism, hrank] using h

end AlmostSchur
