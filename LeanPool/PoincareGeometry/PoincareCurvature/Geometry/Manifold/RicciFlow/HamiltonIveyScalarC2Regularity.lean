/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyIntrinsicSliceRegularityC3

/-!
# C² regularity of scalar curvature from the actual Ricci tensor

Scalar curvature is the contraction of the actual Ricci tensor against the inverse metric.  In a
local frame this is a finite sum of products of Ricci components and inverse Gram-matrix entries.
This file derives its C² regularity from those geometric objects.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)

/-- A C² actual Ricci tensor and C² Riemannian metric give C² scalar curvature by the local-frame
inverse-Gram contraction formula. -/
theorem scalarCurvature_contMDiff_two_of_ricciC2
    [RiemannianBundle TM]
    [ContMDiffVectorBundle 2 E TM I]
    [IsContMDiffRiemannianBundle I 2 E TM]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hRicci : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) x
        (ricciCovariantTwoTensor cov x))) :
    ContMDiff I 𝓘(ℝ) 2 (scalarCurvature (cov := cov)) := by
  classical
  intro x₀
  let e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M) :=
    trivializationAt E TM x₀
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  have hu : IsOpen e.baseSet := e.open_baseSet
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E TM x₀
  have hframe : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
        (fun x ↦ TotalSpace.mk' E x (e.localFrame b i x)) e.baseSet := by
    intro i
    exact e.contMDiffOn_localFrame_baseSet (I := I) (n := 2) b i
  have hInvMatrix := contMDiffOn_localFrameGramMatrix_inv
    (I := I) (E := E) e b hu (subset_refl _)
  have hInv : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) 2
        (fun x ↦ localFrameInverseGramMatrix (I := I) e b x i j) e.baseSet := by
    intro i j
    rw [contMDiffOn_pi_space] at hInvMatrix
    have hi := hInvMatrix i
    rw [contMDiffOn_pi_space] at hi
    simpa [localFrameInverseGramMatrix] using hi j
  have hRicciOn : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) x
        (ricciCovariantTwoTensor cov x)) e.baseSet :=
    hRicci.contMDiffOn.mono (Set.subset_univ _)
  have hRicciFrame : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) 2
        (fun x ↦ TotalSpace.mk' ℝ x
          (ricciCurvature (cov := cov) x (e.localFrame b i x) (e.localFrame b j x)))
        e.baseSet := by
    intro i j
    have hfirst : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 2
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x
          (ricciCovariantTwoTensor cov x (e.localFrame b i x))) e.baseSet := by
      simpa using hRicciOn.clm_bundle_apply (hframe i)
    have hsecond := hfirst.clm_bundle_apply (hframe j)
    simpa [ricciCovariantTwoTensor_apply] using hsecond
  have hTerm : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) 2
        (fun x ↦ TotalSpace.mk' ℝ x
          (localFrameInverseGramMatrix (I := I) e b x i j *
            ricciCurvature (cov := cov) x (e.localFrame b i x) (e.localFrame b j x)))
        e.baseSet := by
    intro i j
    simpa [Pi.smul_apply, smul_eq_mul] using
      (hInv i j).smul_section (hRicciFrame i j)
  have hRow : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) 2
        (fun x ↦ TotalSpace.mk' ℝ x
          (∑ j : Fin (Module.finrank ℝ E),
            localFrameInverseGramMatrix (I := I) e b x i j *
              ricciCurvature (cov := cov) x (e.localFrame b i x) (e.localFrame b j x)))
        e.baseSet := by
    intro i
    simpa using ContMDiffOn.sum_section
      (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
      (fun j _ ↦ hTerm i j)
  have hSum : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) 2
      (fun x ↦ TotalSpace.mk' ℝ x
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          localFrameInverseGramMatrix (I := I) e b x i j *
            ricciCurvature (cov := cov) x (e.localFrame b i x) (e.localFrame b j x)))
      e.baseSet := by
    simpa using ContMDiffOn.sum_section
      (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
      (fun i _ ↦ hRow i)
  have hSumAt := hSum.contMDiffAt (hu.mem_nhds hx₀)
  have hcontractAt : ContMDiffAt I 𝓘(ℝ) 2
      (fun x ↦ ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        localFrameInverseGramMatrix (I := I) e b x i j *
          ricciCurvature (cov := cov) x (e.localFrame b i x) (e.localFrame b j x)) x₀ := by
    simpa [Bundle.Trivial.eq_trivialization M ℝ] using
      ((trivializationAt ℝ (Bundle.Trivial M ℝ) x₀).contMDiffAt_section_iff
        (n := (2 : WithTop ℕ∞))
        (FiberBundle.mem_baseSet_trivializationAt' x₀)).mp hSumAt
  refine hcontractAt.congr_of_eventuallyEq ?_
  filter_upwards [hu.mem_nhds hx₀] with x hx
  exact scalarCurvature_eq_sum_localFrame_inverseGram (cov := cov) e b hx

end CovariantDerivative

namespace CovariantDerivative.TimeDependentRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle 4 E (TangentSpace I : M → Type _) I]
  [IsManifold I (minSmoothness ℝ 2) M]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]
  [IsManifold I ((3 : ℕ∞) + 1) M]
  [SigmaCompactSpace M] [CompactSpace M] [Nonempty M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- A C³ connection slice and C² metric produce C² scalar curvature through the derived actual
Ricci section and its inverse-Gram trace. -/
theorem scalarCurvature_contMDiff_two_of_connectionC3
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov τ) 1)
    (hcov₂ : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov τ) 2)
    (hcov₃ : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov τ) 3)
    (t : ℝ)
    (hmetric₂ :
      letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      IsContMDiffRiemannianBundle I 2 E TM) :
    letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    ContMDiff I 𝓘(ℝ) 2
      (CovariantDerivative.scalarCurvature (cov := cov t)) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM := g.slice_isContMDiffRiemannianBundle t
  letI : IsContMDiffRiemannianBundle I 2 E TM := hmetric₂
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  letI : ContMDiffCovariantDerivative (cov t) 2 := hcov₂ t
  letI : ContMDiffCovariantDerivative (cov t) 3 := hcov₃ t
  have hRicciSection : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : M ↦ TM z →L[ℝ] TM z →L[ℝ] ℝ) y
        (RicciFlow.ricciBilinearFormSection (I := I) (M := M) (cov t) y)) :=
    CovariantDerivative.ricciBilinearFormSection_contMDiff_two
      (I := I) (M := M) (cov t) (Module.finBasis ℝ E)
  have hRicci₂ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : M ↦ TM z →L[ℝ] TM z →L[ℝ] ℝ) y
        (CovariantDerivative.ricciCovariantTwoTensor (cov t) y)) := by
    have hfun :
        (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun z : M ↦ TM z →L[ℝ] TM z →L[ℝ] ℝ) y
          (RicciFlow.ricciBilinearFormSection (I := I) (M := M) (cov t) y)) =
        (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun z : M ↦ TM z →L[ℝ] TM z →L[ℝ] ℝ) y
          (CovariantDerivative.ricciCovariantTwoTensor (cov t) y)) := by
      funext y
      apply congrArg (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) y)
      ext u v
      rfl
    simpa only [hfun] using hRicciSection
  exact CovariantDerivative.scalarCurvature_contMDiff_two_of_ricciC2
    (I := I) (M := M) (cov t) hRicci₂

end CovariantDerivative.TimeDependentRiemannianMetric

end
