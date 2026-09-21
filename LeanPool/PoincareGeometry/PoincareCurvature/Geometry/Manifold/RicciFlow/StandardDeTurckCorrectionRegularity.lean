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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.StandardDeTurckEquation
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.StandardDeTurckRegularity
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.DowngradeNormFree
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.HomBundleComp

/-!
# Continuity of the standard Ricci--DeTurck correction

The standard DeTurck correction is the symmetrized covariant derivative of
the correctly contracted vector field `standardDeTurckVectorField`.  This
file derives its fixed-time continuity as a bilinear-form-bundle section from
the actual `C¹` regularity of the background connection.  It does not assert a
coordinate Ricci--DeTurck identity or nonlinear parabolic well-posedness.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff Topology

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "THom" => (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)

local instance instStandardDeTurckBilENormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance instStandardDeTurckBilENormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- The canonical Levi-Civita slice maps `C¹` vector fields to continuous
endomorphism sections on each open set. -/
theorem standardDeTurck_chosenLeviCivitaFamily_contMDiffCovariantDerivativeOn_zero
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) {u : Set M} (hu : IsOpen u) :
    ContMDiffCovariantDerivativeOn E 0
      ((chosenLeviCivitaFamily (I := I) (M := M) g) t).toFun u := by
  haveI := g.someContMDiffLeviCivitaConnection_contMDiff (I := I) (M := M) t
  exact
    CovariantDerivative.TangentFrame.contMDiffCovariantDerivativeOn_zero_of_contMDiffCovariantDerivative_one
      hu

/-- The evolving-metric covariant derivative of the corrected standard
DeTurck field is a continuous tangent-endomorphism section on each open set. -/
theorem standardDeTurckVectorField_covariantDerivative_contMDiffOn_zero
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    {u : Set M} (hu : IsOpen u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 0
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x
        ((chosenLeviCivitaFamily (I := I) (M := M) g t)
          (standardDeTurckVectorField (I := I) (M := M) g background t) x)) u := by
  have hchosen0 :=
    standardDeTurck_chosenLeviCivitaFamily_contMDiffCovariantDerivativeOn_zero
      (I := I) (M := M) g t hu
  have hW :=
    standardDeTurckVectorField_contMDiff_of_contMDiffCovariantDerivative_background
      (I := I) (M := M) g background t hbackground
  exact hchosen0.contMDiff (by simpa using hW.contMDiffOn)

/-- Global form of
`standardDeTurckVectorField_covariantDerivative_contMDiffOn_zero`. -/
theorem standardDeTurckVectorField_covariantDerivative_contMDiff_zero
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 0
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x
        ((chosenLeviCivitaFamily (I := I) (M := M) g t)
          (standardDeTurckVectorField (I := I) (M := M) g background t) x)) := by
  rw [← contMDiffOn_univ]
  exact standardDeTurckVectorField_covariantDerivative_contMDiffOn_zero
    (I := I) (M := M) g background t hbackground isOpen_univ

/-- The covariant half `g ∘ ∇W` of the standard correction is a continuous
bilinear-form-bundle section. -/
theorem metricComp_standardDeTurckVectorField_covariantDerivative_contMDiff_zero
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := _root_.Bundle.BilinearFormBundle (V := TM)) x
        (((g t).inner x).comp
          ((chosenLeviCivitaFamily (I := I) (M := M) g t)
            (standardDeTurckVectorField (I := I) (M := M) g background t) x))) := by
  have hmetric :
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x ((g t).toSection x)) :=
    ((g t).contMDiff_toSection).of_le (by norm_num)
  have hW := standardDeTurckVectorField_covariantDerivative_contMDiff_zero
    (I := I) (M := M) g background t hbackground
  exact hmetric.clm_bundle_comp hW
/-- Fiberwise slot-flip preserves continuity of a bilinear-form-bundle
section without requiring a norm on the total section space. -/
theorem standardDeTurck_contMDiff_flipBilinearFormSection_tangent_zero
    {s : Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x}
    (hs : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := _root_.Bundle.BilinearFormBundle (V := TM)) x (s x))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := _root_.Bundle.BilinearFormBundle (V := TM)) x ((s x).flip)) := by
  intro x0
  have hsx := hs x0
  rw [Bundle.contMDiffAt_section (IB := I) (F := (E →L[ℝ] E →L[ℝ] ℝ))
      (E := _root_.Bundle.BilinearFormBundle (V := TM)) (s := s) x0] at hsx
  rw [Bundle.contMDiffAt_section (IB := I) (F := (E →L[ℝ] E →L[ℝ] ℝ))
      (E := _root_.Bundle.BilinearFormBundle (V := TM)) (s := fun x ↦ (s x).flip) x0]
  have hcomp : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) 0
      (fun x ↦ ContinuousLinearMap.flipBilinear (E := E)
        ((trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
          (_root_.Bundle.BilinearFormBundle (V := TM)) x0 ⟨x, s x⟩).2)) x0 := by
    simpa [Function.comp_def] using
      ((ContinuousLinearMap.flipBilinear (E := E)).contMDiffAt (n := 0)).comp x0 hsx
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [((trivializationAt E TM x0).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt E TM x0))] with x hx
  ext u v
  rw [ContinuousLinearMap.flipBilinear_apply_apply,
    trivializationAt_bilinearFormBundle_apply_eq (F := E) (W := TM) x0 x hx ((s x).flip) u v,
    trivializationAt_bilinearFormBundle_apply_eq (F := E) (W := TM) x0 x hx (s x) v u]
  exact ContinuousLinearMap.flip_apply (s x) _ _

/-- The standard correction is the covariant half `g ∘ ∇W` plus its slot
flip. -/
lemma standardDeTurckCorrection_eq_metricComp_add_flip
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    standardDeTurckCorrection (I := I) (M := M) g background t x u v =
      (((g t).inner x).comp
        ((chosenLeviCivitaFamily (I := I) (M := M) g t)
          (standardDeTurckVectorField (I := I) (M := M) g background t) x)) u v +
      ((((g t).inner x).comp
        ((chosenLeviCivitaFamily (I := I) (M := M) g t)
          (standardDeTurckVectorField (I := I) (M := M) g background t) x)).flip) u v := by
  simp only [standardDeTurckCorrection_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  congr 1
  exact (g t).symm x u _

/-- For a `C¹` background connection slice, the corrected standard DeTurck
term is a continuous bilinear-form-bundle section. -/
theorem standardDeTurckCorrection_contMDiff_zero
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := _root_.Bundle.BilinearFormBundle (V := TM)) x
        (standardDeTurckCorrection (I := I) (M := M) g background t x)) := by
  let C : Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x :=
    fun x ↦ ((g t).inner x).comp
      ((chosenLeviCivitaFamily (I := I) (M := M) g t)
        (standardDeTurckVectorField (I := I) (M := M) g background t) x)
  have hC : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := _root_.Bundle.BilinearFormBundle (V := TM)) x (C x)) :=
    metricComp_standardDeTurckVectorField_covariantDerivative_contMDiff_zero
      (I := I) (M := M) g background t hbackground
  have hflip := standardDeTurck_contMDiff_flipBilinearFormSection_tangent_zero hC
  refine (hC.add_section hflip).congr ?_
  intro x
  congr 1
  ext u v
  exact (standardDeTurckCorrection_eq_metricComp_add_flip
    (I := I) (M := M) g background t x u v).symm

end RicciFlow
