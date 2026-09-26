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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurck
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ContractedBianchiBridge
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.DowngradeNormFree
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.HomBundleComp
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.ContinuousSection

/-!
# Continuity of the covariant derivative of the intrinsic DeTurck vector field

The intrinsic Ricci–DeTurck reaction term is built from the *symmetrized covariant derivative* of the
intrinsic DeTurck vector field, `intrinsicDeTurckCorrection g background t x u v = (g t).inner x (∇W u) v
+ (g t).inner x u (∇W v)`, where `∇W = (chosenLeviCivitaFamily g t) (intrinsicDeTurckVectorField g
background t)`.  Seeing this as a `ContinuousSectionSpace` value (the geometric operator `A` of the
Ricci–DeTurck chart) requires that `∇W` be a *continuous* `Hom(TM, TM)`-section for a merely-`C¹`
DeTurck vector field.

This module supplies exactly that regularity by consuming the fiber-norm-free tangent-bundle level
downgrade `CovariantDerivative.TangentFrame.contMDiffCovariantDerivativeOn_zero_of_contMDiffCovariantDerivative_one`
(a `C¹` covariant derivative on the tangent bundle sends a `C¹` section to a *continuous*
`Hom(TM, TM)`-section).  Because that downgrade carries **no** `Π` fiber-norm hypothesis, applying it to
`chosenLeviCivitaFamily g t` — whose `C¹` covariant-derivative class comes from
`someContMDiffLeviCivitaConnection_contMDiff` — does **not** re-trigger the transported-instance norm
diamond on `NormedAddCommGroup (TangentSpace I x)` (Riemannian vs. flat-`E`).

* `chosenLeviCivitaFamily_contMDiffCovariantDerivativeOn_zero` — the canonical smooth Levi-Civita slice
  is a `C⁰` covariant derivative on every open set.
* `intrinsicDeTurckVectorField_covariantDerivative_contMDiffOn_zero` /
  `intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero` — for a `C¹` background connection
  slice, `∇W` is a continuous `Hom(TM, TM)`-section (locally, resp. globally).
-/

@[expose] public noncomputable section

open Bundle
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

local instance instDeTurckBilENormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance instDeTurckBilENormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- The canonical smooth Levi-Civita slice of a metric family is a `C⁰` covariant derivative on every
open set: it sends a `C¹` vector field to a *continuous* `Hom(TM, TM)`-section.  Obtained by feeding the
`C¹` covariant-derivative class of `chosenLeviCivitaFamily` (from
`someContMDiffLeviCivitaConnection_contMDiff`) to the fiber-norm-free tangent-bundle level downgrade. -/
theorem chosenLeviCivitaFamily_contMDiffCovariantDerivativeOn_zero
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) {u : Set M} (hu : IsOpen u) :
    ContMDiffCovariantDerivativeOn E 0
      ((chosenLeviCivitaFamily (I := I) (M := M) g) t).toFun u := by
  haveI := g.someContMDiffLeviCivitaConnection_contMDiff (I := I) (M := M) t
  exact
    CovariantDerivative.TangentFrame.contMDiffCovariantDerivativeOn_zero_of_contMDiffCovariantDerivative_one
      hu

/-- For a `C¹` background connection slice, the covariant derivative
`∇W = (chosenLeviCivitaFamily g t) (intrinsicDeTurckVectorField g background t)` of the intrinsic
DeTurck vector field is a **continuous** `Hom(TM, TM)`-section on every open set.  This is the
regularity input that lets the intrinsic Ricci–DeTurck reaction term be read as a continuous section
(a `ContinuousSectionSpace` value). -/
theorem intrinsicDeTurckVectorField_covariantDerivative_contMDiffOn_zero
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    {u : Set M} (hu : IsOpen u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 0
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x
        ((chosenLeviCivitaFamily (I := I) (M := M) g t)
          (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x)) u := by
  have hchosen0 := chosenLeviCivitaFamily_contMDiffCovariantDerivativeOn_zero (I := I) (M := M) g t hu
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (T% (intrinsicDeTurckVectorField (I := I) (M := M) g background t)) :=
    intrinsicDeTurckVectorField_contMDiff_of_contMDiffCovariantDerivative_background
      (I := I) (M := M) g background t hbackground
  exact hchosen0.contMDiff (by simpa using hW.contMDiffOn)

/-- Global version of `intrinsicDeTurckVectorField_covariantDerivative_contMDiffOn_zero`: for a `C¹`
background connection slice, `∇W` is a continuous `Hom(TM, TM)`-section on all of `M`. -/
theorem intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 0
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x
        ((chosenLeviCivitaFamily (I := I) (M := M) g t)
          (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x)) := by
  rw [← contMDiffOn_univ]
  exact intrinsicDeTurckVectorField_covariantDerivative_contMDiffOn_zero
    (I := I) (M := M) g background t hbackground isOpen_univ

/-- The covariant part of the intrinsic DeTurck correction, `x ↦ (g t).inner x ∘L ∇W`, is a
continuous `BilinearFormBundle` section for a `C¹` background connection slice.  This is the
fiberwise composition of the `C²` metric section with the continuous `Hom(TM, TM)`-section `∇W`,
proved via the fiber-norm-free bundle-level `clm_bundle_comp`. -/
theorem metricComp_intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := _root_.Bundle.BilinearFormBundle (V := TM)) x
        (((g t).inner x).comp
          ((chosenLeviCivitaFamily (I := I) (M := M) g t)
            (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x))) := by
  have hmetric :
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x ((g t).toSection x)) :=
    ((g t).contMDiff_toSection).of_le (by norm_num)
  have hW := intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
    (I := I) (M := M) g background t hbackground
  exact hmetric.clm_bundle_comp hW
/-- Fiberwise slot-flip preserves continuity of a `BilinearFormBundle` section, fiber-norm-free.
In preferred local coordinates the flip is the fixed model slot-flip `ContinuousLinearMap.flipBilinear`,
so this mirrors `Bundle.contMDiff_symmetrizeBilinearSection` but with the flip operator and without any
`Π` fiber-norm hypothesis (the tangent-bundle readout `trivializationAt_bilinearFormBundle_apply_eq`
needs only the vector-bundle structure). -/
theorem contMDiff_flipBilinearFormSection_tangent_zero
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

/-- The intrinsic DeTurck correction, at the scalar level, is the metric-composition covariant term
`C1 = (g t).inner ∘L ∇W` symmetrized with its slot-flip: `intrinsicDeTurckCorrection = C1 + flip C1`.
Combined with the continuity of `C1`
(`metricComp_intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero`) and of `flip C1`
(`contMDiff_flipBilinearFormSection_tangent_zero`), this exhibits the intrinsic Ricci–DeTurck reaction
term as a sum of two continuous `BilinearFormBundle` sections. -/
lemma intrinsicDeTurckCorrection_eq_metricComp_add_flip
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicDeTurckCorrection (I := I) (M := M) g background t x u v =
      (((g t).inner x).comp
        ((chosenLeviCivitaFamily (I := I) (M := M) g t)
          (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x)) u v +
      ((((g t).inner x).comp
        ((chosenLeviCivitaFamily (I := I) (M := M) g t)
          (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x)).flip) u v := by
  simp only [intrinsicDeTurckCorrection_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  congr 1
  exact (g t).symm x u _

/-- The intrinsic DeTurck correction packaged as a genuine `BilinearFormBundle` section:
`C1 + flip C1`, where `C1 = (g t).inner ∘L ∇W`.  Each summand is ascribed to the bundle-fiber type
`BilinearFormBundle (V := TM) x` (rather than the raw tangent synonym) so the section-level `+`
resolves through the vector-bundle `Add`. -/
noncomputable def intrinsicDeTurckCorrectionSection
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) : Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x :=
  @HAdd.hAdd
    (Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x)
    (Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x)
    (Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x) instHAdd
    (fun x ↦ ((g t).inner x).comp
      ((chosenLeviCivitaFamily (I := I) (M := M) g t)
        (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x))
    (fun x ↦ (((g t).inner x).comp
      ((chosenLeviCivitaFamily (I := I) (M := M) g t)
        (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x)).flip)

@[simp] lemma intrinsicDeTurckCorrectionSection_apply
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
      intrinsicDeTurckCorrectionSection (I := I) (M := M) g background t x u v =
      intrinsicDeTurckCorrection (I := I) (M := M) g background t x u v := by
  change
    (((g t).inner x).comp
        ((chosenLeviCivitaFamily (I := I) (M := M) g t)
          (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x) u v +
      ((((g t).inner x).comp
        ((chosenLeviCivitaFamily (I := I) (M := M) g t)
          (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x)).flip) u v) =
      intrinsicDeTurckCorrection (I := I) (M := M) g background t x u v
  exact (intrinsicDeTurckCorrection_eq_metricComp_add_flip
    (I := I) (M := M) g background t x u v).symm

/-- The intrinsic DeTurck correction is a continuous `BilinearFormBundle` section for a `C¹`
background connection slice.  This is the symmetrized covariant part of the intrinsic Ricci–DeTurck
reaction term (`C1 + flip C1`), assembled fiber-norm-free from
`metricComp_intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero`,
`contMDiff_flipBilinearFormSection_tangent_zero`, and `ContMDiff.add_section`.  Reading the intrinsic
Ricci–DeTurck right-hand side as a `ContinuousSectionSpace` value (the geometric operator `A`) consumes
exactly this regularity. -/
theorem intrinsicDeTurckCorrectionSection_contMDiff_zero
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := _root_.Bundle.BilinearFormBundle (V := TM)) x
        (intrinsicDeTurckCorrectionSection (I := I) (M := M) g background t x)) := by
  have hC1 := metricComp_intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
    (I := I) (M := M) g background t hbackground
  have hflip := contMDiff_flipBilinearFormSection_tangent_zero hC1
  exact hC1.add_section hflip

/-- The intrinsic Ricci–DeTurck right-hand side, packaged as a `BilinearFormBundle` section, is
`(-2) • (Ricci section) + (DeTurck correction section)`.  Given *any* continuous `BilinearFormBundle`
section `rs` representing the intrinsic Ricci tensor (`rs x u v = intrinsicRicciTensor g t x u v`), the
combination `(-2 : ℝ) • rs + intrinsicDeTurckCorrectionSection g background t` is a **continuous**
`BilinearFormBundle` section that agrees pointwise with the geometric Ricci–DeTurck operator
`intrinsicRicciDeTurckRHS`.  This assembles the geometric operator `A`'s value section out of its two
halves — the second-order Ricci part (supplied as the honest continuous-section input `rs`) and the
already-continuous lower-order DeTurck reaction term
(`intrinsicDeTurckCorrectionSection_contMDiff_zero`) — via the vector-bundle section algebra
(`ContMDiff.const_smul_section`, `ContMDiff.add_section`).  It reduces the remaining `A`-regularity
obstruction for the Ricci–DeTurck chart to the single input that the Ricci tensor is a continuous
`BilinearFormBundle` section. -/
theorem exists_intrinsicRicciDeTurckRHSSection_contMDiff_zero_of_ricciSection
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (rs : Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x)
    (hrsCont : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := _root_.Bundle.BilinearFormBundle (V := TM)) x (rs x)))
    (hrsApply : ∀ (x : M) (u v : TM x),
      rs x u v = intrinsicRicciTensor (I := I) (M := M) g t x u v) :
    ∃ rhs : Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x,
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := _root_.Bundle.BilinearFormBundle (V := TM)) x (rhs x)) ∧
      ∀ (x : M) (u v : TM x),
        rhs x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x u v := by
  have hsmul := hrsCont.const_smul_section (a := (-2 : ℝ))
  have hcont := hsmul.add_section
    (intrinsicDeTurckCorrectionSection_contMDiff_zero (I := I) (M := M) g background t hbackground)
  refine ⟨_, hcont, ?_⟩
  intro x u v
  simp only [Pi.add_apply, Pi.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, intrinsicDeTurckCorrectionSection_apply,
    hrsApply, intrinsicRicciDeTurckRHS_apply, intrinsicRicciFlowRHS_apply, ricciFlowRHS_apply,
    intrinsicRicciTensor_apply]

/-- **Continuity of the raw curvature commutator for a `C¹` connection on the tangent bundle.**
For a `C¹` covariant derivative `cov` on `TM` and `C²` vector fields `X`, `Y`, `Z`, the raw curvature
section `curvatureAux X Y Z = ∇_X∇_Y Z − ∇_Y∇_X Z − ∇_{[X,Y]}Z` is a **continuous** `TM`-section.  The
regularity is consistent because the two nested covariant derivatives each drop one class: with a `C¹`
connection the inner `∇_Y Z` is `C¹` (`contMDiff_along` at `n = 1`) and the outer `∇_X(∇_Y Z)` is `C⁰`
(`contMDiff_along` at `n = 0`), using the fiber-norm-free tangent-bundle level downgrade
`contMDiffCovariantDerivativeOn_zero_of_contMDiffCovariantDerivative_one` to supply the `C⁰` connection
instance without hitting the `TangentSpace` fiber-norm diamond; the bracket term `∇_{[X,Y]}Z` is `C⁰`
from `ContDiff.mlieBracket_vectorField` (`C²` fields give a `C⁰` bracket) fed to `contMDiff_along`.  This
is the base regularity input of the `curvatureAux → curvatureTensor → Ricci` route toward reading the
intrinsic Ricci tensor as a continuous `BilinearFormBundle` section (the last geometric-`A` value
regularity input). -/
theorem curvatureAux_contMDiff_zero
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {X Y Z : Π x : M, TangentSpace I x}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun x ↦ TotalSpace.mk' E x (X x)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun x ↦ TotalSpace.mk' E x (Y x)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun x ↦ TotalSpace.mk' E x (Z x))) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) 0
      (fun x ↦ TotalSpace.mk' E x (cov.curvatureAux X Y Z x)) := by
  haveI : ContMDiffVectorBundle 0 E (TangentSpace I : M → Type _) I :=
    ContMDiffVectorBundle.of_le (n := 2) (by norm_num)
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    ContMDiffVectorBundle.of_le (n := 2) (by norm_num)
  have hcov0on : ContMDiffCovariantDerivativeOn E 0 cov.toFun Set.univ :=
    CovariantDerivative.TangentFrame.contMDiffCovariantDerivativeOn_zero_of_contMDiffCovariantDerivative_one
      isOpen_univ
  haveI : CovariantDerivative.ContMDiffCovariantDerivative cov 0 := ⟨hcov0on⟩
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  haveI : IsManifold I ((2 : ℕ∞) + 1) M :=
    IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by exact_mod_cast le_top)
  have hZ2 : ContMDiff I (I.prod 𝓘(ℝ, E)) (1 + 1)
      (fun x ↦ TotalSpace.mk' E x (Z x)) := hZ.of_le (by norm_num)
  have hYZ1 : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun x ↦ TotalSpace.mk' E x (cov.along Y Z x)) :=
    cov.contMDiff_along (hY.of_le (by norm_num)) hZ2
  have hXZ1 : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun x ↦ TotalSpace.mk' E x (cov.along X Z x)) :=
    cov.contMDiff_along (hX.of_le (by norm_num)) hZ2
  have hYZ1' : ContMDiff I (I.prod 𝓘(ℝ, E)) (0 + 1)
      (fun x ↦ TotalSpace.mk' E x (cov.along Y Z x)) := by simpa using hYZ1
  have hXZ1' : ContMDiff I (I.prod 𝓘(ℝ, E)) (0 + 1)
      (fun x ↦ TotalSpace.mk' E x (cov.along X Z x)) := by simpa using hXZ1
  have hT1 : ContMDiff I (I.prod 𝓘(ℝ, E)) 0
      (fun x ↦ TotalSpace.mk' E x (cov.along X (cov.along Y Z) x)) :=
    cov.contMDiff_along (hX.of_le (by norm_num)) hYZ1'
  have hT2 : ContMDiff I (I.prod 𝓘(ℝ, E)) 0
      (fun x ↦ TotalSpace.mk' E x (cov.along Y (cov.along X Z) x)) :=
    cov.contMDiff_along (hY.of_le (by norm_num)) hXZ1'
  have hbr0 : ContMDiff I (I.prod 𝓘(ℝ, E)) 0
      (fun x ↦ TotalSpace.mk' E x (VectorField.mlieBracket I X Y x)) :=
    ContDiff.mlieBracket_vectorField (m := 0) (n := 2) hX hY
      (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num)
  have hZ1 : ContMDiff I (I.prod 𝓘(ℝ, E)) (0 + 1)
      (fun x ↦ TotalSpace.mk' E x (Z x)) := by
    simpa using (hZ.of_le (by norm_num) : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 _)
  have hT3 : ContMDiff I (I.prod 𝓘(ℝ, E)) 0
      (fun x ↦ TotalSpace.mk' E x (cov.along (VectorField.mlieBracket I X Y) Z x)) :=
    cov.contMDiff_along hbr0 hZ1
  have hcomb := (hT1.sub_section hT2).sub_section hT3
  simpa only [CovariantDerivative.curvatureAux] using hcomb

/-- **Local (`On`) continuity of the raw curvature commutator for a `C¹` tangent-bundle connection.**
The `On`-version of `curvatureAux_contMDiff_zero`: for a `C¹` covariant derivative on `TM` and vector
fields `X`, `Y`, `Z` that are `C²` *on an open set* `u` (e.g. the local frame fields of a
trivialization, which are only `C²` on the trivialization base set), the raw curvature section
`curvatureAux X Y Z` is a **continuous** `TM`-section on `u`.  The connection is restricted to `u` via
the `C¹` restriction (`contMDiffCovariantDerivativeOn_one_of_contMDiffCovariantDerivative_one`) and the
fiber-norm-free `C¹ → C⁰` downgrade
(`TangentFrame.contMDiffCovariantDerivativeOn_zero_of_contMDiffCovariantDerivative_one`); the bracket
term is obtained via `ContMDiffOn.mlieBracketWithin_vectorField` (`mlieBracketWithin`) and identified
with `mlieBracket` on the open set.  This is the local-to-global gluing brick for lifting `curvatureAux`
continuity to `curvatureTensor` section continuity along local frames. -/
theorem curvatureAux_contMDiffOn_zero
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {X Y Z : Π x : M, TangentSpace I x} {u : Set M} (hu : IsOpen u)
    (hX : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun x ↦ TotalSpace.mk' E x (X x)) u)
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun x ↦ TotalSpace.mk' E x (Y x)) u)
    (hZ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun x ↦ TotalSpace.mk' E x (Z x)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) 0
      (fun x ↦ TotalSpace.mk' E x (cov.curvatureAux X Y Z x)) u := by
  haveI : ContMDiffVectorBundle 0 E (TangentSpace I : M → Type _) I :=
    ContMDiffVectorBundle.of_le (n := 2) (by norm_num)
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    ContMDiffVectorBundle.of_le (n := 2) (by norm_num)
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  haveI : IsManifold I ((2 : ℕ∞) + 1) M :=
    IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by exact_mod_cast le_top)
  have hcov1 : ContMDiffCovariantDerivativeOn E 1 cov.toFun u :=
    CovariantDerivative.TangentFrame.contMDiffCovariantDerivativeOn_one_of_contMDiffCovariantDerivative_one
      hu
  have hcov0 : ContMDiffCovariantDerivativeOn E 0 cov.toFun u :=
    CovariantDerivative.TangentFrame.contMDiffCovariantDerivativeOn_zero_of_contMDiffCovariantDerivative_one
      hu
  have hX1 := hX.of_le (show (1 : WithTop ℕ∞) ≤ 2 by norm_num)
  have hY1 := hY.of_le (show (1 : WithTop ℕ∞) ≤ 2 by norm_num)
  have hX0 := hX.of_le (show (0 : WithTop ℕ∞) ≤ 2 by norm_num)
  have hY0 := hY.of_le (show (0 : WithTop ℕ∞) ≤ 2 by norm_num)
  have hZ1 := hZ.of_le (show (1 : WithTop ℕ∞) ≤ 2 by norm_num)
  have hYZ1 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
      (fun x ↦ TotalSpace.mk' E x (cov.along Y Z x)) u := by
    simpa [CovariantDerivative.along] using (hcov1.contMDiff hZ).clm_bundle_apply hY1
  have hXZ1 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
      (fun x ↦ TotalSpace.mk' E x (cov.along X Z x)) u := by
    simpa [CovariantDerivative.along] using (hcov1.contMDiff hZ).clm_bundle_apply hX1
  have hT1 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 0
      (fun x ↦ TotalSpace.mk' E x (cov.along X (cov.along Y Z) x)) u := by
    simpa [CovariantDerivative.along] using (hcov0.contMDiff hYZ1).clm_bundle_apply hX0
  have hT2 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 0
      (fun x ↦ TotalSpace.mk' E x (cov.along Y (cov.along X Z) x)) u := by
    simpa [CovariantDerivative.along] using (hcov0.contMDiff hXZ1).clm_bundle_apply hY0
  have hBrWithin : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 0
      (fun x ↦ TotalSpace.mk' E x (VectorField.mlieBracketWithin I X Y u x)) u := by
    simpa using
      (hX.mlieBracketWithin_vectorField (I := I) (m := (0 : ℕ∞)) hY hu.uniqueMDiffOn
        (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num))
  have hBr : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 0
      (fun x ↦ TotalSpace.mk' E x (VectorField.mlieBracket I X Y x)) u := by
    refine ContMDiffOn.congr hBrWithin ?_
    intro x hx
    have hXx : MDiffAt (T% X) x :=
      (((hX x hx).contMDiffAt (hu.mem_nhds hx)).of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).mdifferentiableAt one_ne_zero
    have hYx : MDiffAt (T% Y) x :=
      (((hY x hx).contMDiffAt (hu.mem_nhds hx)).of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).mdifferentiableAt one_ne_zero
    congr 1
    simpa using
      (VectorField.mlieBracketWithin_eq_mlieBracket (I := I) (s := u) (x := x)
        (hu.uniqueMDiffWithinAt hx) hXx hYx).symm
  have hT3 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 0
      (fun x ↦ TotalSpace.mk' E x (cov.along (VectorField.mlieBracket I X Y) Z x)) u := by
    simpa [CovariantDerivative.along] using (hcov0.contMDiff hZ1).clm_bundle_apply hBr
  have hcomb := (hT1.sub_section hT2).sub_section hT3
  simpa only [CovariantDerivative.curvatureAux] using hcomb

/-- **Germ-locality of the raw curvature commutator with only-locally-smooth replacement fields.**
If globally-`C¹`/`C²` fields `X`, `Y`, `σ` agree *near* `y` with arbitrary fields `ea`, `eb`, `ec`
— which carry **no** global regularity hypothesis of their own — then the raw curvature commutator
takes the same value at `y`.  This is the `ContMDiffOn`-friendly companion of
`curvatureAux_eq_of_eventuallyEq_apply` (which requires the "from" fields to be *globally* smooth):
here the local frame fields of a trivialization (only `ContMDiffOn` on the base set) inherit their
differentiability at points near `y` from the global comparison fields via the eventual equality. -/
theorem curvatureAux_apply_eq_of_eventuallyEq_fields
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {ea eb ec X Y σ : Π x : M, TangentSpace I x} {y : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun z ↦ TotalSpace.mk' E z (X z)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (fun z ↦ TotalSpace.mk' E z (Y z)))
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun z ↦ TotalSpace.mk' E z (σ z)))
    (hea : ea =ᶠ[nhds y] X) (heb : eb =ᶠ[nhds y] Y) (hec : ec =ᶠ[nhds y] σ) :
    cov.curvatureAux ea eb ec y = cov.curvatureAux X Y σ y := by
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    ContMDiffVectorBundle.of_le (n := 2) (by norm_num)
  have hcov_congr : ∀ {s t : Π x : M, TangentSpace I x} {z : M},
      MDiffAt (T% s) z → MDiffAt (T% t) z → s =ᶠ[nhds z] t → cov s z = cov t z := by
    intro s t z hs ht hst
    exact IsCovariantDerivativeOn.congr_of_eventuallyEq
      (hcov := cov.isCovariantDerivativeOnUniv) hs ht Filter.univ_mem hst
  have hσ2' : ContMDiff I (I.prod 𝓘(ℝ, E)) (1 + 1)
      (fun z ↦ TotalSpace.mk' E z (σ z)) := hσ.of_le (by norm_num)
  have hAlongYσ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun z ↦ TotalSpace.mk' E z (cov.along Y σ z)) := cov.contMDiff_along hY hσ2'
  have hAlongXσ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun z ↦ TotalSpace.mk' E z (cov.along X σ z)) := cov.contMDiff_along hX hσ2'
  have hEbEc : ∀ᶠ z in nhds y, cov.along eb ec z = cov.along Y σ z := by
    have hec_ev : ∀ᶠ z in nhds y, ec =ᶠ[nhds z] σ := eventually_eventually_nhds.2 hec
    filter_upwards [heb, hec_ev] with z hzeb hzec_ev
    have hσz : MDiffAt (T% σ) z := (hσ z).mdifferentiableAt (by norm_num)
    have htec_ev : (fun w ↦ TotalSpace.mk' E w (ec w)) =ᶠ[nhds z]
        (fun w ↦ TotalSpace.mk' E w (σ w)) := by
      filter_upwards [hzec_ev] with w hw; simp [hw]
    have hecz : MDiffAt (T% ec) z := hσz.congr_of_eventuallyEq htec_ev
    have hcovz : cov ec z = cov σ z := hcov_congr hecz hσz hzec_ev
    simp only [CovariantDerivative.along_apply, hzeb, hcovz]
  have hEaEc : ∀ᶠ z in nhds y, cov.along ea ec z = cov.along X σ z := by
    have hec_ev : ∀ᶠ z in nhds y, ec =ᶠ[nhds z] σ := eventually_eventually_nhds.2 hec
    filter_upwards [hea, hec_ev] with z hzea hzec_ev
    have hσz : MDiffAt (T% σ) z := (hσ z).mdifferentiableAt (by norm_num)
    have htec_ev : (fun w ↦ TotalSpace.mk' E w (ec w)) =ᶠ[nhds z]
        (fun w ↦ TotalSpace.mk' E w (σ w)) := by
      filter_upwards [hzec_ev] with w hw; simp [hw]
    have hecz : MDiffAt (T% ec) z := hσz.congr_of_eventuallyEq htec_ev
    have hcovz : cov ec z = cov σ z := hcov_congr hecz hσz hzec_ev
    simp only [CovariantDerivative.along_apply, hzea, hcovz]
  have hAlongYσ_y : MDiffAt (T% (cov.along Y σ)) y :=
    (hAlongYσ y).mdifferentiableAt one_ne_zero
  have hAlongXσ_y : MDiffAt (T% (cov.along X σ)) y :=
    (hAlongXσ y).mdifferentiableAt one_ne_zero
  have htEbEc_ev : (fun z ↦ TotalSpace.mk' E z (cov.along eb ec z)) =ᶠ[nhds y]
      (fun z ↦ TotalSpace.mk' E z (cov.along Y σ z)) := by
    filter_upwards [hEbEc] with z hz; exact congrArg (TotalSpace.mk' E z) hz
  have htEaEc_ev : (fun z ↦ TotalSpace.mk' E z (cov.along ea ec z)) =ᶠ[nhds y]
      (fun z ↦ TotalSpace.mk' E z (cov.along X σ z)) := by
    filter_upwards [hEaEc] with z hz; exact congrArg (TotalSpace.mk' E z) hz
  have hAlongEbEc_y : MDiffAt (T% (cov.along eb ec)) y :=
    hAlongYσ_y.congr_of_eventuallyEq htEbEc_ev
  have hAlongEaEc_y : MDiffAt (T% (cov.along ea ec)) y :=
    hAlongXσ_y.congr_of_eventuallyEq htEaEc_ev
  have hTermA : cov.along ea (cov.along eb ec) y = cov.along X (cov.along Y σ) y := by
    have hcov1 : cov (cov.along eb ec) y = cov (cov.along Y σ) y :=
      hcov_congr hAlongEbEc_y hAlongYσ_y hEbEc
    have heay : ea y = X y := hea.eq_of_nhds
    simp only [CovariantDerivative.along_apply, heay, hcov1]
  have hTermB : cov.along eb (cov.along ea ec) y = cov.along Y (cov.along X σ) y := by
    have hcov1 : cov (cov.along ea ec) y = cov (cov.along X σ) y :=
      hcov_congr hAlongEaEc_y hAlongXσ_y hEaEc
    have heby : eb y = Y y := heb.eq_of_nhds
    simp only [CovariantDerivative.along_apply, heby, hcov1]
  have hbr : VectorField.mlieBracket I ea eb =ᶠ[nhds y] VectorField.mlieBracket I X Y :=
    hea.mlieBracket_vectorField heb
  have hTermC : cov.along (VectorField.mlieBracket I ea eb) ec y
      = cov.along (VectorField.mlieBracket I X Y) σ y := by
    have hσy : MDiffAt (T% σ) y := (hσ y).mdifferentiableAt (by norm_num)
    have htec_ev : (fun w ↦ TotalSpace.mk' E w (ec w)) =ᶠ[nhds y]
        (fun w ↦ TotalSpace.mk' E w (σ w)) := by
      filter_upwards [hec] with w hw; simp [hw]
    have hecy : MDiffAt (T% ec) y := hσy.congr_of_eventuallyEq htec_ev
    have hcov1 : cov ec y = cov σ y := hcov_congr hecy hσy hec
    have hbry : VectorField.mlieBracket I ea eb y = VectorField.mlieBracket I X Y y :=
      hbr.eq_of_nhds
    simp only [CovariantDerivative.along_apply, hbry, hcov1]
  rw [CovariantDerivative.curvatureAux_apply, CovariantDerivative.curvatureAux_apply,
    hTermA, hTermB, hTermC]

/-- **Pointwise tensoriality of the raw curvature commutator for only-`ContMDiffOn` frame fields.**
For a `C¹` tangent connection and vector fields `ea`, `eb`, `ec` that are `C²` *only on* an open set
`u`, the raw curvature commutator at any `y ∈ u` equals the bundled curvature tensor evaluated on the
frame values.  This is the `On`-version of
`curvatureAux_eq_curvatureTensor_apply_of_eq_left_middle_localFrameCoeff_right`: the fields are
globalised by a bump supported in `u ∩ trivializationAt.baseSet` (so the global comparison field's
trivialization coefficients are `C²` on that patch and vanish off the bump), the value tensoriality is
applied to the globalisation, and the germ-move `curvatureAux_apply_eq_of_eventuallyEq_fields` transfers
the result back to the local fields. -/
theorem curvatureAux_apply_eq_curvatureTensor_of_contMDiffOn_frame
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {ea eb ec : Π x : M, TangentSpace I x} {u : Set M} (hu : IsOpen u) {y : M} (hy : y ∈ u)
    (hea : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun z ↦ TotalSpace.mk' E z (ea z)) u)
    (heb : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun z ↦ TotalSpace.mk' E z (eb z)) u)
    (hec : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun z ↦ TotalSpace.mk' E z (ec z)) u) :
    cov.curvatureAux ea eb ec y =
      CovariantDerivative.curvatureTensor (cov := cov) y (ea y) (eb y) (ec y) := by
  classical
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    ContMDiffVectorBundle.of_le (n := 2) (by norm_num)
  set e := trivializationAt E (TangentSpace I : M → Type _) y with he
  set u' : Set M := u ∩ e.baseSet with hu'def
  have hu'open : IsOpen u' := hu.inter e.open_baseSet
  have hyu' : y ∈ u' := ⟨hy, mem_baseSet_trivializationAt E _ y⟩
  have hu'subu : u' ⊆ u := Set.inter_subset_left
  have hu'sube : u' ⊆ e.baseSet := Set.inter_subset_right
  have hu'nhds : u' ∈ nhds y := hu'open.mem_nhds hyu'
  obtain ⟨ψ, hψtsupp, hψsupp⟩ :=
    (SmoothBumpFunction.nhds_basis_support (I := I) (c := y) hu'nhds).mem_iff.mp hu'nhds
  have hψ : ContMDiff I 𝓘(ℝ) 2 (ψ : M → ℝ) :=
    ψ.contMDiff.of_le (show (2 : WithTop ℕ∞) ≤ ∞ by decide)
  set X : Π z : M, TangentSpace I z := fun z ↦ ψ z • ea z with hXdef
  set Y : Π z : M, TangentSpace I z := fun z ↦ ψ z • eb z with hYdef
  set σ : Π z : M, TangentSpace I z := fun z ↦ ψ z • ec z with hσdef
  have hXglob : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun z ↦ TotalSpace.mk' E z (X z)) := by
    simpa [hXdef] using
      (ContMDiffOn.smul_section_of_tsupport (I := I) (F := E)
        (V := (TangentSpace I : M → Type _)) (u := u') (n := (2 : WithTop ℕ∞)) (ψ := ψ)
        hψ.contMDiffOn hu'open hψtsupp (hea.mono hu'subu))
  have hYglob : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun z ↦ TotalSpace.mk' E z (Y z)) := by
    simpa [hYdef] using
      (ContMDiffOn.smul_section_of_tsupport (I := I) (F := E)
        (V := (TangentSpace I : M → Type _)) (u := u') (n := (2 : WithTop ℕ∞)) (ψ := ψ)
        hψ.contMDiffOn hu'open hψtsupp (heb.mono hu'subu))
  have hσglob : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun z ↦ TotalSpace.mk' E z (σ z)) := by
    simpa [hσdef] using
      (ContMDiffOn.smul_section_of_tsupport (I := I) (F := E)
        (V := (TangentSpace I : M → Type _)) (u := u') (n := (2 : WithTop ℕ∞)) (ψ := ψ)
        hψ.contMDiffOn hu'open hψtsupp (hec.mono hu'subu))
  have hψ1 : {z : M | ψ z = 1} ∈ nhds y := by
    filter_upwards [ψ.eventuallyEq_one] with z hz; simpa using hz
  have hψy1 : (ψ : M → ℝ) y = 1 := by simpa using ψ.eventuallyEq_one.eq_of_nhds
  have hXea : X =ᶠ[nhds y] ea := by
    filter_upwards [hψ1] with z hz
    have : ψ z = 1 := hz
    simp [hXdef, this] <;> rfl
  have hYeb : Y =ᶠ[nhds y] eb := by
    filter_upwards [hψ1] with z hz
    have : ψ z = 1 := hz
    simp [hYdef, this] <;> rfl
  have hσec : σ =ᶠ[nhds y] ec := by
    filter_upwards [hψ1] with z hz
    have : ψ z = 1 := hz
    simp [hσdef, this] <;> rfl
  have hgerm : cov.curvatureAux ea eb ec y = cov.curvatureAux X Y σ y :=
    curvatureAux_apply_eq_of_eventuallyEq_fields
      (hXglob.of_le (by norm_num)) (hYglob.of_le (by norm_num)) hσglob
      hXea.symm hYeb.symm hσec.symm
  let b := Module.finBasis ℝ E
  have hσcoeff : ∀ i, ContMDiff I 𝓘(ℝ) 2
      (fun z ↦ e.localFrameCoeff I b i z (σ z)) := by
    intro i
    have hbase : ContMDiffOn I 𝓘(ℝ) 2
        (fun z ↦ e.localFrameCoeff I b i z (σ z)) u' :=
      contMDiffOn_localFrameCoeff (I := I) (e := e) (b := b) (t := u')
        (k := (2 : WithTop ℕ∞)) hu'open hu'sube hσglob.contMDiffOn i
    have hcompl : ContMDiffOn I 𝓘(ℝ) 2
        (fun z ↦ e.localFrameCoeff I b i z (σ z)) (tsupport ψ)ᶜ := by
      have hzero : ContMDiffOn I 𝓘(ℝ) 2 (fun _ : M ↦ (0 : ℝ)) (tsupport ψ)ᶜ :=
        contMDiff_const.contMDiffOn
      refine hzero.congr ?_
      intro z hz
      have hψz : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [hσdef, hψz]
    have hcover : u' ∪ (tsupport ψ)ᶜ = Set.univ := by
      refine Set.eq_univ_iff_forall.mpr fun z ↦ ?_
      by_cases hz : z ∈ tsupport ψ
      · exact Or.inl (hψtsupp hz)
      · exact Or.inr hz
    exact contMDiff_of_contMDiffOn_union_of_isOpen hbase hcompl hcover hu'open
      (isOpen_compl_iff.mpr (isClosed_tsupport ψ))
  have hXy : X y = ea y := by simp [hXdef, hψy1]
  have hYy : Y y = eb y := by simp [hYdef, hψy1]
  have hσy : σ y = ec y := by simp [hσdef, hψy1]
  have hcoeff_eq : ∀ i,
      e.localFrameCoeff I b i y (σ y) = e.localFrameCoeff I b i y (ec y) := by
    intro i; rw [hσy]
  have htens : cov.curvatureAux X Y σ y =
      CovariantDerivative.curvatureTensor (cov := cov) y (ea y) (eb y) (ec y) :=
    cov.curvatureAux_eq_curvatureTensor_apply_of_eq_left_middle_localFrameCoeff_right
      (b := b) (X := X) (Y := Y) (σ := σ) (x := y)
      (hXglob.of_le (by norm_num)) (hYglob.of_le (by norm_num)) hσglob
      hXy hYy hσcoeff hcoeff_eq
  rw [hgerm, htens]

/-- **Continuity of the bundled curvature tensor contracted along `ContMDiffOn` frame fields.**
For a `C¹` tangent connection and vector fields `ea`, `eb`, `ec` that are `C²` on an open set `u`, the
`TM`-section `z ↦ curvatureTensor z (ea z) (eb z) (ec z)` is *continuous* on `u`.  Immediate from the
raw commutator continuity `curvatureAux_contMDiffOn_zero` and the pointwise identification
`curvatureAux_apply_eq_curvatureTensor_of_contMDiffOn_frame`.  This closes Step 2 of the
Ricci-tensor-section route: `curvatureTensor` in local smooth frames is a continuous bundle section. -/
theorem curvatureTensor_contMDiffOn_frame_zero
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {ea eb ec : Π x : M, TangentSpace I x} {u : Set M} (hu : IsOpen u)
    (hea : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun z ↦ TotalSpace.mk' E z (ea z)) u)
    (heb : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun z ↦ TotalSpace.mk' E z (eb z)) u)
    (hec : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun z ↦ TotalSpace.mk' E z (ec z)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) 0
      (fun z ↦ TotalSpace.mk' E z
        (CovariantDerivative.curvatureTensor (cov := cov) z (ea z) (eb z) (ec z))) u := by
  have hcurv := curvatureAux_contMDiffOn_zero (cov := cov) hu hea heb hec
  refine hcurv.congr ?_
  intro z hz
  exact congrArg (TotalSpace.mk' E z)
    (curvatureAux_apply_eq_curvatureTensor_of_contMDiffOn_frame hu hz hea heb hec).symm

/-- A `C²` tangent connection has a `C¹` bundled curvature tensor when evaluated on two local
`C²` frame fields and one local `C³` frame field. -/
theorem curvatureTensor_contMDiffOn_frame_one
    [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
    [_root_.Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 2]
    {ea eb ec : Π x : M, TangentSpace I x} {u : Set M} (hu : IsOpen u)
    (hea : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun z ↦ TotalSpace.mk' E z (ea z)) u)
    (heb : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (fun z ↦ TotalSpace.mk' E z (eb z)) u)
    (hec : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3 (fun z ↦ TotalSpace.mk' E z (ec z)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
      (fun z ↦ TotalSpace.mk' E z
        (CovariantDerivative.curvatureTensor (cov := cov) z (ea z) (eb z) (ec z))) u := by
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  haveI : IsManifold I (minSmoothness ℝ 3) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  haveI : IsManifold I (minSmoothness ℝ 4) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  haveI : IsManifold I ((2 : ℕ∞) + 1) M :=
    IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by exact_mod_cast le_top)
  haveI : IsManifold I ((3 : ℕ∞) + 1) M :=
    IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by exact_mod_cast le_top)
  have hcurv := CovariantDerivative.curvatureAux_contMDiffOn_one cov hu hea heb hec
  refine hcurv.congr ?_
  intro z hz
  exact congrArg (TotalSpace.mk' E z)
    (curvatureAux_apply_eq_curvatureTensor_of_contMDiffOn_frame hu hz hea heb
      (hec.of_le (by norm_num))).symm

/-- **Finite-dimensional reconstruction continuity for `E →L G`-valued maps.**
If `E` and `G` are finite-dimensional and `b` is a basis of `E`, then a map `f : M → (E →L[ℝ] G)`
is continuous on `t` as soon as each basis evaluation `x ↦ f x (b i)` is.  The continuous linear map
is reconstructed from its finitely-many basis values via `Basis.constrL`, which is continuous because
`ι → G` is finite-dimensional. -/
theorem continuousOn_clm_of_forall_apply_basis
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {t : Set M} {f : M → (E →L[ℝ] G)}
    (h : ∀ i, ContinuousOn (fun x ↦ f x (b i)) t) :
    ContinuousOn f t := by
  classical
  have hrec : ∀ x : M, f x = b.constrL (fun i ↦ f x (b i)) := by
    intro x
    apply ContinuousLinearMap.coe_injective
    refine b.ext (fun i ↦ ?_)
    simp only [ContinuousLinearMap.coe_coe, Module.Basis.constrL_basis]
  set recon : (ι → G) →ₗ[ℝ] (E →L[ℝ] G) :=
    (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] G) ≃ₗ[ℝ] (E →L[ℝ] G)).toLinearMap.comp
      (b.constr ℝ : (ι → G) ≃ₗ[ℝ] (E →ₗ[ℝ] G)).toLinearMap with hreconDef
  have hrecon_apply : ∀ g : ι → G, recon g = b.constrL g := by
    intro g; rfl
  have hcont : Continuous recon := recon.continuous_of_finiteDimensional
  have hg : ContinuousOn (fun x : M ↦ (fun i ↦ f x (b i) : ι → G)) t :=
    continuousOn_pi.mpr h
  have hcomp : ContinuousOn (fun x : M ↦ recon (fun i ↦ f x (b i))) t :=
    hcont.comp_continuousOn hg
  refine hcomp.congr (fun x _ ↦ ?_)
  change f x = recon (fun i ↦ f x (b i))
  rw [hrecon_apply, ← hrec x]

/-- **Frame-component continuity criterion for `BilinearFormBundle` sections.**
A section `s` of the tangent bilinear-form bundle is a *continuous* section as soon as, for every
base point `x0` and every pair of model-basis indices `i, j`, the scalar function
`x ↦ s x (localFrame b i x) (localFrame b j x)` is continuous on the trivialization base set at `x0`
(here `localFrame b i` is the `C²` frame field induced by the trivialization at `x0`).  Continuity is
local, so at each `x0` we read the section in the preferred coordinates
(`trivializationAt_bilinearFormBundle_apply_eq`), reconstruct the coordinate bilinear form from its
finitely-many frame evaluations via `continuousOn_clm_of_forall_apply_basis` applied twice, and
transfer through `Bundle.contMDiffAt_section`. -/
theorem contMDiff_zero_bilinearFormBundleSection_of_forall_localFrame
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {s : Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x}
    (hcomp : ∀ (x0 : M) (i j : ι),
      ContinuousOn (fun x ↦ s x ((trivializationAt E TM x0).localFrame b i x)
        ((trivializationAt E TM x0).localFrame b j x)) (trivializationAt E TM x0).baseSet) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := _root_.Bundle.BilinearFormBundle (V := TM)) x (s x)) := by
  classical
  intro x0
  rw [Bundle.contMDiffAt_section (IB := I) (F := (E →L[ℝ] E →L[ℝ] ℝ))
    (E := _root_.Bundle.BilinearFormBundle (V := TM)) (s := s) x0]
  set e := trivializationAt E TM x0 with he
  have hx0 : x0 ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E TM x0
  have hcontOn : ContinuousOn
      (fun x ↦ (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (_root_.Bundle.BilinearFormBundle (V := TM)) x0 ⟨x, s x⟩).2) e.baseSet := by
    refine continuousOn_clm_of_forall_apply_basis (E := E) b (fun i ↦ ?_)
    refine continuousOn_clm_of_forall_apply_basis (E := E) b (fun j ↦ ?_)
    refine (hcomp x0 i j).congr (fun x hx ↦ ?_)
    have hxe : x ∈ e.baseSet := hx
    rw [trivializationAt_bilinearFormBundle_apply_eq (F := E) (W := TM) x0 x hxe (s x) (b i) (b j)]
    have hli : ∀ k, ((e.continuousLinearEquivAt ℝ x hxe).symm (b k)) = e.localFrame b k x := by
      intro k
      rw [e.localFrame_apply_of_mem_baseSet b hxe]
      rfl
    rw [hli i, hli j]
  have hCM : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) 0
      (fun x ↦ (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (_root_.Bundle.BilinearFormBundle (V := TM)) x0 ⟨x, s x⟩).2) e.baseSet := by
    rw [contMDiffOn_zero_iff]; exact hcontOn
  exact hCM.contMDiffAt (e.open_baseSet.mem_nhds hx0)

/-- The local-frame coefficient linear functional coincides with the basis representation coefficient
for the induced basis on a trivialization fiber.  This is the section-free form of the (`@[simp]`)
`localFrameCoeff_apply_of_mem_baseSet`, obtained by evaluating the latter at a section pinned to the
value `V` at `x`. -/
lemma repr_basisAt_eq_localFrameCoeff
    {ι : Type*} (b : Module.Basis ι ℝ E) (x0 : M)
    {x : M} (hx : x ∈ (trivializationAt E TM x0).baseSet) (V : TM x) (k : ι) :
    ((trivializationAt E TM x0).basisAt b hx).repr V k
      = (trivializationAt E TM x0).localFrameCoeff I b k x V := by
  classical
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    ContMDiffVectorBundle.of_le (n := 2) (by norm_num)
  have h := (trivializationAt E TM x0).localFrameCoeff_apply_of_mem_baseSet (I := I) b hx
    (Function.update (0 : Π y : M, TM y) x V) k
  simpa using h.symm

/-- **Trace expansion of Ricci curvature in a local trivialization frame.**
For `x` in the trivialization base set at `x0`, the Ricci curvature is the frame trace of the
curvature endomorphism: `ricci x u w = ∑ₖ εᵏ(x) (R(eₖ x, u) w)`, where `eₖ = localFrame b k` is the
induced frame and `εᵏ = localFrameCoeff b k` the dual coframe.  The trace is metric-independent
(`LinearMap.trace_eq_matrix_trace` over the frame basis), so any `RiemannianBundle` instance works. -/
lemma ricciCurvature_eq_sum_localFrameCoeff
    [_root_.Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [cov.ContMDiffCovariantDerivative 1]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E) (x0 : M)
    {x : M} (hx : x ∈ (trivializationAt E TM x0).baseSet) (u w : TM x) :
    CovariantDerivative.ricciCurvature (cov := cov) x u w =
      ∑ k, (trivializationAt E TM x0).localFrameCoeff I b k x
        (CovariantDerivative.curvatureTensor (cov := cov) x
          ((trivializationAt E TM x0).localFrame b k x) u w) := by
  classical
  rw [CovariantDerivative.ricciCurvature_apply,
    LinearMap.trace_eq_matrix_trace ℝ ((trivializationAt E TM x0).basisAt b hx), Matrix.trace]
  refine Finset.sum_congr rfl (fun k _ ↦ ?_)
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply,
    CovariantDerivative.ricciEndomorphism_apply,
    (trivializationAt E TM x0).localFrame_apply_of_mem_baseSet b hx]
  exact repr_basisAt_eq_localFrameCoeff b x0 hx _ k

/-- The intrinsic Ricci tensor packaged as a genuine `BilinearFormBundle` (i.e. continuous-linear)
section: the linear-map-valued Ricci curvature `ricciCurvature cov x : TM x →ₗ TM x →ₗ ℝ` is promoted
to `TM x →L TM x →L ℝ` fiberwise via the finite-dimensional `LinearMap.toContinuousLinearMap`. -/
noncomputable def ricciBilinearFormSection
    [_root_.Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative 1] :
    Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x :=
  fun x ↦ LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := TangentSpace I x) (F' := ℝ)).toLinearMap.comp
      (CovariantDerivative.ricciCurvature (cov := cov) x))

@[simp] lemma ricciBilinearFormSection_apply
    [_root_.Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative 1] (x : M) (u v : TM x) :
    ricciBilinearFormSection (I := I) (M := M) cov x u v =
      CovariantDerivative.ricciCurvature (cov := cov) x u v := rfl

/-- **The intrinsic Ricci tensor is a continuous `BilinearFormBundle` section.**
Continuity is established via the frame-component criterion
`contMDiff_zero_bilinearFormBundleSection_of_forall_localFrame`: at each base point `x0`, the
scalar `x ↦ ricci x (eᵢ x) (eⱼ x)` is expanded by the frame trace formula
`ricciCurvature_eq_sum_localFrameCoeff` into a finite sum of `localFrameCoeff` applied to
`curvatureTensor x (eₖ x)(eᵢ x)(eⱼ x)`; each summand is continuous because the frame contraction of
the curvature tensor is a continuous `TM`-section (`curvatureTensor_contMDiffOn_frame_zero`) and the
coframe coefficient of a continuous section is continuous (`contMDiffOn_localFrameCoeff` at `k = 0`).
This supplies the last outstanding input — the continuous Ricci section `rs` — to
`exists_intrinsicRicciDeTurckRHSSection_contMDiff_zero_of_ricciSection`. -/
theorem ricciBilinearFormSection_contMDiff_zero
    [_root_.Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative 1]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := _root_.Bundle.BilinearFormBundle (V := TM)) x
        (ricciBilinearFormSection (I := I) (M := M) cov x)) := by
  classical
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    ContMDiffVectorBundle.of_le (n := 2) (by norm_num)
  refine contMDiff_zero_bilinearFormBundleSection_of_forall_localFrame b (fun x0 i j ↦ ?_)
  have hbase : IsOpen (trivializationAt E TM x0).baseSet := (trivializationAt E TM x0).open_baseSet
  have hframe : ∀ m : ι, ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
      (fun x ↦ TotalSpace.mk' E x ((trivializationAt E TM x0).localFrame b m x))
      (trivializationAt E TM x0).baseSet :=
    fun m ↦ (trivializationAt E TM x0).contMDiffOn_localFrame_baseSet (I := I) (n := 2) b m
  have hsum : Set.EqOn
      (fun x ↦ ricciBilinearFormSection (I := I) (M := M) cov x
        ((trivializationAt E TM x0).localFrame b i x) ((trivializationAt E TM x0).localFrame b j x))
      (fun x ↦ ∑ k, (trivializationAt E TM x0).localFrameCoeff I b k x
        (CovariantDerivative.curvatureTensor (cov := cov) x
          ((trivializationAt E TM x0).localFrame b k x)
          ((trivializationAt E TM x0).localFrame b i x)
          ((trivializationAt E TM x0).localFrame b j x)))
      (trivializationAt E TM x0).baseSet := by
    intro x hx
    dsimp only
    rw [ricciBilinearFormSection_apply]
    exact ricciCurvature_eq_sum_localFrameCoeff b x0 hx
      ((trivializationAt E TM x0).localFrame b i x) ((trivializationAt E TM x0).localFrame b j x)
  refine ContinuousOn.congr ?_ hsum
  refine continuousOn_finset_sum Finset.univ (fun k _ ↦ ?_)
  have hcurv := curvatureTensor_contMDiffOn_frame_zero (cov := cov) hbase
    (hframe k) (hframe i) (hframe j)
  have hcoeff := contMDiffOn_localFrameCoeff (I := I) (e := trivializationAt E TM x0) (b := b)
    (k := (0 : WithTop ℕ∞)) hbase (subset_refl _) hcurv k
  exact hcoeff.continuousOn

/-- The intrinsic Ricci tensor of a `C²` tangent connection is `C¹` as a genuine covariant
two-tensor section.  This regularity is derived from the actual curvature tensor in a genuine local
frame, rather than assumed as an independent analytic input. -/
theorem ricciBilinearFormSection_contMDiff_one
    [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
    [_root_.Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]
    {iota : Type*} [Fintype iota] [DecidableEq iota] (b : Module.Basis iota ℝ E) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := _root_.Bundle.BilinearFormBundle (V := TM)) x
        (ricciBilinearFormSection (I := I) (M := M) cov x)) := by
  classical
  intro x0
  refine CovariantDerivative.contMDiffAt_one_covariantTwoTensor_of_localFrame
    (ricciBilinearFormSection (I := I) (M := M) cov) x0 b ?_
  intro i j
  let e := trivializationAt E TM x0
  have hbase : IsOpen e.baseSet := e.open_baseSet
  have hx0 : x0 ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E TM x0
  have hframe2 : ∀ m : iota, ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
      (fun x ↦ TotalSpace.mk' E x (e.localFrame b m x)) e.baseSet :=
    fun m ↦ e.contMDiffOn_localFrame_baseSet (I := I) (n := 2) b m
  have hframe3 : ∀ m : iota, ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3
      (fun x ↦ TotalSpace.mk' E x (e.localFrame b m x)) e.baseSet :=
    fun m ↦ e.contMDiffOn_localFrame_baseSet (I := I) (n := 3) b m
  let term : iota → M → ℝ := fun k x ↦
    e.localFrameCoeff I b k x
      (CovariantDerivative.curvatureTensor (cov := cov) x
        (e.localFrame b k x) (e.localFrame b i x) (e.localFrame b j x))
  have hterm : ∀ k, ContMDiffOn I 𝓘(ℝ) 1 (term k) e.baseSet := by
    intro k
    have hcurv := curvatureTensor_contMDiffOn_frame_one (cov := cov) hbase
      (hframe2 k) (hframe2 i) (hframe3 j)
    simpa [term] using
      (contMDiffOn_localFrameCoeff (I := I) (e := e) (b := b)
        (k := (1 : WithTop ℕ∞)) hbase (subset_refl _) hcurv k)
  have hsum : ∀ s : Finset iota,
      ContMDiffOn I 𝓘(ℝ) 1 (fun x ↦ s.sum (fun k ↦ term k x)) e.baseSet := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using
        (contMDiffOn_const : ContMDiffOn I 𝓘(ℝ) 1 (fun _ : M ↦ (0 : ℝ)) e.baseSet)
    | @insert k s hk hs =>
        convert (hterm k).add hs using 1 <;> ext x <;>
          simp only [Finset.sum_insert, hk, not_false_eq_true, Pi.add_apply]
  have hreg := (hsum Finset.univ).contMDiffAt (hbase.mem_nhds hx0)
  refine hreg.congr_of_eventuallyEq ?_
  filter_upwards [hbase.mem_nhds hx0] with x hx
  change ricciBilinearFormSection (I := I) (M := M) cov x (e.localFrame b i x)
      (e.localFrame b j x) = (∑ k, term k x)
  rw [ricciBilinearFormSection_apply,
    ricciCurvature_eq_sum_localFrameCoeff b x0 hx]

/-- Pointwise differentiability of the canonical covariant Ricci tensor, with no independent Ricci
regularity assumption. -/
theorem ricciCovariantTwoTensor_mdifferentiableAt
    [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
    [_root_.Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]
    (x : M) :
    MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) y
        (CovariantDerivative.ricciCovariantTwoTensor cov y)) x := by
  have h := ricciBilinearFormSection_contMDiff_one (I := I) (M := M) cov
    (Module.finBasis ℝ E)
  refine ((h x).mdifferentiableAt one_ne_zero).congr_of_eventuallyEq ?_
  filter_upwards [] with y
  apply congrArg (fun B ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
    (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) y B)
  ext u v
  rfl

/-- Pointwise differentiability of the genuine metric-raised Ricci endomorphism, derived from the
`C¹` covariant Ricci tensor and the regularity of the Riemannian Riesz map. -/
theorem raisedRicciEndomorphism_mdifferentiableAt
    [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
    [_root_.Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]
    (x₀ : M) :
    MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z) y
        (CovariantDerivative.raisedRicciEndomorphism cov y)) x₀ := by
  classical
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  let b := Module.finBasis ℝ E
  have hRicci := ricciBilinearFormSection_contMDiff_one (I := I) (M := M) cov b
  have hframe : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (e.localFrame b i y)) e.baseSet :=
    fun i ↦ e.contMDiffOn_localFrame_baseSet (I := I) (n := 1) b i
  refine (contMDiffAt_homBundle_of_forall_apply_localFrame
    (IB := I) (E₁ := TangentSpace I) (E₂ := TangentSpace I) x₀ b ?_).mdifferentiableAt
      one_ne_zero
  intro i
  let omega : ∀ y : M, TangentSpace I y →L[ℝ] ℝ := fun y ↦
    CovariantDerivative.ricciCovariantTwoTensor cov y (e.localFrame b i y)
  have homega : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] ℝ) y (omega y)) e.baseSet := by
    have happ := hRicci.contMDiffOn.clm_bundle_apply (hframe i)
    simpa [omega, ricciBilinearFormSection,
      CovariantDerivative.ricciCovariantTwoTensor] using happ
  have hraised := CovariantDerivative.contMDiffOn_rieszMap_section
    (I := I) (E := E) e b e.open_baseSet (Set.Subset.rfl) homega
  have hat := hraised.contMDiffAt
    (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt E _ x₀))
  refine hat.congr_of_eventuallyEq ?_
  filter_upwards [] with y
  apply congrArg (TotalSpace.mk' E y)
  rfl

/-- The regularity predicate used by the differentiated Ricci-trace API follows from curvature
regularity; it is not an additional hypothesis on Ricci. -/
theorem raisedRicciEndomorphismMDiffAt_of_curvature
    [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
    [_root_.Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]
    (x : M) : CovariantDerivative.raisedRicciEndomorphismMDiffAt cov x := by
  unfold CovariantDerivative.raisedRicciEndomorphismMDiffAt
  exact raisedRicciEndomorphism_mdifferentiableAt (I := I) (M := M) cov x

/-! The scalar-curvature regularity needed by the parabolic layer is also a
consequence of the genuine curvature contraction.  Keeping this as a
separate theorem makes the trace bridge reusable without asking downstream
proofs to postulate differentiability of a scalar readout. -/

theorem scalarCurvature_mdifferentiableAt_of_curvature
    [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
    [_root_.Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]
    (x : M) :
    MDiffAt (CovariantDerivative.scalarCurvature (cov := cov)) x := by
  have hA := raisedRicciEndomorphismMDiffAt_of_curvature
    (I := I) (M := M) cov x
  have htrace := CovariantDerivative.mdifferentiableAt_endomorphismTrace
    (I := I) (F := E) (V := (TangentSpace I : M → Type _)) hA
  refine htrace.congr_of_eventuallyEq ?_
  filter_upwards [] with y
  exact (CovariantDerivative.endomorphismTrace_raisedRicciEndomorphism_eq_scalarCurvature
    (I := I) (M := M) cov y).symm

/-- **The intrinsic Ricci–DeTurck right-hand side is a continuous `BilinearFormBundle` section,
unconditionally** (for a `C¹` background connection slice).  This removes the last hypothesis of
`exists_intrinsicRicciDeTurckRHSSection_contMDiff_zero_of_ricciSection` by *supplying* its Ricci
section input `rs := ricciBilinearFormSection (someContMDiffLeviCivitaConnection g t)` together with
its just-proved continuity `ricciBilinearFormSection_contMDiff_zero` — so the geometric operator `A`'s
value section is now known to be a genuine continuous `BilinearFormBundle` section with **no** assumed
Ricci-section hypothesis.  This closes the geometric-`A` **value-section** regularity (GAP 2); the
remaining `A`-side obstruction is the `picard` Lipschitz/centre bounds for the mild/regularised
representative. -/
theorem exists_intrinsicRicciDeTurckRHSSection_contMDiff_zero
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1) :
    ∃ rhs : Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x,
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := _root_.Bundle.BilinearFormBundle (V := TM)) x (rhs x)) ∧
      ∀ (x : M) (u v : TM x),
        rhs x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x u v := by
  letI : _root_.Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g t).toRiemannianMetric⟩
  haveI hcov :=
    CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g t
  refine exists_intrinsicRicciDeTurckRHSSection_contMDiff_zero_of_ricciSection
    g background t hbackground
    (ricciBilinearFormSection (I := I) (M := M)
      (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
        (I := I) (M := M) g t))
    ?_ ?_
  · exact ricciBilinearFormSection_contMDiff_zero (I := I) (M := M)
      (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
        (I := I) (M := M) g t) (Module.finBasis ℝ E)
  · intro x u v
    rw [ricciBilinearFormSection_apply]
    rfl

open PoincareCurvature.Bundle.Trivialization in
/-- **The intrinsic Ricci–DeTurck RHS as a genuine section-space element.**  For a metric family
`g` and a background connection family whose time-`t` slice is a `C¹` covariant derivative, the
intrinsic Ricci–DeTurck right-hand side `x ↦ intrinsicRicciDeTurckRHS g background t x` — already
known to be a continuous `BilinearFormBundle` section by
`exists_intrinsicRicciDeTurckRHSSection_contMDiff_zero` — packages into an element of the transported
finite-cover `ContinuousSectionSpace`.  This is the *value/output side* of the geometric Ricci–DeTurck
chart operator `A`: for the geometric chart, `A τ s` must be an element of this section space equal
pointwise to the geometric RHS, which is exactly the identification asserted by the chart's `geometric`
field.  The packaging is the honest bridge from the (bundle-level) value-section regularity to the
Banach section space `CSS` in which the chart operator lives; the surviving geometric-`A` obstruction is
the operator's *dependence on the input section* (and its `picard`/mild bounds), not the regularity of
its values. -/
theorem exists_intrinsicRicciDeTurckRHS_continuousSectionSpace
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1) :
    ∃ rhsCSS : ContinuousSectionSpace (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ)
        (V := _root_.Bundle.BilinearFormBundle (V := TM)) et Kc hKc Ko hKo hKoEq hcover,
      ∀ (x : M) (u v : TM x),
        rhsCSS x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x u v := by
  obtain ⟨rhs, hrhs_cont, hrhs_val⟩ :=
    exists_intrinsicRicciDeTurckRHSSection_contMDiff_zero g background t hbackground
  exact ⟨⟨rhs, hrhs_cont.continuous⟩, hrhs_val⟩

open PoincareCurvature.Bundle.Trivialization in
/-- **The section-space packaging of the intrinsic Ricci–DeTurck RHS is pointwise symmetric.**  A
strengthening of `exists_intrinsicRicciDeTurckRHS_continuousSectionSpace` recording that the packaged
`ContinuousSectionSpace` value is a *symmetric* bilinear-form section — i.e. it lies in the pointwise
symmetric locus `{s | ∀ x v w, s x v w = s x w v}`.  This is the honest symmetry content the geometric
Ricci–DeTurck chart exploits (`A τ s ∈ symmetricLocus`), obtained from the intrinsic
`intrinsicRicciDeTurckRHS_symm` (Ricci and the symmetrized DeTurck reaction are both symmetric) through
the value identification, with no assumption beyond the ambient higher smoothness of `M`. -/
theorem exists_intrinsicRicciDeTurckRHS_continuousSectionSpace_symm
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1) :
    ∃ rhsCSS : ContinuousSectionSpace (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ)
        (V := _root_.Bundle.BilinearFormBundle (V := TM)) et Kc hKc Ko hKo hKoEq hcover,
      (∀ (x : M) (u v : TM x),
          rhsCSS x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x u v) ∧
      (∀ (x : M) (u v : TM x), rhsCSS x u v = rhsCSS x v u) := by
  obtain ⟨rhs, hrhs_cont, hrhs_val⟩ :=
    exists_intrinsicRicciDeTurckRHSSection_contMDiff_zero g background t hbackground
  refine ⟨⟨rhs, hrhs_cont.continuous⟩, hrhs_val, fun x u v => ?_⟩
  calc rhs x u v
      = intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x u v := hrhs_val x u v
    _ = intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x v u :=
        intrinsicRicciDeTurckRHS_symm (I := I) (M := M) g background t x u v
    _ = rhs x v u := (hrhs_val x v u).symm

open PoincareCurvature.Bundle.Trivialization in
/-- **The intrinsic Ricci–DeTurck RHS as a named section-space value.**  The `def`-level companion of
`exists_intrinsicRicciDeTurckRHS_continuousSectionSpace`: for a metric family `g`, a background
connection family whose time-`t` slice is a `C¹` covariant derivative, this is the geometric
Ricci–DeTurck right-hand side realised as a genuine element of the transported finite-cover
`ContinuousSectionSpace`.  Having a *named* section-space value (rather than a bare existential) is what
the geometric chart operator `A` and the mild-affine source term `b` can reference directly; its
defining pointwise identity is `intrinsicRicciDeTurckRHSSectionSpace_apply`. -/
noncomputable def intrinsicRicciDeTurckRHSSectionSpace
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1) :
    ContinuousSectionSpace (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ)
      (V := _root_.Bundle.BilinearFormBundle (V := TM)) et Kc hKc Ko hKo hKoEq hcover :=
  ⟨Classical.choose
      (exists_intrinsicRicciDeTurckRHSSection_contMDiff_zero g background t hbackground),
    (Classical.choose_spec
      (exists_intrinsicRicciDeTurckRHSSection_contMDiff_zero g background t hbackground)).1.continuous⟩

open PoincareCurvature.Bundle.Trivialization in
/-- The named section-space Ricci–DeTurck RHS value agrees pointwise with the intrinsic
`intrinsicRicciDeTurckRHS`.  This is the defining identity that ties the section-space value to the
geometric right-hand side (the chart's `geometric` field content). -/
@[simp] theorem intrinsicRicciDeTurckRHSSectionSpace_apply
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (x : M) (u v : TM x) :
    intrinsicRicciDeTurckRHSSectionSpace et Kc hKc Ko hKo hKoEq hcover g background t hbackground x u v
      = intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x u v :=
  (Classical.choose_spec
    (exists_intrinsicRicciDeTurckRHSSection_contMDiff_zero g background t hbackground)).2 x u v

open PoincareCurvature.Bundle.Trivialization in
/-- The named section-space Ricci–DeTurck RHS value is pointwise symmetric (it lies in the pointwise
symmetric locus), a direct consequence of `intrinsicRicciDeTurckRHS_symm`. -/
theorem intrinsicRicciDeTurckRHSSectionSpace_symm
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (x : M) (u v : TM x) :
    intrinsicRicciDeTurckRHSSectionSpace et Kc hKc Ko hKo hKoEq hcover g background t hbackground x u v
      = intrinsicRicciDeTurckRHSSectionSpace et Kc hKc Ko hKo hKoEq hcover
          g background t hbackground x v u := by
  rw [intrinsicRicciDeTurckRHSSectionSpace_apply, intrinsicRicciDeTurckRHSSectionSpace_apply,
    intrinsicRicciDeTurckRHS_symm]

open PoincareCurvature.Bundle.Trivialization in
/-- **Section-space self-DeTurck reduction (general Levi-Civita background).**  The section-space
companion of `intrinsicRicciDeTurckRHS_eq_intrinsicRicciFlowRHS_of_isLeviCivita`: when the background
connection family is Levi-Civita for `g`, the named section-space Ricci–DeTurck RHS value reads out
pointwise as the pure intrinsic Ricci-flow right-hand side `(-2)•Ric`.  The DeTurck reaction term
vanishes in the metric's Levi-Civita gauge, so the affine chart split `A τ s = reaction s + b`
degenerates to its principal source `b` on the identification. -/
theorem intrinsicRicciDeTurckRHSSectionSpace_apply_eq_intrinsicRicciFlowRHS_of_isLeviCivita
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (hLC : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g background)
    (x : M) (u v : TM x) :
    intrinsicRicciDeTurckRHSSectionSpace et Kc hKc Ko hKo hKoEq hcover g background t hbackground x u v
      = intrinsicRicciFlowRHS (I := I) (M := M) g t x u v := by
  rw [intrinsicRicciDeTurckRHSSectionSpace_apply]
  exact congrArg (fun F => F t x u v)
    (intrinsicRicciDeTurckRHS_eq_intrinsicRicciFlowRHS_of_isLeviCivita
      (I := I) (M := M) g background hLC)

open PoincareCurvature.Bundle.Trivialization in
/-- **Section-space self-DeTurck reduction at the chosen Levi-Civita background.**  The directly
consumable specialization of `intrinsicRicciDeTurckRHSSectionSpace_apply_eq_intrinsicRicciFlowRHS_of_isLeviCivita`
to `background := chosenLeviCivitaFamily g` (with the canonical `C¹` witness
`someContMDiffLeviCivitaConnection_contMDiff`, and Levi-Civita hypothesis discharged by
`chosenLeviCivitaFamily_isLeviCivita`).  This is the exact section-space form the chart-closure
identification consumes when the background is the flowing metric's own chosen Levi-Civita
connection. -/
theorem intrinsicRicciDeTurckRHSSectionSpace_chosenLeviCivitaFamily_apply_eq_intrinsicRicciFlowRHS
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (t : ℝ)
    (x : M) (u v : TM x) :
    intrinsicRicciDeTurckRHSSectionSpace et Kc hKc Ko hKo hKoEq hcover g
        (chosenLeviCivitaFamily (I := I) (M := M) g) t
        (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
          (I := I) (M := M) g t)
        x u v
      = intrinsicRicciFlowRHS (I := I) (M := M) g t x u v :=
  intrinsicRicciDeTurckRHSSectionSpace_apply_eq_intrinsicRicciFlowRHS_of_isLeviCivita
    et Kc hKc Ko hKo hKoEq hcover g (chosenLeviCivitaFamily (I := I) (M := M) g) t
    (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g t)
    (chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M) g)
    x u v

/-- **The intrinsic Ricci-flow principal part `(-2)•Ric` is a continuous `BilinearFormBundle`
section**, unconditionally (no background hypothesis).  This is the second-order principal half of the
intrinsic Ricci–DeTurck right-hand side split off from the DeTurck reaction: its continuous section is
`(-2 : ℝ) • ricciBilinearFormSection (someContMDiffLeviCivitaConnection g t)`, continuous by
`ricciBilinearFormSection_contMDiff_zero` and the vector-bundle scalar-multiple closure
`ContMDiff.const_smul_section`.  Packaged as a `ContinuousSectionSpace` value
(`intrinsicRicciFlowRHSSectionSpace`) it is the affine *source* term `b` of the frozen chart split
`A τ s = reaction s + b` about the initial metric. -/
theorem exists_intrinsicRicciFlowRHSSection_contMDiff_zero
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) :
    ∃ rhs : Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x,
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := _root_.Bundle.BilinearFormBundle (V := TM)) x (rhs x)) ∧
      ∀ (x : M) (u v : TM x),
        rhs x u v = intrinsicRicciFlowRHS (I := I) (M := M) g t x u v := by
  letI : _root_.Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g t).toRiemannianMetric⟩
  haveI hcov :=
    CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g t
  refine ⟨_, (ricciBilinearFormSection_contMDiff_zero (I := I) (M := M)
      (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
        (I := I) (M := M) g t) (Module.finBasis ℝ E)).const_smul_section (a := (-2 : ℝ)), ?_⟩
  intro x u v
  have hval : ricciBilinearFormSection (I := I) (M := M)
      (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
        (I := I) (M := M) g t) x u v = intrinsicRicciTensor (I := I) (M := M) g t x u v := by
    rw [ricciBilinearFormSection_apply]; rfl
  simp only [Pi.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hval,
    intrinsicRicciFlowRHS_apply, ricciFlowRHS_apply, intrinsicRicciTensor_apply]

open PoincareCurvature.Bundle.Trivialization in
/-- **The intrinsic Ricci-flow principal part as a named section-space value.**  The `def`-level
companion of `exists_intrinsicRicciFlowRHSSection_contMDiff_zero`: the second-order principal part
`(-2)•Ric` of the intrinsic Ricci–DeTurck right-hand side realised as a genuine element of the
transported finite-cover `ContinuousSectionSpace`.  Unlike `intrinsicRicciDeTurckRHSSectionSpace` it
needs **no** background-connection hypothesis (the intrinsic Levi-Civita connection is automatically
`C¹`).  This is the directly referenceable affine *source* `b` for the frozen chart split
`A τ s = reaction s + b`; its defining pointwise identity is `intrinsicRicciFlowRHSSectionSpace_apply`. -/
noncomputable def intrinsicRicciFlowRHSSectionSpace
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) :
    ContinuousSectionSpace (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ)
      (V := _root_.Bundle.BilinearFormBundle (V := TM)) et Kc hKc Ko hKo hKoEq hcover :=
  ⟨Classical.choose (exists_intrinsicRicciFlowRHSSection_contMDiff_zero g t),
    (Classical.choose_spec (exists_intrinsicRicciFlowRHSSection_contMDiff_zero g t)).1.continuous⟩

open PoincareCurvature.Bundle.Trivialization in
/-- The named section-space Ricci-flow principal value agrees pointwise with the intrinsic
`intrinsicRicciFlowRHS`.  The defining identity tying the affine source `b` to the geometric
second-order principal part. -/
@[simp] theorem intrinsicRicciFlowRHSSectionSpace_apply
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (t : ℝ)
    (x : M) (u v : TM x) :
    intrinsicRicciFlowRHSSectionSpace et Kc hKc Ko hKo hKoEq hcover g t x u v
      = intrinsicRicciFlowRHS (I := I) (M := M) g t x u v :=
  (Classical.choose_spec (exists_intrinsicRicciFlowRHSSection_contMDiff_zero g t)).2 x u v

open PoincareCurvature.Bundle.Trivialization in
/-- **The intrinsic DeTurck correction (the frozen reaction of the metric section) as a named
section-space value.**  The already-continuous zeroth-order DeTurck reaction section
`intrinsicDeTurckCorrectionSection` (continuous by `intrinsicDeTurckCorrectionSection_contMDiff_zero`)
packaged into the transported finite-cover `ContinuousSectionSpace`.  Together with
`intrinsicRicciFlowRHSSectionSpace` (the principal source `b`) it makes the geometric Ricci–DeTurck
right-hand side a genuine sum of two named `CSS` values; its defining pointwise identity is
`intrinsicDeTurckCorrectionSectionSpace_apply`. -/
noncomputable def intrinsicDeTurckCorrectionSectionSpace
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1) :
    ContinuousSectionSpace (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ)
      (V := _root_.Bundle.BilinearFormBundle (V := TM)) et Kc hKc Ko hKo hKoEq hcover :=
  ⟨intrinsicDeTurckCorrectionSection (I := I) (M := M) g background t,
    (intrinsicDeTurckCorrectionSection_contMDiff_zero (I := I) (M := M)
      g background t hbackground).continuous⟩

open PoincareCurvature.Bundle.Trivialization in
/-- The named section-space DeTurck correction value agrees pointwise with the geometric
`intrinsicDeTurckCorrection`. -/
@[simp] theorem intrinsicDeTurckCorrectionSectionSpace_apply
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (x : M) (u v : TM x) :
    intrinsicDeTurckCorrectionSectionSpace et Kc hKc Ko hKo hKoEq hcover g background t hbackground
        x u v
      = intrinsicDeTurckCorrection (I := I) (M := M) g background t x u v :=
  intrinsicDeTurckCorrectionSection_apply (I := I) (M := M) g background t x u v

open PoincareCurvature.Bundle.Trivialization in
/-- **The named geometric Ricci–DeTurck RHS value splits as principal source plus reaction, entirely in
named section-space values.**  The pointwise affine decomposition
`intrinsicRicciDeTurckRHSSectionSpace = intrinsicRicciFlowRHSSectionSpace +
intrinsicDeTurckCorrectionSectionSpace`: the geometric operator `A`'s value section equals the sum of
its second-order principal source `b` and its zeroth-order DeTurck reaction value, both packaged as
genuine `ContinuousSectionSpace` elements.  This is the directly-consumable named-value form of the
chart's frozen affine split `A τ s = reaction s + b` at the metric state. -/
theorem intrinsicRicciDeTurckRHSSectionSpace_eq_intrinsicRicciFlowRHSSectionSpace_add_intrinsicDeTurckCorrectionSectionSpace
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (x : M) (u v : TM x) :
    intrinsicRicciDeTurckRHSSectionSpace et Kc hKc Ko hKo hKoEq hcover g background t hbackground x u v
      = intrinsicRicciFlowRHSSectionSpace et Kc hKc Ko hKo hKoEq hcover g t x u v
        + intrinsicDeTurckCorrectionSectionSpace et Kc hKc Ko hKo hKoEq hcover
            g background t hbackground x u v := by
  rw [intrinsicRicciDeTurckRHSSectionSpace_apply, intrinsicRicciFlowRHSSectionSpace_apply,
    intrinsicDeTurckCorrectionSectionSpace_apply, intrinsicRicciDeTurckRHS_apply]

open PoincareCurvature.Bundle.Trivialization in
/-- **The intrinsic Ricci-flow principal source value is pointwise symmetric.**  The named
second-order source value `b = (-2)•Ric` of the affine chart split `A τ s = reaction s + b` lies in
the pointwise symmetric locus (the intrinsic Ricci tensor is symmetric, so its `(-2)`-multiple is too),
a direct consequence of `intrinsicRicciFlowRHS_symm`.  Unlike the full-RHS symmetry
`intrinsicRicciDeTurckRHSSectionSpace_symm` it needs **no** background-connection hypothesis (the
source carries none).  This is the symmetric-locus content of the chart split's principal source. -/
theorem intrinsicRicciFlowRHSSectionSpace_symm
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (t : ℝ)
    (x : M) (u v : TM x) :
    intrinsicRicciFlowRHSSectionSpace et Kc hKc Ko hKo hKoEq hcover g t x u v
      = intrinsicRicciFlowRHSSectionSpace et Kc hKc Ko hKo hKoEq hcover g t x v u := by
  rw [intrinsicRicciFlowRHSSectionSpace_apply, intrinsicRicciFlowRHSSectionSpace_apply]
  exact intrinsicRicciFlowRHS_symm (I := I) (M := M) g t x u v

open PoincareCurvature.Bundle.Trivialization in
/-- **The intrinsic DeTurck correction (reaction) value is pointwise symmetric.**  The named
zeroth-order reaction value of the affine chart split lies in the pointwise symmetric locus,
unconditionally (both derivation slots read out the metric-symmetric inner product), via
`intrinsicDeTurckCorrection_symm`.  This is the symmetric-locus content of the chart split's reaction
value; together with `intrinsicRicciFlowRHSSectionSpace_symm` it certifies that both named summands of
the geometric Ricci–DeTurck RHS lie in the symmetric locus. -/
theorem intrinsicDeTurckCorrectionSectionSpace_symm
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (x : M) (u v : TM x) :
    intrinsicDeTurckCorrectionSectionSpace et Kc hKc Ko hKo hKoEq hcover
        g background t hbackground x u v
      = intrinsicDeTurckCorrectionSectionSpace et Kc hKc Ko hKo hKoEq hcover
          g background t hbackground x v u := by
  rw [intrinsicDeTurckCorrectionSectionSpace_apply, intrinsicDeTurckCorrectionSectionSpace_apply]
  exact intrinsicDeTurckCorrection_symm (I := I) (M := M) g background t x u v


/-- The **frozen-coefficient symmetrized DeTurck reaction** of a generic `BilinearFormBundle`
section `s` with a tangent-endomorphism coefficient `P`:
`x ↦ (s x).comp (P x) + ((s x).comp (P x)).flip`, whose fiber value is
`(u, v) ↦ s x (P x u) v + s x (P x v) u`.  This is the generic-section analogue of
`intrinsicDeTurckCorrectionSection` (which is exactly this reaction of the *metric* section with
`P := ∇W`), written directly at the tangent bundle.  Unlike the abstract reaction operator
`ContinuousSectionSpace.bilinearDerivationFieldLinearMap`, this construction never requires the
`Π`-fiber-norm instance `[∀ x, SeminormedAddCommGroup (TangentSpace I x)]` (equivalently the
`FiberBundle E (TangentSpace I)` diamond), so it elaborates and is regular at `W := TangentSpace I`
via the fiber-norm-free bundle section algebra. -/
noncomputable def bilinearFormSectionDeTurckReaction
    (s : Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x)
    (P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x) :
    Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x :=
  @HAdd.hAdd
    (Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x)
    (Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x)
    (Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x) instHAdd
    (fun x ↦ (s x).comp (P x))
    (fun x ↦ ((s x).comp (P x)).flip)

@[simp] lemma bilinearFormSectionDeTurckReaction_apply
    (s : Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x)
    (P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
    (x : M) (u v : TM x) :
    bilinearFormSectionDeTurckReaction (I := I) (M := M) s P x u v
      = s x (P x u) v + s x (P x v) u := by
  simp only [bilinearFormSectionDeTurckReaction, Pi.add_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply]
  congr 1

/-- The frozen-coefficient symmetrized DeTurck reaction of a **continuous** `BilinearFormBundle`
section with a **continuous** tangent-endomorphism coefficient is again a continuous
`BilinearFormBundle` section, fiber-norm-free at the tangent bundle.  This is the generic-section
generalisation of `intrinsicDeTurckCorrectionSection_contMDiff_zero`, assembled from
`ContMDiff.clm_bundle_comp` (the composition `s ∘ P`), `contMDiff_flipBilinearFormSection_tangent_zero`
(the slot-flip), and `ContMDiff.add_section`.  It is the output-regularity that makes the frozen-`P`
reaction a well-defined operator on the tangent-bundle `ContinuousSectionSpace`. -/
theorem bilinearFormSectionDeTurckReaction_contMDiff_zero
    {s : Π x : M, _root_.Bundle.BilinearFormBundle (V := TM) x}
    (hs : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := _root_.Bundle.BilinearFormBundle (V := TM)) x (s x)))
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 0
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := _root_.Bundle.BilinearFormBundle (V := TM)) x
        (bilinearFormSectionDeTurckReaction (I := I) (M := M) s P x)) := by
  have h1 := hs.clm_bundle_comp hP
  have h2 := contMDiff_flipBilinearFormSection_tangent_zero h1
  exact h1.add_section h2


open PoincareCurvature.Bundle.Trivialization in
/-- The **frozen-coefficient DeTurck reaction operator on the tangent-bundle continuous section
space**.  For a continuous tangent-endomorphism coefficient `P` (typically the frozen DeTurck
coefficient `∇W`), this sends a continuous `BilinearFormBundle` section `s` to the continuous section
`x ↦ (s x).comp (P x) + ((s x).comp (P x)).flip`, whose fiber value is `(u, v) ↦ s(Pu, v) + s(Pv, u)`
(the symmetrized frozen-coefficient DeTurck derivation).  Its well-definedness (the output is a genuine
`ContinuousSectionSpace` element) is discharged by `bilinearFormSectionDeTurckReaction_contMDiff_zero`
through the `ContMDiff 0 ↔ Continuous` bridge, entirely fiber-norm-free.

This is the tangent-bundle (`W := TangentSpace I`) reaction operator that the abstract generic-fibre
operator `ContinuousSectionSpace.bilinearDerivationFieldLinearMap` cannot supply at `TM`, because the
latter demands the `Π`-fibre-norm instance `[∀ x, SeminormedAddCommGroup (TangentSpace I x)]`
(equivalently the un-synthesizable `FiberBundle E (TangentSpace I)` normed diamond).  Here the operator
is assembled directly from the fiber-norm-free bundle section algebra, so it lives on the concrete
`BilinearFormBundle` section space the Ricci–DeTurck chart operator `A` acts on. -/
noncomputable def deTurckReactionSectionMap
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x))) :
    ContinuousSectionSpace (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ)
        (V := _root_.Bundle.BilinearFormBundle (V := TM)) et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ)
        (V := _root_.Bundle.BilinearFormBundle (V := TM)) et Kc hKc Ko hKo hKoEq hcover :=
  fun s ↦ ⟨bilinearFormSectionDeTurckReaction (I := I) (M := M) s.toFun P,
    (bilinearFormSectionDeTurckReaction_contMDiff_zero (I := I) (M := M)
      (contMDiff_zero_iff.mpr s.continuous_toFun) (contMDiff_zero_iff.mpr hP)).continuous⟩

open PoincareCurvature.Bundle.Trivialization in
@[simp] lemma deTurckReactionSectionMap_apply
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ)
      (V := _root_.Bundle.BilinearFormBundle (V := TM)) et Kc hKc Ko hKo hKoEq hcover)
    (x : M) (u v : TM x) :
    deTurckReactionSectionMap (I := I) (M := M) et Kc hKc Ko hKo hKoEq hcover hP s x u v
      = s x (P x u) v + s x (P x v) u :=
  bilinearFormSectionDeTurckReaction_apply (I := I) (M := M) s.toFun P x u v

end RicciFlow
