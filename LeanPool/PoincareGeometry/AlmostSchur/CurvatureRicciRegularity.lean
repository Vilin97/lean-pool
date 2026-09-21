/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.LeviCivitaRegularityTwo
public import LeanPool.PoincareGeometry.AlmostSchur.EndomorphismFrameRegularity
public import LeanPool.PoincareGeometry.AlmostSchur.BundledRicciBochner

/-! # Local regularity of actual curvature and Ricci contractions

The connection hypotheses are geometric compatibility and torsion-freeness;
the regularity of the curvature expressions is derived, not assumed.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff Topology BigOperators
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 3 E (TangentSpace I : M → Type _)]
local notation "TM" => (TangentSpace I : M → Type _)
local instance curvatureRicciFiniteDimensional (x : M) : FiniteDimensional ℝ (TM x) :=
  VectorBundle.finiteDimensional ℝ E TM x

/-- The raw curvature of locally C³ tangent fields is locally C¹. -/
theorem contMDiffAt_curvatureAux_one (cov : CovariantDerivative I E TM)
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {X Y Z : Π y, TM y} {x : M}
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Y) x)
    (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Z) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1 (T% (cov.curvatureAux X Y Z)) x := by
  letI : IsManifold I (minSmoothness ℝ (3 : ℕ∞)) M :=
    IsManifold.of_le (n := ∞) (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)
  letI : IsManifold I ((3 : ℕ∞) + 1) M :=
    IsManifold.of_le (n := ∞) (by exact_mod_cast (le_top : (3 + 1 : ℕ∞) ≤ ⊤))
  have hYZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 (T% (cov.along Y Z)) x :=
    contMDiffAt_covariantAlong_of_metric_torsion_two cov hm ht hY hZ
  have hXZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 (T% (cov.along X Z)) x :=
    contMDiffAt_covariantAlong_of_metric_torsion_two cov hm ht hX hZ
  have h1 := contMDiffAt_covariantAlong_of_metric_torsion cov hm ht
    (hX.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)) hYZ
  have h2 := contMDiffAt_covariantAlong_of_metric_torsion cov hm ht
    (hY.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)) hXZ
  have hb : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 (T% (VectorField.mlieBracket I X Y)) x :=
    hX.mlieBracket_vectorField hY (m := 2) (n := 3) (by norm_num)
  have h3 := contMDiffAt_covariantAlong_of_metric_torsion cov hm ht hb
    (hZ.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3))
  exact (h1.sub_section h2).sub_section h3

/-- Evaluation of the actual bundled curvature tensor on C³ fields is C¹. -/
theorem contMDiffAt_curvatureTensor_apply_one
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {X Y Z : Π y, TM y} {x : M}
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Y) x)
    (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Z) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (T% (fun y ↦ cov.curvatureTensor y (X y) (Y y) (Z y))) x := by
  apply (contMDiffAt_curvatureAux_one cov hm ht hX hY hZ).congr_of_eventuallyEq
  filter_upwards [(contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hX,
    (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hY,
    (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hZ] with y hXy hYy hZy
  apply congrArg (TotalSpace.mk' E y)
  exact (curvatureAux_eq_curvatureTensor_of_contMDiffAt cov
    (hXy.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3))
    (hYy.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3))
    (hZy.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3))).symm

/-- The genuine Ricci-trace endomorphism, now viewed as a continuous linear map. -/
def ricciTraceEndomorphism (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1] (Y Z : Π y, TM y) (x : M) : TM x →L[ℝ] TM x :=
  (cov.ricciEndomorphism x (Y x) (Z x)).toContinuousLinearMap

/-- Full hom-bundle C¹ regularity of the endomorphism whose trace is Ricci. -/
theorem contMDiffAt_ricciTraceEndomorphism_one
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {Y Z : Π y, TM y} {x : M}
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Y) x)
    (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Z) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) (E := fun z ↦ TM z →L[ℝ] TM z)
        y (ricciTraceEndomorphism cov Y Z y)) x := by
  apply contMDiffAt_endomorphism_of_localFrame 1 _ x (Module.finBasis ℝ E)
  intro i
  have hfield := contMDiffAt_curvatureTensor_apply_one cov hm ht
    (contMDiffAt_localFrame_of_mem 3 (trivializationAt E TM x) (Module.finBasis ℝ E) i
      (mem_baseSet_trivializationAt E TM x)) hY hZ
  simpa only [ricciTraceEndomorphism, LinearMap.coe_toContinuousLinearMap',
    CovariantDerivative.ricciEndomorphism_apply] using hfield

/-- Ricci paired with locally C³ fields is a genuine C¹ scalar function. -/
theorem contMDiffAt_ricciCurvature_apply_one
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {Y Z : Π y, TM y} {x : M}
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Y) x)
    (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Z) x) :
    ContMDiffAt I 𝓘(ℝ, ℝ) 1 (fun y ↦ cov.ricciCurvature y (Y y) (Z y)) x := by
  let e := trivializationAt E TM x
  let b := Module.finBasis ℝ E
  have hx := mem_baseSet_trivializationAt E TM x
  have hA := contMDiffAt_ricciTraceEndomorphism_one cov hm ht hY hZ
  have hs : ContMDiffAt I 𝓘(ℝ, ℝ) 1
      (fun y ↦ ∑ i, e.localFrameCoeff I b i y
        (ricciTraceEndomorphism cov Y Z y (e.localFrame b i y))) x :=
    ContMDiffAt.sum (fun i _ ↦ contMDiffAt_localFrameCoeff b hx
      (hA.clm_bundle_apply (contMDiffAt_localFrame_of_mem 1 e b i hx)) i)
  apply hs.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  exact trace_eq_sum_localFrameCoeff e b (ricciTraceEndomorphism cov Y Z) y hy

end AlmostSchur
