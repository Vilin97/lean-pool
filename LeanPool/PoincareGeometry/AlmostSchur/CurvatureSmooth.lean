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

public import LeanPool.PoincareGeometry.AlmostSchur.LeviCivitaSmooth
public import LeanPool.PoincareGeometry.AlmostSchur.ScalarCurvatureTraceDerivative

/-!
# Arbitrary finite regularity of curvature contractions

This file propagates the smooth metric and the smooth Levi--Civita connection
through the curvature tensor, Ricci contraction, and scalar curvature.  The
finite-order statements are kept explicit so that the final `C^∞` theorem is
obtained through `contMDiff_infty`, rather than by assuming smooth curvature.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set
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
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
local notation "TM" => (TangentSpace I : M → Type _)

local instance curvatureSmoothVectorBundleAt (n : ℕ) :
    ContMDiffVectorBundle (↑(n : ℕ)) E TM I :=
  ContMDiffVectorBundle.of_le (n := ∞) (by
    exact WithTop.coe_le_coe.mpr (show (n : ℕ∞) ≤ ⊤ from le_top))

local instance curvatureSmoothVectorBundleAtSucc (n : ℕ) :
    ContMDiffVectorBundle ((n : ℕ∞ω) + 1) E TM I :=
  ContMDiffVectorBundle.of_le (n := ∞) (by
    exact_mod_cast (le_top : (n + 1 : ℕ∞) ≤ ⊤))

local instance curvatureSmoothVectorBundleAtTwo (n : ℕ) :
    ContMDiffVectorBundle ((n : ℕ∞ω) + 2) E TM I :=
  ContMDiffVectorBundle.of_le (n := ∞) (by
    change ((n + 2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr (le_top : (n + 2 : ℕ∞) ≤ ⊤))

local instance curvatureSmoothManifoldAtTwo (n : ℕ) :
    IsManifold I ((n : ℕ∞ω) + 2) M :=
  IsManifold.of_le (n := ∞) (by
    change ((n + 2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr (le_top : (n + 2 : ℕ∞) ≤ ⊤))

/-! ## Raw curvature and the bundled curvature tensor -/

theorem contMDiffAt_curvatureAux_of_order
    (n : ℕ) (cov : CovariantDerivative I E TM)
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {X Y Z : Π y, TM y} {x : M}
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (n + 2) (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (n + 2) (T% Y) x)
    (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (n + 2) (T% Z) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) n
      (T% (cov.curvatureAuxAlmostSchur X Y Z)) x := by
  letI : IsManifold I (minSmoothness ℝ (2 : ℕ∞)) M :=
    IsManifold.of_le (n := ∞) (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  letI : IsManifold I (((n + 2 : ℕ∞) : ℕ∞ω) + 1) M :=
    IsManifold.of_le (n := ∞) (by
      change ((n + 3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr (le_top : (n + 3 : ℕ∞) ≤ ⊤))
  have hYZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (n + 1)
      (T% (cov.alongAlmostSchur Y Z)) x :=
    contMDiffAt_covariantAlong_of_metric_torsion_of_order (I := I) (n + 1)
      cov hm ht hY hZ
  have hXZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (n + 1)
      (T% (cov.alongAlmostSchur X Z)) x :=
    contMDiffAt_covariantAlong_of_metric_torsion_of_order (I := I) (n + 1)
      cov hm ht hX hZ
  have h1 := contMDiffAt_covariantAlong_of_metric_torsion_of_order (I := I) n cov hm ht
    (hX.of_le (by
      change (n : ℕ∞ω) + 1 ≤ (n : ℕ∞ω) + 2
      change ((n + 1 : ℕ∞) : ℕ∞ω) ≤ ((n + 2 : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr (by
        exact_mod_cast (Nat.le_succ (n + 1))))) hYZ
  have h2 := contMDiffAt_covariantAlong_of_metric_torsion_of_order (I := I) n cov hm ht
    (hY.of_le (by
      change (n : ℕ∞ω) + 1 ≤ (n : ℕ∞ω) + 2
      change ((n + 1 : ℕ∞) : ℕ∞ω) ≤ ((n + 2 : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr (by
        exact_mod_cast (Nat.le_succ (n + 1))))) hXZ
  have hb : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (n + 1)
      (T% (VectorField.mlieBracket I X Y)) x :=
    hX.mlieBracket_vectorField hY (m := n + 1) (n := n + 2) (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact le_rfl)
  have h3 := contMDiffAt_covariantAlong_of_metric_torsion_of_order (I := I) n cov hm ht
    hb (hZ.of_le (by
      change (n : ℕ∞ω) + 1 ≤ (n : ℕ∞ω) + 2
      change ((n + 1 : ℕ∞) : ℕ∞ω) ≤ ((n + 2 : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr (by
        exact_mod_cast (Nat.le_succ (n + 1)))))
  exact (h1.sub_section h2).sub_section h3

theorem contMDiffAt_curvatureTensor_apply_of_order
    (n : ℕ) (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {X Y Z : Π y, TM y} {x : M}
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (n + 2) (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (n + 2) (T% Y) x)
    (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (n + 2) (T% Z) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) n
      (T% (fun y ↦ cov.curvatureTensorAlmostSchur y (X y) (Y y) (Z y))) x := by
  have hn : ((n : ℕ∞ω) + 2) ≠ ∞ := by
    change ((n + 2 : ℕ∞) : ℕ∞ω) ≠ ((⊤ : ℕ∞) : ℕ∞ω)
    intro h
    rw [WithTop.coe_inj] at h
    have h' : ((n + 2 : ℕ) : ℕ∞) = ⊤ := by
      simpa [← ENat.natCast_add n 2] using h
    exact (ENat.natCast_ne_top (n + 2)) h'
  apply (contMDiffAt_curvatureAux_of_order (I := I) n cov hm ht hX hY hZ).congr_of_eventuallyEq
  filter_upwards [(contMDiffAt_iff_contMDiffAt_nhds hn).mp hX,
    (contMDiffAt_iff_contMDiffAt_nhds hn).mp hY,
    (contMDiffAt_iff_contMDiffAt_nhds hn).mp hZ] with y hXy hYy hZy
  apply congrArg (TotalSpace.mk' E y)
  exact (curvatureAux_eq_curvatureTensor_of_contMDiffAt cov
    (hXy.of_le (by
      change (2 : ℕ∞ω) ≤ (n : ℕ∞ω) + 2
      exact_mod_cast (by omega : (2 : ℕ) ≤ n + 2)))
    (hYy.of_le (by
      change (2 : ℕ∞ω) ≤ (n : ℕ∞ω) + 2
      exact_mod_cast (by omega : (2 : ℕ) ≤ n + 2)))
    (hZy.of_le (by
      change (2 : ℕ∞ω) ≤ (n : ℕ∞ω) + 2
      exact_mod_cast (by omega : (2 : ℕ) ≤ n + 2)))).symm

/-! ## Ricci and scalar curvature -/

theorem contMDiffAt_ricciTraceEndomorphism_of_order
    (n : ℕ) (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {Y Z : Π y, TM y} {x : M}
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (n + 2) (T% Y) x)
    (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (n + 2) (T% Z) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z ↦ TM z →L[ℝ] TM z) y
          (ricciTraceEndomorphism cov Y Z y)) x := by
  apply contMDiffAt_endomorphism_of_localFrame n _ x (Module.finBasis ℝ E)
  intro i
  have hfield := contMDiffAt_curvatureTensor_apply_of_order (I := I) n cov hm ht
    (contMDiffAt_localFrame_of_mem (n + 2) (trivializationAt E TM x)
      (Module.finBasis ℝ E) i (mem_baseSet_trivializationAt E TM x)) hY hZ
  simpa only [ricciTraceEndomorphism, LinearMap.coe_toContinuousLinearMap',
    CovariantDerivative.ricciEndomorphism_applyAlmostSchur] using hfield

theorem contMDiffAt_ricciCurvature_apply_of_order
    (n : ℕ) (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {Y Z : Π y, TM y} {x : M}
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (n + 2) (T% Y) x)
    (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (n + 2) (T% Z) x) :
    ContMDiffAt I 𝓘(ℝ, ℝ) n
      (fun y ↦ cov.ricciCurvatureAlmostSchur y (Y y) (Z y)) x := by
  let e := trivializationAt E TM x
  let b := Module.finBasis ℝ E
  have hx := mem_baseSet_trivializationAt E TM x
  have hA := contMDiffAt_ricciTraceEndomorphism_of_order (I := I) n cov hm ht hY hZ
  have hs : ContMDiffAt I 𝓘(ℝ, ℝ) n
      (fun y ↦ ∑ i, e.localFrameCoeff I b i y
        (ricciTraceEndomorphism cov Y Z y (e.localFrame b i y))) x :=
    ContMDiffAt.sum (fun i _ ↦ contMDiffAt_localFrameCoeff b hx
      (hA.clm_bundle_apply (contMDiffAt_localFrame_of_mem n e b i hx)) i)
  apply hs.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  exact trace_eq_sum_localFrameCoeff e b (ricciTraceEndomorphism cov Y Z) y hy

theorem contMDiffAt_ricciRaisedEndomorphism_of_order
    (n : ℕ) (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0) (x : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z ↦ TM z →L[ℝ] TM z) y
          (ricciRaisedEndomorphism cov y)) x := by
  let b := Module.finBasis ℝ E
  let e := trivializationAt E TM x
  have hx := mem_baseSet_trivializationAt E TM x
  apply contMDiffAt_endomorphism_of_localFrame n _ x b
  intro i
  apply contMDiffAt_section_of_inner_localFrame_of_order (I := I) n b x x
    (mem_chart_source H x)
  intro j
  simp only [inner_ricciRaisedEndomorphism]
  exact contMDiffAt_ricciCurvature_apply_of_order (I := I) n cov hm ht
    (contMDiffAt_localFrame_of_mem (n + 2) e b i hx)
    (contMDiffAt_localFrame_of_mem (n + 2) e b j hx)

theorem contMDiffAt_scalarCurvature_of_order
    (n : ℕ) (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0) (x : M) :
    ContMDiffAt I 𝓘(ℝ, ℝ) n cov.scalarCurvatureAlmostSchur x := by
  let e := trivializationAt E TM x
  let b := Module.finBasis ℝ E
  have hx := mem_baseSet_trivializationAt E TM x
  have hA := contMDiffAt_ricciRaisedEndomorphism_of_order (I := I) n cov hm ht x
  have hs : ContMDiffAt I 𝓘(ℝ, ℝ) n
      (fun y ↦ ∑ i, e.localFrameCoeff I b i y
        (ricciRaisedEndomorphism cov y (e.localFrame b i y))) x :=
    ContMDiffAt.sum (fun i _ ↦ contMDiffAt_localFrameCoeff b hx
      (hA.clm_bundle_apply (contMDiffAt_localFrame_of_mem n e b i hx)) i)
  apply hs.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  rw [scalarCurvature_eq_trace_ricciRaisedEndomorphism]
  exact trace_eq_sum_localFrameCoeff e b (ricciRaisedEndomorphism cov) y hy

theorem contMDiffAt_scalarCurvature_infty
    (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ cov.scalarCurvatureAlmostSchur := by
  rw [contMDiff_infty]
  intro n x
  exact contMDiffAt_scalarCurvature_of_order (I := I) n cov hm ht x

end AlmostSchur
