/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/

/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import LeanPool.NashEmbedding.NashEmbedding.Riemannian.Induced

/-!
# Pullback metrics and product metrics

Two constructions of `ContMDiffRiemannianMetric`s from old ones:

* the **pullback** `f^*h` of a metric `h` on `N` along a smooth immersion `f : M → N`,
  `(f^*h)_x(v, w) := h_{f x}(df_x v, df_x w)`;
* the **product** `g ⊕ g'` of metrics on `M` and `M'`,
  `(g ⊕ g')_{(x,x')}((v,v'),(w,w')) := g_x(v,w) + g'_{x'}(v',w')`.

The induced metric of `Induced.lean` is the special case of the pullback with
`N` an inner-product space; the product metric is the sum of the pullbacks along the
two projections (`mfderiv_fst`, `mfderiv_snd`), which is how its smoothness is proved
without any description of the tangent bundle of a product.

Applications: the flat torus `Circle × Circle` (so `nashCompact` can be compared with
`nashTorus`), products of spheres, and in general any product of manifolds that already
carry metrics.
-/

open scoped Manifold ContDiff Topology
open Bundle Function ContinuousLinearMap Bornology Metric

noncomputable section

namespace NashEmbedding

section Pullback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

/-- The differential of `f : M → N` at `x`, read on the model spaces (definitional cast of
  `mfderiv`; `diff` of `AmbientMetric.lean` is the case `N = E'`). -/
def mdiff (f : M → N) (x : M) : E →L[ℝ] F := mfderiv I J f x

/-- The pullback form at `x`, on the model space `E`: `(v, w) ↦ h_{f x}(df_x v, df_x w)`. -/
def pullbackForm (f : M → N)
    (h : ContMDiffRiemannianMetric J ∞ F (TangentSpace J : N → Type _)) (x : M) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  (metricAt h (f x)).bilinearComp (mdiff (I := I) (J := J) f x) (mdiff (I := I) (J := J) f x)

/-- The same form, typed on the tangent space (definitional cast; an `abbrev` so that it
  unfolds to `pullbackForm` reducibly). -/
abbrev pullbackFormT (f : M → N)
    (h : ContMDiffRiemannianMetric J ∞ F (TangentSpace J : N → Type _)) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  show E →L[ℝ] E →L[ℝ] ℝ from pullbackForm (I := I) (J := J) f h x

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ F] in
/-- Evaluation of the pullback form. -/
theorem pullbackForm_apply (f : M → N)
    (h : ContMDiffRiemannianMetric J ∞ F (TangentSpace J : N → Type _)) (x : M) (v w : E) :
    pullbackForm (I := I) (J := J) f h x v w =
      metricAt h (f x) (mdiff (I := I) (J := J) f x v) (mdiff (I := I) (J := J) f x w) := rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ F] in
/-- **P1.** Symmetry. -/
theorem pullbackForm_symm (f : M → N)
    (h : ContMDiffRiemannianMetric J ∞ F (TangentSpace J : N → Type _)) (x : M) (v w : E) :
    pullbackForm (I := I) (J := J) f h x v w = pullbackForm (I := I) (J := J) f h x w v := by
  rw [pullbackForm_apply, pullbackForm_apply]
  exact h.symm (f x) _ _

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ F] [IsManifold J ∞ N] in
/-- Injectivity of `mfderiv` gives injectivity of the cast `mdiff`. -/
theorem mdiff_injective {f : M → N} {x : M} (hinj : Injective (mfderiv I J f x)) :
    Injective (mdiff (I := I) (J := J) f x) := by
  intro v w hvw
  exact hinj (show mfderiv I J f x v = mfderiv I J f x w from hvw)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ F] in
/-- **P2.** Positivity, from injectivity of the differential. -/
theorem pullbackForm_pos {f : M → N}
    (h : ContMDiffRiemannianMetric J ∞ F (TangentSpace J : N → Type _)) {x : M}
    (hinj : Injective (mfderiv I J f x)) {v : E} (hv : v ≠ 0) :
    0 < pullbackForm (I := I) (J := J) f h x v v := by
  rw [pullbackForm_apply]
  refine h.pos (f x) _ fun hc => hv ?_
  exact mdiff_injective hinj (by rw [show mdiff (I := I) (J := J) f x v = 0 from hc, map_zero])

omit [IsManifold I ∞ M] [FiniteDimensional ℝ F] in
/-- **P3.** The unit "ball" of the pullback form is von Neumann bounded: it is the preimage
  of the (bounded) unit ball of `h_{f x}` under the injective linear map `df_x`, and an
  injective linear map between finite-dimensional spaces is antilipschitz
  (`LinearMap.exists_antilipschitzWith`, `NormedSpace.isVonNBounded_iff`). -/
theorem pullbackForm_isVonNBounded {f : M → N}
    (h : ContMDiffRiemannianMetric J ∞ F (TangentSpace J : N → Type _)) {x : M}
    (hinj : Injective (mfderiv I J f x)) :
    IsVonNBounded ℝ {v : E | pullbackForm (I := I) (J := J) f h x v v < 1} := by
  obtain ⟨K, hK, hanti⟩ :=
    LinearMap.exists_antilipschitzWith (mdiff (I := I) (J := J) f x).toLinearMap
      (LinearMap.ker_eq_bot.2 (mdiff_injective hinj))
  have hB : IsVonNBounded ℝ {w : F | metricAt h (f x) w w < 1} := h.isVonNBounded (f x)
  obtain ⟨C, hC⟩ := (NormedSpace.isVonNBounded_iff' ℝ).1 hB
  refine Bornology.IsVonNBounded.subset (s₂ := Metric.ball (0 : E) ((K : ℝ) * C + 1)) ?_
    (NormedSpace.isVonNBounded_ball ℝ E ((K : ℝ) * C + 1))
  intro v hv
  have h1 : metricAt h (f x) (mdiff (I := I) (J := J) f x v)
      (mdiff (I := I) (J := J) f x v) < 1 := hv
  have h2 : ‖mdiff (I := I) (J := J) f x v‖ ≤ C :=
    hC _ (show mdiff (I := I) (J := J) f x v ∈ {w : F | metricAt h (f x) w w < 1} from h1)
  have hle : ‖v‖ ≤ (K : ℝ) * ‖mdiff (I := I) (J := J) f x v‖ := by
    have := hanti.le_mul_dist v 0
    simpa [dist_eq_norm] using this
  have hKpos : (0:ℝ) < (K : ℝ) := by exact_mod_cast hK
  have : ‖v‖ < (K : ℝ) * C + 1 := by nlinarith [norm_nonneg (mdiff (I := I) (J := J) f x v)]
  simpa [Metric.mem_ball, dist_eq_norm] using this

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Evaluation of the pullback form read in the trivialization at `x₀`
  (`hom_trivializationAt_apply`, `inCoordinates_apply_eq₂`; same proof as
  `inducedForm_trivialization_apply`). -/
theorem pullbackForm_trivialization_apply (f : M → N)
    (h : ContMDiffRiemannianMetric J ∞ F (TangentSpace J : N → Type _)) {x₀ x : M}
    (hx : x ∈ (chartAt H x₀).source) (a b : E) :
    (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀
        ⟨x, pullbackFormT (I := I) (J := J) f h x⟩).2 a b =
      pullbackForm (I := I) (J := J) f h x (tcoord I x₀ x a) (tcoord I x₀ x b) := by
  have hb : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by simpa using hx
  rw [hom_trivializationAt_apply, inCoordinates_apply_eq₂ hb hb (Set.mem_univ _)]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
    LinearMap.id_coe, id_eq, tcoord]
  exact congrArg₂ (fun v w : TangentSpace I x =>
    pullbackFormT (I := I) (J := J) f h x v w)
    (Trivialization.symmL_apply (R := ℝ) _ hb a).symm
    (Trivialization.symmL_apply (R := ℝ) _ hb b).symm

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Coordinate map from `T_yN ≅ F` to the model fibre, in the trivialization at `y₀`
  (definitional cast of `continuousLinearMapAt`; inverse to `tcoord` on the base set). -/
def tcoordInv (J : ModelWithCorners ℝ F G) [IsManifold J ∞ N] (y₀ y : N) : F →L[ℝ] F :=
  (trivializationAt F (TangentSpace J) y₀).continuousLinearMapAt ℝ y

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ F] in
/-- On the base set, `tcoordInv` inverts `tcoord` (`symmL_continuousLinearMapAt`). -/
theorem tcoord_tcoordInv {y₀ y : N} (hy : y ∈ (chartAt G y₀).source) (a : F) :
    tcoord J y₀ y (tcoordInv J y₀ y a) = a := by
  have hb : y ∈ (trivializationAt F (TangentSpace J) y₀).baseSet := by simpa using hy
  exact (trivializationAt F (TangentSpace J) y₀).symmL_continuousLinearMapAt (R := ℝ) hb a

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Auxiliary form of `inTangentCoordinates_mfderiv_eq'` without finite-dimensionality
  assumptions and without the (unnecessary) chart hypotheses: `inTangentCoordinates` of the
  differential is literally `tcoordInv ∘L mdiff ∘L tcoord`. -/
theorem inTangentCoordinates_mfderiv_eq'' {f : M → N} (x₀ x : M) :
    inTangentCoordinates I J id f (mfderiv I J f) x₀ x =
      tcoordInv J (f x₀) (f x) ∘L mdiff (I := I) (J := J) f x ∘L tcoord I x₀ x := by
  change ContinuousLinearMap.inCoordinates E (TangentSpace I) F (TangentSpace J) x₀ x
      (f x₀) (f x) (mfderiv I J f x) = _
  rw [ContinuousLinearMap.inCoordinates]
  rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The differential in tangent coordinates (source trivialization at `x₀`, target
  trivialization at `f x₀`), for `x` in the chart at `x₀` with `f x` in the chart at
  `f x₀`: `(trivializationAt (f x₀)).continuousLinearMapAt (f x) ∘ df_x ∘ tcoord x₀ x`
  (unfold `inTangentCoordinates`, `inCoordinates`). -/
theorem inTangentCoordinates_mfderiv_eq' {f : M → N} {x₀ x : M}
    (_hx : x ∈ (chartAt H x₀).source) (_hfx : f x ∈ (chartAt G (f x₀)).source) :
    inTangentCoordinates I J id f (mfderiv I J f) x₀ x =
      tcoordInv J (f x₀) (f x) ∘L mdiff (I := I) (J := J) f x ∘L tcoord I x₀ x :=
  inTangentCoordinates_mfderiv_eq'' (I := I) (J := J) x₀ x

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **P4.** Smoothness of the pullback form as a section of the bundle of bilinear forms on
  `TM`.  Near `x₀`, in the trivialization at `x₀`, the section equals
  `x ↦ (hₜ (f x)).bilinearComp (Lₜ x) (Lₜ x)` where
  `Lₜ := inTangentCoordinates I J id f (mfderiv I J f) x₀` is smooth at `x₀`
  (`ContMDiffAt.mfderiv_const`) and `hₜ := fun y => (trivializationAt _ _ (f x₀) ⟨y, h.inner y⟩).2`
  is smooth at `f x₀` (`contMDiffAt_metric_trivialization`); the two coordinate changes on
  the target cancel by `Trivialization.symmL_continuousLinearMapAt`
  (`metric_trivialization_apply`, `pullbackForm_trivialization_apply`,
  `inTangentCoordinates_mfderiv_eq'`, `contMDiffAt_bilinearComp'`). -/
theorem pullbackForm_contMDiff {f : M → N}
    (h : ContMDiffRiemannianMetric J ∞ F (TangentSpace J : N → Type _))
    (hf : ContMDiff I J ∞ f) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (pullbackFormT (I := I) (J := J) f h x)) := by
  intro x₀
  rw [contMDiffAt_section]
  set Lt : M → E →L[ℝ] F := inTangentCoordinates I J id f (mfderiv I J f) x₀
  have hLtm : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] F) ∞ Lt x₀ :=
    (hf x₀).mfderiv_const (m := ∞) (n := ∞) (by simp)
  set ht : N → F →L[ℝ] F →L[ℝ] ℝ := fun y => (trivializationAt (F →L[ℝ] F →L[ℝ] ℝ)
    (fun z => TangentSpace J z →L[ℝ] TangentSpace J z →L[ℝ] ℝ) (f x₀) ⟨y, h.inner y⟩).2 with htdef
  have htm : ContMDiffAt J 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) ∞ ht (f x₀) :=
    contMDiffAt_metric_trivialization h (f x₀)
  have hsmooth : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun x => (ht (f x)).bilinearComp (Lt x) (Lt x)) x₀ :=
    contMDiffAt_bilinearComp' (htm.comp x₀ (hf x₀)) hLtm hLtm
  refine hsmooth.congr_of_eventuallyEq ?_
  filter_upwards [chart_source_mem_nhds H x₀,
    (hf x₀).continuousAt.preimage_mem_nhds (chart_source_mem_nhds G (f x₀))] with x hx hfx
  have hLtx : Lt x = tcoordInv J (f x₀) (f x) ∘L mdiff (I := I) (J := J) f x ∘L tcoord I x₀ x :=
    inTangentCoordinates_mfderiv_eq'' x₀ x
  ext a b
  rw [pullbackForm_trivialization_apply f h hx, pullbackForm_apply]
  change _ = ht (f x) (Lt x a) (Lt x b)
  rw [htdef, metric_trivialization_apply h hfx, hLtx]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [tcoord_tcoordInv hfx, tcoord_tcoordInv hfx]

/-- The pullback metric `f^*h` of a smooth immersion `f : M → N`. -/
def pullbackMetric {f : M → N}
    (h : ContMDiffRiemannianMetric J ∞ F (TangentSpace J : N → Type _))
    (hf : ContMDiff I J ∞ f) (hinj : ∀ x, Injective (mfderiv I J f x)) :
    ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _) where
  inner x := pullbackFormT (I := I) (J := J) f h x
  symm x v w := pullbackForm_symm (I := I) (J := J) f h x v w
  pos x v hv := pullbackForm_pos h (hinj x) hv
  isVonNBounded x := by
    change IsVonNBounded ℝ {v : E | pullbackForm (I := I) (J := J) f h x v v < 1}
    exact pullbackForm_isVonNBounded h (hinj x)
  contMDiff := pullbackForm_contMDiff h hf

omit [FiniteDimensional ℝ F] in
theorem pullbackMetric_inner {f : M → N}
    (h : ContMDiffRiemannianMetric J ∞ F (TangentSpace J : N → Type _))
    (hf : ContMDiff I J ∞ f) (hinj : ∀ x, Injective (mfderiv I J f x)) (x : M) (v w : E) :
    metricAt (pullbackMetric h hf hinj) x v w =
      metricAt h (f x) (mdiff (I := I) (J := J) f x v) (mdiff (I := I) (J := J) f x w) := rfl

end Pullback

/-! ## Product metrics -/

section Product

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- The product form at `p = (x, x')`, on the model space `E × E'`:
  `((v, v'), (w, w')) ↦ g_x(v, w) + g'_{x'}(v', w')`. -/
def prodForm (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (g' : ContMDiffRiemannianMetric I' ∞ E' (TangentSpace I' : M' → Type _)) (p : M × M') :
    (E × E') →L[ℝ] (E × E') →L[ℝ] ℝ :=
  (metricAt g p.1).bilinearComp (fst ℝ E E') (fst ℝ E E') +
    (metricAt g' p.2).bilinearComp (snd ℝ E E') (snd ℝ E E')

/-- The same form, typed on the tangent space of the product (definitional cast:
  `TangentSpace (I.prod I') p = E × E'`). -/
abbrev prodFormT (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (g' : ContMDiffRiemannianMetric I' ∞ E' (TangentSpace I' : M' → Type _)) (p : M × M') :
    TangentSpace (I.prod I') p →L[ℝ] TangentSpace (I.prod I') p →L[ℝ] ℝ :=
  show (E × E') →L[ℝ] (E × E') →L[ℝ] ℝ from prodForm g g' p

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- Evaluation of the product form. -/
theorem prodForm_apply (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (g' : ContMDiffRiemannianMetric I' ∞ E' (TangentSpace I' : M' → Type _)) (p : M × M')
    (v w : E × E') :
    prodForm g g' p v w = metricAt g p.1 v.1 w.1 + metricAt g' p.2 v.2 w.2 := by
  simp [prodForm, ContinuousLinearMap.bilinearComp_apply]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- **Q0.** The product form is the sum of the pullbacks of `g`, `g'` along the two
  projections (`mfderiv_fst`, `mfderiv_snd`). -/
theorem prodForm_eq_pullback (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (g' : ContMDiffRiemannianMetric I' ∞ E' (TangentSpace I' : M' → Type _)) (p : M × M') :
    prodForm g g' p =
      pullbackForm (I := I.prod I') (J := I) Prod.fst g p +
        pullbackForm (I := I.prod I') (J := I') Prod.snd g' p := by
  have h1 : mdiff (I := I.prod I') (J := I) Prod.fst p = ContinuousLinearMap.fst ℝ E E' :=
    mfderiv_fst
  have h2 : mdiff (I := I.prod I') (J := I') Prod.snd p = ContinuousLinearMap.snd ℝ E E' :=
    mfderiv_snd
  refine ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => ?_
  rw [prodForm_apply]
  simp only [_root_.add_apply, pullbackForm_apply, h1, h2,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- **Q1.** Symmetry. -/
theorem prodForm_symm (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (g' : ContMDiffRiemannianMetric I' ∞ E' (TangentSpace I' : M' → Type _)) (p : M × M')
    (v w : E × E') : prodForm g g' p v w = prodForm g g' p w v := by
  have e1 : metricAt g p.1 v.1 w.1 = metricAt g p.1 w.1 v.1 := g.symm p.1 v.1 w.1
  have e2 : metricAt g' p.2 v.2 w.2 = metricAt g' p.2 w.2 v.2 := g'.symm p.2 v.2 w.2
  rw [prodForm_apply, prodForm_apply, e1, e2]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- **Q2.** Positivity (`v ≠ 0` means `v.1 ≠ 0` or `v.2 ≠ 0`; both summands are
  nonnegative, `g.pos`/`g'.pos`). -/
theorem prodForm_pos (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (g' : ContMDiffRiemannianMetric I' ∞ E' (TangentSpace I' : M' → Type _)) (p : M × M')
    {v : E × E'} (hv : v ≠ 0) : 0 < prodForm g g' p v v := by
  have h1 : 0 ≤ metricAt g p.1 v.1 v.1 := by
    rcases eq_or_ne v.1 0 with h | h
    · simp [h]
    · exact (g.pos p.1 v.1 h).le
  have h2 : 0 ≤ metricAt g' p.2 v.2 v.2 := by
    rcases eq_or_ne v.2 0 with h | h
    · simp [h]
    · exact (g'.pos p.2 v.2 h).le
  rw [prodForm_apply]
  rcases eq_or_ne v.1 0 with h | h
  · have h' : v.2 ≠ 0 := fun h2' => hv (Prod.ext h h2')
    have : (0:ℝ) < metricAt g' p.2 v.2 v.2 := g'.pos p.2 v.2 h'
    linarith
  · have : (0:ℝ) < metricAt g p.1 v.1 v.1 := g.pos p.1 v.1 h
    linarith

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- **Q3.** Von Neumann boundedness of the unit "ball" (it is contained in the product of
  the unit balls of `g_x` and `g'_{x'}`, `IsVonNBounded.prod` or
  `NormedSpace.isVonNBounded_iff`). -/
theorem prodForm_isVonNBounded
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (g' : ContMDiffRiemannianMetric I' ∞ E' (TangentSpace I' : M' → Type _)) (p : M × M') :
    IsVonNBounded ℝ {v : E × E' | prodForm g g' p v v < 1} := by
  have hB : IsVonNBounded ℝ {w : E | metricAt g p.1 w w < 1} := g.isVonNBounded p.1
  have hB' : IsVonNBounded ℝ {w : E' | metricAt g' p.2 w w < 1} := g'.isVonNBounded p.2
  obtain ⟨C, hC⟩ := (NormedSpace.isVonNBounded_iff' ℝ).1 hB
  obtain ⟨C', hC'⟩ := (NormedSpace.isVonNBounded_iff' ℝ).1 hB'
  refine Bornology.IsVonNBounded.subset (s₂ := Metric.ball (0 : E × E') (C + C' + 1)) ?_
    (NormedSpace.isVonNBounded_ball ℝ (E × E') (C + C' + 1))
  intro v hv
  have hlt : metricAt g p.1 v.1 v.1 + metricAt g' p.2 v.2 v.2 < 1 := by
    have : prodForm g g' p v v < 1 := hv
    rwa [prodForm_apply] at this
  have h1 : 0 ≤ metricAt g p.1 v.1 v.1 := by
    rcases eq_or_ne v.1 0 with h | h
    · simp [h]
    · exact (g.pos p.1 v.1 h).le
  have h2 : 0 ≤ metricAt g' p.2 v.2 v.2 := by
    rcases eq_or_ne v.2 0 with h | h
    · simp [h]
    · exact (g'.pos p.2 v.2 h).le
  have hn1 : ‖v.1‖ ≤ C :=
    hC _ (show v.1 ∈ {w : E | metricAt g p.1 w w < 1} from by
      simp only [Set.mem_ofPred_eq]; linarith)
  have hn2 : ‖v.2‖ ≤ C' :=
    hC' _ (show v.2 ∈ {w : E' | metricAt g' p.2 w w < 1} from by
      simp only [Set.mem_ofPred_eq]; linarith)
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) hn1
  have hC0' : 0 ≤ C' := le_trans (norm_nonneg _) hn2
  have : ‖v‖ < C + C' + 1 := by
    have hle : ‖v‖ ≤ max ‖v.1‖ ‖v.2‖ := le_of_eq (Prod.norm_def v)
    have : max ‖v.1‖ ‖v.2‖ ≤ C + C' := max_le (by linarith) (by linarith)
    linarith
  simpa [Metric.mem_ball, dist_eq_norm] using this

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- **Q4.** Smoothness of the product form as a section of the bundle of bilinear forms on
  `T(M × M')`: by `prodForm_eq_pullback` it is the sum of two sections that are smooth by
  `pullbackForm_contMDiff` (applied to `contMDiff_fst`, `contMDiff_snd`), and sums of
  smooth sections are smooth (`ContMDiffSection`, `ContMDiffSection.coe_add`). -/
theorem prodForm_contMDiff (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (g' : ContMDiffRiemannianMetric I' ∞ E' (TangentSpace I' : M' → Type _)) :
    ContMDiff (I.prod I') ((I.prod I').prod 𝓘(ℝ, (E × E') →L[ℝ] (E × E') →L[ℝ] ℝ)) ∞
      (fun p => TotalSpace.mk' ((E × E') →L[ℝ] (E × E') →L[ℝ] ℝ) p (prodFormT g g' p)) := by
  have hfst : ContMDiff (I.prod I') I ∞ (Prod.fst : M × M' → M) := contMDiff_fst
  have hsnd : ContMDiff (I.prod I') I' ∞ (Prod.snd : M × M' → M') := contMDiff_snd
  have hA := pullbackForm_contMDiff (I := I.prod I') (J := I) g hfst
  have hB := pullbackForm_contMDiff (I := I.prod I') (J := I') g' hsnd
  refine (hA.add_section hB).congr fun p => ?_
  have hp : prodFormT g g' p =
      (fun p => pullbackFormT (I := I.prod I') (J := I) Prod.fst g p) p +
        (fun p => pullbackFormT (I := I.prod I') (J := I') Prod.snd g' p) p :=
    prodForm_eq_pullback g g' p
  rw [hp]
  rfl

/-- The product metric `g ⊕ g'` on `M × M'`. -/
def prodMetric (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (g' : ContMDiffRiemannianMetric I' ∞ E' (TangentSpace I' : M' → Type _)) :
    ContMDiffRiemannianMetric (I.prod I') ∞ (E × E')
      (TangentSpace (I.prod I') : M × M' → Type _) where
  inner p := prodFormT g g' p
  symm p v w := prodForm_symm g g' p v w
  pos p v hv := prodForm_pos g g' p hv
  isVonNBounded p := by
    change IsVonNBounded ℝ {v : E × E' | prodForm g g' p v v < 1}
    exact prodForm_isVonNBounded g g' p
  contMDiff := prodForm_contMDiff g g'

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
theorem prodMetric_inner (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (g' : ContMDiffRiemannianMetric I' ∞ E' (TangentSpace I' : M' → Type _)) (p : M × M')
    (v w : E × E') :
    metricAt (prodMetric g g') p v w = metricAt g p.1 v.1 w.1 + metricAt g' p.2 v.2 w.2 :=
  prodForm_apply g g' p v w

end Product

end NashEmbedding

end
