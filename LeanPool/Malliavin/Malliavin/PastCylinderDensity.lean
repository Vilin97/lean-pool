/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
module

public import LeanPool.Malliavin.Malliavin.NaturalClarkOcone
public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Density of past Brownian cylinders

This file proves the finite-coordinate density input isolated in
`Malliavin.NaturalClarkOcone`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

noncomputable
section

namespace Malliavin

variable {E F W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Precomposition by a continuous linear map preserves the class of smooth bounded
functionals. -/
theorem IsSmoothBounded.comp_continuousLinearMap
    {f : F → ℝ} (hf : IsSmoothBounded f) (L : E →L[ℝ] F) :
    IsSmoothBounded (f ∘ L) where
  contDiff := hf.contDiff.comp L.contDiff
  bounded := hf.bounded.imp fun C hC x ↦ hC (L x)
  bounded_fderiv := by
    obtain ⟨C, hC⟩ := hf.bounded_fderiv
    refine ⟨C * ‖L‖, fun x ↦ ?_⟩
    rw [fderiv_comp x (hf.differentiable (L x)) L.differentiableAt, L.fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hC (L x)) (ContinuousLinearMap.opNorm_nonneg L))

/-- Finite-measure set indicators generate the real square-integrable functions. -/
private theorem closure_eq_top_of_indicators
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (R : Submodule ℝ (Lp ℝ 2 μ))
    (hone : ∀ (s : Set α) (hs : MeasurableSet s) (hμs : μ s ≠ ∞),
      indicatorConstLp 2 hs hμs (1 : ℝ) ∈ R.topologicalClosure) :
    R.topologicalClosure = ⊤ := by
  have hall : ∀ f : Lp ℝ 2 μ, f ∈ R.topologicalClosure := by
    refine Lp.induction (by norm_num) (fun f ↦ f ∈ R.topologicalClosure) ?_ ?_
      R.isClosed_topologicalClosure
    · intro c s hs hμs
      change indicatorConstLp 2 hs hμs.ne c ∈ R.topologicalClosure
      have heq : indicatorConstLp 2 hs hμs.ne c =
          c • indicatorConstLp 2 hs hμs.ne (1 : ℝ) := by
        ext1
        grw [Lp.coeFn_smul, indicatorConstLp_coeFn, indicatorConstLp_coeFn]
        filter_upwards [] with x
        by_cases hx : x ∈ s <;> simp [hx]
      rw [heq]
      exact R.topologicalClosure.smul_mem c (hone s hs hμs.ne)
    · intro f g _hf _hg _hdisjoint hfm hgm
      exact R.topologicalClosure.add_mem hfm hgm
  apply le_antisymm le_top
  intro f _hf
  exact hall f

/-- A linear isometry equivalence reflects density of subspaces. -/
private theorem dense_of_closure_map_eq_top (e : E ≃ₗᵢ[ℝ] F) (K : Submodule ℝ E)
    (hRtop : (K.map (e : E →ₗ[ℝ] F)).topologicalClosure = ⊤) : Dense (K : Set E) := by
  let R := K.map (e : E →ₗ[ℝ] F)
  have hback : (R.map (e.symm : F →ₗ[ℝ] E)).topologicalClosure = ⊤ :=
    (e.symm.surjective.denseRange).topologicalClosure_map_submodule hRtop
  have hmap : R.map (e.symm : F →ₗ[ℝ] E) = K := by
    apply le_antisymm
    · rintro z ⟨y, ⟨x, hx, rfl⟩, hy⟩
      have hxz : x = z := (e.symm_apply_apply x).symm.trans hy
      rwa [← hxz]
    · intro x hx
      refine ⟨e x, ⟨x, hx, rfl⟩, ?_⟩
      exact e.symm_apply_apply x
  rw [hmap] at hback
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hback

section PastProcess

variable [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

/-- The Brownian path restricted to times at most `a`. -/
def pastProcess (B : ℝ≥0 → W → ℝ) (a : ℝ≥0) : W → (Set.Iic a → ℝ) :=
  fun w t ↦ B t w

/-- Pullbacks of measurable finite-coordinate cylinders along the past process. -/
def pastCylinderEvents (B : ℝ≥0 → W → ℝ) (a : ℝ≥0) : Set (Set W) :=
  Set.preimage (pastProcess B a) ''
    measurableCylinders (fun _ : Set.Iic a ↦ ℝ)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- Finite-coordinate past events form an algebra of sets. -/
theorem isSetAlgebra_pastCylinderEvents (B : ℝ≥0 → W → ℝ) (a : ℝ≥0) :
    IsSetAlgebra (pastCylinderEvents B a) where
  empty_mem := by
    exact ⟨∅, empty_mem_measurableCylinders _, Set.preimage_empty⟩
  compl_mem := by
    rintro s ⟨C, hC, rfl⟩
    exact ⟨Cᶜ, compl_mem_measurableCylinders hC, Set.preimage_compl⟩
  union_mem := by
    rintro s t ⟨C, hC, rfl⟩ ⟨D, hD, rfl⟩
    exact ⟨C ∪ D, union_mem_measurableCylinders hC hD, Set.preimage_union⟩

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] in
/-- The algebra of finite-coordinate past events generates the natural filtration at time `a`. -/
theorem natural_eq_generateFrom_pastCylinderEvents
    (hsm : ∀ t, StronglyMeasurable (B t)) (a : ℝ≥0) :
    Filtration.natural B hsm a =
      MeasurableSpace.generateFrom (pastCylinderEvents B a) := by
  rw [Filtration.natural_eq_comap, ← generateFrom_measurableCylinders,
    MeasurableSpace.comap_generateFrom]
  rfl

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Every finite-coordinate past cylinder is measurable at the corresponding natural-filtration
time. -/
theorem measurableSet_pastCylinderEvents
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) (a : ℝ≥0)
    {s : Set W} (hs : s ∈ pastCylinderEvents B a) : MeasurableSet[𝓕 a] s := by
  rw [hnat, natural_eq_generateFrom_pastCylinderEvents hsm a]
  exact MeasurableSpace.measurableSet_generateFrom hs

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Finite-coordinate past events are measure-dense for the restriction of the probability
measure to the natural filtration at time `a`. -/
theorem measureDense_pastCylinderEvents
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) (a : ℝ≥0) :
    @Measure.MeasureDense W (𝓕 a) (P.trim (𝓕.le a))
      (pastCylinderEvents B a) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hgen : 𝓕 a = MeasurableSpace.generateFrom (pastCylinderEvents B a) := by
    rw [hnat]
    exact natural_eq_generateFrom_pastCylinderEvents hsm a
  let _ : MeasurableSpace W := 𝓕 a
  exact Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite
    (μ := P.trim (𝓕.le a)) (isSetAlgebra_pastCylinderEvents B a) hgen

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The adapted indicator of one finite-coordinate past event is approximable by smooth bounded
past Brownian cylinders. -/
theorem adaptedIndicator_pastCylinder_mem_closure
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) (a : ℝ≥0)
    {s : Set W} (hs : s ∈ pastCylinderEvents B a) :
    adaptedIndicator (P := P) 𝓕 a
        (measurableSet_pastCylinderEvents hsm hnat a hs) ∈
      (pastCylinderSpan hB coordinate coordinate_apply hsm hnat a).topologicalClosure := by
  rcases hs with ⟨C, hC, rfl⟩
  rcases (mem_measurableCylinders C).mp hC with ⟨I, A, hA, rfl⟩
  let L : W →L[ℝ] (I → ℝ) :=
    ContinuousLinearMap.pi fun i ↦ coordinate i.1
  let ν : Measure (I → ℝ) := P.map L
  let _ : IsGaussian ν := by
    dsimp only [ν]
    infer_instance
  let hmp : MeasurePreserving L P ν := L.measurable.measurePreserving P
  let Y : Lp ℝ 2 ν :=
    indicatorConstLp 2 hA (measure_ne_top ν A) (1 : ℝ)
  have hset :
      pastProcess B a ⁻¹' cylinder I A = L ⁻¹' A := by
    ext w
    simp only [Set.mem_preimage, mem_cylinder, Finset.restrict_def, pastProcess, L,
      ContinuousLinearMap.coe_pi', coordinate_apply]
  change adaptedIndicator (P := P) 𝓕 a
      (measurableSet_pastCylinderEvents hsm hnat a
        ⟨cylinder I A, hC, rfl⟩) ∈
    closure (pastCylinderSpan hB coordinate coordinate_apply hsm hnat a :
      Set (lpMeas ℝ ℝ (𝓕 a) 2 P))
  refine Metric.mem_closure_iff.mpr fun ε hε ↦ ?_
  have hY : Y ∈ closure
      (Set.range fun G : {G : (I → ℝ) → ℝ // IsSmoothBounded G} ↦ G.2.toLp ν) :=
    (denseRange_toLp ν) Y
  rcases Metric.mem_closure_iff.mp hY ε hε with ⟨g, ⟨G, rfl⟩, hdist⟩
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let Q : (Fin (Fintype.card I) → ℝ) ≃L[ℝ] (I → ℝ) :=
    ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : I ↦ ℝ) e
  let f : (Fin (Fintype.card I) → ℝ) → ℝ := G.1 ∘ Q
  have hf : IsSmoothBounded f :=
    G.2.comp_continuousLinearMap Q.toContinuousLinearMap
  let t : Fin (Fintype.card I) → ℝ≥0 := fun j ↦ (e j).1
  have ht : ∀ j, t j ≤ a := fun j ↦ (e j).1.2
  let Z := pastCylinderLpMeas hB coordinate coordinate_apply hsm hnat
    f hf.contDiff hf.bounded hf.bounded_fderiv t a ht
  refine ⟨Z, ?_, ?_⟩
  · change Z ∈ pastCylinderSpan hB coordinate coordinate_apply hsm hnat a
    apply Submodule.subset_span
    exact ⟨Fintype.card I, f, hf.contDiff, hf.bounded, hf.bounded_fderiv,
      t, ht, rfl⟩
  · have hfun : (fun w ↦ f (fun j ↦ B (t j) w)) = G.1 ∘ L := by
      funext w
      simp only [f, Function.comp_apply, t, L, ContinuousLinearMap.coe_pi',
        coordinate_apply]
      apply congrArg G.1
      have hy : (fun j ↦ coordinate (e j).1 w) =
          Q.symm (fun i ↦ coordinate i.1 w) := by
        rfl
      rw [hy, Q.apply_symm_apply]
    have hZ : (Z : Lp ℝ 2 P) =
        Lp.compMeasurePreserving L hmp (G.2.toLp ν) := by
      let hG := isSmoothBounded_cylinder coordinate coordinate_apply
        f hf.contDiff hf.bounded hf.bounded_fderiv t
      change hG.toLp P = Lp.compMeasurePreserving L hmp (G.2.toLp ν)
      unfold IsSmoothBounded.toLp
      rw [Lp.toLp_compMeasurePreserving]
      apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp (hG.memLp P 2),
        MemLp.coeFn_toLp ((G.2.memLp ν 2).comp_measurePreserving hmp)] with w hw₁ hw₂
      rw [hw₁, hw₂]
      exact congrFun hfun w
    have hI :
        ((adaptedIndicator (P := P) 𝓕 a
          (measurableSet_pastCylinderEvents hsm hnat a
            ⟨cylinder I A, hC, rfl⟩) :
            lpMeas ℝ ℝ (𝓕 a) 2 P) : Lp ℝ 2 P) =
          Lp.compMeasurePreserving L hmp Y := by
      change indicatorConstLp 2
          (𝓕.le a (pastProcess B a ⁻¹' cylinder I A)
            (measurableSet_pastCylinderEvents hsm hnat a
              ⟨cylinder I A, hC, rfl⟩))
          (measure_ne_top P (pastProcess B a ⁻¹' cylinder I A)) (1 : ℝ) =
        Lp.compMeasurePreserving L hmp Y
      rw [Lp.indicatorConstLp_compMeasurePreserving]
      congr 1
    change dist
      ((adaptedIndicator (P := P) 𝓕 a
        (measurableSet_pastCylinderEvents hsm hnat a
          ⟨cylinder I A, hC, rfl⟩) :
          lpMeas ℝ ℝ (𝓕 a) 2 P) : Lp ℝ 2 P) (Z : Lp ℝ 2 P) < ε
    rw [hI, hZ, (Lp.isometry_compMeasurePreserving hmp).dist_eq]
    exact hdist

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- Smooth bounded functions of finitely many Brownian coordinates are dense in every time
section of the natural filtration. -/
theorem pastCylinderDense
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) :
    PastCylinderDense hB coordinate coordinate_apply hsm hnat := by
  intro a
  let _ : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let K : Submodule ℝ (lpMeas ℝ ℝ (𝓕 a) 2 P) :=
    pastCylinderSpan hB coordinate coordinate_apply hsm hnat a
  let e : lpMeas ℝ ℝ (𝓕 a) 2 P ≃ₗᵢ[ℝ]
      @Lp W ℝ (𝓕 a) _ 2 (P.trim (𝓕.le a)) :=
    lpMeasToLpTrimLie ℝ ℝ 2 P (𝓕.le a)
  let R : Submodule ℝ (@Lp W ℝ (𝓕 a) _ 2 (P.trim (𝓕.le a))) :=
    K.map (e : lpMeas ℝ ℝ (𝓕 a) 2 P →ₗ[ℝ]
      @Lp W ℝ (𝓕 a) _ 2 (P.trim (𝓕.le a)))
  have hMD := measureDense_pastCylinderEvents hB hsm hnat a
  have hone {s : Set W} (hs : MeasurableSet[𝓕 a] s)
      (hPs : P.trim (𝓕.le a) s ≠ ∞) :
      indicatorConstLp 2 hs hPs (1 : ℝ) ∈ R.topologicalClosure := by
    have happ := Measure.MeasureDense.indicatorConstLp_subset_closure
      (X := W) (E := ℝ) (m := 𝓕 a) (μ := P.trim (𝓕.le a))
      (𝒜 := pastCylinderEvents B a) 2 hMD (1 : ℝ) ⟨s, hs, hPs, rfl⟩
    apply (closure_minimal _ R.isClosed_topologicalClosure) happ
    rintro y ⟨t, ht, hPt, rfl⟩
    let Z := adaptedIndicator (P := P) 𝓕 a
      (measurableSet_pastCylinderEvents hsm hnat a ht)
    have hZ : Z ∈ K.topologicalClosure := by
      exact adaptedIndicator_pastCylinder_mem_closure
        hB coordinate coordinate_apply hsm hnat a ht
    have heq : e Z = indicatorConstLp 2
        (measurableSet_pastCylinderEvents hsm hnat a ht) hPt (1 : ℝ) := by
      apply e.symm.injective
      rw [e.symm_apply_apply]
      apply Subtype.ext
      simpa only [Z, adaptedIndicator] using
        (lpMeasToLpTrimLie_symm_indicator (F := ℝ) (p := 2)
          (μ := P) (hm := 𝓕.le a)
          (measurableSet_pastCylinderEvents hsm hnat a ht) hPt (1 : ℝ)).symm
    rw [← heq]
    apply K.topologicalClosure_map
      (e : lpMeas ℝ ℝ (𝓕 a) 2 P →L[ℝ]
        @Lp W ℝ (𝓕 a) _ 2 (P.trim (𝓕.le a)))
    exact ⟨Z, hZ, rfl⟩
  exact dense_of_closure_map_eq_top e K
    (@closure_eq_top_of_indicators W (𝓕 a) (P.trim (𝓕.le a)) R
      fun _ hs hPs => hone hs hPs)

/-- Malliavin--Itô duality against elementary processes in the natural filtration. -/
theorem smoothElementaryNaturalItoDuality_natural
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) :
    SmoothElementaryNaturalItoDuality
      hB coordinate coordinate_apply generated hsm hnat := by
  exact smoothElementaryNaturalItoDuality_of_pastCylinderDense
    hB coordinate coordinate_apply generated hsm hnat
      (pastCylinderDense hB coordinate coordinate_apply hsm hnat)

/-- Smooth-core Malliavin--Itô duality in the natural filtration. -/
theorem smoothNaturalItoDuality_natural
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) :
    SmoothNaturalItoDuality
      hB coordinate coordinate_apply generated hsm hnat := by
  exact smoothNaturalItoDuality_of_elementary
    hB coordinate coordinate_apply generated hsm hnat
      (smoothElementaryNaturalItoDuality_natural
        hB coordinate coordinate_apply generated hsm hnat)

/-- Malliavin--Itô duality for every `D12` functional and natural predictable integrand. -/
theorem naturalItoDuality_natural
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (F : D12 P) (U : PredictableProcessL2 𝓕 P) :
    inner ℝ (F.1 - expectationL2 F.1) (naturalItoIntegral hB hsm hnat U) =
      inner ℝ
        (predictableProjection 𝓕
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (mderivD12 P F))) U := by
  exact naturalItoDuality_of_smooth
    hB coordinate coordinate_apply generated hsm hnat
      (smoothNaturalItoDuality_natural
        hB coordinate coordinate_apply generated hsm hnat) F U

end PastProcess

end Malliavin

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
