/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Elliptic.Core2
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Elliptic.Core2

/-!
# Hopf problem: foundations · local orbit quotient

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private theorem BranchedQuotientAtlas.project_localInverse_eventuallyEq {E M Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace Q] {q : M → Q} (hq : Continuous q) (e : OpenPartialHomeomorph Q E) {z : E}
    (hz : z ∈ e.target) {a : M} (ha : q a = e.symm z)
    (hf :
      IsLocalDiffeomorphAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (e ∘ q) a) :
    q ∘ hf.localInverse =ᶠ[𝓝 z] e.symm := by
  have hcoord : (e ∘ q) a = z := by simp only [Function.comp_apply, ha, e.right_inv hz]
  have hinv : hf.localInverse z = a := by
    rw [← hcoord]
    exact hf.localInverse_left_inv hf.localInverse_mem_target
  have hcont : ContinuousAt (q ∘ hf.localInverse) z := by
    have h := hq.continuousAt.comp hf.localInverse_contMDiffAt.continuousAt
    simpa only [hcoord] using h
  have hsource : ∀ᶠ w in 𝓝 z, q (hf.localInverse w) ∈ e.source :=
    hcont
      (e.open_source.mem_nhds
        (by simpa only [Function.comp_apply, hinv, ha] using e.map_target hz))
  have hright : ∀ᶠ w in 𝓝 z, e (q (hf.localInverse w)) = w := by
    rw [← hcoord]
    exact hf.localInverse_eventuallyEq_right
  filter_upwards [hsource, hright] with w hw he
  change q (hf.localInverse w) = e.symm w
  exact (e.left_inv hw).symm.trans (congrArg e.symm he)

private theorem
    BranchedQuotientAtlas.contDiffAt_transition_of_lift {E M Q : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] {q : M → Q}
    (hq : Continuous q) (e f : OpenPartialHomeomorph Q E)
    (hhol :
      ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (f ∘ q)
        (q ⁻¹' f.source))
    {z : E} (hz : z ∈ (e.symm.trans f).source) {a : M} (ha : q a = e.symm z)
    (hf :
      IsLocalDiffeomorphAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (e ∘ q) a) :
    ContDiffAt ℂ ω (e.symm.trans f) z := by
  have hcoord : (e ∘ q) a = z := by simp only [Function.comp_apply, ha, e.right_inv hz.1]
  have hinv : hf.localInverse z = a := by
    rw [← hcoord]
    exact hf.localInverse_left_inv hf.localInverse_mem_target
  have hfirst :
    ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω hf.localInverse z := by
    simpa only [hcoord] using hf.localInverse_contMDiffAt
  have hsecond : ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (f ∘ q) a :=
    hhol.contMDiffAt
      ((f.open_source.preimage hq).mem_nhds
        (by
          change q a ∈ f.source
          rw [ha]
          exact hz.2))
  have hcomp : ContDiffAt ℂ ω ((f ∘ q) ∘ hf.localInverse) z :=
    (hsecond.comp_of_eq hfirst hinv).contDiffAt
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [project_localInverse_eventuallyEq hq e hz.1 ha hf] with w hw
  change f (e.symm w) = f (q (hf.localInverse w))
  exact congrArg f hw.symm

private structure
    BranchedQuotientAtlas.Data {E M Q : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] (q : M → Q) (ι : Type*) where
  chart : ι → OpenPartialHomeomorph Q E
  cover : ∀ x : Q, ∃ i, x ∈ (chart i).source
  continuous_project : Continuous q
  pullback_contMDiff :
    ∀ i,
      ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (chart i ∘ q)
        (q ⁻¹' (chart i).source)
  overlap_lift :
    ∀ i j,
      i ≠ j →
        ∀ z ∈ ((chart i).symm.trans (chart j)).source,
          ∃ a : M,
            q a = (chart i).symm z ∧
              IsLocalDiffeomorphAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
                (chart i ∘ q) a

private def
    BranchedQuotientAtlas.Data.indexAt {E M Q : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] {q : M → Q} {ι : Type*}
    (D : BranchedQuotientAtlas.Data (E := E) q ι) (x : Q) : ι :=
  (D.cover x).choose

private theorem BranchedQuotientAtlas.Data.mem_chart_source {E M Q : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] {q : M → Q}
    {ι : Type*} (D : BranchedQuotientAtlas.Data (E := E) q ι) (x : Q) :
    x ∈ (D.chart (D.indexAt x)).source :=
  (D.cover x).choose_spec

@[instance_reducible]
private def BranchedQuotientAtlas.Data.chartedSpace {E M Q : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] {q : M → Q}
    {ι : Type*} (D : BranchedQuotientAtlas.Data (E := E) q ι) : ChartedSpace E Q
    where
  atlas := Set.range D.chart
  chartAt x := D.chart (D.indexAt x)
  mem_chart_source := D.mem_chart_source
  chart_mem_atlas x := Set.mem_range_self (D.indexAt x)

private theorem BranchedQuotientAtlas.Data.chart_mem_atlas {E M Q : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] {q : M → Q}
    {ι : Type*} (D : BranchedQuotientAtlas.Data (E := E) q ι) (i : ι) :
    letI := D.chartedSpace
    D.chart i ∈ atlas E Q :=
  Set.mem_range_self i

private theorem BranchedQuotientAtlas.Data.chartAt_eq {E M Q : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] {q : M → Q}
    {ι : Type*} (D : BranchedQuotientAtlas.Data (E := E) q ι) (x : Q) :
    letI := D.chartedSpace
    chartAt E x = D.chart (D.indexAt x) :=
  rfl

private theorem
    BranchedQuotientAtlas.Data.contDiffOn_transition {E M Q : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] {q : M → Q}
    {ι : Type*} (D : BranchedQuotientAtlas.Data (E := E) q ι) (i j : ι) :
    ContDiffOn ℂ ω ((D.chart i).symm.trans (D.chart j))
      ((D.chart i).symm.trans (D.chart j)).source := by
  intro z hz
  by_cases hij : i = j
  · subst j
    apply contDiffWithinAt_id.congr_of_mem ?_ hz
    intro w hw
    exact (D.chart i).right_inv hw.1
  · obtain ⟨a, ha, hf⟩ := D.overlap_lift i j hij z hz
    exact
      (BranchedQuotientAtlas.contDiffAt_transition_of_lift D.continuous_project (D.chart i)
          (D.chart j) (D.pullback_contMDiff j) hz ha hf).contDiffWithinAt

private theorem BranchedQuotientAtlas.Data.isManifold {E M Q : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] {q : M → Q}
    {ι : Type*} (D : BranchedQuotientAtlas.Data (E := E) q ι) :
    letI := D.chartedSpace
    IsManifold (modelWithCornersSelf ℂ E) ω Q := by
  let := D.chartedSpace
  apply isManifold_of_contDiffOn
  rintro e f ⟨i, rfl⟩ ⟨j, rfl⟩
  simpa using D.contDiffOn_transition i j

private theorem BranchedQuotientAtlas.Data.contMDiff_project {E M Q : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] {q : M → Q}
    {ι : Type*} (D : BranchedQuotientAtlas.Data (E := E) q ι) :
    letI := D.chartedSpace
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω q := by
  let := D.chartedSpace
  let := D.isManifold
  intro a
  have hsource := D.mem_chart_source (q a)
  have hhol :=
    (D.pullback_contMDiff (D.indexAt (q a))).contMDiffAt
      (((D.chart (D.indexAt (q a))).open_source.preimage D.continuous_project).mem_nhds hsource)
  apply
    (contMDiffAt_iff_target_of_mem_source (I := (modelWithCornersSelf ℂ E)) (I' :=
        (modelWithCornersSelf ℂ E)) (D.mem_chart_source (q a))).mpr
  refine ⟨D.continuous_project.continuousAt, ?_⟩
  simpa [extChartAt, OpenPartialHomeomorph.extend, D.chartAt_eq, Function.comp_def] using hhol

private def OnePointAtlas.inclusionChart {Q : Type*} [TopologicalSpace Q] [Nonempty Q] :
    OpenPartialHomeomorph Q (OnePoint Q) :=
  OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph ((↑) : Q → OnePoint Q)

@[simp]
private theorem OnePointAtlas.inclusionChart_source {Q : Type*} [TopologicalSpace Q] [Nonempty Q] :
    (inclusionChart (Q := Q)).source = Set.univ :=
  OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph_source _

@[simp]
private theorem OnePointAtlas.inclusionChart_target {Q : Type*} [TopologicalSpace Q] [Nonempty Q] :
    (inclusionChart (Q := Q)).target = Set.range ((↑) : Q → OnePoint Q) :=
  OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph_target _

@[simp]
private theorem OnePointAtlas.inclusionChart_symm_coe {Q : Type*} [TopologicalSpace Q] [Nonempty Q]
    (q : Q) : (inclusionChart (Q := Q)).symm (q : OnePoint Q) = q :=
  (inclusionChart (Q := Q)).left_inv (by simp)

private def OnePointAtlas.oldChart {Q : Type*} [TopologicalSpace Q] [Nonempty Q] [ChartedSpace ℂ Q]
    (q : Q) : OpenPartialHomeomorph (OnePoint Q) ℂ :=
  (inclusionChart (Q := Q)).symm.trans (chartAt ℂ q)

@[simp]
private theorem OnePointAtlas.oldChart_coe {Q : Type*} [TopologicalSpace Q] [Nonempty Q]
    [ChartedSpace ℂ Q] (q x : Q) : oldChart q (x : OnePoint Q) = chartAt ℂ q x := by
  change chartAt ℂ q ((inclusionChart (Q := Q)).symm (x : OnePoint Q)) = _
  rw [inclusionChart_symm_coe]

private theorem OnePointAtlas.oldChart_comp_coe {Q : Type*} [TopologicalSpace Q] [Nonempty Q]
    [ChartedSpace ℂ Q] (q : Q) : oldChart q ∘ ((↑) : Q → OnePoint Q) = chartAt ℂ q := by
  funext x
  exact oldChart_coe q x

@[simp]
private theorem OnePointAtlas.coe_mem_oldChart_source {Q : Type*} [TopologicalSpace Q] [Nonempty Q]
    [ChartedSpace ℂ Q] (q x : Q) :
    (x : OnePoint Q) ∈ (oldChart q).source ↔ x ∈ (chartAt ℂ q).source := by
  change
    ((x : OnePoint Q) ∈ (inclusionChart (Q := Q)).target ∧
        (inclusionChart (Q := Q)).symm (x : OnePoint Q) ∈ (chartAt ℂ q).source) ↔
      _
  simp only [inclusionChart_target, Set.mem_range_self, inclusionChart_symm_coe, true_and]

private theorem OnePointAtlas.oldChart_preimage_source {Q : Type*} [TopologicalSpace Q] [Nonempty Q]
    [ChartedSpace ℂ Q] (q : Q) :
    ((↑) : Q → OnePoint Q) ⁻¹' (oldChart q).source = (chartAt ℂ q).source := by
  ext x
  exact coe_mem_oldChart_source q x

private theorem
    OnePointAtlas.infty_not_mem_oldChart_source {Q : Type*} [TopologicalSpace Q] [Nonempty Q]
    [ChartedSpace ℂ Q] (q : Q) : ((OnePoint.infty) : OnePoint Q) ∉ (oldChart q).source := by
  intro hx
  have hr : ((OnePoint.infty) : OnePoint Q) ∈ Set.range ((↑) : Q → OnePoint Q) :=
    inclusionChart_target (Q := Q) ▸ hx.1
  obtain ⟨x, hx⟩ := hr
  exact OnePoint.coe_ne_infty x hx

private theorem
    OnePointAtlas.oldChart_pullback_holomorphic {Q : Type*} [TopologicalSpace Q] [Nonempty Q]
    [ChartedSpace ℂ Q] [IsManifold 𝓘(ℂ) ω Q] (q : Q) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (oldChart q ∘ ((↑) : Q → OnePoint Q))
      (((↑) : Q → OnePoint Q) ⁻¹' (oldChart q).source) := by
  rw [oldChart_comp_coe, oldChart_preimage_source]
  exact contMDiffOn_chart

private theorem OnePointAtlas.oldChart_pullback_localDiffeomorph {Q : Type*} [TopologicalSpace Q]
    [Nonempty Q] [ChartedSpace ℂ Q] [IsManifold 𝓘(ℂ) ω Q] (q x : Q)
    (hx : (x : OnePoint Q) ∈ (oldChart q).source) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (oldChart q ∘ ((↑) : Q → OnePoint Q)) x := by
  rw [oldChart_comp_coe]
  refine
    ⟨{  toPartialEquiv := (chartAt ℂ q).toPartialEquiv
        open_source := (chartAt ℂ q).open_source
        open_target := (chartAt ℂ q).open_target
        contMDiffOn_toFun := contMDiffOn_chart
        contMDiffOn_invFun := contMDiffOn_chart_symm }, ?_, ?_⟩
  · exact (coe_mem_oldChart_source q x).mp hx
  · exact Set.eqOn_refl _ _

private def OnePointAtlas.chart {Q : Type*} [TopologicalSpace Q] [Nonempty Q] [ChartedSpace ℂ Q]
    (e : OpenPartialHomeomorph (OnePoint Q) ℂ) : Option Q → OpenPartialHomeomorph (OnePoint Q) ℂ
  | none => e
  | some q => oldChart q

private theorem
    OnePointAtlas.chart_cover {Q : Type*} [TopologicalSpace Q] [Nonempty Q] [ChartedSpace ℂ Q]
    (e : OpenPartialHomeomorph (OnePoint Q) ℂ) (he : ((OnePoint.infty) : OnePoint Q) ∈ e.source)
    (x : OnePoint Q) : ∃ i, x ∈ (chart e i).source := by
  induction x using OnePoint.rec
  · exact ⟨Option.none, he⟩
  · rename_i q
    exact ⟨Option.some q, (coe_mem_oldChart_source q q).mpr (mem_chart_source ℂ q)⟩

private theorem OnePointAtlas.overlap_ne_infty {Q : Type*} [TopologicalSpace Q] [Nonempty Q]
    [ChartedSpace ℂ Q] (e : OpenPartialHomeomorph (OnePoint Q) ℂ) (i j : Option Q) (hij : i ≠ j)
    (z : ℂ) (hz : z ∈ ((chart e i).symm.trans (chart e j)).source) :
    (chart e i).symm z ≠ ((OnePoint.infty) : OnePoint Q) := by
  intro hinfty
  cases i with
  | some q =>
    apply infty_not_mem_oldChart_source q
    rw [← hinfty]
    exact (oldChart q).map_target hz.1
  | none =>
    cases j with
    | none => exact hij rfl
    | some q =>
      apply infty_not_mem_oldChart_source q
      rw [← hinfty]
      exact hz.2

private def OnePointAtlas.data {Q : Type*} [TopologicalSpace Q] [Nonempty Q] [ChartedSpace ℂ Q]
    (e : OpenPartialHomeomorph (OnePoint Q) ℂ) [IsManifold 𝓘(ℂ) ω Q]
    (he : ((OnePoint.infty) : OnePoint Q) ∈ e.source)
    (hholo :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (e ∘ ((↑) : Q → OnePoint Q)) (((↑) : Q → OnePoint Q) ⁻¹' e.source))
    (hlocal :
      ∀ x : Q,
        (x : OnePoint Q) ∈ e.source →
          IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (e ∘ ((↑) : Q → OnePoint Q)) x) :
    BranchedQuotientAtlas.Data (E := ℂ) ((↑) : Q → OnePoint Q) (Option Q)
    where
  chart := chart e
  cover := chart_cover e he
  continuous_project := OnePoint.continuous_coe
  pullback_contMDiff
    i := by
    cases i with
    | none => exact hholo
    | some q => exact oldChart_pullback_holomorphic q
  overlap_lift i j hij z
    hz := by
    have hne := overlap_ne_infty e i j hij z hz
    obtain ⟨x, hx⟩ : ∃ x : Q, (x : OnePoint Q) = (chart e i).symm z := by
      induction h : (chart e i).symm z using OnePoint.rec
      · exact (hne h).elim
      · rename_i x
        exact ⟨x, rfl⟩
    have hsource : (x : OnePoint Q) ∈ (chart e i).source := by
      rw [hx]
      exact (chart e i).map_target hz.1
    refine ⟨x, hx, ?_⟩
    cases i with
    | none => exact hlocal x hsource
    | some q => exact oldChart_pullback_localDiffeomorph q x hsource

private def FreeActionLocus.locus (G X : Type*) [Group G] [MulAction G X] : Set X :=
  {x | ∀ g : G, g • x = x → g = 1}

private abbrev FreeActionLocus.Space (G X : Type*) [Group G] [MulAction G X] :=
  { x : X // x ∈ locus G X }

private theorem
    FreeActionLocus.smul_mem_locus (G X : Type*) [Group G] [MulAction G X] (g : G) {x : X}
    (hx : x ∈ locus G X) : g • x ∈ locus G X := by
  intro h hh
  have he : g⁻¹ * h * g = 1 :=
    hx _
      (by
        simpa only [SemigroupAction.mul_smul, inv_smul_smul] using congrArg (fun y => g⁻¹ • y) hh)
  simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left, inv_mul_cancel,
    one_mul] using congrArg (fun k : G => g * k * g⁻¹) he

private theorem FreeActionLocus.smul_mem_locus_iff (G X : Type*) [Group G] [MulAction G X] (g : G)
    (x : X) : g • x ∈ locus G X ↔ x ∈ locus G X := by
  refine ⟨fun hx => ?_, smul_mem_locus G X g⟩
  simpa only [inv_smul_smul] using smul_mem_locus G X g⁻¹ hx

private instance FreeActionLocus.mulAction (G X : Type*) [Group G] [MulAction G X] :
    MulAction G (Space G X)
    where
  smul g x := ⟨g • x.val, smul_mem_locus G X g x.property⟩
  one_smul x := Subtype.ext (one_smul G x.val)
  mul_smul g h x := Subtype.ext (SemigroupAction.mul_smul g h x.val)

private instance FreeActionLocus.isCancelSMul (G X : Type*) [Group G] [MulAction G X] :
    IsCancelSMul G (Space G X) := by
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro g x hx
  exact x.property g (congrArg Subtype.val hx)

private instance FreeActionLocus.continuousConstSMul (G X : Type*) [Group G] [MulAction G X]
    [TopologicalSpace X] [ContinuousConstSMul G X] : ContinuousConstSMul G (Space G X) where
  continuous_const_smul
    g := ((ContinuousConstSMul.continuous_const_smul g).comp continuous_subtype_val).subtype_mk _

private instance FreeActionLocus.properlyDiscontinuousSMul (G X : Type*) [Group G] [MulAction G X]
    [TopologicalSpace X] [ProperlyDiscontinuousSMul G X] : ProperlyDiscontinuousSMul G (Space G X)
    where
  finite_disjoint_inter_image {K L} hK
    hL := by
    apply
      (ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := G)
          (hK.image continuous_subtype_val) (hL.image continuous_subtype_val)).subset
    rintro g ⟨y, ⟨x, hx, hxy⟩, hy⟩
    exact ⟨y.val, ⟨x.val, ⟨x, hx, rfl⟩, congrArg Subtype.val hxy⟩, ⟨y, hy, rfl⟩⟩

private theorem FreeActionLocus.isOfFinOrder_of_smul_eq (G X : Type*) [Group G] [MulAction G X]
    [TopologicalSpace X] [ProperlyDiscontinuousSMul G X] (g : G) (x : X) (hg : g • x = x) :
    IsOfFinOrder g := by
  let := (ProperlyDiscontinuousSMul.finite_stabilizer (Γ := G) x).fintype
  exact
    (MulAction.stabilizer G x).subtype.isOfFinOrder
      (isOfFinOrder_of_finite (⟨g, hg⟩ : MulAction.stabilizer G x))

private theorem
    FreeActionLocus.isOpen_locus (G X : Type*) [Group G] [MulAction G X] [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] [ContinuousConstSMul G X]
    [ProperlyDiscontinuousSMul G X] : IsOpen (locus G X) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨U, hU, hdis⟩ := ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self G x
  apply Filter.mem_of_superset hU
  intro y hy g hgy
  exact hx g (hdis g ⟨y, ⟨y, hy, hgy⟩, hy⟩)

private def
    FreeActionLocus.opens (G X : Type*) [Group G] [MulAction G X] [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X] :
    TopologicalSpace.Opens X :=
  ⟨locus G X, isOpen_locus G X⟩

private instance FreeActionLocus.chartedSpace (G X E : Type*) [Group G] [TopologicalSpace X]
    [MulAction G X] [T2Space X] [LocallyCompactSpace X] [ContinuousConstSMul G X]
    [ProperlyDiscontinuousSMul G X] [NormedAddCommGroup E] [ChartedSpace E X] :
    ChartedSpace E (Space G X) :=
  inferInstanceAs (ChartedSpace E (opens G X))

private theorem FreeActionLocus.smul_contMDiff (G X E : Type*) [Group G] [TopologicalSpace X]
    [MulAction G X] [T2Space X] [LocallyCompactSpace X] [ContinuousConstSMul G X]
    [ProperlyDiscontinuousSMul G X] [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E X]
    (n : ℕ∞ω)
    (hG :
      ∀ g : G,
        ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n (fun x : X => g • x))
    (g : G) :
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n
      (fun x : Space G X => g • x) := by
  intro x
  have he :
    ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n
        (fun y : Space G X => ((g • y : Space G X) : X)) x ↔
      ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n
        (fun y : Space G X => g • y) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (U := opens G X)
      (fun y : Space G X => g • y) Set.univ x
  exact he.mp (((hG g).comp (contMDiff_subtype_val (U := opens G X))) x)

@[instance_reducible]
private def LocalOrbitQuotient.restrictedAction {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (H : Subgroup G) (U : TopologicalSpace.Opens X)
    (hU : ∀ h : H, Set.MapsTo (fun x : X => (h : G) • x) U U) : MulAction H U
    where
  smul h x := ⟨(h : G) • (x : X), hU h x.property⟩
  one_smul x := Subtype.ext (one_smul G (x : X))
  mul_smul h k x := Subtype.ext (SemigroupAction.mul_smul (h : G) (k : G) (x : X))

private abbrev LocalOrbitQuotient.LocalQuotient {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (H : Subgroup G) (U : TopologicalSpace.Opens X)
    (hU : ∀ h : H, Set.MapsTo (fun x : X => (h : G) • x) U U) :=
  letI := restrictedAction H U hU
  Quotient (MulAction.orbitRel H U)

private def LocalOrbitQuotient.localProjection {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (H : Subgroup G) (U : TopologicalSpace.Opens X)
    (hU : ∀ h : H, Set.MapsTo (fun x : X => (h : G) • x) U U) : U → LocalQuotient H U hU :=
  Quotient.mk _

private theorem
    LocalOrbitQuotient.localProjection_eq_iff {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (H : Subgroup G) (U : TopologicalSpace.Opens X)
    (hU : ∀ h : H, Set.MapsTo (fun x : X => (h : G) • x) U U) (x y : U) :
    localProjection H U hU x = localProjection H U hU y ↔ ∃ h : H, (h : G) • (y : X) = (x : X) := by
  let := restrictedAction H U hU
  rw [localProjection, Quotient.eq]
  change (∃ h : H, h • y = x) ↔ _
  exact exists_congr fun h => Subtype.ext_iff

private theorem
    LocalOrbitQuotient.localProjection_surjective {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (H : Subgroup G) (U : TopologicalSpace.Opens X)
    (hU : ∀ h : H, Set.MapsTo (fun x : X => (h : G) • x) U U) :
    Function.Surjective (localProjection H U hU) :=
  Quotient.mk_surjective

private theorem
    LocalOrbitQuotient.localProjection_continuous {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (H : Subgroup G) (U : TopologicalSpace.Opens X)
    (hU : ∀ h : H, Set.MapsTo (fun x : X => (h : G) • x) U U) :
    Continuous (localProjection H U hU) :=
  continuous_quotient_mk'

private def
    LocalOrbitQuotient.imageOpen {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    (U : TopologicalSpace.Opens X) [ContinuousConstSMul G X] :
    TopologicalSpace.Opens (Quotient (MulAction.orbitRel G X)) :=
  ⟨Quotient.mk (MulAction.orbitRel G X) '' (U : Set X),
    MulAction.isOpenQuotientMap_quotientMk.isOpenMap _ U.isOpen⟩

private def LocalOrbitQuotient.imageProjection {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (U : TopologicalSpace.Opens X) [ContinuousConstSMul G X] :
    U → imageOpen (G := G) U := fun x => ⟨Quotient.mk _ (x : X), x, x.property, rfl⟩

private theorem
    LocalOrbitQuotient.imageProjection_surjective {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (U : TopologicalSpace.Opens X) [ContinuousConstSMul G X] :
    Function.Surjective (imageProjection (G := G) U) := by
  rintro ⟨q, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

private theorem
    LocalOrbitQuotient.imageProjection_continuous {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (U : TopologicalSpace.Opens X) [ContinuousConstSMul G X] :
    Continuous (imageProjection (G := G) U) :=
  (continuous_quotient_mk'.comp continuous_subtype_val).subtype_mk _

private theorem
    LocalOrbitQuotient.imageProjection_isOpenMap {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (U : TopologicalSpace.Opens X) [ContinuousConstSMul G X] :
    IsOpenMap (imageProjection (G := G) U) :=
  (MulAction.isOpenQuotientMap_quotientMk.isOpenMap.comp
        U.isOpen.isOpenMap_subtype_val).subtype_mk
    _

private theorem LocalOrbitQuotient.imageProjection_isOpenQuotientMap {G X : Type*} [Group G]
    [TopologicalSpace X] [MulAction G X] (U : TopologicalSpace.Opens X)
    [ContinuousConstSMul G X] : IsOpenQuotientMap (imageProjection (G := G) U) :=
  ⟨imageProjection_surjective U, imageProjection_continuous U, imageProjection_isOpenMap U⟩

private def
    LocalOrbitQuotient.localToImage {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    (H : Subgroup G) (U : TopologicalSpace.Opens X)
    (hU : ∀ h : H, Set.MapsTo (fun x : X => (h : G) • x) U U) [ContinuousConstSMul G X] :
    LocalQuotient H U hU → imageOpen (G := G) U :=
  Quotient.lift (imageProjection (G := G) U) fun x y h =>
    by
    apply Subtype.ext
    apply Quotient.sound
    obtain ⟨g, hg⟩ := h
    exact ⟨(g : G), congrArg Subtype.val hg⟩

private theorem
    LocalOrbitQuotient.localToImage_continuous {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (H : Subgroup G) (U : TopologicalSpace.Opens X)
    (hU : ∀ h : H, Set.MapsTo (fun x : X => (h : G) • x) U U) [ContinuousConstSMul G X] :
    Continuous (localToImage H U hU) :=
  (imageProjection_continuous U).quotient_lift _

private theorem
    LocalOrbitQuotient.localToImage_surjective {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (H : Subgroup G) (U : TopologicalSpace.Opens X)
    (hU : ∀ h : H, Set.MapsTo (fun x : X => (h : G) • x) U U) [ContinuousConstSMul G X] :
    Function.Surjective (localToImage H U hU) := by
  intro q
  obtain ⟨x, rfl⟩ := imageProjection_surjective U q
  exact ⟨localProjection H U hU x, rfl⟩

private theorem
    LocalOrbitQuotient.localToImage_isOpenMap {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (H : Subgroup G) (U : TopologicalSpace.Opens X)
    (hU : ∀ h : H, Set.MapsTo (fun x : X => (h : G) • x) U U) [ContinuousConstSMul G X] :
    IsOpenMap (localToImage H U hU) :=
  IsOpenMap.of_comp (localProjection_continuous H U hU) (localProjection_surjective H U hU)
    (imageProjection_isOpenMap U)

private theorem
    LocalOrbitQuotient.localToImage_injective {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (H : Subgroup G) (U : TopologicalSpace.Opens X)
    (hU : ∀ h : H, Set.MapsTo (fun x : X => (h : G) • x) U U) [ContinuousConstSMul G X]
    (hreturn : ∀ g : G, (((g • ·) '' (U : Set X)) ∩ U).Nonempty → g ∈ H) :
    Function.Injective (localToImage H U hU) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro x y h
  have hxy :
    Quotient.mk (MulAction.orbitRel G X) (x : X) = Quotient.mk (MulAction.orbitRel G X) (y : X) :=
    congrArg Subtype.val h
  obtain ⟨g, hg⟩ := Quotient.exact hxy
  have hgH : g ∈ H := hreturn g ⟨x, ⟨y, y.property, hg⟩, x.property⟩
  exact (localProjection_eq_iff H U hU x y).mpr ⟨⟨g, hgH⟩, hg⟩

private def LocalOrbitQuotient.localHomeomorph {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] (H : Subgroup G) (U : TopologicalSpace.Opens X)
    (hU : ∀ h : H, Set.MapsTo (fun x : X => (h : G) • x) U U) [ContinuousConstSMul G X]
    (hreturn : ∀ g : G, (((g • ·) '' (U : Set X)) ∩ U).Nonempty → g ∈ H) :
    LocalQuotient H U hU ≃ₜ imageOpen (G := G) U :=
  Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective (localToImage H U hU)
      ⟨localToImage_injective H U hU hreturn, localToImage_surjective H U hU⟩)
    (localToImage_continuous H U hU) (localToImage_isOpenMap H U hU)

private theorem
    isLocalDiffeomorphAt_of_comp_opensSubtypeVal {E F H K M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H]
    [TopologicalSpace K] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N]
    [ChartedSpace K N] (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ F K)
    (U : TopologicalSpace.Opens M) {f : M → N} (x : U)
    (hf : IsLocalDiffeomorphAt I J ω (f ∘ (Subtype.val : U → M)) x) :
    IsLocalDiffeomorphAt I J ω f (x : M) := by
  obtain ⟨φ, hx, he⟩ := hf
  let e := opensInclusionPartialDiffeomorph I U ⟨x⟩
  have hxU : (x : M) ∈ e.target := by
    change (x : M) ∈ (U.openPartialHomeomorphSubtypeCoe ⟨x⟩).target
    rw [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
    change (x : M) ∈ U
    exact x.property
  have hinv : e.symm (x : M) = x := e.left_inv (Set.mem_univ x)
  refine ⟨e.symm.trans φ, ⟨hxU, ?_⟩, ?_⟩
  · change e.symm (x : M) ∈ φ.source
    rw [hinv]
    exact hx
  intro y hy
  have hval : ((e.symm y : U) : M) = y := e.right_inv hy.1
  change f y = φ (e.symm y)
  exact (congrArg f hval.symm).trans (he hy.2)

public
theorem isLocalDiffeomorphAt_congr_of_eventuallyEq {E F H K M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H]
    [TopologicalSpace K] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N]
    [ChartedSpace K N] {I : ModelWithCorners ℂ E H} {J : ModelWithCorners ℂ F K} {n : ℕ∞ω}
    {f g : M → N} {x : M} (hf : IsLocalDiffeomorphAt I J n f x) (hgf : g =ᶠ[𝓝 x] f) :
    IsLocalDiffeomorphAt I J n g x := by
  obtain ⟨U, hUf, hU, hxU⟩ := mem_nhds_iff.mp hgf
  obtain ⟨Φ, hx, hΦ⟩ := hf
  let Ψ : PartialDiffeomorph I J M N n :=
    { toPartialEquiv := (Φ.toOpenPartialHomeomorph.restrOpen U hU).toPartialEquiv
      open_source := (Φ.toOpenPartialHomeomorph.restrOpen U hU).open_source
      open_target := (Φ.toOpenPartialHomeomorph.restrOpen U hU).open_target
      contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono Set.inter_subset_left
      contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono Set.inter_subset_left }
  refine ⟨Ψ, ⟨hx, hxU⟩, ?_⟩
  intro y hy
  exact (hUf hy.2).trans (hΦ hy.1)

end Mathoverflow1973

end
