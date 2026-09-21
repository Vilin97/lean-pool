/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Recognition.Smale1
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.Recognition.Smale1

/-!
# Hopf problem: foundations · core 2

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

private def ε : Lattice :=
  ![1, 2, -4, 0]

private def ε' : Lattice :=
  ![1, 3, -3, 0]

private def γ (v : Lattice) : ℤ :=
  v 0

private theorem det_T₁ : T₁.det = 1 := by decide

private theorem det_T₂ : T₂.det = 1 := by decide

private theorem γ_ε' : γ ε' = 1 :=
  rfl

private theorem contDiffOn_of_sub_mem_discrete {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : Submodule ℤ E) [DiscreteTopology L] {f : E → E} {s : Set E} (hf : ContinuousOn f s)
    (hL : ∀ x ∈ s, f x - x ∈ L) (n : ℕ∞ω) : ContDiffOn ℂ n f s := by
  let g : s → L := fun x => ⟨f x - x, hL x x.property⟩
  have hg : Continuous g := (hf.domRestrict.sub continuous_subtype_val).subtype_mk _
  have hg' : IsLocallyConstant g := (IsLocallyConstant.iff_continuous g).mpr hg
  intro x hx
  have heq : ∀ᶠ y in 𝓝[s] x, f y - y = f x - x := by
    apply (eventually_nhds_subtype_iff s ⟨x, hx⟩ _).mp
    exact (hg'.eventually_eq ⟨x, hx⟩).mono fun y hy => congrArg Subtype.val hy
  apply
    (contDiff_id.add contDiff_const).contDiffWithinAt.congr_of_eventuallyEq_of_mem (s := s) (f :=
      fun y => y + (f x - x)) ?_ hx
  exact heq.mono fun y hy => (sub_eq_iff_eq_add.mp hy).trans (add_comm _ _)

private theorem DiscreteQuotient.quotient_localHomeomorph {E : Type*} [NormedAddCommGroup E]
    (L : Submodule ℤ E) [DiscreteTopology L] : IsLocalHomeomorph (L.mkQ : E → E ⧸ L) := by
  have : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
  exact
    (AddSubgroup.isAddQuotientCoveringMap_of_comm L.toAddSubgroup
        DiscreteTopology.isDiscrete).isCoveringMap.isLocalHomeomorph

private def DiscreteQuotient.representative {E : Type*} [NormedAddCommGroup E] (L : Submodule ℤ E)
    (x : E ⧸ L) : E :=
  (L.mkQ_surjective x).choose

private theorem
    DiscreteQuotient.mkQ_representative {E : Type*} [NormedAddCommGroup E] (L : Submodule ℤ E)
    (x : E ⧸ L) : L.mkQ (representative L x) = x :=
  (L.mkQ_surjective x).choose_spec

private def DiscreteQuotient.chart {E : Type*} [NormedAddCommGroup E] (L : Submodule ℤ E)
    [DiscreteTopology L] (x : E ⧸ L) : OpenPartialHomeomorph (E ⧸ L) E :=
  (quotient_localHomeomorph L).localInverseAt (representative L x)

private instance
    DiscreteQuotient.chartedSpace {E : Type*} [NormedAddCommGroup E] (L : Submodule ℤ E)
    [DiscreteTopology L] : ChartedSpace E (E ⧸ L)
    where
  atlas := Set.range (chart L)
  chartAt := chart L
  mem_chart_source
    x := by
    have h :=
      (quotient_localHomeomorph L).apply_self_mem_localInverseAt_source (x := representative L x)
    simpa only [chart, mkQ_representative] using h
  chart_mem_atlas x := Set.mem_range_self x

@[simp]
private theorem DiscreteQuotient.chart_symm {E : Type*} [NormedAddCommGroup E] (L : Submodule ℤ E)
    [DiscreteTopology L] (x : E ⧸ L) : (chart L x).symm = (L.mkQ : E → E ⧸ L) :=
  (quotient_localHomeomorph L).localInverseAt_symm (representative L x)

private theorem DiscreteQuotient.mkQ_chart {E : Type*} [NormedAddCommGroup E] (L : Submodule ℤ E)
    [DiscreteTopology L] (x y : E ⧸ L) (hy : y ∈ (chart L x).source) : L.mkQ (chart L x y) = y :=
  (quotient_localHomeomorph L).apply_localInverseAt_of_mem hy

private theorem
    DiscreteQuotient.transition_sub_mem {E : Type*} [NormedAddCommGroup E] (L : Submodule ℤ E)
    [DiscreteTopology L] (x y : E ⧸ L) (z : E)
    (hz : z ∈ ((chart L x).symm.trans (chart L y)).source) :
    ((chart L x).symm.trans (chart L y)) z - z ∈ L := by
  apply (Submodule.Quotient.eq L).mp
  change L.mkQ (((chart L x).symm.trans (chart L y)) z) = L.mkQ z
  rw [OpenPartialHomeomorph.trans_apply, chart_symm]
  apply mkQ_chart
  simpa only [OpenPartialHomeomorph.symm_symm, chart_symm, Set.mem_preimage] using hz.2

private instance DiscreteQuotient.isManifold {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : Submodule ℤ E) [DiscreteTopology L] (n : ℕ∞ω) :
    IsManifold (modelWithCornersSelf ℂ E) n (E ⧸ L) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨x, rfl⟩ := he
  obtain ⟨y, rfl⟩ := he'
  have h :=
    contDiffOn_of_sub_mem_discrete L ((chart L x).symm.trans (chart L y)).continuousOn
      (transition_sub_mem L x y) n
  simpa using h

private theorem DiscreteQuotient.contMDiff_mkQ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : Submodule ℤ E) [DiscreteTopology L] (n : ℕ∞ω) :
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n (L.mkQ : E → E ⧸ L) := by
  apply contMDiff_iff.mpr
  refine ⟨L.continuous_mkQ, ?_⟩
  intro x y
  have h : ContDiffOn ℂ n (chart L y ∘ L.mkQ) (L.mkQ ⁻¹' (chart L y).source) := by
    apply contDiffOn_of_sub_mem_discrete L
    · exact (chart L y).continuousOn.comp L.continuous_mkQ.continuousOn (fun z hz => hz)
    · intro z hz
      exact (Submodule.Quotient.eq L).mp (mkQ_chart L y (L.mkQ z) hz)
  have hchart : chartAt E y = chart L y := rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, chartAt_self_eq] using h

private theorem DiscreteQuotient.contMDiff_of_comp_mkQ {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (L : Submodule ℤ E) [DiscreteTopology L] {F H M : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] (I : ModelWithCorners ℂ F H) (n : ℕ∞ω) {f : E ⧸ L → M}
    (hf : ContMDiff (modelWithCornersSelf ℂ E) I n (f ∘ L.mkQ)) :
    ContMDiff (modelWithCornersSelf ℂ E) I n f := by
  intro x
  rw [contMDiffAt_iff_source]
  have hchart : chartAt E x = chart L x := rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, chart_symm] using
    (hf.contMDiffAt.contMDiffWithinAt (s := Set.univ) (x := chart L x x))

private instance DiscreteQuotient.lieAddGroup {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : Submodule ℤ E) [DiscreteTopology L] (n : ℕ∞ω) :
    LieAddGroup (modelWithCornersSelf ℂ E) n (E ⧸ L)
    where
  contMDiff_add := by
    have h :
      ContMDiff (modelWithCornersSelf ℂ (E × E)) (modelWithCornersSelf ℂ E) n
        (fun z : E × E => L.mkQ (z.1 + z.2)) :=
      (contMDiff_mkQ L n).comp (contDiff_fst.add contDiff_snd).contMDiff
    intro x
    rw [contMDiffAt_iff_source]
    have hchart : ∀ y : E ⧸ L, chartAt E y = chart L y := fun _ => rfl
    have hs :
      ((extChartAt ((modelWithCornersSelf ℂ E).prod (modelWithCornersSelf ℂ E)) x).symm :
          E × E → (E ⧸ L) × (E ⧸ L)) =
        fun z => (L.mkQ z.1, L.mkQ z.2) := by
      rw [extChartAt_prod, PartialEquiv.prod_coe_symm]
      simp only [extChartAt_coe_symm, hchart, chart_symm, modelWithCornersSelf_coe_symm,
        Function.comp_def, id_eq]
    have ht :
      extChartAt ((modelWithCornersSelf ℂ E).prod (modelWithCornersSelf ℂ E)) x x =
        (chart L x.1 x.1, chart L x.2 x.2) :=
      rfl
    have hr : Set.range ((modelWithCornersSelf ℂ E).prod (modelWithCornersSelf ℂ E)) = Set.univ :=
      Set.range_eq_univ.mpr fun z => ⟨z, rfl⟩
    rw [hs, ht, hr]
    simpa only [Function.comp_def, map_add] using
      (h.contMDiffAt.contMDiffWithinAt (s := Set.univ) (x := (chart L x.1 x.1, chart L x.2 x.2)))
  contMDiff_neg := by
    apply contMDiff_of_comp_mkQ L (modelWithCornersSelf ℂ E) n
    simpa [Function.comp_def, map_neg] using
      (contMDiff_mkQ L n).comp (contDiff_neg : ContDiff ℂ n (fun z : E => -z)).contMDiff

/-- The two-dimensional complex coordinate space. -/
public
abbrev ComplexPlane₂ :=
  Fin 2 → ℂ

private def complexCoordinates : (Fin 4 → ℝ) ≃ₗ[ℝ] ComplexPlane₂
    where
  toFun x := ![⟨x 0, x 1⟩, ⟨x 2, x 3⟩]
  invFun z := ![(z 0).re, (z 0).im, (z 1).re, (z 1).im]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv z := by ext i; fin_cases i <;> rfl
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' r
    x := by
    ext i : 1
    fin_cases i <;> apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

private abbrev RealPair₂ :=
  (Fin 2 → ℝ) × (Fin 2 → ℝ)

private def
    DiscreteQuotient.linearBiholomorph {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (L : Submodule ℤ E) (K : Submodule ℤ F)
    [DiscreteTopology L] [DiscreteTopology K] (e : E ≃L[ℂ] F)
    (h : L.map (e.toLinearEquiv.restrictScalars ℤ).toLinearMap = K) :
    Diffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) (E ⧸ L) (F ⧸ K) ω
    where
  toEquiv := (Submodule.Quotient.equiv L K (e.toLinearEquiv.restrictScalars ℤ) h).toEquiv
  contMDiff_toFun := by
    apply contMDiff_of_comp_mkQ
    exact (contMDiff_mkQ K ω).comp e.contDiff.contMDiff
  contMDiff_invFun := by
    apply contMDiff_of_comp_mkQ
    exact (contMDiff_mkQ L ω).comp e.symm.contDiff.contMDiff

private def columnLattice (P : Matrix (Fin 2) (Fin 4) ℂ) : Submodule ℤ ComplexPlane₂ :=
  Submodule.span ℤ (Set.range P.col)

private theorem column_mul_mem (P : Matrix (Fin 2) (Fin 4) ℂ) (A : LatticeMatrix) (j : Fin 4) :
    (P * A.map (Int.castRingHom ℂ)).col j ∈ columnLattice P := by
  have he : (P * A.map (Int.castRingHom ℂ)).col j = ∑ k, A k j • P.col k := by
    ext i
    simp [Matrix.mul_apply, Matrix.col, Matrix.transpose_apply, zsmul_eq_mul, mul_comm]
  rw [he]
  exact
    Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))

private theorem columnLattice_mul_le (P : Matrix (Fin 2) (Fin 4) ℂ) (A : LatticeMatrix) :
    columnLattice (P * A.map (Int.castRingHom ℂ)) ≤ columnLattice P := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact column_mul_mem P A j

private theorem columnLattice_mul_eq (P : Matrix (Fin 2) (Fin 4) ℂ) (A B : LatticeMatrix)
    (hAB : A * B = 1) : columnLattice (P * A.map (Int.castRingHom ℂ)) = columnLattice P := by
  apply le_antisymm (columnLattice_mul_le P A)
  have hP : (P * A.map (Int.castRingHom ℂ)) * B.map (Int.castRingHom ℂ) = P := by
    rw [Matrix.mul_assoc, ← Matrix.map_mul, hAB]
    simp
  have h := columnLattice_mul_le (P * A.map (Int.castRingHom ℂ)) B
  rwa [hP] at h

private theorem map_columnLattice (P : Matrix (Fin 2) (Fin 4) ℂ) (R : Matrix (Fin 2) (Fin 2) ℂ) :
    (columnLattice P).map (R.mulVecLin.restrictScalars ℤ) = columnLattice (R * P) := by
  rw [columnLattice, columnLattice, Submodule.map_span]
  congr 1
  rw [← Set.range_comp]
  congr 1

private theorem eventuallyEq_of_localHomeomorph_comp_eq {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {q : X → Y} (hq : IsLocalHomeomorph q) {f g : Z → X}
    {z : Z} (hf : ContinuousAt f z) (hg : ContinuousAt g z) (hz : f z = g z)
    (he : ∀ᶠ w in 𝓝 z, q (f w) = q (g w)) : f =ᶠ[𝓝 z] g := by
  let e := hq.localInverseAt (f z)
  have hU : e.target ∈ 𝓝 (f z) := e.open_target.mem_nhds hq.self_mem_localInverseAt_target
  have hfU : ∀ᶠ w in 𝓝 z, f w ∈ e.target := hf hU
  have hgU : ∀ᶠ w in 𝓝 z, g w ∈ e.target := hg (hz ▸ hU)
  filter_upwards [hfU, hgU, he] with w hfw hgw hw
  exact hq.injOn_localInverseAt_target hfw hgw hw

private theorem quotientCoveringMap_of_localHomeomorph {X Y G : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [Group G] [MulAction G X] [ContinuousConstSMul G X] [IsCancelSMul G X]
    {q : X → Y} (hq : IsLocalHomeomorph q) (hs : Function.Surjective q)
    (ho : ∀ x y, q x = q y ↔ x ∈ MulAction.orbit G y) : IsQuotientCoveringMap q G
    where
  toIsQuotientMap := hq.isOpenMap.isQuotientMap hq.continuous hs
  continuous_const_smul := ContinuousConstSMul.continuous_const_smul
  apply_eq_iff_mem_orbit := ho _ _
  disjoint
    x := by
    let e := hq.localInverseAt x
    refine ⟨e.target, e.open_target.mem_nhds hq.self_mem_localInverseAt_target, ?_⟩
    rintro g ⟨z, ⟨w, hw, rfl⟩, hgw⟩
    have heq : q (g • w) = q w := (ho _ _).mpr ⟨g, rfl⟩
    have heq' : g • w = (1 : G) • w := by
      simpa only [one_smul] using hq.injOn_localInverseAt_target hgw hw heq
    exact IsCancelSMul.right_cancel _ _ w heq'

private theorem localHomeomorph_prod_id {B X Y : Type*} [TopologicalSpace B] [TopologicalSpace X]
    [TopologicalSpace Y] {q : X → Y} (hq : IsLocalHomeomorph q) :
    IsLocalHomeomorph (fun z : B × X => (z.1, q z.2)) := by
  intro x
  obtain ⟨e, he, hqe⟩ := hq x.2
  refine ⟨(OpenPartialHomeomorph.refl B).prod e, ⟨Set.mem_univ _, he⟩, ?_⟩
  funext y
  exact congrArg (Prod.mk y.1) (congrFun hqe y.2)

private def
    CoveringQuotient.representative {M Q G : Type*} [TopologicalSpace M] [TopologicalSpace Q]
    [Group G] [MulAction G M] {q : M → Q} (hq : IsQuotientCoveringMap q G) (x : Q) : M :=
  (hq.surjective x).choose

private theorem CoveringQuotient.project_representative {M Q G : Type*} [TopologicalSpace M]
    [TopologicalSpace Q] [Group G] [MulAction G M] {q : M → Q} (hq : IsQuotientCoveringMap q G)
    (x : Q) : q (representative hq x) = x :=
  (hq.surjective x).choose_spec

private def CoveringQuotient.localInverse {M Q G : Type*} [TopologicalSpace M] [TopologicalSpace Q]
    [Group G] [MulAction G M] {q : M → Q} (hq : IsQuotientCoveringMap q G) (x : M) :
    OpenPartialHomeomorph Q M :=
  hq.isCoveringMap.isLocalHomeomorph.localInverseAt x

@[simp]
private theorem CoveringQuotient.localInverse_symm {M Q G : Type*} [TopologicalSpace M]
    [TopologicalSpace Q] [Group G] [MulAction G M] {q : M → Q} (hq : IsQuotientCoveringMap q G)
    (x : M) : (localInverse hq x).symm = q :=
  hq.isCoveringMap.isLocalHomeomorph.localInverseAt_symm x

private theorem CoveringQuotient.project_localInverse {M Q G : Type*} [TopologicalSpace M]
    [TopologicalSpace Q] [Group G] [MulAction G M] {q : M → Q} (hq : IsQuotientCoveringMap q G)
    (x : M) {y : Q} (hy : y ∈ (localInverse hq x).source) : q (localInverse hq x y) = y :=
  hq.isCoveringMap.isLocalHomeomorph.apply_localInverseAt_of_mem hy

private theorem CoveringQuotient.contMDiffOn_lift {E M Q G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] [Group G]
    [MulAction G M] {q : M → Q} (hq : IsQuotientCoveringMap q G) (n : ℕ∞ω)
    (hG :
      ∀ g : G,
        ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n (fun x : M => g • x))
    (a : M) :
    ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n (localInverse hq a ∘ q)
      (q ⁻¹' (localInverse hq a).source) := by
  intro x hx
  have hcont : ContinuousAt (localInverse hq a ∘ q) x :=
    ((localInverse hq a).continuousAt hx).comp hq.continuous.continuousAt
  obtain ⟨g, hg⟩ := hq.apply_eq_iff_mem_orbit.mp (project_localInverse hq a hx)
  have hsource : ∀ᶠ y in 𝓝 x, q y ∈ (localInverse hq a).source :=
    hq.continuous.continuousAt ((localInverse hq a).open_source.mem_nhds hx)
  have heq : (localInverse hq a ∘ q) =ᶠ[𝓝 x] (fun y => g • y) := by
    apply
      eventuallyEq_of_localHomeomorph_comp_eq hq.isCoveringMap.isLocalHomeomorph hcont
        (hG g).continuous.continuousAt hg.symm
    exact hsource.mono fun y hy => (project_localInverse hq a hy).trans (hq.map_smul g).symm
  exact ((hG g).contMDiffAt.congr_of_eventuallyEq heq).contMDiffWithinAt

private def CoveringQuotient.chart {E M Q G : Type*} [NormedAddCommGroup E] [TopologicalSpace M]
    [ChartedSpace E M] [TopologicalSpace Q] [Group G] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G) (x : Q) : OpenPartialHomeomorph Q E :=
  (localInverse hq (representative hq x)).trans (chartAt E (representative hq x))

@[instance_reducible]
private def
    CoveringQuotient.chartedSpace {E M Q G : Type*} [NormedAddCommGroup E] [TopologicalSpace M]
    [ChartedSpace E M] [TopologicalSpace Q] [Group G] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G) : ChartedSpace E Q
    where
  atlas := Set.range (chart (E := E) hq)
  chartAt := chart (E := E) hq
  mem_chart_source
    x := by
    change
      x ∈ (localInverse hq (representative hq x)).source ∧
        localInverse hq (representative hq x) x ∈ (chartAt E (representative hq x)).source
    constructor
    · have h :=
        hq.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source (x :=
          representative hq x)
      simpa only [localInverse, project_representative] using h
    · have h : localInverse hq (representative hq x) x = representative hq x := by
        simpa only [localInverse, project_representative] using
          hq.isCoveringMap.isLocalHomeomorph.localInverseAt_apply_self (x := representative hq x)
      rw [h]
      exact mem_chart_source E (representative hq x)
  chart_mem_atlas x := Set.mem_range_self x

private theorem
    CoveringQuotient.chart_symm {E M Q G : Type*} [NormedAddCommGroup E] [TopologicalSpace M]
    [ChartedSpace E M] [TopologicalSpace Q] [Group G] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G) (x : Q) :
    ((chart (E := E) hq x).symm : E → Q) = q ∘ (chartAt E (representative hq x)).symm := by
  funext z
  change
    (localInverse hq (representative hq x)).symm ((chartAt E (representative hq x)).symm z) = _
  rw [localInverse_symm]
  rfl

private theorem CoveringQuotient.transition_eq {E M Q G : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] [Group G] [MulAction G M]
    {q : M → Q} (hq : IsQuotientCoveringMap q G) (x y : Q) :
    (((chart (E := E) hq x).symm.trans (chart (E := E) hq y)) : E → E) =
      chartAt E (representative hq y) ∘
        (localInverse hq (representative hq y) ∘ q) ∘ (chartAt E (representative hq x)).symm := by
  funext z
  simp only [OpenPartialHomeomorph.trans_apply, chart_symm, Function.comp_apply]
  rfl

private theorem CoveringQuotient.contDiffOn_transition {E M Q G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] [Group G]
    [MulAction G M] {q : M → Q} (hq : IsQuotientCoveringMap q G) (n : ℕ∞ω)
    [IsManifold (modelWithCornersSelf ℂ E) n M]
    (hG :
      ∀ g : G,
        ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n (fun x : M => g • x))
    (x y : Q) :
    ContDiffOn ℂ n ((chart (E := E) hq x).symm.trans (chart (E := E) hq y))
      ((chart (E := E) hq x).symm.trans (chart (E := E) hq y)).source := by
  intro z hz
  have hza : z ∈ (chartAt E (representative hq x)).target := hz.1.1
  have hy : q ((chartAt E (representative hq x)).symm z) ∈ (chart (E := E) hq y).source := by
    simpa only [OpenPartialHomeomorph.symm_symm, chart_symm, Function.comp_apply,
      Set.mem_preimage] using hz.2
  have ha := (chartAt E (representative hq x)).map_target hza
  have hb :
    localInverse hq (representative hq y) (q ((chartAt E (representative hq x)).symm z)) ∈
      (chartAt E (representative hq y)).source :=
    hy.2
  have hmid :=
    (contMDiffOn_lift hq n hG (representative hq y)).contMDiffAt
      (((localInverse hq (representative hq y)).open_source.preimage hq.continuous).mem_nhds hy.1)
  have hc := ((contMDiffAt_iff_of_mem_source ha hb).mp hmid).2
  have hc' :
    ContDiffAt ℂ n
      (chartAt E (representative hq y) ∘
        (localInverse hq (representative hq y) ∘ q) ∘ (chartAt E (representative hq x)).symm)
      z := by
    simpa [extChartAt, OpenPartialHomeomorph.extend, contDiffWithinAt_univ,
      (chartAt E (representative hq x)).right_inv hza] using hc
  rw [transition_eq]
  exact hc'.contDiffWithinAt

private theorem
    CoveringQuotient.isManifold {E M Q G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] [Group G] [MulAction G M]
    {q : M → Q} (hq : IsQuotientCoveringMap q G) (n : ℕ∞ω)
    [IsManifold (modelWithCornersSelf ℂ E) n M]
    (hG :
      ∀ g : G,
        ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n (fun x : M => g • x)) :
    letI := chartedSpace (E := E) hq
    IsManifold (modelWithCornersSelf ℂ E) n Q := by
  let := chartedSpace (E := E) hq
  apply isManifold_of_contDiffOn
  rintro e e' ⟨x, rfl⟩ ⟨y, rfl⟩
  simpa using contDiffOn_transition hq n hG x y

private theorem CoveringQuotient.contMDiff_project {E M Q G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] [Group G]
    [MulAction G M] {q : M → Q} (hq : IsQuotientCoveringMap q G) (n : ℕ∞ω)
    [IsManifold (modelWithCornersSelf ℂ E) n M]
    (hG :
      ∀ g : G,
        ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n (fun x : M => g • x)) :
    letI := chartedSpace (E := E) hq
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n q := by
  let := chartedSpace (E := E) hq
  let := isManifold hq n hG
  intro x
  have hy : q x ∈ (chart (E := E) hq (q x)).source := mem_chart_source E (q x)
  have hmid :=
    (contMDiffOn_lift hq n hG (representative hq (q x))).contMDiffAt
      (((localInverse hq (representative hq (q x))).open_source.preimage hq.continuous).mem_nhds
        hy.1)
  have hc :
    ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n
      (chartAt E (representative hq (q x))) (localInverse hq (representative hq (q x)) (q x)) := by
    simpa [extChartAt, OpenPartialHomeomorph.extend] using
      (contMDiffAt_extChartAt' (I := modelWithCornersSelf ℂ E) (n := n) hy.2)
  apply
    (contMDiffAt_iff_target_of_mem_source (I := modelWithCornersSelf ℂ E) (I' :=
        modelWithCornersSelf ℂ E) (mem_chart_source E (q x))).mpr
  refine ⟨hq.continuous.continuousAt, ?_⟩
  have hchart : chartAt E (q x) = chart (E := E) hq (q x) := rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, chart, Function.comp_def] using
    hc.comp x hmid

private theorem CoveringQuotient.contMDiff_of_comp {E M Q G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] [Group G]
    [MulAction G M] {q : M → Q} (hq : IsQuotientCoveringMap q G) {F H N : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H] [TopologicalSpace N]
    [ChartedSpace H N] (I : ModelWithCorners ℂ F H) (n : ℕ∞ω)
    [IsManifold (modelWithCornersSelf ℂ E) n M] {f : Q → N}
    (hf : ContMDiff (modelWithCornersSelf ℂ E) I n (f ∘ q)) :
    letI := chartedSpace (E := E) hq
    ContMDiff (modelWithCornersSelf ℂ E) I n f := by
  let := chartedSpace (E := E) hq
  intro x
  rw [contMDiffAt_iff_source]
  have hx : x ∈ (chart (E := E) hq x).source := mem_chart_source E x
  have hsrc :=
    (contMDiffAt_iff_source_of_mem_source (I := modelWithCornersSelf ℂ E) (I' := I) hx.2).mp
      (hf.contMDiffAt (x := localInverse hq (representative hq x) x))
  have hchart : chartAt E x = chart (E := E) hq x := rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, chart, Function.comp_def] using hsrc

private theorem CoveringQuotient.contMDiffOn_of_comp {E M Q G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] [Group G]
    [MulAction G M] {q : M → Q} (hq : IsQuotientCoveringMap q G) {F H N : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H] [TopologicalSpace N]
    [ChartedSpace H N] (I : ModelWithCorners ℂ F H) (n : ℕ∞ω)
    [IsManifold (modelWithCornersSelf ℂ E) n M] {f : Q → N} {U : Set Q} (hU : IsOpen U)
    (hf : ContMDiffOn (modelWithCornersSelf ℂ E) I n (f ∘ q) (q ⁻¹' U)) :
    letI := chartedSpace (E := E) hq
    ContMDiffOn (modelWithCornersSelf ℂ E) I n f U := by
  let := chartedSpace (E := E) hq
  intro x hxU
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_iff_source]
  have hx : x ∈ (chart (E := E) hq x).source := mem_chart_source E x
  have hpre : localInverse hq (representative hq x) x ∈ q ⁻¹' U := by
    change q (localInverse hq (representative hq x) x) ∈ U
    rw [project_localInverse hq _ hx.1]
    exact hxU
  have hf' := hf.contMDiffAt ((hU.preimage hq.continuous).mem_nhds hpre)
  have hsrc :=
    (contMDiffAt_iff_source_of_mem_source (I := modelWithCornersSelf ℂ E) (I' := I) hx.2).mp hf'
  have hchart : chartAt E x = chart (E := E) hq x := rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, chart, Function.comp_def] using hsrc

private theorem CoveringQuotient.localInverse_holomorphic {E M Q G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] [Group G]
    [MulAction G M] {q : M → Q} (hq : IsQuotientCoveringMap q G) (n : ℕ∞ω)
    [IsManifold (modelWithCornersSelf ℂ E) n M]
    (hG :
      ∀ g : G,
        ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n (fun x : M => g • x))
    (a : M) :
    letI := chartedSpace (E := E) hq
    ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n (localInverse hq a)
      (localInverse hq a).source :=
  contMDiffOn_of_comp hq (modelWithCornersSelf ℂ E) n (localInverse hq a).open_source
    (contMDiffOn_lift hq n hG a)

private theorem CoveringQuotient.project_isLocalDiffeomorph {E M Q G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] [Group G]
    [MulAction G M] {q : M → Q} (hq : IsQuotientCoveringMap q G)
    [IsManifold (modelWithCornersSelf ℂ E) ω M]
    (hG :
      ∀ g : G,
        ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (fun x : M => g • x)) :
    letI := chartedSpace (E := E) hq
    IsLocalDiffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω q := by
  let := chartedSpace (E := E) hq
  intro x
  let Φ : PartialDiffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) M Q ω :=
    { toPartialEquiv := (localInverse hq x).symm.toPartialEquiv
      open_source := (localInverse hq x).open_target
      open_target := (localInverse hq x).open_source
      contMDiffOn_toFun := by
        change
          ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
            (localInverse hq x).symm (localInverse hq x).target
        rw [localInverse_symm]
        exact (contMDiff_project hq ω hG).contMDiffOn
      contMDiffOn_invFun := localInverse_holomorphic hq ω hG x }
  refine ⟨Φ, hq.isCoveringMap.isLocalHomeomorph.self_mem_localInverseAt_target, ?_⟩
  intro y _
  change q y = (localInverse hq x).symm y
  rw [localInverse_symm]

private def
    opensInclusionPartialDiffeomorph {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)
    (U : TopologicalSpace.Opens M) (hU : Nonempty U) : PartialDiffeomorph I I U M ω := by
  let e := U.openPartialHomeomorphSubtypeCoe hU
  refine
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
      contMDiffOn_invFun := ?_ }
  intro x hx
  have hxU : x ∈ U := by simpa [e] using hx
  have he : (Subtype.val ∘ e.symm) =ᶠ[𝓝 x] id := by
    filter_upwards [U.isOpen.mem_nhds hxU] with y hy
    exact
      e.right_inv
        (by
          simpa only [e, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using hy)
  have hs : ContMDiffAt I I ω (Subtype.val ∘ e.symm) x := contMDiffAt_id.congr_of_eventuallyEq he
  have hi : ContMDiffAt I I ω (Subtype.val ∘ e.symm) x ↔ ContMDiffAt I I ω e.symm x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact (hi.mp hs).contMDiffWithinAt

private theorem
    isLocalDiffeomorph_subtypeVal {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)
    (U : TopologicalSpace.Opens M) : IsLocalDiffeomorph I I ω (Subtype.val : U → M) := by
  intro x
  refine ⟨opensInclusionPartialDiffeomorph I U ⟨x⟩, Set.mem_univ _, ?_⟩
  intro y _
  rfl

private theorem isLocalDiffeomorphAt_codRestrictOpens {E F H K M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H]
    [TopologicalSpace K] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N]
    [ChartedSpace K N] (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ F K) {f : M → N}
    {x : M} (hf : IsLocalDiffeomorphAt I J ω f x) (V : TopologicalSpace.Opens N)
    (hV : ∀ x, f x ∈ V) : IsLocalDiffeomorphAt I J ω (fun y => (⟨f y, hV y⟩ : V)) x := by
  obtain ⟨Φ, hx, he⟩ := hf
  let eV := opensInclusionPartialDiffeomorph J V ⟨⟨f x, hV x⟩⟩
  let Ψ := Φ.trans eV.symm
  have hxV : Φ x ∈ V := by
    rw [← he hx]
    exact hV x
  have hxV' : Φ x ∈ (V.openPartialHomeomorphSubtypeCoe ⟨⟨f x, hV x⟩⟩).target := by simpa using hxV
  refine ⟨Ψ, ⟨hx, hxV'⟩, ?_⟩
  intro y hy
  have hyV : Φ y ∈ (V.openPartialHomeomorphSubtypeCoe ⟨⟨f x, hV x⟩⟩).target := hy.2
  apply Subtype.ext
  change f y = ((V.openPartialHomeomorphSubtypeCoe ⟨⟨f x, hV x⟩⟩).symm (Φ y) : N)
  have hv := (V.openPartialHomeomorphSubtypeCoe ⟨⟨f x, hV x⟩⟩).right_inv hyV
  exact (he hy.1).trans hv.symm

private theorem isLocalDiffeomorph_codRestrictOpens {E F H K M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H]
    [TopologicalSpace K] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N]
    [ChartedSpace K N] (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ F K) {f : M → N}
    (hf : IsLocalDiffeomorph I J ω f) (V : TopologicalSpace.Opens N) (hV : ∀ x, f x ∈ V) :
    IsLocalDiffeomorph I J ω (fun x => (⟨f x, hV x⟩ : V)) := fun x =>
  isLocalDiffeomorphAt_codRestrictOpens I J (hf x) V hV

private theorem isLocalDiffeomorphAt_restrictOpens {E F H K M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H]
    [TopologicalSpace K] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N]
    [ChartedSpace K N] (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ F K) {f : M → N}
    {x : M} (hf : IsLocalDiffeomorphAt I J ω f x) (U : TopologicalSpace.Opens M)
    (V : TopologicalSpace.Opens N) (hUV : Set.MapsTo f (U : Set M) (V : Set N)) (hx : x ∈ U) :
    IsLocalDiffeomorphAt I J ω (fun y : U => (⟨f y, hUV y.2⟩ : V)) ⟨x, hx⟩ := by
  have hU : IsLocalDiffeomorphAt I J ω (fun y : U => f y) ⟨x, hx⟩ :=
    (isLocalDiffeomorph_subtypeVal I U ⟨x, hx⟩).comp (K := J) (P := N) hf
  exact isLocalDiffeomorphAt_codRestrictOpens I J hU V (fun y => hUV y.2)

private theorem isLocalDiffeomorph_restrictOpens {E F H K M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H]
    [TopologicalSpace K] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N]
    [ChartedSpace K N] (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ F K) {f : M → N}
    (hf : IsLocalDiffeomorph I J ω f) (U : TopologicalSpace.Opens M)
    (V : TopologicalSpace.Opens N) (hUV : Set.MapsTo f (U : Set M) (V : Set N)) :
    IsLocalDiffeomorph I J ω (fun x : U => (⟨f x, hUV x.2⟩ : V)) := by
  have hU : IsLocalDiffeomorph I J ω (fun x : U => f x) := by
    intro x
    exact (isLocalDiffeomorph_subtypeVal I U x).comp (K := J) (P := N) (hf x)
  exact isLocalDiffeomorph_codRestrictOpens I J hU V (fun x => hUV x.2)

/-- The four-dimensional real coordinate space underlying `ComplexPlane₂`. -/
public
abbrev RealPlane₄ :=
  Fin 4 → ℝ

end Mathoverflow1973

end
