/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Pi1.ThreefoldOverlapMappingTorus1
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.PeriodFamily.HolomorphicPeriodMap1
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods1
import all LeanPool.HopfProblem.Pi1.MappingTorus
import all LeanPool.HopfProblem.Pi1.ThreefoldOverlapMappingTorus1

/-!
# Hopf problem: elliptic · core 2

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

private def Elliptic.familyPeriods (j : Kind) : HolomorphicPeriodMap ℂ SpecialPeriods.Disc :=
  match j with
  | .three => SpecialPeriods.threePeriodMap
  | .four => SpecialPeriods.fourPeriodMap

private def Elliptic.familyRotation (j : Kind) :
    Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) SpecialPeriods.Disc
      SpecialPeriods.Disc ω :=
  match j with
  | .three => SpecialPeriods.threeRotation
  | .four => SpecialPeriods.fourRotation

private theorem
    Elliptic.familyRotation_iterate_order (j : Kind) : (familyRotation j)^[j.order] = id := by
  cases j
  · exact SpecialPeriods.discRotateThree_iterate_order
  · exact SpecialPeriods.discRotateFour_iterate_order

private abbrev Elliptic.Family (j : Kind) :=
  (familyPeriods j).TotalSpace

private abbrev Elliptic.FamilyModel :=
  ℂ × ComplexPlane₂

@[instance_reducible]
private def Elliptic.familyCoveringChartedSpace :
    ChartedSpace FamilyModel (SpecialPeriods.Disc × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (SpecialPeriods.Disc × ComplexPlane₂))

attribute [local instance] Elliptic.familyCoveringChartedSpace in
private theorem Elliptic.familyCoveringManifold :
    IsManifold (modelWithCornersSelf ℂ FamilyModel) ω (SpecialPeriods.Disc × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact
    IsManifold.prod (I := modelWithCornersSelf ℂ ℂ) (I' := modelWithCornersSelf ℂ ComplexPlane₂)
      SpecialPeriods.Disc ComplexPlane₂

attribute [local instance] Elliptic.familyCoveringChartedSpace Elliptic.familyCoveringManifold in
private theorem Elliptic.familyPeriodEquiv_matrix (j : Kind) (z : SpecialPeriods.Disc)
    (x : RealPlane₄) :
    (familyPeriods j).periodEquiv z x =
      ((familyPeriods j).point z).val.matrix *ᵥ (fun i => (x i : ℂ)) := by
  rw [HolomorphicPeriodMap.periodEquiv_coordinates]
  ext i
  fin_cases i <;> simp [PeriodPoint.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

attribute [local instance] Elliptic.familyCoveringChartedSpace Elliptic.familyCoveringManifold in
private theorem Elliptic.familyPeriods_matrix_covariance (j : Kind) (z : SpecialPeriods.Disc) :
    ((familyPeriods j).point (familyRotation j z)).val.matrix * j.matrix.map (Int.castRingHom ℂ) =
      linearMatrix j ((familyPeriods j).point z) * ((familyPeriods j).point z).val.matrix := by
  cases j
  · exact SpecialPeriods.threePeriodMap_matrix_covariance z
  · exact SpecialPeriods.fourPeriodMap_matrix_covariance z

attribute [local instance] Elliptic.familyCoveringChartedSpace Elliptic.familyCoveringManifold in
private theorem Elliptic.familyPeriodEquiv_flatLinear (j : Kind) (z : SpecialPeriods.Disc)
    (x : RealPlane₄) :
    (familyPeriods j).periodEquiv (familyRotation j z) (flatLinear j x) =
      linearMatrix j ((familyPeriods j).point z) *ᵥ (familyPeriods j).periodEquiv z x := by
  rw [familyPeriodEquiv_matrix, flatLinear_complexCast, Matrix.mulVec_mulVec,
    familyPeriodEquiv_matrix, Matrix.mulVec_mulVec, familyPeriods_matrix_covariance]

attribute [local instance] Elliptic.familyCoveringChartedSpace Elliptic.familyCoveringManifold in
private theorem Elliptic.familyPeriodEquiv_symm_linearMatrix (j : Kind) (z : SpecialPeriods.Disc)
    (w : ComplexPlane₂) :
    ((familyPeriods j).periodEquiv (familyRotation j z)).symm
        (linearMatrix j ((familyPeriods j).point z) *ᵥ w) =
      flatLinear j (((familyPeriods j).periodEquiv z).symm w) := by
  apply ((familyPeriods j).periodEquiv (familyRotation j z)).injective
  rw [LinearEquiv.apply_symm_apply, familyPeriodEquiv_flatLinear, LinearEquiv.apply_symm_apply]

attribute [local instance] Elliptic.familyCoveringChartedSpace Elliptic.familyCoveringManifold in
private def Elliptic.familyPermutation (j : Kind) (v : Lattice) : Equiv.Perm (Family j) :=
  (familyRotation j).toEquiv.prodCongr (flatTorusAffine j v).toEquiv

attribute [local instance] Elliptic.familyCoveringChartedSpace Elliptic.familyCoveringManifold in
@[simp]
private theorem Elliptic.familyPermutation_apply (j : Kind) (v : Lattice) (x : Family j) :
    familyPermutation j v x = (familyRotation j x.1, flatTorusAffine j v x.2) :=
  rfl

attribute [local instance] Elliptic.familyCoveringChartedSpace Elliptic.familyCoveringManifold in
private def Elliptic.familyLift (j : Kind) (v : Lattice) (x : SpecialPeriods.Disc × ComplexPlane₂) :
    SpecialPeriods.Disc × ComplexPlane₂ :=
  (familyRotation j x.1,
    linearMatrix j ((familyPeriods j).point x.1) *ᵥ x.2 +
      (familyPeriods j).periodEquiv (familyRotation j x.1) ((1 / (j.order : ℝ)) • realCast v))

attribute [local instance] Elliptic.familyCoveringChartedSpace Elliptic.familyCoveringManifold in
private theorem Elliptic.familyLift_quotientMap (j : Kind) (v : Lattice)
    (x : SpecialPeriods.Disc × ComplexPlane₂) :
    (familyPeriods j).quotientMap (familyLift j v x) =
      familyPermutation j v ((familyPeriods j).quotientMap x) := by
  change
    (familyRotation j x.1,
        standardLattice.mkQ
          (((familyPeriods j).periodEquiv (familyRotation j x.1)).symm
            (linearMatrix j ((familyPeriods j).point x.1) *ᵥ x.2 +
              (familyPeriods j).periodEquiv (familyRotation j x.1)
                ((1 / (j.order : ℝ)) • realCast v)))) =
      (familyRotation j x.1,
        flatTorusAffine j v (standardLattice.mkQ (((familyPeriods j).periodEquiv x.1).symm x.2)))
  rw [flatTorusAffine_mkQ, map_add, LinearEquiv.symm_apply_apply,
    familyPeriodEquiv_symm_linearMatrix]
  rfl

attribute [local instance] Elliptic.familyCoveringChartedSpace Elliptic.familyCoveringManifold in
private theorem Elliptic.familyLinearLift_holomorphic (j : Kind) :
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ ComplexPlane₂) ω
      (fun x : SpecialPeriods.Disc × ComplexPlane₂ =>
        linearMatrix j ((familyPeriods j).point x.1) *ᵥ x.2) := by
  have hf :
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ ℂ) ω
      (Prod.fst : SpecialPeriods.Disc × ComplexPlane₂ → SpecialPeriods.Disc) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst
  have hs :
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ ComplexPlane₂) ω
      (Prod.snd : SpecialPeriods.Disc × ComplexPlane₂ → ComplexPlane₂) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_snd
  have hτ := (familyPeriods j).holomorphic_tau.comp hf
  have hμ := (familyPeriods j).holomorphic_mu.comp hf
  have hτ0 : ∀ x : SpecialPeriods.Disc × ComplexPlane₂, ((familyPeriods j).point x.1).val.τ ≠ 0 :=
    fun x => ((familyPeriods j).point x.1).val.τ_ne_zero ((familyPeriods j).point x.1).property.1
  have h₀ := (contMDiff_pi_space.mp hs) 0
  have h₁ := (contMDiff_pi_space.mp hs) 1
  cases j
  · apply contMDiff_pi_space.mpr
    intro i
    fin_cases i
    · convert (((contMDiff_const (c := (-1 : ℂ))).div₀ hτ hτ0).mul h₀) using 1
      funext x
      simp [linearMatrix, PeriodPoint.R₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Function.comp_def]
    · convert (((((contMDiff_const (c := (1 : ℂ))).sub hμ).div₀ hτ hτ0).mul h₀).add h₁) using 1
      funext x
      simp [linearMatrix, PeriodPoint.R₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Function.comp_def]
  · apply contMDiff_pi_space.mpr
    intro i
    fin_cases i
    · convert (((contMDiff_const (c := (1 : ℂ))).div₀ hτ hτ0).mul h₀) using 1
      funext x
      simp [linearMatrix, PeriodPoint.R₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Function.comp_def]
    · convert (((hμ.neg.div₀ hτ hτ0).mul h₀).add h₁) using 1
      funext x
      simp [linearMatrix, PeriodPoint.R₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Function.comp_def]

attribute [local instance] Elliptic.familyCoveringChartedSpace Elliptic.familyCoveringManifold in
private theorem Elliptic.familyLift_holomorphic (j : Kind) (v : Lattice) :
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ FamilyModel) ω
      (familyLift j v) := by
  have hf :
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ ℂ) ω
      (fun x : SpecialPeriods.Disc × ComplexPlane₂ => familyRotation j x.1) := by
    rw [modelWithCornersSelf_prod]
    exact (familyRotation j).contMDiff_toFun.comp contMDiff_fst
  have hw :=
    (familyLinearLift_holomorphic j).add
      (((familyPeriods j).holomorphic_periodEquiv_const ((1 / (j.order : ℝ)) • realCast v)).comp
        hf)
  rw [modelWithCornersSelf_prod] at hf hw ⊢
  exact hf.prodMk hw

attribute [local instance] Elliptic.familyCoveringChartedSpace Elliptic.familyCoveringManifold in
private theorem Elliptic.familyPermutation_holomorphic (j : Kind) (v : Lattice) :
    letI := (familyPeriods j).totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ FamilyModel) ω
      (familyPermutation j v) := by
  let := (familyPeriods j).coveringAction
  let := (familyPeriods j).totalChartedSpace
  apply
    CoveringQuotient.contMDiff_of_comp (E := FamilyModel) (familyPeriods j).quotientCoveringMap
      (modelWithCornersSelf ℂ FamilyModel) ω
  have h := ((familyPeriods j).quotientMap_holomorphic).comp (familyLift_holomorphic j v)
  convert! h using 1
  funext x
  exact (familyLift_quotientMap j v x).symm

private theorem Elliptic.LogGauge.exponential_neg_one_third :
    CuspUniformization.exponential (-(1 / (3 : ℂ))) = -SpecialPeriods.rho := by
  have hρ : Complex.exp ((Real.pi : ℂ) / 3 * Complex.I) = SpecialPeriods.rho := by
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using SpecialPeriods.rho_eq_exp.symm
  rw [CuspUniformization.exponential,
    show
      (2 * Real.pi * Complex.I : ℂ) * -(1 / 3) =
        (Real.pi : ℂ) / 3 * Complex.I - Real.pi * Complex.I
      by ring,
    Complex.exp_sub_pi_mul_I, hρ]

private theorem Elliptic.LogGauge.exponential_neg_one_fourth :
    CuspUniformization.exponential (-(1 / (4 : ℂ))) = -Complex.I := by
  rw [CuspUniformization.exponential,
    show (2 * Real.pi * Complex.I : ℂ) * -(1 / 4) = -(Real.pi : ℂ) / 2 * Complex.I by ring,
    Complex.exp_neg_pi_div_two_mul_I]

private theorem Elliptic.LogGauge.familyRotation_val_exponential (j : Elliptic.Kind)
    (z : SpecialPeriods.Disc) :
    (Elliptic.familyRotation j z : ℂ) =
      CuspUniformization.exponential (-(1 / (j.order : ℂ))) * (z : ℂ) := by
  cases j
  · change
      -SpecialPeriods.rho * (z : ℂ) = CuspUniformization.exponential (-(1 / (3 : ℂ))) * (z : ℂ)
    rw [exponential_neg_one_third]
  · change -Complex.I * (z : ℂ) = CuspUniformization.exponential (-(1 / (4 : ℂ))) * (z : ℂ)
    rw [exponential_neg_one_fourth]

private theorem
    Elliptic.LogGauge.familyRotation_ne_zero (j : Elliptic.Kind) (z : SpecialPeriods.Disc)
    (hz : (z : ℂ) ≠ 0) : (Elliptic.familyRotation j z : ℂ) ≠ 0 := by
  rw [familyRotation_val_exponential]
  exact mul_ne_zero (CuspUniformization.exponential_ne_zero _) hz

private theorem
    Elliptic.LogGauge.familyRotation_logarithms (j : Elliptic.Kind) (z : SpecialPeriods.Disc)
    (s r : ℂ) (hs : CuspUniformization.exponential s = (z : ℂ))
    (hr : CuspUniformization.exponential r = (Elliptic.familyRotation j z : ℂ)) :
    ∃ n : ℤ, r = s - 1 / (j.order : ℂ) + n := by
  apply (CuspUniformization.exponential_eq_iff r (s - 1 / (j.order : ℂ))).mp
  rw [hr, familyRotation_val_exponential, sub_eq_add_neg, CuspUniformization.exponential_add, hs]
  exact mul_comm _ _

private theorem
    Elliptic.LogGauge.logarithm_familyRotation (j : Elliptic.Kind) (z : SpecialPeriods.Disc)
    (hz : (z : ℂ) ≠ 0) :
    ∃ n : ℤ,
      CuspUniformization.logarithm (Elliptic.familyRotation j z : ℂ) =
        CuspUniformization.logarithm (z : ℂ) - 1 / (j.order : ℂ) + n :=
  familyRotation_logarithms j z _ _ (CuspUniformization.exponential_logarithm hz)
    (CuspUniformization.exponential_logarithm (familyRotation_ne_zero j z hz))

@[instance_reducible]
private def Elliptic.CyclicAction.action {M : Type*} {m : ℕ} [NeZero m] (σ : Equiv.Perm M)
    (hσ : σ ^ m = 1) : MulAction (Multiplicative (ZMod m)) M
    where
  smul g x := (σ ^ g.toAdd.val) x
  one_smul
    x := by
    change (σ ^ (0 : ZMod m).val) x = x
    simp
  mul_smul g h
    x := by
    change (σ ^ (g.toAdd + h.toAdd).val) x = (σ ^ g.toAdd.val) ((σ ^ h.toAdd.val) x)
    rw [ZMod.val_add, ← pow_eq_pow_mod _ hσ, pow_add]
    rfl

private def Elliptic.CyclicAction.generator (m : ℕ) : Multiplicative (ZMod m) :=
  Multiplicative.ofAdd 1

private theorem
    Elliptic.CyclicAction.smul_eq_iterate {M : Type*} {m : ℕ} [NeZero m] (σ : Equiv.Perm M)
    (hσ : σ ^ m = 1) (g : Multiplicative (ZMod m)) (x : M) :
    letI := action σ hσ
    g • x = (σ : M → M)^[g.toAdd.val] x := by
  change (σ ^ g.toAdd.val) x = _
  rw [Equiv.Perm.coe_pow]

private theorem
    Elliptic.CyclicAction.ofAdd_natCast_smul {M : Type*} {m : ℕ} [NeZero m] (σ : Equiv.Perm M)
    (hσ : σ ^ m = 1) (r : ℕ) (x : M) :
    letI := action σ hσ
    Multiplicative.ofAdd (r : ZMod m) • x = (σ : M → M)^[r] x := by
  change (σ ^ (r : ZMod m).val) x = _
  rw [ZMod.val_natCast, ← pow_eq_pow_mod r hσ, Equiv.Perm.coe_pow]

@[simp]
private theorem
    Elliptic.CyclicAction.generator_smul {M : Type*} {m : ℕ} [NeZero m] (σ : Equiv.Perm M)
    (hσ : σ ^ m = 1) (x : M) :
    letI := action σ hσ
    generator m • x = σ x := by simpa [generator] using ofAdd_natCast_smul σ hσ 1 x

private theorem Elliptic.CyclicAction.isCancelSMul {M : Type*} {m : ℕ} [NeZero m] (σ : Equiv.Perm M)
    (hσ : σ ^ m = 1) (hfree : ∀ r : ℕ, 0 < r → r < m → ∀ x : M, (σ : M → M)^[r] x ≠ x) :
    letI := action σ hσ
    IsCancelSMul (Multiplicative (ZMod m)) M := by
  let := action σ hσ
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro g x hx
  have hval : g.toAdd.val = 0 := by
    by_contra hval
    exact
      hfree g.toAdd.val (Nat.pos_of_ne_zero hval) (ZMod.val_lt _) x
        ((smul_eq_iterate σ hσ g x).symm.trans hx)
  apply Multiplicative.ext
  exact (ZMod.val_eq_zero _).mp hval

private theorem
    Elliptic.CyclicAction.isCancelSMul_iff {M : Type*} {m : ℕ} [NeZero m] (σ : Equiv.Perm M)
    (hσ : σ ^ m = 1) :
    letI := action σ hσ
    IsCancelSMul (Multiplicative (ZMod m)) M ↔
      ∀ r : ℕ, 0 < r → r < m → ∀ x : M, (σ : M → M)^[r] x ≠ x := by
  let := action σ hσ
  constructor
  · intro hcancel r hr hrm x hx
    let := hcancel
    have hg : Multiplicative.ofAdd (r : ZMod m) = (1 : Multiplicative (ZMod m)) :=
      IsCancelSMul.eq_one_of_smul ((ofAdd_natCast_smul σ hσ r x).trans hx)
    have hz : (r : ZMod m) = 0 := congrArg Multiplicative.toAdd hg
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt hrm, ZMod.val_zero] at hv
    omega
  · exact isCancelSMul σ hσ

private theorem Elliptic.CyclicAction.continuousConstSMul {M : Type*} {m : ℕ} [NeZero m]
    [TopologicalSpace M] (σ : Equiv.Perm M) (hσ : σ ^ m = 1) (hcont : Continuous (σ : M → M)) :
    letI := action σ hσ
    ContinuousConstSMul (Multiplicative (ZMod m)) M := by
  let := action σ hσ
  refine ⟨fun g => ?_⟩
  simpa only [smul_eq_iterate σ hσ] using hcont.iterate g.toAdd.val

private theorem Elliptic.CyclicAction.smul_contMDiff {M : Type*} {m : ℕ} [NeZero m] {𝕜 E H : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} [TopologicalSpace M] [ChartedSpace H M]
    (σ : Equiv.Perm M) (hσ : σ ^ m = 1) (hreg : ContMDiff I I n (σ : M → M))
    (g : Multiplicative (ZMod m)) :
    letI := action σ hσ
    ContMDiff I I n (fun x : M => g • x) := by
  let := action σ hσ
  simpa only [smul_eq_iterate σ hσ] using hreg.iterate g.toAdd.val

private abbrev Elliptic.FiniteQuotient.Space (G M : Type*) [Group G] [MulAction G M] :=
  MulAction.orbitRel.Quotient G M

private def
    Elliptic.FiniteQuotient.project (G M : Type*) [Group G] [MulAction G M] : M → Space G M :=
  Quotient.mk (MulAction.orbitRel G M)

private theorem Elliptic.FiniteQuotient.project_surjective (G M : Type*) [Group G] [MulAction G M] :
    Function.Surjective (project G M) :=
  Quotient.mk_surjective

private theorem
    Elliptic.FiniteQuotient.project_eq_iff_mem_orbit (G M : Type*) [Group G] [MulAction G M]
    (x y : M) : project G M x = project G M y ↔ x ∈ MulAction.orbit G y :=
  Quotient.eq''

@[simp]
private theorem Elliptic.FiniteQuotient.project_smul (G M : Type*) [Group G] [MulAction G M] (g : G)
    (x : M) : project G M (g • x) = project G M x :=
  (project_eq_iff_mem_orbit G M _ _).mpr ⟨g, rfl⟩

private theorem
    Elliptic.FiniteQuotient.project_isQuotientMap (G M : Type*) [Group G] [MulAction G M]
    [TopologicalSpace M] : Topology.IsQuotientMap (project G M) :=
  isQuotientMap_quotient_mk'

private theorem Elliptic.FiniteQuotient.project_continuous (G M : Type*) [Group G] [MulAction G M]
    [TopologicalSpace M] : Continuous (project G M) :=
  (project_isQuotientMap G M).continuous

private theorem
    Elliptic.FiniteQuotient.project_isOpenQuotientMap (G M : Type*) [Group G] [MulAction G M]
    [TopologicalSpace M] [ContinuousConstSMul G M] : IsOpenQuotientMap (project G M) :=
  MulAction.isOpenQuotientMap_quotientMk

private theorem Elliptic.FiniteQuotient.spaceCompactSpace (G M : Type*) [Group G] [MulAction G M]
    [TopologicalSpace M] [CompactSpace M] : CompactSpace (Space G M) :=
  inferInstance

private theorem Elliptic.FiniteQuotient.spaceSecondCountableTopology (G M : Type*) [Group G]
    [MulAction G M] [TopologicalSpace M] [SecondCountableTopology M] [ContinuousConstSMul G M] :
    SecondCountableTopology (Space G M) :=
  (project_isQuotientMap G M).secondCountableTopology (project_isOpenQuotientMap G M).isOpenMap

private theorem Elliptic.FiniteQuotient.spaceT2Space (G M : Type*) [Group G] [MulAction G M]
    [TopologicalSpace M] [Finite G] [LocallyCompactSpace M] [T2Space M]
    [ContinuousConstSMul G M] : T2Space (Space G M) :=
  inferInstance

private theorem Elliptic.FiniteQuotient.project_isQuotientCoveringMap (G M : Type*) [Group G]
    [MulAction G M] [TopologicalSpace M] [Finite G] [LocallyCompactSpace M] [T2Space M]
    [ContinuousConstSMul G M] [IsCancelSMul G M] : IsQuotientCoveringMap (project G M) G :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

private theorem
    Elliptic.FiniteQuotient.project_isCoveringMap (G M : Type*) [Group G] [MulAction G M]
    [TopologicalSpace M] [Finite G] [LocallyCompactSpace M] [T2Space M] [ContinuousConstSMul G M]
    [IsCancelSMul G M] : IsCoveringMap (project G M) :=
  (project_isQuotientCoveringMap G M).isCoveringMap

private def Elliptic.FiniteQuotient.fibreEquivGroup (G M : Type*) [Group G] [MulAction G M]
    [TopologicalSpace M] [Finite G] [LocallyCompactSpace M] [T2Space M] [ContinuousConstSMul G M]
    [IsCancelSMul G M] (x : Space G M) : (project G M ⁻¹' { x }) ≃ G :=
  (project_isQuotientCoveringMap G M).fiberEquivGroup
    ⟨(project_surjective G M x).choose, (project_surjective G M x).choose_spec⟩

private theorem Elliptic.FiniteQuotient.fibre_card (G M : Type*) [Group G] [MulAction G M]
    [TopologicalSpace M] [Finite G] [LocallyCompactSpace M] [T2Space M] [ContinuousConstSMul G M]
    [IsCancelSMul G M] (x : Space G M) : Nat.card (project G M ⁻¹' { x }) = Nat.card G :=
  Nat.card_congr (fibreEquivGroup G M x)

@[instance_reducible]
private def Elliptic.FiniteQuotient.chartedSpace (G M : Type*) [Group G] [MulAction G M] {E : Type*}
    [NormedAddCommGroup E] [TopologicalSpace M] [ChartedSpace E M] [Finite G]
    [LocallyCompactSpace M] [T2Space M] [ContinuousConstSMul G M] [IsCancelSMul G M] :
    ChartedSpace E (Space G M) :=
  CoveringQuotient.chartedSpace (E := E) (project_isQuotientCoveringMap G M)

private theorem Elliptic.FiniteQuotient.project_holomorphic (G M : Type*) [Group G] [MulAction G M]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M]
    [Finite G] [LocallyCompactSpace M] [T2Space M] [ContinuousConstSMul G M] [IsCancelSMul G M]
    [IsManifold (modelWithCornersSelf ℂ E) ω M]
    (hG :
      ∀ g : G,
        ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (fun x : M => g • x)) :
    letI := chartedSpace (E := E) G M
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (project G M) :=
  CoveringQuotient.contMDiff_project (project_isQuotientCoveringMap G M) ω hG

private instance Elliptic.instLocal2 (j : Kind) : NeZero j.order :=
  ⟨Nat.ne_of_gt j.order_pos⟩

private abbrev Elliptic.CyclicGroup (j : Kind) :=
  Multiplicative (ZMod j.order)

@[instance_reducible]
private def
    Elliptic.affineAction (j : Kind) (p : FixedPeriod j) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    MulAction (CyclicGroup j) p.val.Torus :=
  CyclicAction.action (affinePermutation j p v) (affinePermutation_pow_order j p v hv)

private theorem Elliptic.affineAction_generator_smul (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (x : p.val.Torus) :
    letI := affineAction j p v hv
    CyclicAction.generator j.order • x = affineBiholomorph j p v x :=
  CyclicAction.generator_smul (affinePermutation j p v) (affinePermutation_pow_order j p v hv) x

private theorem Elliptic.affineAction_free_iff (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) :
    letI := affineAction j p v hv
    IsCancelSMul (CyclicGroup j) p.val.Torus ↔ AdmissibleTwist j v := by
  refine
    (CyclicAction.isCancelSMul_iff (affinePermutation j p v)
          (affinePermutation_pow_order j p v hv)).trans
      ?_
  simpa only [Equiv.Perm.coe_pow] using affinePermutation_free_iff j p v hv

private theorem Elliptic.affineAction_free (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    letI := affineAction j p v hv.1
    IsCancelSMul (CyclicGroup j) p.val.Torus :=
  (affineAction_free_iff j p v hv.1).mpr hv

private theorem Elliptic.affineAction_continuous (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) :
    letI := affineAction j p v hv
    ContinuousConstSMul (CyclicGroup j) p.val.Torus :=
  CyclicAction.continuousConstSMul (affinePermutation j p v)
    (affinePermutation_pow_order j p v hv) (affineBiholomorph j p v).continuous

private abbrev
    Elliptic.Surface (j : Kind) (p : FixedPeriod j) (v : Lattice) (hv : AdmissibleTwist j v) :=
  @FiniteQuotient.Space (CyclicGroup j) p.val.Torus _ (affineAction j p v hv.1)

private def Elliptic.surfaceProjection (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : p.val.Torus → Surface j p v hv :=
  @FiniteQuotient.project (CyclicGroup j) p.val.Torus _ (affineAction j p v hv.1)

private theorem Elliptic.surfaceProjection_surjective (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : Function.Surjective (surfaceProjection j p v hv) :=
  Quotient.mk_surjective

private theorem Elliptic.surfaceProjection_continuous (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : Continuous (surfaceProjection j p v hv) := by
  let := affineAction j p v hv.1
  exact FiniteQuotient.project_continuous (CyclicGroup j) p.val.Torus

private instance Elliptic.surfaceCompact (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : CompactSpace (Surface j p v hv) := by
  let := affineAction j p v hv.1
  exact FiniteQuotient.spaceCompactSpace (CyclicGroup j) p.val.Torus

private instance Elliptic.surfacePathConnected (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : PathConnectedSpace (Surface j p v hv) :=
  (surfaceProjection_surjective j p v hv).pathConnectedSpace
    (surfaceProjection_continuous j p v hv)

private theorem
    Elliptic.surfaceProjection_isCoveringMap (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : IsCoveringMap (surfaceProjection j p v hv) := by
  let := affineAction j p v hv.1
  let := affineAction_continuous j p v hv.1
  let := affineAction_free j p v hv
  exact FiniteQuotient.project_isCoveringMap (CyclicGroup j) p.val.Torus

private theorem Elliptic.surfaceProjection_fibre_card (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : Surface j p v hv) :
    Nat.card (surfaceProjection j p v hv ⁻¹' { y }) = j.order := by
  let := affineAction j p v hv.1
  let := affineAction_continuous j p v hv.1
  let := affineAction_free j p v hv
  change Nat.card (FiniteQuotient.project (CyclicGroup j) p.val.Torus ⁻¹' { y }) = j.order
  rw [FiniteQuotient.fibre_card (CyclicGroup j) p.val.Torus]
  simp [CyclicGroup, Nat.card_eq_fintype_card, ZMod.card]

private theorem Elliptic.pow_mem_unitDisc_iff (m : ℕ) (hm : 0 < m) (z : ℂ) :
    z ^ m ∈ SpecialPeriods.unitDisc ↔ z ∈ SpecialPeriods.unitDisc := by
  change Dist.dist (z ^ m) 0 < 1 ↔ Dist.dist z 0 < 1
  rw [dist_zero_right, dist_zero_right, norm_pow]
  exact pow_lt_one_iff_of_nonneg (norm_nonneg z) hm.ne'

private theorem Elliptic.complexPower_preimage_unitDisc (m : ℕ) (hm : 0 < m) :
    (fun z : ℂ => z ^ m) ⁻¹' (SpecialPeriods.unitDisc : Set ℂ) =
      (SpecialPeriods.unitDisc : Set ℂ) := by
  ext z
  exact pow_mem_unitDisc_iff m hm z

private def
    Elliptic.discPower (m : ℕ) (hm : 0 < m) (z : SpecialPeriods.Disc) : SpecialPeriods.Disc :=
  ⟨(z : ℂ) ^ m, (pow_mem_unitDisc_iff m hm z).mpr z.property⟩

@[simp]
private theorem Elliptic.discPower_coe (m : ℕ) (hm : 0 < m) (z : SpecialPeriods.Disc) :
    (discPower m hm z : ℂ) = (z : ℂ) ^ m :=
  rfl

private theorem Elliptic.discPower_holomorphic (m : ℕ) (hm : 0 < m) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (discPower m hm) := by
  intro z
  have he :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun w : SpecialPeriods.Disc => (discPower m hm w : ℂ)) z ↔
      ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (discPower m hm) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp ((contMDiff_subtype_val.pow m) z)

private theorem Elliptic.discPower_continuous (m : ℕ) (hm : 0 < m) : Continuous (discPower m hm) :=
  (discPower_holomorphic m hm).continuous

private theorem Elliptic.discPower_surjective (m : ℕ) (hm : 0 < m) :
    Function.Surjective (discPower m hm) := by
  intro w
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (w : ℂ) hm
  have hmem : z ∈ SpecialPeriods.unitDisc := (pow_mem_unitDisc_iff m hm z).mp (hz ▸ w.property)
  exact ⟨⟨z, hmem⟩, Subtype.ext hz⟩

private theorem Elliptic.complexPower_isProperMap (m : ℕ) (hm : 0 < m) :
    IsProperMap (fun z : ℂ => z ^ m) := by
  have hp : 0 < (Polynomial.X ^ m : Polynomial ℂ).degree := by
    rw [Polynomial.degree_X_pow]
    exact_mod_cast hm
  simpa only [Polynomial.eval_X_pow] using (Polynomial.X ^ m : Polynomial ℂ).isProperMap_eval hp

private theorem
    Elliptic.discPower_isProperMap (m : ℕ) (hm : 0 < m) : IsProperMap (discPower m hm) := by
  let e : SpecialPeriods.Disc ≃ₜ ((fun z : ℂ => z ^ m) ⁻¹' (SpecialPeriods.unitDisc : Set ℂ)) :=
    Homeomorph.setCongr (complexPower_preimage_unitDisc m hm).symm
  have hp :=
    ((complexPower_isProperMap m hm).restrictPreimage (SpecialPeriods.unitDisc : Set ℂ)).comp
      e.isProperMap
  have he :
    (SpecialPeriods.unitDisc : Set ℂ).restrictPreimage (fun z : ℂ => z ^ m) ∘ e =
      discPower m hm := by
    funext z
    rfl
  rwa [he] at hp

private def Elliptic.discZero : SpecialPeriods.Disc :=
  ⟨0, by simp [SpecialPeriods.unitDisc]⟩

private theorem Elliptic.discPower_coe_eq_zero_iff (m : ℕ) (hm : 0 < m) (z : SpecialPeriods.Disc) :
    (discPower m hm z : ℂ) = 0 ↔ (z : ℂ) = 0 := by
  simp only [discPower_coe, pow_eq_zero_iff hm.ne']

@[simp]
private theorem Elliptic.discPower_eq_zero_iff (m : ℕ) (hm : 0 < m) (z : SpecialPeriods.Disc) :
    discPower m hm z = discZero ↔ z = discZero := by
  rw [Subtype.ext_iff, Subtype.ext_iff]
  exact discPower_coe_eq_zero_iff m hm z

private theorem Elliptic.familyPermutation_iterate (j : Kind) (v : Lattice) (r : ℕ) (x : Family j) :
    (familyPermutation j v)^[r] x = ((familyRotation j)^[r] x.1, (flatTorusAffine j v)^[r] x.2) :=
  by
  induction r with
  | zero => rfl
  | succ r ih => simp only [Function.iterate_succ_apply', ih, familyPermutation_apply]

private theorem
    Elliptic.familyPermutation_pow_apply (j : Kind) (v : Lattice) (r : ℕ) (x : Family j) :
    (familyPermutation j v ^ r) x = ((familyRotation j)^[r] x.1, (flatTorusAffine j v)^[r] x.2) :=
  by
  rw [Equiv.Perm.coe_pow]
  exact familyPermutation_iterate j v r x

private theorem
    Elliptic.familyPermutation_pow_order (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    familyPermutation j v ^ j.order = 1 := by
  apply Equiv.ext
  intro x
  rw [familyPermutation_pow_apply, familyRotation_iterate_order,
    flatTorusAffine_iterate_order j v hv]
  rfl

private theorem
    Elliptic.familyPermutation_pow_ne (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (r : ℕ) (hr : 0 < r) (hrm : r < j.order) (x : Family j) : (familyPermutation j v ^ r) x ≠ x :=
  by
  intro hx
  rw [familyPermutation_pow_apply] at hx
  exact flatTorusAffine_iterate_ne j v hv r hr hrm x.2 (congrArg Prod.snd hx)

@[simp]
private theorem Elliptic.familyRotation_zero (j : Kind) : familyRotation j discZero = discZero := by
  cases j <;> apply Subtype.ext
  · change -SpecialPeriods.rho * (0 : ℂ) = 0
    exact MulZeroClass.mul_zero _
  · change -Complex.I * (0 : ℂ) = 0
    exact MulZeroClass.mul_zero _

private theorem Elliptic.familyRotation_iterate_fixed_iff (j : Kind) (r : ℕ) (hr : 0 < r)
    (hrm : r < j.order) (z : SpecialPeriods.Disc) : (familyRotation j)^[r] z = z ↔ z = discZero :=
  by
  cases j
  · exact SpecialPeriods.discRotateThree_iterate_fixed_iff r hr hrm z
  · exact SpecialPeriods.discRotateFour_iterate_fixed_iff r hr hrm z

private theorem
    Elliptic.familyPermutation_free_iff (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    (∀ r : ℕ, 0 < r → r < j.order → ∀ x : Family j, (familyPermutation j v ^ r) x ≠ x) ↔
      AdmissibleTwist j v := by
  constructor
  · intro hf
    apply (flatTorusPermutation_free_iff j v hv).mp
    intro r hr hrm y hy
    apply hf r hr hrm (discZero, y)
    rw [familyPermutation_pow_apply]
    apply Prod.ext (Function.iterate_fixed (familyRotation_zero j) r)
    simpa only [Equiv.Perm.coe_pow, flatTorusPermutation, Homeomorph.coe_toEquiv] using hy
  · intro ha
    exact familyPermutation_pow_ne j v ha

@[instance_reducible]
private def Elliptic.familyAction (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    MulAction (CyclicGroup j) (Family j) :=
  CyclicAction.action (familyPermutation j v) (familyPermutation_pow_order j v hv)

private theorem
    Elliptic.familyAction_generator_smul (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (x : Family j) :
    letI := familyAction j v hv
    CyclicAction.generator j.order • x = familyPermutation j v x :=
  CyclicAction.generator_smul (familyPermutation j v) (familyPermutation_pow_order j v hv) x

private theorem Elliptic.familyAction_apply (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : Family j) :
    letI := familyAction j v hv
    g • x = ((familyRotation j)^[g.toAdd.val] x.1, (flatTorusAffine j v)^[g.toAdd.val] x.2) :=
  (CyclicAction.smul_eq_iterate (familyPermutation j v) (familyPermutation_pow_order j v hv) g
        x).trans
    (familyPermutation_iterate j v g.toAdd.val x)

private theorem Elliptic.familyAction_free_iff (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    letI := familyAction j v hv
    IsCancelSMul (CyclicGroup j) (Family j) ↔ AdmissibleTwist j v := by
  refine
    (CyclicAction.isCancelSMul_iff (familyPermutation j v)
          (familyPermutation_pow_order j v hv)).trans
      ?_
  simpa only [Equiv.Perm.coe_pow] using familyPermutation_free_iff j v hv

private theorem Elliptic.familyAction_free (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := familyAction j v hv.1
    IsCancelSMul (CyclicGroup j) (Family j) :=
  (familyAction_free_iff j v hv.1).mpr hv

private theorem Elliptic.familyAction_holomorphic (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) :
    letI := (familyPeriods j).totalChartedSpace
    letI := familyAction j v hv
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ FamilyModel) ω
      (fun x : Family j => g • x) := by
  let := (familyPeriods j).totalChartedSpace
  exact
    CyclicAction.smul_contMDiff (familyPermutation j v) (familyPermutation_pow_order j v hv)
      (familyPermutation_holomorphic j v) g

private theorem Elliptic.familyAction_continuous (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    letI := familyAction j v hv
    ContinuousConstSMul (CyclicGroup j) (Family j) := by
  apply
    CyclicAction.continuousConstSMul (familyPermutation j v) (familyPermutation_pow_order j v hv)
  let := (familyPeriods j).totalChartedSpace
  exact (familyPermutation_holomorphic j v).continuous

private theorem Elliptic.discPower_familyRotation (j : Kind) (z : SpecialPeriods.Disc) :
    discPower j.order j.order_pos (familyRotation j z) = discPower j.order j.order_pos z := by
  cases j <;> apply Subtype.ext
  · change (-SpecialPeriods.rho * (z : ℂ)) ^ 3 = (z : ℂ) ^ 3
    rw [mul_pow, neg_pow, SpecialPeriods.rho_cube]
    norm_num
  · change (-Complex.I * (z : ℂ)) ^ 4 = (z : ℂ) ^ 4
    norm_num [mul_pow]

private theorem
    Elliptic.discPower_familyRotation_iterate (j : Kind) (r : ℕ) (z : SpecialPeriods.Disc) :
    discPower j.order j.order_pos ((familyRotation j)^[r] z) = discPower j.order j.order_pos z := by
  induction r with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply', discPower_familyRotation, ih]

private theorem Elliptic.familyAction_discPower (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : Family j) :
    letI := familyAction j v hv
    discPower j.order j.order_pos (g • x).1 = discPower j.order j.order_pos x.1 := by
  let := familyAction j v hv
  rw [familyAction_apply]
  exact discPower_familyRotation_iterate j g.toAdd.val x.1

private def Elliptic.FiniteQuotient.descend {G M B : Type*} [Group G] [MulAction G M] (f : M → B)
    (hf : ∀ (g : G) (x : M), f (g • x) = f x) : Space G M → B :=
  Quotient.lift f
    (by
      rintro x y ⟨g, hg⟩
      rw [← hg]
      exact hf g y)

@[simp]
private theorem Elliptic.FiniteQuotient.descend_project {G M B : Type*} [Group G] [MulAction G M]
    (f : M → B) (hf : ∀ (g : G) (x : M), f (g • x) = f x) (x : M) :
    descend f hf (project G M x) = f x :=
  rfl

private theorem Elliptic.FiniteQuotient.descend_surjective {G M B : Type*} [Group G] [MulAction G M]
    (f : M → B) (hf : ∀ (g : G) (x : M), f (g • x) = f x) (hs : Function.Surjective f) :
    Function.Surjective (descend f hf) := by
  intro b
  obtain ⟨x, hx⟩ := hs b
  exact ⟨project G M x, hx⟩

private theorem Elliptic.FiniteQuotient.descend_preimage_eq_image {G M B : Type*} [Group G]
    [MulAction G M] (f : M → B) (hf : ∀ (g : G) (x : M), f (g • x) = f x) (K : Set B) :
    descend f hf ⁻¹' K = project G M '' (f ⁻¹' K) := by
  ext q
  obtain ⟨x, rfl⟩ := project_surjective G M q
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    change descend f hf (project G M x) ∈ K
    rw [← hxy, descend_project]
    exact hy

private theorem Elliptic.FiniteQuotient.descend_continuous {G M B : Type*} [Group G] [MulAction G M]
    (f : M → B) (hf : ∀ (g : G) (x : M), f (g • x) = f x) [TopologicalSpace M]
    [TopologicalSpace B] (hc : Continuous f) : Continuous (descend f hf) :=
  (project_isQuotientMap G M).continuous_iff.mpr hc

private theorem
    Elliptic.FiniteQuotient.descend_isProperMap {G M B : Type*} [Group G] [MulAction G M]
    (f : M → B) (hf : ∀ (g : G) (x : M), f (g • x) = f x) [TopologicalSpace M]
    [TopologicalSpace B] (hp : IsProperMap f) : IsProperMap (descend f hf) :=
  isProperMap_of_comp_of_surj (project_continuous G M) (descend_continuous f hf hp.continuous) hp
    (project_surjective G M)

private instance Elliptic.discLocallyCompact : LocallyCompactSpace SpecialPeriods.Disc :=
  SpecialPeriods.unitDisc.isOpen.locallyCompactSpace

private def Elliptic.upstairsProjection (j : Kind) (x : Family j) : SpecialPeriods.Disc :=
  discPower j.order j.order_pos x.1

private theorem
    Elliptic.upstairsProjection_invariant (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : Family j) :
    letI := familyAction j v hv
    upstairsProjection j (g • x) = upstairsProjection j x :=
  familyAction_discPower j v hv g x

private abbrev Elliptic.Filling (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :=
  @FiniteQuotient.Space (CyclicGroup j) (Family j) _ (familyAction j v hv.1)

private def Elliptic.fillingQuotient (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    Family j → Filling j v hv :=
  @FiniteQuotient.project (CyclicGroup j) (Family j) _ (familyAction j v hv.1)

private theorem
    Elliptic.fillingQuotient_surjective (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    Function.Surjective (fillingQuotient j v hv) :=
  Quotient.mk_surjective

private theorem
    Elliptic.fillingQuotient_continuous (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    Continuous (fillingQuotient j v hv) := by
  let := familyAction j v hv.1
  exact FiniteQuotient.project_continuous (CyclicGroup j) (Family j)

private instance Elliptic.fillingChartedSpace (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    ChartedSpace FamilyModel (Filling j v hv) := by
  letI := (familyPeriods j).totalChartedSpace
  let := familyAction j v hv.1
  let := familyAction_continuous j v hv.1
  let := familyAction_free j v hv
  exact FiniteQuotient.chartedSpace (E := FamilyModel) (CyclicGroup j) (Family j)

private theorem Elliptic.fillingQuotient_isCoveringMap (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) : IsCoveringMap (fillingQuotient j v hv) := by
  let := familyAction j v hv.1
  let := familyAction_continuous j v hv.1
  let := familyAction_free j v hv
  exact FiniteQuotient.project_isCoveringMap (CyclicGroup j) (Family j)

private theorem
    Elliptic.fillingQuotient_holomorphic (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := (familyPeriods j).totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ FamilyModel) ω
      (fillingQuotient j v hv) := by
  let := (familyPeriods j).totalChartedSpace
  let := (familyPeriods j).totalSpace_isManifold
  let := familyAction j v hv.1
  let := familyAction_continuous j v hv.1
  let := familyAction_free j v hv
  exact
    FiniteQuotient.project_holomorphic (CyclicGroup j) (Family j)
      (familyAction_holomorphic j v hv.1)

private def Elliptic.fillingProjection (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    Filling j v hv → SpecialPeriods.Disc := by
  letI := familyAction j v hv.1
  exact FiniteQuotient.descend (upstairsProjection j) (upstairsProjection_invariant j v hv.1)

private abbrev Elliptic.HigherHomology.MappingTorusQuotient.Circle :=
  MappingTorus.Circle

private def
    Elliptic.HigherHomology.MappingTorusQuotient.twist {X : Type*} [TopologicalSpace X] (m : ℕ)
    (B : X ≃ₜ X) :
    (Elliptic.HigherHomology.MappingTorusQuotient.Circle × X) ≃ₜ
      (Elliptic.HigherHomology.MappingTorusQuotient.Circle × X) :=
  (Homeomorph.addRight
        (((1 : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle)).prodCongr
    B

@[simp]
private theorem
    Elliptic.HigherHomology.MappingTorusQuotient.twist_apply {X : Type*} [TopologicalSpace X]
    (m : ℕ) (B : X ≃ₜ X) (a : Elliptic.HigherHomology.MappingTorusQuotient.Circle) (x : X) :
    twist m B (a, x) =
      (a + (((1 : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle), B x) :=
  rfl

private theorem Elliptic.HigherHomology.MappingTorusQuotient.twist_pow_apply {X : Type*}
    [TopologicalSpace X] (m : ℕ) (B : X ≃ₜ X) (n : ℕ)
    (a : Elliptic.HigherHomology.MappingTorusQuotient.Circle) (x : X) :
    (twist m B ^ n) (a, x) =
      (a + (((n : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle),
        (B ^ n) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Homeomorph.mul_apply, ih, twist_apply]
    apply Prod.ext
    · change
        a + (((n : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle) +
            (((1 : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle) =
          a + ((((n + 1 : ℕ) : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle)
      rw [add_assoc, ← AddCircle.coe_add]
      congr 2
      push_cast
      ring
    · simp only [pow_succ', Homeomorph.mul_apply]

private theorem Elliptic.HigherHomology.MappingTorusQuotient.twist_zpow_apply {X : Type*}
    [TopologicalSpace X] (m : ℕ) (B : X ≃ₜ X) (n : ℤ)
    (a : Elliptic.HigherHomology.MappingTorusQuotient.Circle) (x : X) :
    (twist m B ^ n) (a, x) =
      (a + (((n : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle),
        (B ^ n) x) := by
  cases n with
  | ofNat
    n =>
    change
      (twist m B ^ (n : ℤ)) (a, x) =
        (a + ((((n : ℤ) : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle),
          (B ^ (n : ℤ)) x)
    simpa only [Int.cast_natCast, zpow_natCast] using twist_pow_apply m B n a x
  | negSucc n =>
    rw [zpow_negSucc]
    apply (twist m B ^ (n + 1)).injective
    change (twist m B ^ (n + 1)) ((twist m B ^ (n + 1)).symm (a, x)) = _
    rw [Homeomorph.apply_symm_apply, twist_pow_apply]
    apply Prod.ext
    · change
        a =
          a +
              ((((Int.negSucc n : ℤ) : ℝ) / m : ℝ) :
                Elliptic.HigherHomology.MappingTorusQuotient.Circle) +
            ((((n + 1 : ℕ) : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle)
      have ht : (((Int.negSucc n : ℤ) : ℝ) / m : ℝ) + (((n + 1 : ℕ) : ℝ) / m : ℝ) = 0 := by
        push_cast
        ring
      rw [add_assoc, ← AddCircle.coe_add, ht, AddCircle.coe_zero, add_zero]
    · change x = (B ^ (n + 1)) ((B ^ (Int.negSucc n : ℤ)) x)
      rw [zpow_negSucc, Homeomorph.inv_apply, Homeomorph.apply_symm_apply]

private def Elliptic.HigherHomology.MappingTorusQuotient.homeomorphPermHom_mo1973_15464
    {X : Type*} [TopologicalSpace X] : (X ≃ₜ X) →* Equiv.Perm X
    where
  toFun := Homeomorph.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem Elliptic.HigherHomology.MappingTorusQuotient.twist_pow_order {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) : twist m B ^ m = 1 := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hc : ((1 : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle) = 0 := by
    simpa only [Int.cast_one] using MappingTorus.circle_intCast 1
  apply Homeomorph.ext
  rintro ⟨a, x⟩
  rw [twist_pow_apply]
  simp only [div_self hm, hc, add_zero, hB, Homeomorph.one_apply]

private theorem Elliptic.HigherHomology.MappingTorusQuotient.twistPerm_pow_order {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    (twist m B).toEquiv ^ m = 1 := by
  change homeomorphPermHom_mo1973_15464 (twist m B) ^ m = 1
  rw [← map_pow, twist_pow_order m B hB, map_one]

@[instance_reducible]
private def
    Elliptic.HigherHomology.MappingTorusQuotient.productAction {X : Type*} [TopologicalSpace X]
    (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    MulAction (Multiplicative (ZMod m))
      (Elliptic.HigherHomology.MappingTorusQuotient.Circle × X) :=
  Elliptic.CyclicAction.action (twist m B).toEquiv (twistPerm_pow_order m B hB)

private theorem
    Elliptic.HigherHomology.MappingTorusQuotient.productAction_continuousConstSMul {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    letI := productAction m B hB
    ContinuousConstSMul (Multiplicative (ZMod m))
      (Elliptic.HigherHomology.MappingTorusQuotient.Circle × X) := by
  exact
    Elliptic.CyclicAction.continuousConstSMul (twist m B).toEquiv (twistPerm_pow_order m B hB)
      (twist m B).continuous

private theorem
    Elliptic.HigherHomology.MappingTorusQuotient.cyclicAction_ofAdd_intCast_smul {M : Type*}
    (m : ℕ) [NeZero m] (σ : Equiv.Perm M) (hσ : σ ^ m = 1) (n : ℤ) (x : M) :
    letI := Elliptic.CyclicAction.action σ hσ
    Multiplicative.ofAdd (n : ZMod m) • x = (σ ^ n) x := by
  change (σ ^ (n : ZMod m).val) x = (σ ^ n) x
  rw [← zpow_natCast, ZMod.val_intCast, ← zpow_eq_zpow_emod' n hσ]

private theorem Elliptic.HigherHomology.MappingTorusQuotient.ofAdd_intCast_smul {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) (n : ℤ)
    (a : Elliptic.HigherHomology.MappingTorusQuotient.Circle) (x : X) :
    letI := productAction m B hB
    Multiplicative.ofAdd (n : ZMod m) • (a, x) =
      (a + (((n : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle),
        (B ^ n) x) := by
  change ((twist m B).toEquiv ^ (n : ZMod m).val) (a, x) = _
  rw [← zpow_natCast, ZMod.val_intCast, ← zpow_eq_zpow_emod' n (twistPerm_pow_order m B hB)]
  have hp : (twist m B).toEquiv ^ n = (twist m B ^ n).toEquiv :=
    (homeomorphPermHom_mo1973_15464.map_zpow (twist m B) n).symm
  rw [hp]
  exact twist_zpow_apply m B n a x

private theorem Elliptic.HigherHomology.MappingTorusQuotient.fibre_zpow_add_mul_period {X : Type*}
    [TopologicalSpace X] (m : ℕ) (B : X ≃ₜ X) (hB : B ^ m = 1) (k n : ℤ) :
    B ^ (k + (m : ℤ) * n) = B ^ k := by
  rw [zpow_add, zpow_mul, zpow_natCast, hB, one_zpow, mul_one]

private theorem Elliptic.HigherHomology.MappingTorusQuotient.circle_scaled_eq_iff (m : ℕ) [NeZero m]
    (s t : ℝ) (n : ℤ) :
    ((s / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle) =
        ((t / m + (n : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle) ↔
      ∃ k : ℤ, s = t + ((n + (m : ℤ) * k : ℤ) : ℝ) := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  constructor
  · intro h
    obtain ⟨k, hk⟩ := (MappingTorus.circle_coe_eq_iff _ _).mp h.symm
    refine ⟨k, ?_⟩
    push_cast
    calc
      s = (s / m) * m := (div_mul_cancel₀ s hm).symm
      _ = (t / m + (n : ℝ) / m + (k : ℝ)) * m := by rw [hk]
      _ = t + ((n : ℝ) + (m : ℝ) * k) := by
        rw [add_mul, add_mul, div_mul_cancel₀ _ hm, div_mul_cancel₀ _ hm]
        ring
  · rintro ⟨k, hk⟩
    apply Eq.symm
    apply (MappingTorus.circle_coe_eq_iff _ _).mpr
    refine ⟨k, ?_⟩
    rw [hk]
    push_cast
    field_simp [hm]
    ring

private theorem Elliptic.HigherHomology.MappingTorusQuotient.symm_zpow_neg {X : Type*}
    [TopologicalSpace X] (B : X ≃ₜ X) (n : ℤ) : B.symm ^ (-n) = B ^ n := by
  change (B⁻¹) ^ (-n) = B ^ n
  rw [inv_zpow, zpow_neg, inv_inv]

private def Elliptic.LogGauge.quotientEquiv (G : Type*) [Group G] {M N : Type*} [MulAction G M]
    [MulAction G N] (e : M ≃ N) (heq : ∀ (g : G) (x : M), e (g • x) = g • e x) :
    Elliptic.FiniteQuotient.Space G M ≃ Elliptic.FiniteQuotient.Space G N :=
  Quotient.congr e
    (by
      intro x y
      change (x ∈ MulAction.orbit G y) ↔ (e x ∈ MulAction.orbit G (e y))
      constructor
      · rintro ⟨g, hg⟩
        exact ⟨g, (heq g y).symm.trans (congrArg e hg)⟩
      · rintro ⟨g, hg⟩
        exact ⟨g, e.injective ((heq g y).trans hg)⟩)

private theorem Elliptic.HigherHomology.MappingTorusQuotient.cyclicConjugacy_smul {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N] {m : ℕ} [NeZero m] (σ : Equiv.Perm M)
    (hσ : σ ^ m = 1) (τ : Equiv.Perm N) (hτ : τ ^ m = 1) (e : M ≃ₜ N)
    (he : ∀ x, e (σ x) = τ (e x)) (g : Multiplicative (ZMod m)) (x : M) :
    letI := Elliptic.CyclicAction.action σ hσ
    letI := Elliptic.CyclicAction.action τ hτ
    e (g • x) = g • e x := by
  let := Elliptic.CyclicAction.action σ hσ
  let := Elliptic.CyclicAction.action τ hτ
  rw [Elliptic.CyclicAction.smul_eq_iterate σ hσ, Elliptic.CyclicAction.smul_eq_iterate τ hτ]
  exact Function.Semiconj.iterate_right he g.toAdd.val x

private def Elliptic.HigherHomology.MappingTorusQuotient.cyclicQuotientCongr {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N] {m : ℕ} [NeZero m] (σ : Equiv.Perm M)
    (hσ : σ ^ m = 1) (τ : Equiv.Perm N) (hτ : τ ^ m = 1) (e : M ≃ₜ N)
    (he : ∀ x, e (σ x) = τ (e x)) :
    letI := Elliptic.CyclicAction.action σ hσ
    letI := Elliptic.CyclicAction.action τ hτ
    Elliptic.FiniteQuotient.Space (Multiplicative (ZMod m)) M ≃ₜ
      Elliptic.FiniteQuotient.Space (Multiplicative (ZMod m)) N := by
  let := Elliptic.CyclicAction.action σ hσ
  let := Elliptic.CyclicAction.action τ hτ
  refine
    { toEquiv :=
        Elliptic.LogGauge.quotientEquiv (Multiplicative (ZMod m)) e.toEquiv
          (cyclicConjugacy_smul σ hσ τ hτ e he)
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · apply
      (Elliptic.FiniteQuotient.project_isQuotientMap (Multiplicative (ZMod m))
          M).continuous_iff.mpr
    exact
      (Elliptic.FiniteQuotient.project_continuous (Multiplicative (ZMod m)) N).comp e.continuous
  · apply
      (Elliptic.FiniteQuotient.project_isQuotientMap (Multiplicative (ZMod m))
          N).continuous_iff.mpr
    exact
      (Elliptic.FiniteQuotient.project_continuous (Multiplicative (ZMod m)) M).comp
        e.symm.continuous

private abbrev Elliptic.HigherHomology.MappingTorusQuotient.ProductQuotient {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :=
  letI := productAction m B hB
  Elliptic.FiniteQuotient.Space (Multiplicative (ZMod m))
    (Elliptic.HigherHomology.MappingTorusQuotient.Circle × X)

private def
    Elliptic.HigherHomology.MappingTorusQuotient.project {X : Type*} [TopologicalSpace X] (m : ℕ)
    [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1)
    (p : Elliptic.HigherHomology.MappingTorusQuotient.Circle × X) : ProductQuotient m B hB := by
  letI := productAction m B hB
  exact
    Elliptic.FiniteQuotient.project (Multiplicative (ZMod m))
      (Elliptic.HigherHomology.MappingTorusQuotient.Circle × X) p

private theorem Elliptic.HigherHomology.MappingTorusQuotient.project_surjective {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    Function.Surjective (project m B hB) := by
  let := productAction m B hB
  exact
    Elliptic.FiniteQuotient.project_surjective (Multiplicative (ZMod m))
      (Elliptic.HigherHomology.MappingTorusQuotient.Circle × X)

private theorem Elliptic.HigherHomology.MappingTorusQuotient.project_continuous {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    Continuous (project m B hB) := by
  let := productAction m B hB
  exact
    Elliptic.FiniteQuotient.project_continuous (Multiplicative (ZMod m))
      (Elliptic.HigherHomology.MappingTorusQuotient.Circle × X)

private theorem Elliptic.HigherHomology.MappingTorusQuotient.project_eq_iff {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1)
    (p q : Elliptic.HigherHomology.MappingTorusQuotient.Circle × X) :
    project m B hB p = project m B hB q ↔
      ∃ n : ℤ,
        p =
          (q.1 + (((n : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle),
            (B ^ n) q.2) := by
  let := productAction m B hB
  change
    Elliptic.FiniteQuotient.project (Multiplicative (ZMod m))
          (Elliptic.HigherHomology.MappingTorusQuotient.Circle × X) p =
        Elliptic.FiniteQuotient.project (Multiplicative (ZMod m))
          (Elliptic.HigherHomology.MappingTorusQuotient.Circle × X) q ↔
      _
  rw [Elliptic.FiniteQuotient.project_eq_iff_mem_orbit]
  constructor
  · rintro ⟨g, hg⟩
    have he : Multiplicative.ofAdd ((g.toAdd.val : ℤ) : ZMod m) = g := by
      apply Multiplicative.ext
      simp
    have hs := ofAdd_intCast_smul m B hB (g.toAdd.val : ℤ) q.1 q.2
    rw [he] at hs
    exact ⟨g.toAdd.val, hg.symm.trans hs⟩
  · rintro ⟨n, hp⟩
    refine ⟨Multiplicative.ofAdd (n : ZMod m), ?_⟩
    change Multiplicative.ofAdd (n : ZMod m) • (q.1, q.2) = p
    rw [ofAdd_intCast_smul]
    exact hp.symm

private def
    Elliptic.HigherHomology.MappingTorusQuotient.cylinderMap {X : Type*} [TopologicalSpace X]
    (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) (p : ℝ × X) : ProductQuotient m B hB :=
  project m B hB (((p.1 / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle), p.2)

private theorem Elliptic.HigherHomology.MappingTorusQuotient.cylinderMap_continuous {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    Continuous (cylinderMap m B hB) :=
  (project_continuous m B hB).comp
    (((AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_fst.div_const (m : ℝ))).prodMk
      continuous_snd)

private theorem Elliptic.HigherHomology.MappingTorusQuotient.cylinderMap_deck {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) (n : ℤ) (p : ℝ × X) :
    cylinderMap m B hB (MappingTorus.deck B.symm n p) = cylinderMap m B hB p := by
  apply (project_eq_iff m B hB _ _).mpr
  refine ⟨n, ?_⟩
  apply Prod.ext
  · change
      (((p.1 + (n : ℝ)) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle) =
        ((p.1 / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle) +
          (((n : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle)
    rw [add_div, AddCircle.coe_add]
  · change (B.symm ^ (-n)) p.2 = (B ^ n) p.2
    rw [symm_zpow_neg]

private def
    Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusMap {X : Type*} [TopologicalSpace X]
    (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    MappingTorus.Torus B.symm → ProductQuotient m B hB :=
  Quotient.lift (cylinderMap m B hB)
    (by
      rintro p q ⟨n, rfl⟩
      exact (cylinderMap_deck m B hB n p).symm)

@[simp]
private theorem Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusMap_mk {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) (t : ℝ) (x : X) :
    mappingTorusMap m B hB (MappingTorus.mk B.symm (t, x)) =
      project m B hB (((t / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle), x) :=
  rfl

private theorem Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusMap_continuous {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    Continuous (mappingTorusMap m B hB) :=
  (cylinderMap_continuous m B hB).quotient_lift _

private theorem Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusMap_injective {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    Function.Injective (mappingTorusMap m B hB) := by
  intro p q h
  obtain ⟨⟨t, x⟩, rfl⟩ := MappingTorus.mk_surjective B.symm p
  obtain ⟨⟨s, y⟩, rfl⟩ := MappingTorus.mk_surjective B.symm q
  change
    project m B hB (((t / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle), x) =
      project m B hB (((s / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle), y) at h
  obtain ⟨n, hn⟩ := (project_eq_iff m B hB _ _).mp h
  have hf := congrArg Prod.fst hn
  change
    ((t / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle) =
      ((s / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle) +
        (((n : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle) at hf
  rw [← AddCircle.coe_add] at hf
  obtain ⟨k, hk⟩ := (circle_scaled_eq_iff m t s n).mp hf
  have hx : x = (B ^ n) y := congrArg Prod.snd hn
  apply Eq.symm
  apply (MappingTorus.mk_eq_mk_iff B.symm (s, y) (t, x)).mpr
  refine ⟨n + (m : ℤ) * k, hk, ?_⟩
  rw [symm_zpow_neg, fibre_zpow_add_mul_period m B hB]
  exact hx

private theorem Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusMap_surjective {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    Function.Surjective (mappingTorusMap m B hB) := by
  intro q
  obtain ⟨⟨a, x⟩, rfl⟩ := project_surjective m B hB q
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective a
  refine ⟨MappingTorus.mk B.symm (t * m, x), ?_⟩
  rw [mappingTorusMap_mk]
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  simp only [div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ hm, mul_one]

private instance Elliptic.HigherHomology.MappingTorusQuotient.productQuotient_t2 {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) [CompactSpace X]
    [T2Space X] : T2Space (ProductQuotient m B hB) := by
  let := productAction m B hB
  let := productAction_continuousConstSMul m B hB
  exact
    Elliptic.FiniteQuotient.spaceT2Space (Multiplicative (ZMod m))
      (Elliptic.HigherHomology.MappingTorusQuotient.Circle × X)

private def Elliptic.HigherHomology.MappingTorusQuotient.toProductHomeomorph {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) [CompactSpace X]
    [T2Space X] : MappingTorus.Torus B.symm ≃ₜ ProductQuotient m B hB :=
  Continuous.homeoOfEquivCompactToT2 (f :=
    Equiv.ofBijective (mappingTorusMap m B hB)
      ⟨mappingTorusMap_injective m B hB, mappingTorusMap_surjective m B hB⟩)
    (mappingTorusMap_continuous m B hB)

private def Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusHomeomorph {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) [CompactSpace X]
    [T2Space X] : ProductQuotient m B hB ≃ₜ MappingTorus.Torus B.symm :=
  (toProductHomeomorph m B hB).symm

@[simp]
private theorem
    Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusHomeomorph_symm_mk {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) [CompactSpace X]
    [T2Space X] (t : ℝ) (x : X) :
    (mappingTorusHomeomorph m B hB).symm (MappingTorus.mk B.symm (t, x)) =
      project m B hB (((t / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle), x) :=
  rfl

private theorem
    Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusHomeomorph_project {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) [CompactSpace X]
    [T2Space X] (t : ℝ) (x : X) :
    mappingTorusHomeomorph m B hB
        (project m B hB ((t : Elliptic.HigherHomology.MappingTorusQuotient.Circle), x)) =
      MappingTorus.mk B.symm (t * m, x) := by
  apply (mappingTorusHomeomorph m B hB).symm.injective
  rw [Homeomorph.symm_apply_apply, mappingTorusHomeomorph_symm_mk]
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  simp only [div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ hm, mul_one]

private theorem Elliptic.discPower_eq_iff_scalar_iterate (m : ℕ) (hm : 0 < m) (c : ℂ) (hc : ‖c‖ = 1)
    (hroot : IsPrimitiveRoot c m) (z w : SpecialPeriods.Disc) :
    discPower m hm z = discPower m hm w ↔ ∃ r < m, (SpecialPeriods.discScalar c hc)^[r] w = z := by
  let : NeZero m := ⟨hm.ne'⟩
  constructor
  · intro he
    have hp : (z : ℂ) ^ m = (w : ℂ) ^ m := congrArg Subtype.val he
    by_cases hw : (w : ℂ) = 0
    · have hz : (z : ℂ) = 0 :=
        (pow_eq_zero_iff hm.ne').mp (by simpa only [hw, zero_pow hm.ne'] using hp)
      exact ⟨0, hm, Subtype.ext (hw.trans hz.symm)⟩
    · have hr : ((z : ℂ) / (w : ℂ)) ^ m = 1 := by rw [div_pow, hp, div_self (pow_ne_zero m hw)]
      obtain ⟨r, hrm, hr⟩ := hroot.eq_pow_of_pow_eq_one hr
      refine ⟨r, hrm, Subtype.ext ?_⟩
      rw [SpecialPeriods.discScalar_iterate_val, hr, div_mul_cancel₀ _ hw]
  · rintro ⟨r, _, rfl⟩
    apply Subtype.ext
    change ((SpecialPeriods.discScalar c hc)^[r] w : ℂ) ^ m = (w : ℂ) ^ m
    rw [SpecialPeriods.discScalar_iterate_val, mul_pow, ← pow_mul, Nat.mul_comm r m, pow_mul,
      hroot.pow_eq_one, one_pow, one_mul]

private theorem Elliptic.neg_rho_isPrimitiveRoot : IsPrimitiveRoot (-SpecialPeriods.rho) 3 := by
  apply IsPrimitiveRoot.mk_of_lt _ (by decide)
  · calc
      (-SpecialPeriods.rho) ^ 3 = -(SpecialPeriods.rho ^ 3) := by ring
      _ = 1 := by rw [SpecialPeriods.rho_cube]; norm_num
  · exact fun r hr hrm => SpecialPeriods.neg_rho_pow_ne_one hr hrm

private theorem Elliptic.discPower_three_eq_iff (z w : SpecialPeriods.Disc) :
    discPower 3 (by decide) z = discPower 3 (by decide) w ↔
      ∃ r < 3, SpecialPeriods.discRotateThree^[r] w = z :=
  discPower_eq_iff_scalar_iterate 3 (by decide) (-SpecialPeriods.rho)
    (by simpa using SpecialPeriods.norm_rho) neg_rho_isPrimitiveRoot z w

private theorem Elliptic.discPower_four_eq_iff (z w : SpecialPeriods.Disc) :
    discPower 4 (by decide) z = discPower 4 (by decide) w ↔
      ∃ r < 4, SpecialPeriods.discRotateFour^[r] w = z :=
  discPower_eq_iff_scalar_iterate 4 (by decide) (-Complex.I) (by simp)
    Complex.isPrimitiveRoot_neg_I z w

private theorem Elliptic.discPower_eq_iff_familyRotation (j : Kind) (z w : SpecialPeriods.Disc) :
    discPower j.order j.order_pos z = discPower j.order j.order_pos w ↔
      ∃ r < j.order, (familyRotation j)^[r] w = z := by
  cases j
  · exact discPower_three_eq_iff z w
  · exact discPower_four_eq_iff z w

private theorem Elliptic.complexPower_hasDerivAt (m : ℕ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => w ^ m) ((m : ℂ) * z ^ (m - 1)) z :=
  hasDerivAt_pow m z

private theorem Elliptic.complexPower_holomorphic (m : ℕ) : ContDiff ℂ ω (fun z : ℂ => z ^ m) :=
  contDiff_id.pow m

private theorem
    Elliptic.complexPower_coefficient_ne_zero (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0) :
    (m : ℂ) * z ^ (m - 1) ≠ 0 :=
  mul_ne_zero (by exact_mod_cast hm.ne') (pow_ne_zero _ hz)

private def Elliptic.complexPowerChart (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0) :
    OpenPartialHomeomorph ℂ ℂ :=
  ((complexPower_holomorphic m).contDiffAt.toOpenPartialHomeomorph (fun w : ℂ => w ^ m)
        ((complexPower_hasDerivAt m z).hasFDerivAt_equiv
          (complexPower_coefficient_ne_zero m hm z hz))
        (by simp)).restr
    {w | w ≠ 0}

private theorem Elliptic.mem_complexPowerChart_source (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0) :
    z ∈ (complexPowerChart m hm z hz).source := by
  have ho : IsOpen {w : ℂ | w ≠ 0} := isOpen_ne_fun continuous_id continuous_const
  rw [complexPowerChart, OpenPartialHomeomorph.restr_source' _ _ ho]
  exact
    ⟨(complexPower_holomorphic m).contDiffAt.mem_toOpenPartialHomeomorph_source
        ((complexPower_hasDerivAt m z).hasFDerivAt_equiv
          (complexPower_coefficient_ne_zero m hm z hz))
        (by simp),
      hz⟩

private theorem Elliptic.complexPowerChart_source_ne_zero (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0)
    {w : ℂ} (hw : w ∈ (complexPowerChart m hm z hz).source) : w ≠ 0 := by
  have ho : IsOpen {w : ℂ | w ≠ 0} := isOpen_ne_fun continuous_id continuous_const
  rw [complexPowerChart, OpenPartialHomeomorph.restr_source' _ _ ho] at hw
  exact hw.2

private theorem Elliptic.complexPowerChart_holomorphic (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0) :
    ContDiffOn ℂ ω (complexPowerChart m hm z hz) (complexPowerChart m hm z hz).source :=
  (complexPower_holomorphic m).contDiffOn

private theorem
    Elliptic.complexPowerChart_symm_holomorphic (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0) :
    ContDiffOn ℂ ω (complexPowerChart m hm z hz).symm (complexPowerChart m hm z hz).target := by
  intro w hw
  have hne :=
    complexPowerChart_source_ne_zero m hm z hz ((complexPowerChart m hm z hz).map_target hw)
  exact
    ((complexPowerChart m hm z hz).contDiffAt_symm hw
        ((complexPower_hasDerivAt m _).hasFDerivAt_equiv
          (complexPower_coefficient_ne_zero m hm _ hne))
        (complexPower_holomorphic m).contDiffAt).contDiffWithinAt

public
theorem Elliptic.complexPower_isLocalDiffeomorphAt (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0) :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (fun w : ℂ => w ^ m) z := by
  refine
    ⟨{  toPartialEquiv := (complexPowerChart m hm z hz).toPartialEquiv
        open_source := (complexPowerChart m hm z hz).open_source
        open_target := (complexPowerChart m hm z hz).open_target
        contMDiffOn_toFun := (complexPowerChart_holomorphic m hm z hz).contMDiffOn
        contMDiffOn_invFun := (complexPowerChart_symm_holomorphic m hm z hz).contMDiffOn },
      mem_complexPowerChart_source m hm z hz, fun _ _ => rfl⟩

end Mathoverflow1973

end
