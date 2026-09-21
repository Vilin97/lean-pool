/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Uniformization.CuspUniformization3
public import LeanPool.HopfProblem.Recognition.Degree2
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.PeriodFamily.HolomorphicPeriodMap1
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods1
import all LeanPool.HopfProblem.Elliptic.Core2
import all LeanPool.HopfProblem.Recognition.Degree2
import all LeanPool.HopfProblem.Elliptic.Core3
import all LeanPool.HopfProblem.Uniformization.CuspUniformization3

/-!
# Hopf problem: elliptic · core 4

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

private def Elliptic.LogGauge.baseOpen : TopologicalSpace.Opens SpecialPeriods.Disc :=
  ⟨{z | (z : ℂ) ≠ 0}, isOpen_ne_fun continuous_subtype_val continuous_const⟩

private abbrev Elliptic.LogGauge.BaseStar :=
  baseOpen

private def
    Elliptic.LogGauge.familyOpen : TopologicalSpace.Opens (SpecialPeriods.Disc × RealTorus₄) :=
  ⟨{x | (x.1 : ℂ) ≠ 0},
    isOpen_ne_fun (continuous_subtype_val.comp continuous_fst) continuous_const⟩

private abbrev Elliptic.LogGauge.FamilyStar (_P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) :=
  familyOpen

private def
    Elliptic.LogGauge.coverOpen : TopologicalSpace.Opens (SpecialPeriods.Disc × ComplexPlane₂) :=
  ⟨{x | (x.1 : ℂ) ≠ 0},
    isOpen_ne_fun (continuous_subtype_val.comp continuous_fst) continuous_const⟩

private abbrev Elliptic.LogGauge.CoverStar :=
  coverOpen

private def
    Elliptic.LogGauge.project (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (x : CoverStar) :
    FamilyStar P :=
  ⟨P.quotientMap x, x.2⟩

private theorem
    Elliptic.LogGauge.project_surjective (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) :
    Function.Surjective (project P) := by
  intro x
  obtain ⟨y, hy⟩ := P.quotientMap_surjective x.1
  have hy0 : (y.1 : ℂ) ≠ 0 := by
    have hb : y.1 = x.1.1 := congrArg Prod.fst hy
    rw [hb]
    exact x.2
  exact ⟨⟨y, hy0⟩, Subtype.ext hy⟩

private def
    Elliptic.LogGauge.periodVector (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : Lattice)
    (z : SpecialPeriods.Disc) : ComplexPlane₂ :=
  P.periodEquiv z (Elliptic.realCast v)

@[simp]
private theorem Elliptic.LogGauge.periodVector_neg (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc)
    (v : Lattice) (z : SpecialPeriods.Disc) : periodVector P (-v) z = -periodVector P v z := by
  change P.periodEquiv z (Elliptic.realCast (-v)) = -P.periodEquiv z (Elliptic.realCast v)
  rw [show Elliptic.realCast (-v) = -Elliptic.realCast v by ext i; simp [Elliptic.realCast],
    map_neg]

private theorem Elliptic.LogGauge.periodVector_mem_lattice
    (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : Lattice) (z : SpecialPeriods.Disc) :
    periodVector P v z ∈ (P.point z).lattice := by
  rw [← P.periodEquiv_map_lattice z]
  exact
    Submodule.mem_map.mpr
      ⟨Elliptic.realCast v, (Elliptic.standardLattice_mem_iff _).mpr ⟨v, rfl⟩, rfl⟩

private theorem Elliptic.LogGauge.periodVector_holomorphic
    (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : Lattice) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ComplexPlane₂) ω
      (periodVector P v) :=
  P.holomorphic_periodEquiv_const (Elliptic.realCast v)

private theorem Elliptic.LogGauge.quotientMap_integer_period
    (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : Lattice) (z : SpecialPeriods.Disc)
    (u : ComplexPlane₂) (a : ℂ) (n : ℤ) :
    P.quotientMap (z, u + (a + n) • periodVector P v z) =
      P.quotientMap (z, u + a • periodVector P v z) := by
  rw [← P.fibreInclusion_mkQ, ← P.fibreInclusion_mkQ]
  apply congrArg (P.fibreInclusion z)
  apply (Submodule.Quotient.eq _).mpr
  have hp := (P.point z).lattice.smul_mem n (periodVector_mem_lattice P v z)
  convert hp using 1
  rw [add_smul, Int.cast_smul_eq_zsmul]
  abel

private theorem Elliptic.LogGauge.quotientMap_eq_of_scalar_int
    (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : Lattice) (z : SpecialPeriods.Disc)
    (u : ComplexPlane₂) {a b : ℂ} (hab : ∃ n : ℤ, a = b + n) :
    P.quotientMap (z, u + a • periodVector P v z) =
      P.quotientMap (z, u + b • periodVector P v z) := by
  obtain ⟨n, rfl⟩ := hab
  exact quotientMap_integer_period P v z u b n

private def Elliptic.LogGauge.sectionCoordinate (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc)
    (v : Lattice) (z : SpecialPeriods.Disc) : RealTorus₄ :=
  standardLattice.mkQ
    ((P.periodEquiv z).symm (CuspUniformization.logarithm z • periodVector P v z))

@[simp]
private theorem
    Elliptic.LogGauge.sectionCoordinate_neg (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc)
    (v : Lattice) (z : SpecialPeriods.Disc) :
    sectionCoordinate P (-v) z = -sectionCoordinate P v z := by
  simp only [sectionCoordinate, periodVector_neg, smul_neg, map_neg]

private def
    Elliptic.LogGauge.gaugeMap (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : Lattice)
    (x : FamilyStar P) : FamilyStar P :=
  ⟨(x.1.1, x.1.2 + sectionCoordinate P v x.1.1), x.2⟩

@[simp]
private theorem
    Elliptic.LogGauge.gaugeMap_neg_gaugeMap (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc)
    (v : Lattice) (x : FamilyStar P) : gaugeMap P (-v) (gaugeMap P v x) = x := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (x.1.2 + sectionCoordinate P v x.1.1) + sectionCoordinate P (-v) x.1.1 = x.1.2
    rw [sectionCoordinate_neg, add_neg_cancel_right]

private def
    Elliptic.LogGauge.gaugeEquiv (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : Lattice) :
    Equiv.Perm (FamilyStar P) where
  toFun := gaugeMap P v
  invFun := gaugeMap P (-v)
  left_inv := gaugeMap_neg_gaugeMap P v
  right_inv x := by simpa only [neg_neg] using gaugeMap_neg_gaugeMap P (-v) x

private def
    Elliptic.LogGauge.gaugeLift (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : Lattice)
    (a : ℂ → ℂ) (x : CoverStar) : CoverStar :=
  ⟨(x.1.1, x.1.2 + a x.1.1 • periodVector P v x.1.1), x.2⟩

@[simp]
private theorem Elliptic.LogGauge.gaugeMap_project (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc)
    (v : Lattice) (x : CoverStar) :
    gaugeMap P v (project P x) = project P (gaugeLift P v CuspUniformization.logarithm x) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  change
    standardLattice.mkQ ((P.periodEquiv x.1.1).symm x.1.2) +
        standardLattice.mkQ
          ((P.periodEquiv x.1.1).symm
            (CuspUniformization.logarithm x.1.1 • periodVector P v x.1.1)) =
      standardLattice.mkQ
        ((P.periodEquiv x.1.1).symm
          (x.1.2 + CuspUniformization.logarithm x.1.1 • periodVector P v x.1.1))
  rw [map_add, map_add]

private theorem Elliptic.LogGauge.gaugeMap_project_localLog
    (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : Lattice) {z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (x : CoverStar) :
    gaugeMap P v (project P x) = project P (gaugeLift P v (CuspUniformization.localLog z₀) x) := by
  rw [gaugeMap_project]
  apply Subtype.ext
  exact
    quotientMap_eq_of_scalar_int P v x.1.1 x.1.2
      (CuspUniformization.logarithm_eq_localLog_add_int hz₀ x.2)

private def Elliptic.LogGauge.zeroSection (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc)
    (z : BaseStar) : FamilyStar P :=
  ⟨(z.1, 0), z.2⟩

private def
    Elliptic.LogGauge.sectionMap (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : Lattice) :
    BaseStar → FamilyStar P :=
  gaugeMap P v ∘ zeroSection P

private theorem
    Elliptic.LogGauge.sectionMap_formula (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc)
    (v : Lattice) (z : BaseStar) :
    (sectionMap P v z : P.TotalSpace) =
      P.quotientMap (z.1, CuspUniformization.logarithm z.1 • periodVector P v z.1) := by
  apply Prod.ext
  · rfl
  · exact zero_add _

private def Elliptic.LogGauge.starPermutation {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) : Equiv.Perm (FamilyStar D.periods) :=
  (D.permutation v).subtypeEquiv
    (fun x => by
      change (x.1 : ℂ) ≠ 0 ↔ (Elliptic.familyRotation j x.1 : ℂ) ≠ 0
      rw [familyRotation_val_exponential, mul_ne_zero_iff]
      exact ⟨fun hx => ⟨CuspUniformization.exponential_ne_zero _, hx⟩, fun hx => hx.2⟩)

@[simp]
private theorem Elliptic.LogGauge.starPermutation_coe {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (x : FamilyStar D.periods) :
    (starPermutation D v x : D.TotalSpace) = D.permutation v x :=
  rfl

private def
    Elliptic.LogGauge.starLift {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j) (v : Lattice)
    (x : CoverStar) : CoverStar :=
  ⟨D.complexLift v x, familyRotation_ne_zero j x.1.1 x.2⟩

@[simp]
private theorem Elliptic.LogGauge.starPermutation_project {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (x : CoverStar) :
    starPermutation D v (project D.periods x) = project D.periods (starLift D v x) := by
  apply Subtype.ext
  exact (D.complexLift_quotientMap v x).symm

private theorem Elliptic.LogGauge.periodVector_covariance {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (z : SpecialPeriods.Disc) :
    Elliptic.linearMatrix j (D.periods.point z) *ᵥ periodVector D.periods v z =
      periodVector D.periods v (Elliptic.familyRotation j z) := by
  have h := D.periodEquiv_flatLinear z (Elliptic.realCast v)
  rw [Elliptic.flatLinear_fixes_realCast j v hv] at h
  exact h.symm

private theorem Elliptic.LogGauge.complexLift_translation {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (z : SpecialPeriods.Disc) :
    D.periods.periodEquiv z ((1 / (j.order : ℝ)) • Elliptic.realCast v) =
      (1 / (j.order : ℂ)) • periodVector D.periods v z := by
  rw [map_smul]
  ext i
  simp only [periodVector, Pi.smul_apply, Complex.real_smul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_natCast, smul_eq_mul]

private theorem Elliptic.LogGauge.complexLift_formula {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (z : SpecialPeriods.Disc)
    (u : ComplexPlane₂) :
    D.complexLift v (z, u) =
      (Elliptic.familyRotation j z,
        Elliptic.linearMatrix j (D.periods.point z) *ᵥ u +
          (1 / (j.order : ℂ)) • periodVector D.periods v (Elliptic.familyRotation j z)) := by
  unfold Elliptic.Equivariant.Data.complexLift
  rw [complexLift_translation]

private theorem
    Elliptic.LogGauge.periodVector_zero {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (z : SpecialPeriods.Disc) : periodVector D.periods 0 z = 0 := by
  change D.periods.periodEquiv z (Elliptic.realCast 0) = 0
  rw [show Elliptic.realCast 0 = 0 by ext i; simp [Elliptic.realCast], map_zero]

private theorem Elliptic.LogGauge.gaugeLift_starLift_project {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v) (x : CoverStar) :
    project D.periods (gaugeLift D.periods v CuspUniformization.logarithm (starLift D v x)) =
      project D.periods (starLift D 0 (gaugeLift D.periods v CuspUniformization.logarithm x)) := by
  apply Subtype.ext
  change
    D.periods.quotientMap
        (Elliptic.familyRotation j x.1.1,
          (D.complexLift v x.1).2 +
            CuspUniformization.logarithm (Elliptic.familyRotation j x.1.1 : ℂ) •
              periodVector D.periods v (Elliptic.familyRotation j x.1.1)) =
      D.periods.quotientMap
        (D.complexLift 0
          (x.1.1,
            x.1.2 + CuspUniformization.logarithm (x.1.1 : ℂ) • periodVector D.periods v x.1.1))
  rw [show x.1 = (x.1.1, x.1.2) by rfl, complexLift_formula, complexLift_formula]
  simp only [periodVector_zero, smul_zero, add_zero, Matrix.mulVec_add, Matrix.mulVec_smul,
    periodVector_covariance D v hv]
  rw [add_assoc, ← add_smul]
  apply
    quotientMap_eq_of_scalar_int D.periods v (Elliptic.familyRotation j x.1.1)
      (Elliptic.linearMatrix j (D.periods.point x.1.1) *ᵥ x.1.2)
  obtain ⟨n, hn⟩ := logarithm_familyRotation j x.1.1 x.2
  exact ⟨n, by rw [hn]; ring⟩

private theorem Elliptic.LogGauge.gaugeMap_intertwines {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (x : FamilyStar D.periods) :
    gaugeMap D.periods v (starPermutation D v x) = starPermutation D 0 (gaugeMap D.periods v x) :=
  by
  obtain ⟨y, rfl⟩ := project_surjective D.periods x
  rw [starPermutation_project, gaugeMap_project, gaugeMap_project, starPermutation_project]
  exact gaugeLift_starLift_project D v hv y

private theorem Elliptic.LogGauge.starPermutation_iterate_coe {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (r : ℕ) (x : FamilyStar D.periods) :
    ((starPermutation D v)^[r] x : D.TotalSpace) = (D.permutation v)^[r] x := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', starPermutation_coe, ih]

private theorem Elliptic.LogGauge.starPermutation_pow_order {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    starPermutation D v ^ j.order = 1 := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  change ((starPermutation D v ^ j.order) x : D.TotalSpace) = x
  rw [Equiv.Perm.coe_pow, starPermutation_iterate_coe, ← Equiv.Perm.coe_pow,
    D.permutation_pow_order v hv]
  rfl

@[instance_reducible]
private def Elliptic.LogGauge.starAction {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    MulAction (Elliptic.CyclicGroup j) (FamilyStar D.periods) :=
  Elliptic.CyclicAction.action (starPermutation D v) (starPermutation_pow_order D v hv)

private theorem
    Elliptic.LogGauge.starAction_coe {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : j.matrix *ᵥ v = v) (g : Elliptic.CyclicGroup j)
    (x : FamilyStar D.periods) :
    letI := D.action v hv
    letI := starAction D v hv
    ((g • x : FamilyStar D.periods) : D.TotalSpace) = g • (x : D.TotalSpace) := by
  let := D.action v hv
  let := starAction D v hv
  change
    ((starPermutation D v ^ g.toAdd.val) x : D.TotalSpace) =
      (D.permutation v ^ g.toAdd.val) (x : D.TotalSpace)
  rw [Equiv.Perm.coe_pow, starPermutation_iterate_coe, Equiv.Perm.coe_pow]

private theorem Elliptic.LogGauge.gaugeMap_starAction {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : Elliptic.CyclicGroup j) (x : FamilyStar D.periods) :
    gaugeMap D.periods v (@SMul.smul _ _ (starAction D v hv).toSMul g x) =
      @SMul.smul _ _ (starAction D 0 (by simp)).toSMul g (gaugeMap D.periods v x) := by
  have h : Function.Semiconj (gaugeMap D.periods v) (starPermutation D v) (starPermutation D 0) :=
    gaugeMap_intertwines D v hv
  change
    gaugeMap D.periods v ((starPermutation D v ^ g.toAdd.val) x) =
      (starPermutation D 0 ^ g.toAdd.val) (gaugeMap D.periods v x)
  rw [Equiv.Perm.coe_pow, Equiv.Perm.coe_pow]
  exact h.iterate_right g.toAdd.val x

private theorem
    Elliptic.LogGauge.starAction_free {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    letI := starAction D v hv
    IsCancelSMul (Elliptic.CyclicGroup j) (FamilyStar D.periods) := by
  let := starAction D v hv
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro g x hx
  let := D.action v hv
  have hc : g • (x : D.TotalSpace) = (x : D.TotalSpace) :=
    (starAction_coe D v hv g x).symm.trans (congrArg Subtype.val hx)
  have hb : (Elliptic.familyRotation j)^[g.toAdd.val] x.1.1 = x.1.1 := by
    simpa only [D.action_apply v hv g] using congrArg Prod.fst hc
  have hg : g.toAdd.val = 0 := by
    by_contra hg
    have hz :=
      (Elliptic.familyRotation_iterate_fixed_iff j g.toAdd.val (Nat.pos_of_ne_zero hg)
            (ZMod.val_lt _) x.1.1).mp
        hb
    exact x.2 (congrArg Subtype.val hz)
  apply Multiplicative.ext
  exact (ZMod.val_eq_zero _).mp hg

private theorem Elliptic.LogGauge.starAction_holomorphic {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : Elliptic.CyclicGroup j) :
    letI := D.periods.totalChartedSpace
    letI := starAction D v hv
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (fun x : FamilyStar D.periods => g • x) := by
  let := D.periods.totalChartedSpace
  let := starAction D v hv
  let := D.action v hv
  intro x
  have he :
    ContMDiffAt (modelWithCornersSelf ℂ Elliptic.FamilyModel)
        (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω
        (fun y : FamilyStar D.periods => ((g • y : FamilyStar D.periods) : D.TotalSpace)) x ↔
      ContMDiffAt (modelWithCornersSelf ℂ Elliptic.FamilyModel)
        (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (fun y : FamilyStar D.periods => g • y)
        x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  apply he.mp
  have h :
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω
      (fun y : FamilyStar D.periods => g • (y : D.TotalSpace)) :=
    (D.action_holomorphic v hv g).comp contMDiff_subtype_val
  simpa only [starAction_coe] using h x

private theorem Elliptic.LogGauge.starAction_continuous {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    letI := starAction D v hv
    ContinuousConstSMul (Elliptic.CyclicGroup j) (FamilyStar D.periods) := by
  let := D.periods.totalChartedSpace
  let := starAction D v hv
  exact ⟨fun g => (starAction_holomorphic D v hv g).continuous⟩

@[instance_reducible]
private def Elliptic.LogGauge.gaugeCoveringChartedSpace :
    ChartedSpace Elliptic.FamilyModel (SpecialPeriods.Disc × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (SpecialPeriods.Disc × ComplexPlane₂))

attribute [local instance] Elliptic.LogGauge.gaugeCoveringChartedSpace in
private theorem Elliptic.LogGauge.gaugeCoveringManifold :
    IsManifold (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω
      (SpecialPeriods.Disc × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact
    IsManifold.prod (I := (modelWithCornersSelf ℂ ℂ)) (I' :=
      (modelWithCornersSelf ℂ ComplexPlane₂)) SpecialPeriods.Disc ComplexPlane₂

attribute [local instance] Elliptic.LogGauge.gaugeCoveringChartedSpace
    Elliptic.LogGauge.gaugeCoveringManifold in
private theorem Elliptic.LogGauge.project_isLocalDiffeomorph
    (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) :
    letI := P.totalChartedSpace
    IsLocalDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (project P) := by
  let := P.totalChartedSpace
  let := P.coveringAction
  have hq :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω P.quotientMap :=
    CoveringQuotient.project_isLocalDiffeomorph P.quotientCoveringMap P.coveringAction_holomorphic
  exact
    isLocalDiffeomorph_restrictOpens (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) hq coverOpen familyOpen (fun _ hx => hx)

attribute [local instance] Elliptic.LogGauge.gaugeCoveringChartedSpace
    Elliptic.LogGauge.gaugeCoveringManifold in
private theorem
    Elliptic.LogGauge.project_holomorphic (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) :
    letI := P.totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (project P) := by
  let := P.totalChartedSpace
  exact (project_isLocalDiffeomorph P).contMDiff

attribute [local instance] Elliptic.LogGauge.gaugeCoveringChartedSpace
    Elliptic.LogGauge.gaugeCoveringManifold in
private theorem
    Elliptic.LogGauge.gaugeLift_holomorphicAt (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc)
    (v : Lattice) {a : ℂ → ℂ} {x : CoverStar} (ha : ContDiffAt ℂ ω a (x.1.1 : ℂ)) :
    ContMDiffAt (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (gaugeLift P v a) x := by
  have hb :
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel) (modelWithCornersSelf ℂ ℂ) ω
      (fun y : CoverStar => y.1.1) := by
    have hfst :
      ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel) (modelWithCornersSelf ℂ ℂ) ω
        (Prod.fst : SpecialPeriods.Disc × ComplexPlane₂ → SpecialPeriods.Disc) := by
      rw [modelWithCornersSelf_prod]
      exact contMDiff_fst
    exact hfst.comp contMDiff_subtype_val
  have hw :
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel) (modelWithCornersSelf ℂ ComplexPlane₂)
      ω (fun y : CoverStar => y.1.2) := by
    have hsnd :
      ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel)
        (modelWithCornersSelf ℂ ComplexPlane₂) ω
        (Prod.snd : SpecialPeriods.Disc × ComplexPlane₂ → ComplexPlane₂) := by
      rw [modelWithCornersSelf_prod]
      exact contMDiff_snd
    exact hsnd.comp contMDiff_subtype_val
  have hbc :
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel) (modelWithCornersSelf ℂ ℂ) ω
      (fun y : CoverStar => (y.1.1 : ℂ)) :=
    contMDiff_subtype_val.comp hb
  have hscalar :
    ContMDiffAt (modelWithCornersSelf ℂ Elliptic.FamilyModel) (modelWithCornersSelf ℂ ℂ) ω
      (fun y : CoverStar => a y.1.1) x :=
    ha.contMDiffAt.comp x hbc.contMDiffAt
  have hp :
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel) (modelWithCornersSelf ℂ ComplexPlane₂)
      ω (fun y : CoverStar => periodVector P v y.1.1) :=
    (periodVector_holomorphic P v).comp hb
  have hsum :
    ContMDiffAt (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ ComplexPlane₂) ω
      (fun y : CoverStar => y.1.2 + a y.1.1 • periodVector P v y.1.1) x :=
    hw.contMDiffAt.add (hscalar.smul hp.contMDiffAt)
  have hpair :
    ContMDiffAt (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω
      (fun y : CoverStar => (y.1.1, y.1.2 + a y.1.1 • periodVector P v y.1.1)) x := by
    simpa only [← modelWithCornersSelf_prod] using hb.contMDiffAt.prodMk hsum
  have he :
    ContMDiffAt (modelWithCornersSelf ℂ Elliptic.FamilyModel)
        (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (Subtype.val ∘ gaugeLift P v a) x ↔
      ContMDiffAt (modelWithCornersSelf ℂ Elliptic.FamilyModel)
        (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (gaugeLift P v a) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp hpair

attribute [local instance] Elliptic.LogGauge.gaugeCoveringChartedSpace
    Elliptic.LogGauge.gaugeCoveringManifold in
private theorem Elliptic.LogGauge.gaugeMap_comp_project_holomorphic
    (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : Lattice) :
    letI := P.totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (gaugeMap P v ∘ project P) := by
  let := P.totalChartedSpace
  intro x
  have hl := gaugeLift_holomorphicAt P v (x := x) (CuspUniformization.localLog_contDiffAt x.2)
  have h := (project_holomorphic P).contMDiffAt.comp x hl
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (gaugeMap_project_localLog P v x.2)

attribute [local instance] Elliptic.LogGauge.gaugeCoveringChartedSpace
    Elliptic.LogGauge.gaugeCoveringManifold in
private theorem
    Elliptic.LogGauge.gaugeMap_holomorphic (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc)
    (v : Lattice) :
    letI := P.totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (gaugeMap P v) := by
  let := P.totalChartedSpace
  exact
    contMDiff_of_comp_localDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (project_isLocalDiffeomorph P) (project_surjective P)
      (gaugeMap_comp_project_holomorphic P v)

attribute [local instance] Elliptic.LogGauge.gaugeCoveringChartedSpace
    Elliptic.LogGauge.gaugeCoveringManifold in
private theorem
    Elliptic.LogGauge.gaugeMap_continuous (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc)
    (v : Lattice) : Continuous (gaugeMap P v) := by
  let := P.totalChartedSpace
  exact (gaugeMap_holomorphic P v).continuous

private def
    Elliptic.LogGauge.restrictedProject (G : Type*) [Group G] {M : Type*} [TopologicalSpace M]
    [MulAction G M] (U : TopologicalSpace.Opens M)
    (V : TopologicalSpace.Opens (Elliptic.FiniteQuotient.Space G M))
    (hpre :
      Elliptic.FiniteQuotient.project G M ⁻¹' (V : Set (Elliptic.FiniteQuotient.Space G M)) =
        (U : Set M))
    (x : U) : V :=
  ⟨Elliptic.FiniteQuotient.project G M x,
    by
    change
      (x : M) ∈
        Elliptic.FiniteQuotient.project G M ⁻¹' (V : Set (Elliptic.FiniteQuotient.Space G M))
    rw [hpre]
    exact x.2⟩

private theorem Elliptic.LogGauge.restrictedProject_surjective (G : Type*) [Group G] {M : Type*}
    [TopologicalSpace M] [MulAction G M] (U : TopologicalSpace.Opens M)
    (V : TopologicalSpace.Opens (Elliptic.FiniteQuotient.Space G M))
    (hpre :
      Elliptic.FiniteQuotient.project G M ⁻¹' (V : Set (Elliptic.FiniteQuotient.Space G M)) =
        (U : Set M)) :
    Function.Surjective (restrictedProject G U V hpre) := by
  intro y
  obtain ⟨x, hx⟩ := Elliptic.FiniteQuotient.project_surjective G M y.1
  have hxU : x ∈ (U : Set M) := by
    rw [← hpre]
    change Elliptic.FiniteQuotient.project G M x ∈ (V : Set (Elliptic.FiniteQuotient.Space G M))
    rw [hx]
    exact y.2
  exact ⟨⟨x, hxU⟩, Subtype.ext hx⟩

private def
    Elliptic.LogGauge.openQuotientEquiv (G : Type*) [Group G] {M : Type*} [TopologicalSpace M]
    [MulAction G M] (U : TopologicalSpace.Opens M) [MulAction G U]
    (V : TopologicalSpace.Opens (Elliptic.FiniteQuotient.Space G M))
    (hcompat : ∀ (g : G) (x : U), ((g • x : U) : M) = g • (x : M))
    (hpre :
      Elliptic.FiniteQuotient.project G M ⁻¹' (V : Set (Elliptic.FiniteQuotient.Space G M)) =
        (U : Set M)) :
    Elliptic.FiniteQuotient.Space G U ≃ V :=
  (Equiv.subtypeQuotientEquivQuotientSubtype (fun x : M => x ∈ (U : Set M)) (s₁ :=
      MulAction.orbitRel G M) (s₂ := MulAction.orbitRel G U)
      (fun y => y ∈ (V : Set (Elliptic.FiniteQuotient.Space G M)))
      (by
        intro x
        change x ∈ (U : Set M) ↔ x ∈ Elliptic.FiniteQuotient.project G M ⁻¹' (V : Set _)
        rw [hpre])
      (by
        intro x y
        change (x ∈ MulAction.orbit G y) ↔ ((x : M) ∈ MulAction.orbit G (y : M))
        constructor
        · rintro ⟨g, hg⟩
          exact ⟨g, (hcompat g y).symm.trans (congrArg Subtype.val hg)⟩
        · rintro ⟨g, hg⟩
          exact ⟨g, Subtype.ext ((hcompat g y).trans hg)⟩)).symm

@[simp]
private theorem Elliptic.LogGauge.openQuotientEquiv_project (G : Type*) [Group G] {M : Type*}
    [TopologicalSpace M] [MulAction G M] (U : TopologicalSpace.Opens M) [MulAction G U]
    (V : TopologicalSpace.Opens (Elliptic.FiniteQuotient.Space G M))
    (hcompat : ∀ (g : G) (x : U), ((g • x : U) : M) = g • (x : M))
    (hpre :
      Elliptic.FiniteQuotient.project G M ⁻¹' (V : Set (Elliptic.FiniteQuotient.Space G M)) =
        (U : Set M))
    (x : U) :
    openQuotientEquiv G U V hcompat hpre (Elliptic.FiniteQuotient.project G U x) =
      restrictedProject G U V hpre x :=
  rfl

@[simp]
private theorem Elliptic.LogGauge.openQuotientEquiv_symm_restrictedProject (G : Type*) [Group G]
    {M : Type*} [TopologicalSpace M] [MulAction G M] (U : TopologicalSpace.Opens M)
    [MulAction G U] (V : TopologicalSpace.Opens (Elliptic.FiniteQuotient.Space G M))
    (hcompat : ∀ (g : G) (x : U), ((g • x : U) : M) = g • (x : M))
    (hpre :
      Elliptic.FiniteQuotient.project G M ⁻¹' (V : Set (Elliptic.FiniteQuotient.Space G M)) =
        (U : Set M))
    (x : U) :
    (openQuotientEquiv G U V hcompat hpre).symm (restrictedProject G U V hpre x) =
      Elliptic.FiniteQuotient.project G U x := by
  rw [← openQuotientEquiv_project G U V hcompat hpre x, Equiv.symm_apply_apply]

private theorem Elliptic.LogGauge.subtypeAction_isCancelSMul (G : Type*) [Group G] {M : Type*}
    [TopologicalSpace M] [MulAction G M] (U : TopologicalSpace.Opens M) [MulAction G U]
    (hcompat : ∀ (g : G) (x : U), ((g • x : U) : M) = g • (x : M)) [IsCancelSMul G M] :
    IsCancelSMul G U where
  right_cancel' g h x
    he := by
    apply IsCancelSMul.right_cancel g h (x : M)
    simpa only [hcompat] using congrArg Subtype.val he

private theorem Elliptic.LogGauge.subtypeAction_holomorphic (G : Type*) [Group G] {M : Type*}
    [TopologicalSpace M] [MulAction G M] (U : TopologicalSpace.Opens M) [MulAction G U]
    (hcompat : ∀ (g : G) (x : U), ((g • x : U) : M) = g • (x : M)) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E M]
    (hM :
      ∀ g : G,
        ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (fun x : M => g • x))
    (g : G) :
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (fun x : U => g • x) := by
  intro x
  have hi :
    ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
        (fun y : U => ((g • y : U) : M)) x ↔
      ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (fun y : U => g • y)
        x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  apply hi.mp
  simpa only [hcompat, Function.comp_def] using
    ((hM g).comp contMDiff_subtype_val).contMDiffAt (x := x)

public
theorem
    Elliptic.LogGauge.subtypeAction_continuousConstSMul (G : Type*) [Group G] {M : Type*}
    [TopologicalSpace M] [MulAction G M] (U : TopologicalSpace.Opens M) [MulAction G U]
    (hcompat : ∀ (g : G) (x : U), ((g • x : U) : M) = g • (x : M)) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E M]
    (hM :
      ∀ g : G,
        ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (fun x : M => g • x)) :
    ContinuousConstSMul G U where
  continuous_const_smul g := (subtypeAction_holomorphic G U hcompat hM g).continuous

private theorem
    Elliptic.LogGauge.restrictedProject_isLocalDiffeomorph (G : Type*) [Group G] {M : Type*}
    [TopologicalSpace M] [MulAction G M] (U : TopologicalSpace.Opens M)
    (V : TopologicalSpace.Opens (Elliptic.FiniteQuotient.Space G M))
    (hpre :
      Elliptic.FiniteQuotient.project G M ⁻¹' (V : Set (Elliptic.FiniteQuotient.Space G M)) =
        (U : Set M))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E M]
    (hM :
      ∀ g : G,
        ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (fun x : M => g • x))
    [Finite G] [LocallyCompactSpace M] [T2Space M] [ContinuousConstSMul G M] [IsCancelSMul G M]
    [IsManifold (modelWithCornersSelf ℂ E) ω M] :
    letI := Elliptic.FiniteQuotient.chartedSpace (E := E) G M
    IsLocalDiffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
      (restrictedProject G U V hpre) := by
  let := Elliptic.FiniteQuotient.chartedSpace (E := E) G M
  have hUV : Set.MapsTo (Elliptic.FiniteQuotient.project G M) (U : Set M) (V : Set _) := by
    intro x hx
    change x ∈ Elliptic.FiniteQuotient.project G M ⁻¹' (V : Set _)
    rwa [hpre]
  exact
    isLocalDiffeomorph_restrictOpens (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
      (CoveringQuotient.project_isLocalDiffeomorph
        (Elliptic.FiniteQuotient.project_isQuotientCoveringMap G M) hM)
      U V hUV

private def Elliptic.LogGauge.openQuotientBiholomorph (G : Type*) [Group G] {M : Type*}
    [TopologicalSpace M] [MulAction G M] (U : TopologicalSpace.Opens M) [MulAction G U]
    (V : TopologicalSpace.Opens (Elliptic.FiniteQuotient.Space G M))
    (hcompat : ∀ (g : G) (x : U), ((g • x : U) : M) = g • (x : M))
    (hpre :
      Elliptic.FiniteQuotient.project G M ⁻¹' (V : Set (Elliptic.FiniteQuotient.Space G M)) =
        (U : Set M))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E M]
    (hM :
      ∀ g : G,
        ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (fun x : M => g • x))
    [Finite G] [LocallyCompactSpace M] [T2Space M] [ContinuousConstSMul G M] [IsCancelSMul G M]
    [IsManifold (modelWithCornersSelf ℂ E) ω M] :
    letI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
    letI := subtypeAction_continuousConstSMul G U hcompat hM
    letI := subtypeAction_isCancelSMul G U hcompat
    letI := Elliptic.FiniteQuotient.chartedSpace (E := E) G M
    letI := Elliptic.FiniteQuotient.chartedSpace (E := E) G U
    Diffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
      (Elliptic.FiniteQuotient.Space G U) V ω := by
  letI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let := subtypeAction_continuousConstSMul G U hcompat hM
  let := subtypeAction_isCancelSMul G U hcompat
  let := Elliptic.FiniteQuotient.chartedSpace (E := E) G M
  let := Elliptic.FiniteQuotient.chartedSpace (E := E) G U
  have hr := restrictedProject_isLocalDiffeomorph G U V hpre hM
  refine
    { toEquiv := openQuotientEquiv G U V hcompat hpre
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · apply
      CoveringQuotient.contMDiff_of_comp
        (Elliptic.FiniteQuotient.project_isQuotientCoveringMap G U) (modelWithCornersSelf ℂ E) ω
    exact hr.contMDiff
  · apply
      contMDiff_of_comp_localDiffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
        (modelWithCornersSelf ℂ E) hr (restrictedProject_surjective G U V hpre)
    have he :
      (openQuotientEquiv G U V hcompat hpre).symm ∘ restrictedProject G U V hpre =
        Elliptic.FiniteQuotient.project G U := by
      funext x
      exact openQuotientEquiv_symm_restrictedProject G U V hcompat hpre x
    rw [he]
    exact
      Elliptic.FiniteQuotient.project_holomorphic G U (subtypeAction_holomorphic G U hcompat hM)

private theorem Elliptic.LogGauge.discLocallyCompact : LocallyCompactSpace SpecialPeriods.Disc :=
  SpecialPeriods.unitDisc.isOpen.locallyCompactSpace

attribute [local instance] Elliptic.LogGauge.discLocallyCompact in
private theorem Elliptic.LogGauge.familyStarLocallyCompact : LocallyCompactSpace familyOpen :=
  familyOpen.isOpen.locallyCompactSpace

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
private def Elliptic.LogGauge.StarQuotient {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : j.matrix *ᵥ v = v) : Type :=
  @Elliptic.FiniteQuotient.Space (Elliptic.CyclicGroup j) (FamilyStar D.periods) _
    (starAction D v hv)

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
private instance
    Elliptic.LogGauge.starTopology {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : j.matrix *ᵥ v = v) : TopologicalSpace (StarQuotient D v hv) :=
  inferInstanceAs
    (TopologicalSpace
      (@Elliptic.FiniteQuotient.Space (Elliptic.CyclicGroup j) (FamilyStar D.periods) _
        (starAction D v hv)))

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
private def Elliptic.LogGauge.starProject {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : j.matrix *ᵥ v = v) : FamilyStar D.periods → StarQuotient D v hv :=
  @Elliptic.FiniteQuotient.project (Elliptic.CyclicGroup j) (FamilyStar D.periods) _
    (starAction D v hv)

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
private theorem Elliptic.LogGauge.starProject_surjective {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    Function.Surjective (starProject D v hv) :=
  Quotient.mk_surjective

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
private theorem
    Elliptic.LogGauge.starCoveringMap {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    letI := starAction D v hv
    IsQuotientCoveringMap (starProject D v hv) (Elliptic.CyclicGroup j) := by
  let := starAction D v hv
  let := starAction_continuous D v hv
  let := starAction_free D v hv
  exact
    Elliptic.FiniteQuotient.project_isQuotientCoveringMap (Elliptic.CyclicGroup j)
      (FamilyStar D.periods)

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
@[instance_reducible]
private def Elliptic.LogGauge.starChartedSpace {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    ChartedSpace Elliptic.FamilyModel (StarQuotient D v hv) := by
  let := D.periods.totalChartedSpace
  let := starAction D v hv
  exact CoveringQuotient.chartedSpace (E := Elliptic.FamilyModel) (starCoveringMap D v hv)

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
private theorem Elliptic.LogGauge.starProject_holomorphic {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    letI := D.periods.totalChartedSpace
    letI := starChartedSpace D v hv
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (starProject D v hv) := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := starAction D v hv
  exact
    CoveringQuotient.contMDiff_project (starCoveringMap D v hv) ω (starAction_holomorphic D v hv)

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
private abbrev
    Elliptic.LogGauge.TautologicalStar {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j) :=
  StarQuotient D 0 (Matrix.mulVec_zero j.matrix)

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
private def
    Elliptic.LogGauge.gaugeQuotientEquiv {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : j.matrix *ᵥ v = v) : StarQuotient D v hv ≃ TautologicalStar D :=
  @quotientEquiv (Elliptic.CyclicGroup j) _ (FamilyStar D.periods) (FamilyStar D.periods)
    (starAction D v hv) (starAction D 0 (Matrix.mulVec_zero j.matrix)) (gaugeEquiv D.periods v)
    (gaugeMap_starAction D v hv)

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
private def Elliptic.LogGauge.gaugeQuotientBiholomorph {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    letI := starChartedSpace D v hv
    letI := starChartedSpace D 0 (Matrix.mulVec_zero j.matrix)
    Diffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) (StarQuotient D v hv) (TautologicalStar D)
      ω := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := starChartedSpace D v hv
  let := starChartedSpace D 0 (Matrix.mulVec_zero j.matrix)
  refine
    { toEquiv := gaugeQuotientEquiv D v hv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · let := starAction D v hv
    apply
      CoveringQuotient.contMDiff_of_comp (starCoveringMap D v hv)
        (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω
    exact
      (starProject_holomorphic D 0 (Matrix.mulVec_zero j.matrix)).comp
        (gaugeMap_holomorphic D.periods v)
  · let := starAction D 0 (Matrix.mulVec_zero j.matrix)
    apply
      CoveringQuotient.contMDiff_of_comp (starCoveringMap D 0 (Matrix.mulVec_zero j.matrix))
        (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω
    exact (starProject_holomorphic D v hv).comp (gaugeMap_holomorphic D.periods (-v))

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
private def
    Elliptic.LogGauge.starUpstairsProjection {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (x : FamilyStar D.periods) : BaseStar :=
  ⟨Elliptic.discPower j.order j.order_pos x.1.1,
    by
    change (x.1.1 : ℂ) ^ j.order ≠ 0
    exact pow_ne_zero _ x.2⟩

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
private theorem Elliptic.LogGauge.starUpstairsProjection_invariant {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : Elliptic.CyclicGroup j) (x : FamilyStar D.periods) :
    letI := starAction D v hv
    starUpstairsProjection D (g • x) = starUpstairsProjection D x := by
  let := D.action v hv
  let := starAction D v hv
  apply Subtype.ext
  change
    Elliptic.discPower j.order j.order_pos ((g • x : FamilyStar D.periods) : D.TotalSpace).1 =
      Elliptic.discPower j.order j.order_pos (x : D.TotalSpace).1
  rw [starAction_coe D v hv]
  exact D.action_discPower v hv g x

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
private def Elliptic.LogGauge.starProjection {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : j.matrix *ᵥ v = v) : StarQuotient D v hv → BaseStar := by
  let := starAction D v hv
  exact
    Elliptic.FiniteQuotient.descend (starUpstairsProjection D)
      (starUpstairsProjection_invariant D v hv)

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
private def Elliptic.LogGauge.fillingOpen {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) : TopologicalSpace.Opens (D.Space v hv) :=
  ⟨{x | (D.projection v hv x : ℂ) ≠ 0},
    isOpen_ne_fun (continuous_subtype_val.comp (D.projection_continuous v hv)) continuous_const⟩

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
private abbrev Elliptic.LogGauge.FillingStar {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :=
  fillingOpen D v hv

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
@[simp]
private theorem Elliptic.LogGauge.quotient_preimage_fillingOpen {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    (D.quotient v hv) ⁻¹' (fillingOpen D v hv : Set (D.Space v hv)) =
      (familyOpen : Set D.TotalSpace) := by
  ext x
  change (D.projection v hv (D.quotient v hv x) : ℂ) ≠ 0 ↔ (x.1 : ℂ) ≠ 0
  simp only [D.projection_quotient, Elliptic.discPower_coe, ne_eq,
    pow_eq_zero_iff j.order_pos.ne']

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
private def
    Elliptic.LogGauge.fillingStarProject {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (x : FamilyStar D.periods) :
    FillingStar D v hv :=
  ⟨D.quotient v hv x, by
    change (D.projection v hv (D.quotient v hv x) : ℂ) ≠ 0
    rw [D.projection_quotient, Elliptic.discPower_coe]
    exact pow_ne_zero _ x.2⟩

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
private theorem Elliptic.LogGauge.fillingStarProject_surjective {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    Function.Surjective (fillingStarProject D v hv) := by
  let := D.action v hv.1
  exact
    restrictedProject_surjective (Elliptic.CyclicGroup j) familyOpen (fillingOpen D v hv)
      (quotient_preimage_fillingOpen D v hv)

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
private def
    Elliptic.LogGauge.fillingStarProjection {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (x : FillingStar D v hv) : BaseStar :=
  ⟨D.projection v hv x, x.2⟩

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
private def
    Elliptic.LogGauge.fillingOpenComparison {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    letI := starChartedSpace D v hv.1
    letI := D.chartedSpace v hv
    Diffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) (StarQuotient D v hv.1) (FillingStar D v hv)
      ω := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.action v hv.1
  let := D.action_continuous v hv.1
  let := D.action_free v hv
  let := starAction D v hv.1
  exact
    openQuotientBiholomorph (Elliptic.CyclicGroup j) familyOpen (fillingOpen D v hv)
      (starAction_coe D v hv.1) (quotient_preimage_fillingOpen D v hv)
      (D.action_holomorphic v hv.1)

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
private def Elliptic.LogGauge.fillingToTautologicalBiholomorph {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    letI := D.chartedSpace v hv
    letI := starChartedSpace D 0 (Matrix.mulVec_zero j.matrix)
    Diffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) (FillingStar D v hv) (TautologicalStar D) ω :=
  by
  let := D.chartedSpace v hv
  let := starChartedSpace D v hv.1
  let := starChartedSpace D 0 (Matrix.mulVec_zero j.matrix)
  exact (fillingOpenComparison D v hv).symm.trans (gaugeQuotientBiholomorph D v hv.1)

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
@[simp]
private theorem Elliptic.LogGauge.fillingToTautologicalBiholomorph_project {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (x : FamilyStar D.periods) :
    fillingToTautologicalBiholomorph D v hv (fillingStarProject D v hv x) =
      starProject D 0 (Matrix.mulVec_zero j.matrix) (gaugeMap D.periods v x) :=
  rfl

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
private theorem Elliptic.LogGauge.fillingToTautologicalBiholomorph_base {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (x : FillingStar D v hv) :
    starProjection D 0 (Matrix.mulVec_zero j.matrix) (fillingToTautologicalBiholomorph D v hv x) =
      fillingStarProjection D v hv x := by
  obtain ⟨y, rfl⟩ := fillingStarProject_surjective D v hv x
  rfl

private theorem Elliptic.LogGauge.sectionMap_formula_of_exponential
    (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : Lattice) (z : BaseStar) (s : ℂ)
    (hs : CuspUniformization.exponential s = (z.1 : ℂ)) :
    (sectionMap P v z : P.TotalSpace) = P.quotientMap (z.1, s • periodVector P v z.1) := by
  rw [sectionMap_formula]
  have hlogs : ∃ n : ℤ, CuspUniformization.logarithm (z.1 : ℂ) = s + n :=
    (CuspUniformization.exponential_eq_iff _ _).mp
      ((CuspUniformization.exponential_logarithm z.2).trans hs.symm)
  simpa only [zero_add] using quotientMap_eq_of_scalar_int P v z.1 0 hlogs

private theorem Elliptic.LogGauge.gaugeMap_project_of_exponential
    (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : Lattice) (x : CoverStar) (s : ℂ)
    (hs : CuspUniformization.exponential s = (x.1.1 : ℂ)) :
    (gaugeMap P v (project P x) : P.TotalSpace) =
      P.quotientMap (x.1.1, x.1.2 + s • periodVector P v x.1.1) := by
  rw [gaugeMap_project]
  exact
    quotientMap_eq_of_scalar_int P v x.1.1 x.1.2
      ((CuspUniformization.exponential_eq_iff _ _).mp
        ((CuspUniformization.exponential_logarithm x.2).trans hs.symm))

private def Elliptic.LogGauge.mainFillingToTautologicalBiholomorph {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) :
    letI := D.chartedSpace j.twist (Elliptic.mainTwist_admissible j)
    letI := starChartedSpace D 0 (Matrix.mulVec_zero j.matrix)
    Diffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (FillingStar D j.twist (Elliptic.mainTwist_admissible j)) (TautologicalStar D) ω :=
  fillingToTautologicalBiholomorph D j.twist (Elliptic.mainTwist_admissible j)

private theorem Elliptic.LogGauge.mainFillingToTautologicalBiholomorph_base {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j)
    (x : FillingStar D j.twist (Elliptic.mainTwist_admissible j)) :
    starProjection D 0 (Matrix.mulVec_zero j.matrix) (mainFillingToTautologicalBiholomorph D x) =
      fillingStarProjection D j.twist (Elliptic.mainTwist_admissible j) x :=
  fillingToTautologicalBiholomorph_base D j.twist (Elliptic.mainTwist_admissible j) x

private def
    Elliptic.discRadial (t : unitInterval) (z : SpecialPeriods.Disc) : SpecialPeriods.Disc :=
  ⟨(1 - (t : ℝ)) • (z : ℂ),
    by
    have ha : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.property.2
    have ha1 : 1 - (t : ℝ) ≤ 1 := by linarith [t.property.1]
    have hn : ‖(1 - (t : ℝ)) • (z : ℂ)‖ < 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
      exact
        (mul_le_of_le_one_left (norm_nonneg _) ha1).trans_lt (SpecialPeriods.disc_norm_lt_one z)
    simpa [SpecialPeriods.unitDisc] using hn⟩

private theorem Elliptic.discRadial_continuous :
    Continuous (fun p : unitInterval × SpecialPeriods.Disc => discRadial p.1 p.2) :=
  ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp continuous_snd)).subtype_mk
    _

@[simp]
private theorem Elliptic.discRadial_zero (z : SpecialPeriods.Disc) : discRadial 0 z = z := by
  apply Subtype.ext
  simp [discRadial]

@[simp]
private theorem Elliptic.discRadial_one (z : SpecialPeriods.Disc) : discRadial 1 z = discZero := by
  apply Subtype.ext
  simp [discRadial, discZero]

@[simp]
private theorem
    Elliptic.discRadial_discZero (t : unitInterval) : discRadial t discZero = discZero := by
  apply Subtype.ext
  simp [discRadial, discZero]

private theorem Elliptic.discRadial_familyRotation (j : Kind) (t : unitInterval)
    (z : SpecialPeriods.Disc) :
    discRadial t (familyRotation j z) = familyRotation j (discRadial t z) := by
  cases j <;> apply Subtype.ext
  · change
      (1 - (t : ℝ)) • (-SpecialPeriods.rho * (z : ℂ)) =
        -SpecialPeriods.rho * ((1 - (t : ℝ)) • (z : ℂ))
    simp only [Complex.real_smul]
    ring
  · change (1 - (t : ℝ)) • (-Complex.I * (z : ℂ)) = -Complex.I * ((1 - (t : ℝ)) • (z : ℂ))
    simp only [Complex.real_smul]
    ring

private theorem Elliptic.discRadial_familyRotation_iterate (j : Kind) (t : unitInterval) (n : ℕ)
    (z : SpecialPeriods.Disc) :
    discRadial t ((familyRotation j)^[n] z) = (familyRotation j)^[n] (discRadial t z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', discRadial_familyRotation, ih]

private def Elliptic.familyRadial (j : Kind) (t : unitInterval) (x : Family j) : Family j :=
  (discRadial t x.1, x.2)

private theorem Elliptic.familyRadial_continuous (j : Kind) :
    Continuous (fun p : unitInterval × Family j => familyRadial j p.1 p.2) :=
  (discRadial_continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
    (continuous_snd.comp continuous_snd)

@[simp]
private theorem Elliptic.familyRadial_zero (j : Kind) (x : Family j) : familyRadial j 0 x = x := by
  exact Prod.ext (discRadial_zero x.1) rfl

@[simp]
private theorem Elliptic.familyRadial_one (j : Kind) (x : Family j) :
    familyRadial j 1 x = (discZero, x.2) := by exact Prod.ext (discRadial_one x.1) rfl

private theorem Elliptic.familyRadial_fixed (j : Kind) (t : unitInterval) (x : Family j)
    (hx : x.1 = discZero) : familyRadial j t x = x := by
  exact Prod.ext (by change discRadial t x.1 = x.1; rw [hx, discRadial_discZero]) rfl

private theorem Elliptic.familyRadial_equivariant (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (t : unitInterval) (x : Family j) :
    letI := familyAction j v hv
    familyRadial j t (g • x) = g • familyRadial j t x := by
  let := familyAction j v hv
  rw [familyAction_apply, familyAction_apply]
  exact Prod.ext (discRadial_familyRotation_iterate j t g.toAdd.val x.1) rfl

private def Elliptic.fillingRadial (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (t : unitInterval) : Filling j v hv → Filling j v hv := by
  letI := familyAction j v hv.1
  exact
    FiniteQuotient.descend (fun x => fillingQuotient j v hv (familyRadial j t x))
      (fun g x => by
        rw [familyRadial_equivariant]
        exact FiniteQuotient.project_smul (CyclicGroup j) (Family j) g _)

@[simp]
private theorem
    Elliptic.fillingRadial_fillingQuotient (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (t : unitInterval) (x : Family j) :
    fillingRadial j v hv t (fillingQuotient j v hv x) =
      fillingQuotient j v hv (familyRadial j t x) :=
  rfl

private theorem
    Elliptic.fillingRadial_continuous (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    Continuous (fun p : unitInterval × Filling j v hv => fillingRadial j v hv p.1 p.2) := by
  have hq : Topology.IsQuotientMap (fillingQuotient j v hv) := isQuotientMap_quotient_mk'
  apply hq.continuous_lift_prod_right
  exact (fillingQuotient_continuous j v hv).comp (familyRadial_continuous j)

@[simp]
private theorem Elliptic.fillingRadial_zero (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (x : Filling j v hv) : fillingRadial j v hv 0 x = x := by
  obtain ⟨y, rfl⟩ := fillingQuotient_surjective j v hv x
  rw [fillingRadial_fillingQuotient, familyRadial_zero]

private theorem
    Elliptic.fillingRadial_one_mem_central (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (x : Filling j v hv) : fillingRadial j v hv 1 x ∈ fillingProjection j v hv ⁻¹' { discZero } :=
  by
  obtain ⟨y, rfl⟩ := fillingQuotient_surjective j v hv x
  rw [fillingRadial_fillingQuotient, familyRadial_one]
  exact (discPower_eq_zero_iff j.order j.order_pos discZero).mpr rfl

private theorem Elliptic.fillingRadial_fixed (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (t : unitInterval) (x : Filling j v hv) (hx : fillingProjection j v hv x = discZero) :
    fillingRadial j v hv t x = x := by
  obtain ⟨y, rfl⟩ := fillingQuotient_surjective j v hv x
  change discPower j.order j.order_pos y.1 = discZero at hx
  rw [fillingRadial_fillingQuotient,
    familyRadial_fixed j t y ((discPower_eq_zero_iff j.order j.order_pos y.1).mp hx)]

private def
    Elliptic.fillingCentralSubtypeInclusion (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    ContinuousMap (fillingProjection j v hv ⁻¹' { discZero }) (Filling j v hv) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def Elliptic.fillingCentralRetraction (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    ContinuousMap (Filling j v hv) (fillingProjection j v hv ⁻¹' { discZero }) :=
  ⟨fun x => ⟨fillingRadial j v hv 1 x, fillingRadial_one_mem_central j v hv x⟩,
    ((fillingRadial_continuous j v hv).comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩

private def Elliptic.torusFibreMap (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (z : SpecialPeriods.Disc) : ((familyPeriods j).point z).Torus → Filling j v hv :=
  fillingQuotient j v hv ∘ (familyPeriods j).fibreInclusion z

private theorem
    Elliptic.torusFibreMap_holomorphic (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (z : SpecialPeriods.Disc) :
    ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂) (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      ω (torusFibreMap j v hv z) := by
  let := (familyPeriods j).totalChartedSpace
  exact (fillingQuotient_holomorphic j v hv).comp ((familyPeriods j).fibreInclusion_holomorphic z)

private theorem
    Elliptic.torusFibreMap_continuous (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (z : SpecialPeriods.Disc) : Continuous (torusFibreMap j v hv z) :=
  (torusFibreMap_holomorphic j v hv z).continuous

@[simp]
private theorem Elliptic.fillingProjection_torusFibreMap (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (z : SpecialPeriods.Disc) (x : ((familyPeriods j).point z).Torus) :
    fillingProjection j v hv (torusFibreMap j v hv z x) = discPower j.order j.order_pos z :=
  rfl

private theorem Elliptic.range_torusFibreMap (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (z : SpecialPeriods.Disc) :
    Set.range (torusFibreMap j v hv z) =
      fillingProjection j v hv ⁻¹' {discPower j.order j.order_pos z} := by
  let := familyAction j v hv.1
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact fillingProjection_torusFibreMap j v hv z x
  · intro hq
    obtain ⟨x, rfl⟩ := fillingQuotient_surjective j v hv q
    have hp : discPower j.order j.order_pos x.1 = discPower j.order j.order_pos z := hq
    obtain ⟨r, hr, hrot⟩ := (discPower_eq_iff_familyRotation j z x.1).mp hp.symm
    let g : CyclicGroup j := Multiplicative.ofAdd (r : ZMod j.order)
    have hg : g.toAdd.val = r := ZMod.val_natCast_of_lt hr
    have hbase : (g • x).1 = z := by
      rw [familyAction_apply, hg]
      exact hrot
    have hx : g • x ∈ Set.range ((familyPeriods j).fibreInclusion z) := by
      rw [(familyPeriods j).range_fibreInclusion]
      exact hbase
    obtain ⟨y, hy⟩ := hx
    refine ⟨y, ?_⟩
    change fillingQuotient j v hv ((familyPeriods j).fibreInclusion z y) = _
    rw [hy]
    exact FiniteQuotient.project_smul (CyclicGroup j) (Family j) g x

private theorem Elliptic.fillingProjection_fibre_connected (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (b : SpecialPeriods.Disc) :
    IsConnected (fillingProjection j v hv ⁻¹' { b }) := by
  obtain ⟨z, rfl⟩ := discPower_surjective j.order j.order_pos b
  rw [← range_torusFibreMap j v hv z]
  exact isConnected_range (torusFibreMap_continuous j v hv z)

private def Elliptic.Equivariant.Data.fillingHomeomorph {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    D.Space v hv ≃ₜ Elliptic.Filling j v hv :=
  Homeomorph.refl _

private theorem Elliptic.Equivariant.Data.projection_fibre_isConnected {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (b : SpecialPeriods.Disc) : IsConnected (D.projection v hv ⁻¹' { b }) :=
  Elliptic.fillingProjection_fibre_connected j v hv b

private def
    Elliptic.Equivariant.Data.fillingRadial {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (t : unitInterval) :
    D.Space v hv → D.Space v hv :=
  Elliptic.fillingRadial j v hv t

@[simp]
private theorem Elliptic.Equivariant.Data.fillingRadial_quotient {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (t : unitInterval) (x : D.TotalSpace) :
    D.fillingRadial v hv t (D.quotient v hv x) =
      D.quotient v hv (Elliptic.discRadial t x.1, x.2) :=
  rfl

private theorem Elliptic.Equivariant.Data.fillingRadial_continuous {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    Continuous (fun p : unitInterval × D.Space v hv => D.fillingRadial v hv p.1 p.2) :=
  Elliptic.fillingRadial_continuous j v hv

@[simp]
private theorem Elliptic.Equivariant.Data.fillingRadial_zero {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (x : D.Space v hv) : D.fillingRadial v hv 0 x = x :=
  Elliptic.fillingRadial_zero j v hv x

private theorem Elliptic.Equivariant.Data.fillingRadial_fixed {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (t : unitInterval) (x : D.Space v hv) (hx : D.projection v hv x = Elliptic.discZero) :
    D.fillingRadial v hv t x = x :=
  Elliptic.fillingRadial_fixed j v hv t x hx

private def Elliptic.Equivariant.Data.fillingCentralSubtypeInclusion {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    ContinuousMap (D.projection v hv ⁻¹' { Elliptic.discZero }) (D.Space v hv) :=
  Elliptic.fillingCentralSubtypeInclusion j v hv

private def Elliptic.Equivariant.Data.fillingCentralRetraction {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    ContinuousMap (D.Space v hv) (D.projection v hv ⁻¹' { Elliptic.discZero }) :=
  Elliptic.fillingCentralRetraction j v hv

end Mathoverflow1973

end
