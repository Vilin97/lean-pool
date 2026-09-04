/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Uniformization.SpecialPeriods7
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.PeriodFamily.HolomorphicPeriodMap1
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods1
import all LeanPool.HopfProblem.Elliptic.Core2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods7

/-!
# Hopf problem: elliptic · core 3

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

private structure Elliptic.Equivariant.Data (j : Elliptic.Kind) where
  periods : HolomorphicPeriodMap ℂ SpecialPeriods.Disc
  covariance :
    ∀ z, periods.point (Elliptic.familyRotation j z) = Elliptic.periodStep j (periods.point z)

private abbrev Elliptic.Equivariant.Data.TotalSpace {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) :=
  D.periods.TotalSpace

private def
    Elliptic.Equivariant.Data.permutation {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) : Equiv.Perm D.TotalSpace :=
  Elliptic.familyPermutation j v

@[simp]
private theorem Elliptic.Equivariant.Data.permutation_apply {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (x : D.TotalSpace) :
    D.permutation v x = (Elliptic.familyRotation j x.1, Elliptic.flatTorusAffine j v x.2) :=
  rfl

private theorem Elliptic.Equivariant.Data.permutation_pow_order {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    D.permutation v ^ j.order = 1 :=
  Elliptic.familyPermutation_pow_order j v hv

@[instance_reducible]
private def Elliptic.Equivariant.Data.action {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : j.matrix *ᵥ v = v) : MulAction (Elliptic.CyclicGroup j) D.TotalSpace :=
  Elliptic.familyAction j v hv

private theorem Elliptic.Equivariant.Data.action_apply {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : Elliptic.CyclicGroup j) (x : D.TotalSpace) :
    letI := D.action v hv
    g • x =
      ((Elliptic.familyRotation j)^[g.toAdd.val] x.1,
        (Elliptic.flatTorusAffine j v)^[g.toAdd.val] x.2) :=
  Elliptic.familyAction_apply j v hv g x

private theorem Elliptic.Equivariant.Data.action_free {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    letI := D.action v hv.1
    IsCancelSMul (Elliptic.CyclicGroup j) D.TotalSpace :=
  Elliptic.familyAction_free j v hv

private theorem Elliptic.Equivariant.Data.action_continuous {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    letI := D.action v hv
    ContinuousConstSMul (Elliptic.CyclicGroup j) D.TotalSpace :=
  Elliptic.familyAction_continuous j v hv

private theorem Elliptic.Equivariant.Data.action_discPower {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : Elliptic.CyclicGroup j) (x : D.TotalSpace) :
    letI := D.action v hv
    Elliptic.discPower j.order j.order_pos (g • x).1 =
      Elliptic.discPower j.order j.order_pos x.1 :=
  Elliptic.familyAction_discPower j v hv g x

private def Elliptic.Equivariant.Data.centralPeriod {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) : Elliptic.FixedPeriod j :=
  ⟨D.periods.point SpecialPeriods.discZero,
    (D.covariance SpecialPeriods.discZero).symm.trans
      (congrArg D.periods.point (Elliptic.familyRotation_zero j))⟩

private theorem Elliptic.Equivariant.Data.periodEquiv_matrix {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (z : SpecialPeriods.Disc) (x : Elliptic.RealCoordinates) :
    D.periods.periodEquiv z x = (D.periods.point z).val.matrix *ᵥ (fun i => (x i : ℂ)) := by
  rw [HolomorphicPeriodMap.periodEquiv_coordinates]
  ext i
  fin_cases i <;> simp [PeriodPoint.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

private theorem Elliptic.Equivariant.Data.periodEquiv_eq_periodEquiv {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (z : SpecialPeriods.Disc) (x : Elliptic.RealCoordinates) :
    D.periods.periodEquiv z x = Elliptic.periodEquiv (D.periods.point z) x := by
  rw [D.periodEquiv_matrix, Elliptic.periodEquiv_matrix]

private theorem Elliptic.Equivariant.Data.matrix_covariance {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (z : SpecialPeriods.Disc) :
    (D.periods.point (Elliptic.familyRotation j z)).val.matrix *
        j.matrix.map (Int.castRingHom ℂ) =
      Elliptic.linearMatrix j (D.periods.point z) * (D.periods.point z).val.matrix := by
  rw [D.covariance z]
  cases j
  · change
      (D.periods.point z).val.step₁.matrix * A₁.map (Int.castRingHom ℂ) =
        (D.periods.point z).val.R₁ * (D.periods.point z).val.matrix
    rw [PeriodPoint.step₁_matrix _
        ((D.periods.point z).val.τ_ne_zero (D.periods.point z).property.1),
      Matrix.mul_assoc]
    have h : (T₁.map (Int.castRingHom ℂ)).transpose * A₁.map (Int.castRingHom ℂ) = 1 := by
      change T₁.transpose.map (Int.castRingHom ℂ) * A₁.map (Int.castRingHom ℂ) = 1
      rw [← Matrix.map_mul, show T₁.transpose * A₁ = 1 by decide]
      simp
    rw [h, Matrix.mul_one]
  · change
      (D.periods.point z).val.step₂.matrix * A₂.map (Int.castRingHom ℂ) =
        (D.periods.point z).val.R₂ * (D.periods.point z).val.matrix
    rw [PeriodPoint.step₂_matrix _
        ((D.periods.point z).val.τ_ne_zero (D.periods.point z).property.1),
      Matrix.mul_assoc]
    have h : (T₂.map (Int.castRingHom ℂ)).transpose * A₂.map (Int.castRingHom ℂ) = 1 := by
      change T₂.transpose.map (Int.castRingHom ℂ) * A₂.map (Int.castRingHom ℂ) = 1
      rw [← Matrix.map_mul, show T₂.transpose * A₂ = 1 by decide]
      simp
    rw [h, Matrix.mul_one]

private theorem Elliptic.Equivariant.Data.periodEquiv_flatLinear {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (z : SpecialPeriods.Disc) (x : Elliptic.RealCoordinates) :
    D.periods.periodEquiv (Elliptic.familyRotation j z) (Elliptic.flatLinear j x) =
      Elliptic.linearMatrix j (D.periods.point z) *ᵥ D.periods.periodEquiv z x := by
  rw [D.periodEquiv_matrix, Elliptic.flatLinear_complexCast, Matrix.mulVec_mulVec,
    D.periodEquiv_matrix, Matrix.mulVec_mulVec, D.matrix_covariance]

private theorem Elliptic.Equivariant.Data.periodEquiv_symm_linearMatrix {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (z : SpecialPeriods.Disc) (w : ComplexPlane₂) :
    (D.periods.periodEquiv (Elliptic.familyRotation j z)).symm
        (Elliptic.linearMatrix j (D.periods.point z) *ᵥ w) =
      Elliptic.flatLinear j ((D.periods.periodEquiv z).symm w) := by
  apply (D.periods.periodEquiv (Elliptic.familyRotation j z)).injective
  rw [LinearEquiv.apply_symm_apply, D.periodEquiv_flatLinear, LinearEquiv.apply_symm_apply]

@[instance_reducible]
private def Elliptic.Equivariant.Data.equivariantCoveringChartedSpace :
    ChartedSpace Elliptic.FamilyModel (SpecialPeriods.Disc × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (SpecialPeriods.Disc × ComplexPlane₂))

attribute [local instance] Elliptic.Equivariant.Data.equivariantCoveringChartedSpace in
private theorem Elliptic.Equivariant.Data.equivariantCoveringManifold :
    IsManifold (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω
      (SpecialPeriods.Disc × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact
    IsManifold.prod (I := modelWithCornersSelf ℂ ℂ) (I' := modelWithCornersSelf ℂ ComplexPlane₂)
      SpecialPeriods.Disc ComplexPlane₂

attribute [local instance] Elliptic.Equivariant.Data.equivariantCoveringChartedSpace
    Elliptic.Equivariant.Data.equivariantCoveringManifold in
private def
    Elliptic.Equivariant.Data.complexLift {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (x : SpecialPeriods.Disc × ComplexPlane₂) :
    SpecialPeriods.Disc × ComplexPlane₂ :=
  (Elliptic.familyRotation j x.1,
    Elliptic.linearMatrix j (D.periods.point x.1) *ᵥ x.2 +
      D.periods.periodEquiv (Elliptic.familyRotation j x.1)
        ((1 / (j.order : ℝ)) • Elliptic.realCast v))

attribute [local instance] Elliptic.Equivariant.Data.equivariantCoveringChartedSpace
    Elliptic.Equivariant.Data.equivariantCoveringManifold in
private theorem Elliptic.Equivariant.Data.complexLift_quotientMap {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (x : SpecialPeriods.Disc × ComplexPlane₂) :
    D.periods.quotientMap (D.complexLift v x) = D.permutation v (D.periods.quotientMap x) := by
  change
    (Elliptic.familyRotation j x.1,
        standardLattice.mkQ
          ((D.periods.periodEquiv (Elliptic.familyRotation j x.1)).symm
            (Elliptic.linearMatrix j (D.periods.point x.1) *ᵥ x.2 +
              D.periods.periodEquiv (Elliptic.familyRotation j x.1)
                ((1 / (j.order : ℝ)) • Elliptic.realCast v)))) =
      (Elliptic.familyRotation j x.1,
        Elliptic.flatTorusAffine j v (standardLattice.mkQ ((D.periods.periodEquiv x.1).symm x.2)))
  rw [Elliptic.flatTorusAffine_mkQ, map_add, LinearEquiv.symm_apply_apply,
    D.periodEquiv_symm_linearMatrix]
  rfl

attribute [local instance] Elliptic.Equivariant.Data.equivariantCoveringChartedSpace
    Elliptic.Equivariant.Data.equivariantCoveringManifold in
private theorem Elliptic.Equivariant.Data.linearLift_holomorphic {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) :
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel) (modelWithCornersSelf ℂ ComplexPlane₂)
      ω
      (fun x : SpecialPeriods.Disc × ComplexPlane₂ =>
        Elliptic.linearMatrix j (D.periods.point x.1) *ᵥ x.2) := by
  have hf :
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel) (modelWithCornersSelf ℂ ℂ) ω
      (Prod.fst : SpecialPeriods.Disc × ComplexPlane₂ → SpecialPeriods.Disc) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst
  have hs :
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel) (modelWithCornersSelf ℂ ComplexPlane₂)
      ω (Prod.snd : SpecialPeriods.Disc × ComplexPlane₂ → ComplexPlane₂) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_snd
  have hτ := D.periods.holomorphic_tau.comp hf
  have hμ := D.periods.holomorphic_mu.comp hf
  have hτ0 : ∀ x : SpecialPeriods.Disc × ComplexPlane₂, (D.periods.point x.1).val.τ ≠ 0 :=
    fun x => (D.periods.point x.1).val.τ_ne_zero (D.periods.point x.1).property.1
  have h₀ := (contMDiff_pi_space.mp hs) 0
  have h₁ := (contMDiff_pi_space.mp hs) 1
  cases j
  · apply contMDiff_pi_space.mpr
    intro i
    fin_cases i
    · convert (((contMDiff_const (c := (-1 : ℂ))).div₀ hτ hτ0).mul h₀) using 1
      funext x
      simp [Elliptic.linearMatrix, PeriodPoint.R₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Function.comp_def]
    · convert (((((contMDiff_const (c := (1 : ℂ))).sub hμ).div₀ hτ hτ0).mul h₀).add h₁) using 1
      funext x
      simp [Elliptic.linearMatrix, PeriodPoint.R₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Function.comp_def]
  · apply contMDiff_pi_space.mpr
    intro i
    fin_cases i
    · convert (((contMDiff_const (c := (1 : ℂ))).div₀ hτ hτ0).mul h₀) using 1
      funext x
      simp [Elliptic.linearMatrix, PeriodPoint.R₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Function.comp_def]
    · convert (((hμ.neg.div₀ hτ hτ0).mul h₀).add h₁) using 1
      funext x
      simp [Elliptic.linearMatrix, PeriodPoint.R₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Function.comp_def]

attribute [local instance] Elliptic.Equivariant.Data.equivariantCoveringChartedSpace
    Elliptic.Equivariant.Data.equivariantCoveringManifold in
private theorem Elliptic.Equivariant.Data.complexLift_holomorphic {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) :
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (D.complexLift v) := by
  have hf :
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel) (modelWithCornersSelf ℂ ℂ) ω
      (fun x : SpecialPeriods.Disc × ComplexPlane₂ => Elliptic.familyRotation j x.1) := by
    rw [modelWithCornersSelf_prod]
    exact (Elliptic.familyRotation j).contMDiff_toFun.comp contMDiff_fst
  have hw :=
    D.linearLift_holomorphic.add
      ((D.periods.holomorphic_periodEquiv_const ((1 / (j.order : ℝ)) • Elliptic.realCast v)).comp
        hf)
  rw [modelWithCornersSelf_prod] at hf hw ⊢
  exact hf.prodMk hw

attribute [local instance] Elliptic.Equivariant.Data.equivariantCoveringChartedSpace
    Elliptic.Equivariant.Data.equivariantCoveringManifold in
private theorem Elliptic.Equivariant.Data.permutation_holomorphic {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) :
    letI := D.periods.totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (D.permutation v) := by
  let := D.periods.coveringAction
  let := D.periods.totalChartedSpace
  apply
    CoveringQuotient.contMDiff_of_comp (E := Elliptic.FamilyModel) D.periods.quotientCoveringMap
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω
  have h := D.periods.quotientMap_holomorphic.comp (D.complexLift_holomorphic v)
  convert! h using 1
  funext x
  exact (D.complexLift_quotientMap v x).symm

attribute [local instance] Elliptic.Equivariant.Data.equivariantCoveringChartedSpace
    Elliptic.Equivariant.Data.equivariantCoveringManifold in
private theorem Elliptic.Equivariant.Data.action_holomorphic {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : Elliptic.CyclicGroup j) :
    letI := D.periods.totalChartedSpace
    letI := D.action v hv
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (fun x : D.TotalSpace => g • x) := by
  let := D.periods.totalChartedSpace
  exact
    Elliptic.CyclicAction.smul_contMDiff (D.permutation v) (D.permutation_pow_order v hv)
      (D.permutation_holomorphic v) g

public
theorem
    Elliptic.Equivariant.Data.discLocallyCompact : LocallyCompactSpace SpecialPeriods.Disc :=
  SpecialPeriods.unitDisc.isOpen.locallyCompactSpace

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
private def Elliptic.Equivariant.Data.upstairsProjection {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (x : D.TotalSpace) : SpecialPeriods.Disc :=
  Elliptic.discPower j.order j.order_pos x.1

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
private theorem Elliptic.Equivariant.Data.upstairsProjection_surjective {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) : Function.Surjective D.upstairsProjection :=
  (Elliptic.discPower_surjective j.order j.order_pos).comp D.periods.projection_surjective

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
private theorem Elliptic.Equivariant.Data.upstairsProjection_proper {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) : IsProperMap D.upstairsProjection :=
  (Elliptic.discPower_isProperMap j.order j.order_pos).comp D.periods.projection_proper

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
private theorem Elliptic.Equivariant.Data.upstairsProjection_invariant {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : Elliptic.CyclicGroup j) (x : D.TotalSpace) :
    letI := D.action v hv
    D.upstairsProjection (g • x) = D.upstairsProjection x :=
  D.action_discPower v hv g x

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
private def Elliptic.Equivariant.Data.Space {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) : Type :=
  @Elliptic.FiniteQuotient.Space (Elliptic.CyclicGroup j) D.TotalSpace _ (D.action v hv.1)

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
private instance Elliptic.Equivariant.Data.spaceTopology {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    TopologicalSpace (D.Space v hv) :=
  inferInstanceAs
    (TopologicalSpace
      (@Elliptic.FiniteQuotient.Space (Elliptic.CyclicGroup j) D.TotalSpace _ (D.action v hv.1)))

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
private def Elliptic.Equivariant.Data.quotient {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) : D.TotalSpace → D.Space v hv :=
  @Elliptic.FiniteQuotient.project (Elliptic.CyclicGroup j) D.TotalSpace _ (D.action v hv.1)

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
private theorem Elliptic.Equivariant.Data.quotient_surjective {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    Function.Surjective (D.quotient v hv) :=
  Quotient.mk_surjective

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
private theorem Elliptic.Equivariant.Data.quotient_continuous {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    Continuous (D.quotient v hv) := by
  let := D.action v hv.1
  exact Elliptic.FiniteQuotient.project_continuous (Elliptic.CyclicGroup j) D.TotalSpace

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
private theorem Elliptic.Equivariant.Data.quotient_eq_iff_mem_orbit {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (x y : D.TotalSpace) :
    letI := D.action v hv.1
    D.quotient v hv x = D.quotient v hv y ↔ x ∈ MulAction.orbit (Elliptic.CyclicGroup j) y := by
  let := D.action v hv.1
  exact Elliptic.FiniteQuotient.project_eq_iff_mem_orbit (Elliptic.CyclicGroup j) D.TotalSpace x y

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
@[simp]
private theorem Elliptic.Equivariant.Data.quotient_smul {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (g : Elliptic.CyclicGroup j) (x : D.TotalSpace) :
    letI := D.action v hv.1
    D.quotient v hv (g • x) = D.quotient v hv x := by
  let := D.action v hv.1
  exact Elliptic.FiniteQuotient.project_smul (Elliptic.CyclicGroup j) D.TotalSpace g x

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
private instance
    Elliptic.Equivariant.Data.spaceT2 {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) : T2Space (D.Space v hv) := by
  let := D.action v hv.1
  let := D.action_continuous v hv.1
  exact Elliptic.FiniteQuotient.spaceT2Space (Elliptic.CyclicGroup j) D.TotalSpace

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
private instance Elliptic.Equivariant.Data.spaceSecondCountable {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    SecondCountableTopology (D.Space v hv) := by
  let := D.action v hv.1
  let := D.action_continuous v hv.1
  exact Elliptic.FiniteQuotient.spaceSecondCountableTopology (Elliptic.CyclicGroup j) D.TotalSpace

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
private theorem Elliptic.Equivariant.Data.quotientCoveringMap {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    letI := D.action v hv.1
    IsQuotientCoveringMap (D.quotient v hv) (Elliptic.CyclicGroup j) := by
  let := D.action v hv.1
  let := D.action_continuous v hv.1
  let := D.action_free v hv
  exact
    Elliptic.FiniteQuotient.project_isQuotientCoveringMap (Elliptic.CyclicGroup j) D.TotalSpace

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
private theorem Elliptic.Equivariant.Data.quotient_isCoveringMap {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    IsCoveringMap (D.quotient v hv) := by
  let := D.action v hv.1
  exact (D.quotientCoveringMap v hv).isCoveringMap

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
@[instance_reducible]
private def
    Elliptic.Equivariant.Data.chartedSpace {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    ChartedSpace Elliptic.FamilyModel (D.Space v hv) := by
  let := D.periods.totalChartedSpace
  let := D.action v hv.1
  exact CoveringQuotient.chartedSpace (E := Elliptic.FamilyModel) (D.quotientCoveringMap v hv)

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
private theorem
    Elliptic.Equivariant.Data.isManifold {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    letI := D.chartedSpace v hv
    IsManifold (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (D.Space v hv) := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.action v hv.1
  exact CoveringQuotient.isManifold (D.quotientCoveringMap v hv) ω (D.action_holomorphic v hv.1)

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
private theorem Elliptic.Equivariant.Data.quotient_holomorphic {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace v hv
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (D.quotient v hv) := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.action v hv.1
  exact
    CoveringQuotient.contMDiff_project (D.quotientCoveringMap v hv) ω
      (D.action_holomorphic v hv.1)

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
private theorem Elliptic.Equivariant.Data.quotient_fibre_card {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (y : D.Space v hv) : Nat.card (D.quotient v hv ⁻¹' { y }) = j.order := by
  let := D.action v hv.1
  let := D.action_continuous v hv.1
  let := D.action_free v hv
  calc
    _ = Nat.card (Elliptic.CyclicGroup j) :=
      Elliptic.FiniteQuotient.fibre_card (Elliptic.CyclicGroup j) D.TotalSpace y
    _ = j.order := by simp [Elliptic.CyclicGroup, Nat.card_eq_fintype_card, ZMod.card]

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
private def
    Elliptic.Equivariant.Data.projection {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) : D.Space v hv → SpecialPeriods.Disc := by
  let := D.action v hv.1
  exact
    Elliptic.FiniteQuotient.descend D.upstairsProjection (D.upstairsProjection_invariant v hv.1)

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
@[simp]
private theorem Elliptic.Equivariant.Data.projection_quotient {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (x : D.TotalSpace) :
    D.projection v hv (D.quotient v hv x) = Elliptic.discPower j.order j.order_pos x.1 :=
  rfl

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
private theorem Elliptic.Equivariant.Data.projection_surjective {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    Function.Surjective (D.projection v hv) := by
  let := D.action v hv.1
  exact
    Elliptic.FiniteQuotient.descend_surjective D.upstairsProjection
      (D.upstairsProjection_invariant v hv.1) D.upstairsProjection_surjective

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
private theorem Elliptic.Equivariant.Data.projection_proper {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    IsProperMap (D.projection v hv) := by
  let := D.action v hv.1
  exact
    Elliptic.FiniteQuotient.descend_isProperMap D.upstairsProjection
      (D.upstairsProjection_invariant v hv.1) D.upstairsProjection_proper

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
private theorem Elliptic.Equivariant.Data.projection_continuous {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    Continuous (D.projection v hv) :=
  (D.projection_proper v hv).continuous

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
private theorem Elliptic.Equivariant.Data.projection_central_fibre {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    D.projection v hv ⁻¹' { Elliptic.discZero } =
      D.quotient v hv '' {x : D.TotalSpace | x.1 = Elliptic.discZero} := by
  let := D.action v hv.1
  change
    Elliptic.FiniteQuotient.descend D.upstairsProjection
          (D.upstairsProjection_invariant v hv.1) ⁻¹'
        { Elliptic.discZero } =
      _
  rw [Elliptic.FiniteQuotient.descend_preimage_eq_image]
  congr 1
  ext x
  exact Elliptic.discPower_eq_zero_iff j.order j.order_pos x.1

end Mathoverflow1973

end
