/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.HomologyTheory.FirstHurewicz3
public import LeanPool.HopfProblem.Recognition.Smale2
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz3
import all LeanPool.HopfProblem.Recognition.Smale2

/-!
# Hopf problem: period family · period domain

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

/-- The type of four integral period vectors. -/
public
abbrev FullPeriodMatrix.IntegerPeriods :=
  (Fin 2 → ℤ) × (Fin 2 → ℤ)

/-- The integral period vector selected by an index. -/
public
def FullPeriodMatrix.periodVector (p : FullPeriodMatrix) : IntegerPeriods →+ ComplexPlane₂
    where
  toFun c := (fun i => (c.1 i : ℂ)) + p.matrix *ᵥ (fun i => (c.2 i : ℂ))
  map_zero' := by ext i; fin_cases i <;> simp []
  map_add' c
    d := by
    ext i
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Int.cast_add, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
    ring

private theorem FullPeriodMatrix.periodVector_eq_periodLinear (p : FullPeriodMatrix)
    (c : IntegerPeriods) :
    p.periodVector c = p.periodLinear ((fun i => (c.1 i : ℝ)), (fun i => (c.2 i : ℝ))) := by
  ext i
  fin_cases i <;> simp [periodVector, periodLinear, Matrix.vecHead, Matrix.vecTail]

public
theorem FullPeriodMatrix.periodVector_injective (p : FullPeriodMatrix) :
    Function.Injective p.periodVector := by
  intro c d h
  rw [p.periodVector_eq_periodLinear, p.periodVector_eq_periodLinear] at h
  have he := p.periodLinear_bijective.1 h
  apply Prod.ext
  · ext i
    have hi : (c.1 i : ℝ) = (d.1 i : ℝ) := congrFun (congrArg Prod.fst he) i
    exact_mod_cast hi
  · ext i
    have hi : (c.2 i : ℝ) = (d.2 i : ℝ) := congrFun (congrArg Prod.snd he) i
    exact_mod_cast hi

private theorem
    FullPeriodMatrix.periodVector_mem_lattice (p : FullPeriodMatrix) (c : IntegerPeriods) :
    p.periodVector c ∈ p.lattice :=
  (p.mem_lattice_iff _).mpr ⟨c.1, c.2, rfl⟩

private def
    FullPeriodMatrix.periodLatticeMap (p : FullPeriodMatrix) : IntegerPeriods →+ p.lattice :=
  p.periodVector.codRestrict p.lattice.toAddSubgroup p.periodVector_mem_lattice

private theorem FullPeriodMatrix.periodLatticeMap_bijective (p : FullPeriodMatrix) :
    Function.Bijective p.periodLatticeMap := by
  constructor
  · intro c d h
    exact p.periodVector_injective (congrArg Subtype.val h)
  · intro z
    obtain ⟨m, n, hmn⟩ := (p.mem_lattice_iff z).mp z.property
    exact ⟨(m, n), Subtype.ext hmn.symm⟩

private def
    FullPeriodMatrix.periodLatticeEquiv (p : FullPeriodMatrix) : IntegerPeriods ≃+ p.lattice :=
  AddEquiv.ofBijective p.periodLatticeMap p.periodLatticeMap_bijective

private def FullPeriodMatrix.latticeEquiv (p : FullPeriodMatrix) : p.lattice ≃+ IntegerPeriods :=
  p.periodLatticeEquiv.symm

private theorem FullPeriodMatrix.periodVector_latticeEquiv (p : FullPeriodMatrix) (z : p.lattice) :
    p.periodVector (p.latticeEquiv z) = z :=
  congrArg Subtype.val (p.periodLatticeEquiv.apply_symm_apply z)

private theorem FullPeriodMatrix.quotientCovering (p : FullPeriodMatrix) :
    IsAddQuotientCoveringMap p.lattice.mkQ p.lattice.toAddSubgroup := by
  apply p.lattice.toAddSubgroup.isAddQuotientCoveringMap_of_comm
  change IsDiscrete (p.lattice : Set ComplexPlane₂)
  let : DiscreteTopology (p.lattice : Set ComplexPlane₂) := p.lattice_discrete
  exact DiscreteTopology.isDiscrete

private def
    FullPeriodMatrix.zeroLift (p : FullPeriodMatrix) : p.lattice.mkQ ⁻¹' ({0} : Set p.Torus) :=
  ⟨0, by simp⟩

private def FullPeriodMatrix.fundamentalGroupEquiv (p : FullPeriodMatrix) :
    FundamentalGroup p.Torus 0 ≃* Multiplicative IntegerPeriods :=
  ((p.quotientCovering.fundamentalGroupEquiv p.zeroLift).trans MulOpposite.opMulEquiv.symm).trans
    p.latticeEquiv.toMultiplicative

private theorem FullPeriodMatrix.fundamentalGroupEquiv_monodromy (p : FullPeriodMatrix)
    (γ : FundamentalGroup p.Torus 0) :
    p.periodVector (p.fundamentalGroupEquiv γ).toAdd =
      (p.quotientCovering.isCoveringMap.monodromy γ p.zeroLift : ComplexPlane₂) := by
  have h := p.quotientCovering.unop_fundamentalGroupToMulOpposite_smul (e := p.zeroLift) (γ := γ)
  change
    p.periodVector
        (p.latticeEquiv
          (p.quotientCovering.fundamentalGroupToMulOpposite p.zeroLift γ).unop.toAdd) =
      _
  rw [p.periodVector_latticeEquiv]
  change
    ((p.quotientCovering.fundamentalGroupToMulOpposite p.zeroLift γ).unop.toAdd : ComplexPlane₂) +
        0 =
      _ at h
  simpa only [add_zero] using h

private theorem FullPeriodMatrix.mkQ_periodVector (p : FullPeriodMatrix) (c : IntegerPeriods) :
    p.lattice.mkQ (p.periodVector c) = 0 :=
  (Submodule.Quotient.mk_eq_zero p.lattice).mpr (p.periodVector_mem_lattice c)

private def FullPeriodMatrix.periodLoop (p : FullPeriodMatrix) (c : IntegerPeriods) :
    Path (0 : p.Torus) 0 :=
  ((Path.segment (0 : ComplexPlane₂) (p.periodVector c)).map p.lattice.continuous_mkQ).cast
    (map_zero p.lattice.mkQ).symm (p.mkQ_periodVector c).symm

private theorem FullPeriodMatrix.periodLoop_apply (p : FullPeriodMatrix) (c : IntegerPeriods)
    (t : unitInterval) : p.periodLoop c t = p.lattice.mkQ ((t : ℝ) • p.periodVector c) := by
  simp only [periodLoop, Path.cast_coe, Path.map_coe, Function.comp_apply, Path.segment_apply,
    AffineMap.lineMap_apply_module, smul_zero, zero_add]

private theorem FullPeriodMatrix.periodLoop_monodromy (p : FullPeriodMatrix) (c : IntegerPeriods) :
    p.quotientCovering.isCoveringMap.monodromy (FundamentalGroup.fromPath ⟦p.periodLoop c⟧)
        p.zeroLift =
      ⟨p.periodVector c, p.mkQ_periodVector c⟩ := by
  apply
    p.quotientCovering.isCoveringMap.monodromy_eq_of_map_eq
      (Path.Homotopic.Quotient.mk (Path.segment (0 : ComplexPlane₂) (p.periodVector c)))
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

private theorem FullPeriodMatrix.fundamentalGroupEquiv_periodLoop (p : FullPeriodMatrix)
    (c : IntegerPeriods) :
    p.fundamentalGroupEquiv (FundamentalGroup.fromPath ⟦p.periodLoop c⟧) =
      Multiplicative.ofAdd c := by
  apply Multiplicative.toAdd.injective
  apply p.periodVector_injective
  rw [p.fundamentalGroupEquiv_monodromy, p.periodLoop_monodromy]
  rfl

private def PeriodDomain.periodVector (p : PeriodDomain) : Lattice →+ ComplexPlane₂
    where
  toFun c := p.val.matrix *ᵥ (fun i => (c i : ℂ))
  map_zero' := by
    simp only [Pi.zero_apply, Int.cast_zero]
    exact Matrix.mulVec_zero _
  map_add' c
    d := by
    simp only [Pi.add_apply, Int.cast_add]
    exact Matrix.mulVec_add _ _ _

@[simp]
private theorem PeriodDomain.periodVector_apply (p : PeriodDomain) (c : Lattice) :
    p.periodVector c = p.val.matrix *ᵥ (fun i => (c i : ℂ)) :=
  rfl

private theorem PeriodDomain.periodVector_eq_sum (p : PeriodDomain) (c : Lattice) :
    p.periodVector c = ∑ i, c i • p.basis i := by
  ext j
  simp [periodVector, Matrix.mulVec, dotProduct, p.basis_apply, zsmul_eq_mul, mul_comm]

private theorem PeriodDomain.periodVector_injective (p : PeriodDomain) :
    Function.Injective p.periodVector := by
  intro c d h
  have hi : LinearIndependent ℤ p.basis := p.basis.linearIndependent.restrict_scalars' ℤ
  apply funext
  apply (Fintype.linearIndependent_iffₛ.mp hi) c d
  rw [← p.periodVector_eq_sum, ← p.periodVector_eq_sum]
  exact h

private theorem PeriodDomain.mem_lattice_iff (p : PeriodDomain) (z : ComplexPlane₂) :
    z ∈ p.lattice ↔ ∃ c : Lattice, p.periodVector c = z := by
  rw [p.lattice_eq_span_basis, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, (p.periodVector_eq_sum c).trans hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, (p.periodVector_eq_sum c).symm.trans hc⟩

private theorem PeriodDomain.periodVector_mem_lattice (p : PeriodDomain) (c : Lattice) :
    p.periodVector c ∈ p.lattice :=
  (p.mem_lattice_iff _).mpr ⟨c, rfl⟩

private def PeriodDomain.periodLatticeMap (p : PeriodDomain) : Lattice →+ p.lattice :=
  p.periodVector.codRestrict p.lattice.toAddSubgroup p.periodVector_mem_lattice

private theorem PeriodDomain.periodLatticeMap_bijective (p : PeriodDomain) :
    Function.Bijective p.periodLatticeMap := by
  constructor
  · intro c d h
    exact p.periodVector_injective (congrArg Subtype.val h)
  · intro z
    obtain ⟨c, hc⟩ := (p.mem_lattice_iff z).mp z.property
    exact ⟨c, Subtype.ext hc⟩

private def PeriodDomain.periodLatticeEquiv (p : PeriodDomain) : Lattice ≃+ p.lattice :=
  AddEquiv.ofBijective p.periodLatticeMap p.periodLatticeMap_bijective

private def PeriodDomain.latticeEquiv (p : PeriodDomain) : p.lattice ≃+ Lattice :=
  p.periodLatticeEquiv.symm

private theorem PeriodDomain.periodVector_latticeEquiv (p : PeriodDomain) (z : p.lattice) :
    p.periodVector (p.latticeEquiv z) = z :=
  congrArg Subtype.val (p.periodLatticeEquiv.apply_symm_apply z)

private theorem PeriodDomain.quotientCovering (p : PeriodDomain) :
    IsAddQuotientCoveringMap p.lattice.mkQ p.lattice.toAddSubgroup := by
  apply p.lattice.toAddSubgroup.isAddQuotientCoveringMap_of_comm
  change IsDiscrete (p.lattice : Set ComplexPlane₂)
  let : DiscreteTopology (p.lattice : Set ComplexPlane₂) := p.lattice_discrete
  exact DiscreteTopology.isDiscrete

private def PeriodDomain.zeroLift (p : PeriodDomain) : p.lattice.mkQ ⁻¹' ({0} : Set p.Torus) :=
  ⟨0, by simp⟩

private def PeriodDomain.fundamentalGroupEquiv (p : PeriodDomain) :
    FundamentalGroup p.Torus 0 ≃* Multiplicative Lattice :=
  ((p.quotientCovering.fundamentalGroupEquiv p.zeroLift).trans MulOpposite.opMulEquiv.symm).trans
    p.latticeEquiv.toMultiplicative

private theorem PeriodDomain.fundamentalGroupEquiv_monodromy (p : PeriodDomain)
    (g : FundamentalGroup p.Torus 0) :
    p.periodVector (p.fundamentalGroupEquiv g).toAdd =
      (p.quotientCovering.isCoveringMap.monodromy g p.zeroLift : ComplexPlane₂) := by
  have h := p.quotientCovering.unop_fundamentalGroupToMulOpposite_smul (e := p.zeroLift) (γ := g)
  change
    p.periodVector
        (p.latticeEquiv
          (p.quotientCovering.fundamentalGroupToMulOpposite p.zeroLift g).unop.toAdd) =
      _
  rw [p.periodVector_latticeEquiv]
  change
    ((p.quotientCovering.fundamentalGroupToMulOpposite p.zeroLift g).unop.toAdd : ComplexPlane₂) +
        0 =
      _ at h
  simpa only [add_zero] using h

private theorem PeriodDomain.mkQ_periodVector (p : PeriodDomain) (c : Lattice) :
    p.lattice.mkQ (p.periodVector c) = 0 :=
  (Submodule.Quotient.mk_eq_zero p.lattice).mpr (p.periodVector_mem_lattice c)

private def PeriodDomain.periodLoop (p : PeriodDomain) (c : Lattice) : Path (0 : p.Torus) 0 :=
  ((Path.segment (0 : ComplexPlane₂) (p.periodVector c)).map p.lattice.continuous_mkQ).cast
    (map_zero p.lattice.mkQ).symm (p.mkQ_periodVector c).symm

private theorem PeriodDomain.periodLoop_apply (p : PeriodDomain) (c : Lattice) (t : unitInterval) :
    p.periodLoop c t = p.lattice.mkQ ((t : ℝ) • p.periodVector c) := by
  simp only [periodLoop, Path.cast_coe, Path.map_coe, Function.comp_apply, Path.segment_apply,
    AffineMap.lineMap_apply_module, smul_zero, zero_add]

private theorem PeriodDomain.periodLoop_monodromy (p : PeriodDomain) (c : Lattice) :
    p.quotientCovering.isCoveringMap.monodromy (FirstHurewicz.loopQuotient (p.periodLoop c))
        p.zeroLift =
      ⟨p.periodVector c, p.mkQ_periodVector c⟩ := by
  apply
    p.quotientCovering.isCoveringMap.monodromy_eq_of_map_eq
      (Path.Homotopic.Quotient.mk (Path.segment (0 : ComplexPlane₂) (p.periodVector c)))
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

@[simp]
private theorem PeriodDomain.fundamentalGroupEquiv_periodLoop (p : PeriodDomain) (c : Lattice) :
    p.fundamentalGroupEquiv (FirstHurewicz.loopQuotient (p.periodLoop c)) =
      Multiplicative.ofAdd c := by
  apply Multiplicative.toAdd.injective
  apply p.periodVector_injective
  rw [p.fundamentalGroupEquiv_monodromy, p.periodLoop_monodromy]
  rfl

private def PeriodDomain.singularH1Equiv (p : PeriodDomain) :
    FirstHurewicz.SingularH1 p.Torus ≃ₗ[ℤ] Lattice :=
  FirstHurewicz.singularH1EquivOfPi1 (0 : p.Torus) p.fundamentalGroupEquiv

@[simp]
private theorem PeriodDomain.singularH1Equiv_loopHomologyClass (p : PeriodDomain)
    (q : Path (0 : p.Torus) 0) :
    p.singularH1Equiv (FirstHurewicz.loopHomologyClass q) =
      (p.fundamentalGroupEquiv (FirstHurewicz.loopQuotient q)).toAdd :=
  FirstHurewicz.singularH1EquivOfPi1_loopHomologyClass (0 : p.Torus) p.fundamentalGroupEquiv q

private theorem PeriodDomain.singularH1Equiv_periodLoop (p : PeriodDomain) (c : Lattice) :
    p.singularH1Equiv (FirstHurewicz.loopHomologyClass (p.periodLoop c)) = c := by
  rw [p.singularH1Equiv_loopHomologyClass, p.fundamentalGroupEquiv_periodLoop]
  rfl

@[simp]
private theorem PeriodDomain.singularH1Equiv_symm_apply (p : PeriodDomain) (c : Lattice) :
    p.singularH1Equiv.symm c = FirstHurewicz.loopHomologyClass (p.periodLoop c) := by
  apply p.singularH1Equiv.injective
  rw [LinearEquiv.apply_symm_apply, p.singularH1Equiv_periodLoop]

end Mathoverflow1973

end
