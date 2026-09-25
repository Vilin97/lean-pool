/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveUniformizer
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedUnramifiedField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.MultiplicativeSeries
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.PowerSeries.Evaluation
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
/-!
# Completed p-adic Lubin--Tate levels

For the completed maximal-unramified coefficient field

`E = Frac(W(AlgebraicClosure (ZMod p)))`,

this file base-changes the standard primitive Lubin--Tate polynomial from
`ℚ_[p]` to `E` and takes its actual splitting field.  The complete discrete
valuation on that finite separable extension is selected from the integral
closure of the canonical Witt valuation ring.  This is the mixed-
characteristic evaluation field needed by the changed-uniformizer descent.

The integral polynomial, splitting field, and valuations below are the
existing mathlib/LCFT objects.  No parallel p-adic field, integer ring, or
completion is introduced.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Polynomial
open scoped PowerSeries
open scoped PowerSeries.WithPiTopology

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

/-- The primitive standard Lubin--Tate polynomial over the canonical
valuation ring of the completed-unramified field. -/
noncomputable def padicCompletedPrimitivePolynomialInteger
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Polynomial
      (padicCompletedUnramifiedCompleteDVF p).valuationSubring :=
  (standardLubinTatePrimitivePolynomial
      (padicLocalField p)
      (padicIntEquivValuationSubring p (p : ℤ_[p])) n).map
    (padicCompletedUnramifiedIntegerMap p)

/-- The primitive standard Lubin--Tate polynomial after base change from
`ℚ_[p]` to the completed-unramified fraction field. -/
noncomputable def padicCompletedPrimitivePolynomial
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Polynomial (padicCompletedUnramifiedField p) :=
  (standardLubinTatePrimitivePolynomialOverField
      (padicLocalField p)
      (padicIntEquivValuationSubring p (p : ℤ_[p])) n).map
    (algebraMap ℚ_[p] (padicCompletedUnramifiedField p))

/-- Mapping the integral completed primitive polynomial to the fraction
field gives the field-valued base change. -/
theorem padicCompletedPrimitivePolynomialInteger_map
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicCompletedPrimitivePolynomialInteger p n).map
        (algebraMap
          (padicCompletedUnramifiedCompleteDVF p).valuationSubring
          (padicCompletedUnramifiedField p)) =
      padicCompletedPrimitivePolynomial p n := by
  let O := (padicLocalField p).valuationSubring
  let A := (padicCompletedUnramifiedCompleteDVF p).valuationSubring
  let E := padicCompletedUnramifiedField p
  let Q :=
    standardLubinTatePrimitivePolynomial
      (padicLocalField p)
      (padicIntEquivValuationSubring p (p : ℤ_[p])) n
  have hmaps :
      (algebraMap A E).comp
          (padicCompletedUnramifiedIntegerMap p) =
        (algebraMap ℚ_[p] E).comp (algebraMap O ℚ_[p]) := by
    ext z
    exact padicCompletedUnramifiedIntegerMap_coe p z
  change
    (Q.map (padicCompletedUnramifiedIntegerMap p)).map
        (algebraMap A E) =
      (Q.map (algebraMap O ℚ_[p])).map
        (algebraMap ℚ_[p] E)
  rw [Polynomial.map_map, Polynomial.map_map, hmaps]

/-- The integral completed primitive polynomial is monic. -/
theorem padicCompletedPrimitivePolynomialInteger_monic
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicCompletedPrimitivePolynomialInteger p n).Monic :=
  (standardLubinTatePrimitivePolynomial_monic
    (padicLocalField p)
    (padicIntEquivValuationSubring p (p : ℤ_[p])) n).map _

/-- The field-valued completed primitive polynomial is monic. -/
theorem padicCompletedPrimitivePolynomial_monic
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicCompletedPrimitivePolynomial p n).Monic :=
  (standardLubinTatePrimitivePolynomialOverField_monic
    (padicLocalField p)
    (padicIntEquivValuationSubring p (p : ℤ_[p])) n).map _

/-- The completed primitive polynomial has degree `(p - 1) * p ^ n`. -/
theorem padicCompletedPrimitivePolynomial_natDegree
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicCompletedPrimitivePolynomial p n).natDegree =
      (p - 1) * p ^ n := by
  have hcard :
      Nat.card (padicLocalField p).residueField = p := by
    simpa [padicLocalField] using
      padicCompleteDVF_residueField_card p
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  calc
    (padicCompletedPrimitivePolynomial p n).natDegree =
        (standardLubinTatePrimitivePolynomialOverField
          (padicLocalField p) π n).natDegree :=
      (standardLubinTatePrimitivePolynomialOverField_monic
        (padicLocalField p) π n).natDegree_map
          (algebraMap ℚ_[p] (padicCompletedUnramifiedField p))
    _ = (Nat.card (padicLocalField p).residueField - 1) *
        Nat.card (padicLocalField p).residueField ^ n :=
      standardLubinTatePrimitivePolynomialOverField_natDegree
        (padicLocalField p) π n
    _ = (p - 1) * p ^ n := by rw [hcard]

/-- The completed primitive polynomial remains separable after base change. -/
theorem padicCompletedPrimitivePolynomial_separable
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicCompletedPrimitivePolynomial p n).Separable :=
  (standardLubinTatePrimitivePolynomialOverField_separable
    (padicMultiplicativeLubinTateSeries_isUniformizer p) n).map

/-- The actual finite splitting field over the completed-unramified
coefficient field. -/
def padicCompletedLevelField
    (p : ℕ) [Fact p.Prime] (n : ℕ) :=
  (padicCompletedPrimitivePolynomial p n).SplittingField

@[reducible]
instance padicCompletedLevelFieldField
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Field (padicCompletedLevelField p n) := by
  change Field (padicCompletedPrimitivePolynomial p n).SplittingField
  infer_instance

@[reducible]
noncomputable instance padicCompletedLevelFieldAlgebra
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Algebra (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n) := by
  change Algebra (padicCompletedUnramifiedField p)
    (padicCompletedPrimitivePolynomial p n).SplittingField
  infer_instance

section

/-- The completed Lubin–Tate level field is a module over the completed unramified base. -/
local instance padicCompletedLevelFieldModule
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    @Module (padicCompletedUnramifiedField p) (padicCompletedLevelField p n)
      (inferInstance : DivisionRing (padicCompletedUnramifiedField p)).toRing.toSemiring
      (inferInstance : AddCommGroup (padicCompletedLevelField p n)).toAddCommMonoid :=
  @Algebra.toModule (padicCompletedUnramifiedField p) (padicCompletedLevelField p n)
    _ _ (padicCompletedLevelFieldAlgebra p n)

instance padicCompletedLevelField_finiteDimensional
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    FiniteDimensional (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n) := by
  change FiniteDimensional (padicCompletedUnramifiedField p)
    (padicCompletedPrimitivePolynomial p n).SplittingField
  infer_instance

end

/-- The completed level is the splitting field of a separable polynomial,
hence is Galois over its completed-unramified base. -/
noncomputable instance padicCompletedLevelField_isGalois
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsGalois (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n) := by
  change IsGalois (padicCompletedUnramifiedField p)
    (padicCompletedPrimitivePolynomial p n).SplittingField
  exact
    IsGalois.of_separable_splitting_field
      (padicCompletedPrimitivePolynomial_separable p n)

/-- The completed primitive polynomial splits over the completed level. -/
theorem padicCompletedPrimitivePolynomial_splits
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ((padicCompletedPrimitivePolynomial p n).map
      (algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n))).Splits :=
  Polynomial.SplittingField.splits
    (padicCompletedPrimitivePolynomial p n)

/-- The roots of the completed primitive polynomial generate its splitting
field. -/
theorem padicCompletedPrimitivePolynomial_adjoin_rootSet
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Algebra.adjoin (padicCompletedUnramifiedField p)
        ((padicCompletedPrimitivePolynomial p n).rootSet
          (padicCompletedLevelField p n) :
          Set (padicCompletedLevelField p n)) =
      ⊤ :=
  Polynomial.SplittingField.adjoin_rootSet
    (padicCompletedPrimitivePolynomial p n)

private theorem padicCompletedPrimitivePolynomial_map_degree_ne_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ((padicCompletedPrimitivePolynomial p n).map
      (algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n))).degree ≠ 0 := by
  have hmonic :=
    (padicCompletedPrimitivePolynomial_monic p n).map
      (algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n))
  rw [Polynomial.degree_eq_natDegree hmonic.ne_zero,
    (padicCompletedPrimitivePolynomial_monic p n).natDegree_map,
    padicCompletedPrimitivePolynomial_natDegree]
  exact_mod_cast
    (Nat.mul_pos
      (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
      (Nat.pow_pos (Fact.out : p.Prime).pos)).ne'

/-- A chosen primitive standard division point in the completed level. -/
noncomputable def padicCompletedPrimitiveRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    padicCompletedLevelField p n :=
  Polynomial.rootOfSplits
    (Polynomial.SplittingField.splits
      (padicCompletedPrimitivePolynomial p n))
    (padicCompletedPrimitivePolynomial_map_degree_ne_zero p n)

/-- The chosen completed primitive point is a root of the genuine
base-changed primitive polynomial. -/
theorem padicCompletedPrimitiveRoot_isRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ((padicCompletedPrimitivePolynomial p n).map
      (algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n))).IsRoot
      (padicCompletedPrimitiveRoot p n) :=
  Polynomial.eval_rootOfSplits
    (Polynomial.SplittingField.splits
      (padicCompletedPrimitivePolynomial p n))
    (padicCompletedPrimitivePolynomial_map_degree_ne_zero p n)

/-- The integral completed primitive polynomial annihilates the chosen
root in the actual splitting field. -/
theorem padicCompletedPrimitiveRoot_aeval_integerPolynomial
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Polynomial.aeval (padicCompletedPrimitiveRoot p n)
        (padicCompletedPrimitivePolynomialInteger p n) = 0 := by
  calc
    Polynomial.aeval (padicCompletedPrimitiveRoot p n)
        (padicCompletedPrimitivePolynomialInteger p n) =
      Polynomial.aeval (padicCompletedPrimitiveRoot p n)
        ((padicCompletedPrimitivePolynomialInteger p n).map
          (algebraMap
            (padicCompletedUnramifiedCompleteDVF p).valuationSubring
            (padicCompletedUnramifiedField p))) := by
      symm
      exact
        Polynomial.aeval_map_algebraMap
          (padicCompletedUnramifiedField p)
          (padicCompletedPrimitiveRoot p n)
          (padicCompletedPrimitivePolynomialInteger p n)
    _ =
      Polynomial.aeval (padicCompletedPrimitiveRoot p n)
        (padicCompletedPrimitivePolynomial p n) := by
      rw [padicCompletedPrimitivePolynomialInteger_map]
    _ = 0 := by
      simpa [Polynomial.IsRoot, Polynomial.aeval_def] using
        padicCompletedPrimitiveRoot_isRoot p n

/-- The chosen primitive point is integral over the canonical Witt
valuation ring. -/
theorem padicCompletedPrimitiveRoot_isIntegral
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsIntegral
      (padicCompletedUnramifiedCompleteDVF p).valuationSubring
      (padicCompletedPrimitiveRoot p n) :=
  ⟨padicCompletedPrimitivePolynomialInteger p n,
    padicCompletedPrimitivePolynomialInteger_monic p n,
    padicCompletedPrimitiveRoot_aeval_integerPolynomial p n⟩

private theorem padicCompletedLevelCompleteDVFData_exists
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ∃ target : CompleteDVF.{0, 0} (padicCompletedLevelField p n),
      ∃ hExt :
          (padicCompletedUnramifiedCompleteDVF p).valuation.HasExtension
            target.valuation,
        letI :
            (padicCompletedUnramifiedCompleteDVF p).valuation.HasExtension
              target.valuation := hExt
        IsIntegralClosure target.valuationSubring
            (padicCompletedUnramifiedCompleteDVF p).valuationSubring
            (padicCompletedLevelField p n) ∧
          degree (padicCompletedUnramifiedCompleteDVF p).toDVF target.toDVF =
            ramificationIndex
                (padicCompletedUnramifiedCompleteDVF p).toDVF target.toDVF *
              residueDegree
                (padicCompletedUnramifiedCompleteDVF p).toDVF target.toDVF := by
  exact
    exists_integralClosure_standard_fundamental_identity
      (K := padicCompletedUnramifiedField p)
      (L := padicCompletedLevelField p n)
      (padicCompletedUnramifiedCompleteDVF p)

/-- The complete discrete valuation on the completed level selected from its
actual integral closure over the Witt valuation ring. -/
noncomputable def padicCompletedLevelCompleteDVF
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    CompleteDVF.{0, 0} (padicCompletedLevelField p n) :=
  Classical.choose (padicCompletedLevelCompleteDVFData_exists p n)

/-- The selected completed-level valuation extends the completed-unramified
base valuation. -/
theorem padicCompletedLevelCompleteDVF_hasExtension
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicCompletedUnramifiedCompleteDVF p).valuation.HasExtension
      (padicCompletedLevelCompleteDVF p n).valuation :=
  Classical.choose
    (Classical.choose_spec
      (padicCompletedLevelCompleteDVFData_exists p n))

noncomputable instance padicCompletedLevelCompleteDVF_hasExtensionInstance
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicCompletedUnramifiedCompleteDVF p).valuation.HasExtension
      (padicCompletedLevelCompleteDVF p n).valuation :=
  padicCompletedLevelCompleteDVF_hasExtension p n

/-- The completed-level valuation ring is the actual integral closure of the
completed-unramified valuation ring. -/
theorem padicCompletedLevelCompleteDVF_isIntegralClosure
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsIntegralClosure
      (padicCompletedLevelCompleteDVF p n).valuationSubring
      (padicCompletedUnramifiedCompleteDVF p).valuationSubring
      (padicCompletedLevelField p n) :=
  (Classical.choose_spec
    (Classical.choose_spec
      (padicCompletedLevelCompleteDVFData_exists p n))).1

/-- The chosen completed primitive root belongs to the selected
integral-closure valuation ring. -/
theorem padicCompletedPrimitiveRoot_mem_valuationSubring
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    padicCompletedPrimitiveRoot p n ∈
      (padicCompletedLevelCompleteDVF p n).valuation.valuationSubring := by
  let : IsIntegralClosure
      (padicCompletedLevelCompleteDVF p n).valuationSubring
      (padicCompletedUnramifiedCompleteDVF p).valuationSubring
      (padicCompletedLevelField p n) :=
    padicCompletedLevelCompleteDVF_isIntegralClosure p n
  rcases
      (IsIntegralClosure.isIntegral_iff
        (A := (padicCompletedLevelCompleteDVF p n).valuationSubring)
        (R := (padicCompletedUnramifiedCompleteDVF p).valuationSubring)
        (B := padicCompletedLevelField p n)).1
        (padicCompletedPrimitiveRoot_isIntegral p n) with
    ⟨z, hz⟩
  change
    (padicCompletedLevelCompleteDVF p n).valuation
        (padicCompletedPrimitiveRoot p n) ≤ 1
  rw [← hz]
  exact z.property

/-- The chosen primitive point as an element of the completed-level
valuation ring. -/
noncomputable def padicCompletedPrimitiveRootInteger
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicCompletedLevelCompleteDVF p n).valuationSubring :=
  ⟨padicCompletedPrimitiveRoot p n,
    padicCompletedPrimitiveRoot_mem_valuationSubring p n⟩

/-- Coercing the integral primitive point returns the chosen splitting-field
root. -/
@[simp]
theorem padicCompletedPrimitiveRootInteger_coe
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicCompletedPrimitiveRootInteger p n :
      padicCompletedLevelField p n) =
        padicCompletedPrimitiveRoot p n :=
  rfl

/-- The integral primitive polynomial annihilates the primitive point in
the completed-level valuation ring. -/
theorem padicCompletedPrimitiveRootInteger_aeval
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Polynomial.aeval (padicCompletedPrimitiveRootInteger p n)
        (padicCompletedPrimitivePolynomialInteger p n) = 0 := by
  let base := padicCompletedUnramifiedCompleteDVF p
  let target := padicCompletedLevelCompleteDVF p n
  let i : target.valuationSubring →ₐ[base.valuationSubring]
      padicCompletedLevelField p n :=
    IsScalarTower.toAlgHom base.valuationSubring target.valuationSubring
      (padicCompletedLevelField p n)
  apply Subtype.ext
  change
    i (Polynomial.aeval (padicCompletedPrimitiveRootInteger p n)
      (padicCompletedPrimitivePolynomialInteger p n)) = i 0
  rw [← Polynomial.aeval_algHom_apply (f := i), map_zero]
  simpa [i] using
    padicCompletedPrimitiveRoot_aeval_integerPolynomial p n

/-- Base change preserves the weak Eisenstein condition for the completed
primitive polynomial. -/
theorem padicCompletedPrimitivePolynomialInteger_isWeaklyEisensteinAt
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicCompletedPrimitivePolynomialInteger p n).IsWeaklyEisensteinAt
      (padicCompletedUnramifiedCompleteDVF p).maximalIdeal := by
  rw [← padicCompletedUnramifiedIntegerMap_map_maximalIdeal p]
  exact
    (standardLubinTatePrimitivePolynomial_isEisensteinAt
      (padicMultiplicativeLubinTateSeries_isUniformizer p)
      n).isWeaklyEisensteinAt.map
        (padicCompletedUnramifiedIntegerMap p)

/-- The completed primitive point lies in the maximal ideal of the selected
level valuation ring. -/
theorem padicCompletedPrimitiveRootInteger_mem_maximalIdeal
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    padicCompletedPrimitiveRootInteger p n ∈
      (padicCompletedLevelCompleteDVF p n).maximalIdeal := by
  let base := padicCompletedUnramifiedCompleteDVF p
  let target := padicCompletedLevelCompleteDVF p n
  let Q := padicCompletedPrimitivePolynomialInteger p n
  let lambda := padicCompletedPrimitiveRootInteger p n
  have hlambdaPow :
      lambda ^
          ((Q.map
            (algebraMap base.valuationSubring
              target.valuationSubring)).natDegree) ∈
        base.maximalIdeal.map
          (algebraMap base.valuationSubring target.valuationSubring) :=
    (padicCompletedPrimitivePolynomialInteger_isWeaklyEisensteinAt
      p n).pow_natDegree_le_of_aeval_zero_of_monic_mem_map
        (by
          simpa [base, target, Q, lambda] using
            padicCompletedPrimitiveRootInteger_aeval p n)
        (by
          simpa [Q] using
            padicCompletedPrimitivePolynomialInteger_monic p n)
        _ le_rfl
  have hlambdaPow' :
      lambda ^
          ((Q.map
            (algebraMap base.valuationSubring
              target.valuationSubring)).natDegree) ∈
        target.maximalIdeal :=
    (maximalIdeal_map_integerMap_le base.toDVF target.toDVF) hlambdaPow
  exact
    (IsLocalRing.maximalIdeal.isMaximal
      target.valuationSubring).isPrime.mem_of_pow_mem _ hlambdaPow'

private noncomputable local instance (priority := 50)
    padicCompletedLevelWittUniformSpace
    (p : ℕ) [Fact p.Prime] :
    UniformSpace (padicCompletedUnramifiedWittRing p) :=
  ⊥

private noncomputable local instance
    padicCompletedLevelTargetWithIdeal
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    WithIdeal
      (padicCompletedLevelCompleteDVF p n).valuationSubring where
  i := (padicCompletedLevelCompleteDVF p n).maximalIdeal

private noncomputable local instance
    padicCompletedLevelTargetCompleteSpace
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    CompleteSpace
      (padicCompletedLevelCompleteDVF p n).valuationSubring := by
  let target := padicCompletedLevelCompleteDVF p n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).1

private noncomputable local instance
    padicCompletedLevelTargetT2Space
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    T2Space
      (padicCompletedLevelCompleteDVF p n).valuationSubring := by
  let target := padicCompletedLevelCompleteDVF p n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).2

/-- The chosen completed primitive point is a genuine convergent evaluation
point for Witt-coefficient power series. -/
theorem padicCompletedPrimitiveRootInteger_hasEval
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    PowerSeries.HasEval (padicCompletedPrimitiveRootInteger p n) := by
  apply WithIdeal.isTopologicallyNilpotent_of_mem
  exact padicCompletedPrimitiveRootInteger_mem_maximalIdeal p n

/-- The canonical Witt-coefficient map into the valuation ring of the
actual completed level. -/
noncomputable def padicCompletedLevelWittCoefficientHom
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    padicCompletedUnramifiedWittRing p →+*
      (padicCompletedLevelCompleteDVF p n).valuationSubring :=
  (integerMap
      (padicCompletedUnramifiedCompleteDVF p).toDVF
      (padicCompletedLevelCompleteDVF p n).toDVF).comp
    (padicCompletedUnramifiedWittRingEquivValuationSubring p).toRingHom

/-- The Witt-coefficient map is the ambient fraction-field algebra map
after coercion. -/
@[simp]
theorem padicCompletedLevelWittCoefficientHom_apply
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : padicCompletedUnramifiedWittRing p) :
    ((padicCompletedLevelWittCoefficientHom p n a :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
      padicCompletedLevelField p n) =
        algebraMap (padicCompletedUnramifiedField p)
          (padicCompletedLevelField p n)
          (algebraMap (padicCompletedUnramifiedWittRing p)
            (padicCompletedUnramifiedField p) a) := by
  rfl

/-- With the discrete coefficient topology, the canonical Witt map into
the completed level is continuous. -/
theorem padicCompletedLevelWittCoefficientHom_continuous
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Continuous (padicCompletedLevelWittCoefficientHom p n) :=
  continuous_of_discreteTopology

private noncomputable local instance
    padicCompletedLevelWittAlgebra
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Algebra (padicCompletedUnramifiedWittRing p)
      (padicCompletedLevelCompleteDVF p n).valuationSubring :=
  (padicCompletedLevelWittCoefficientHom p n).toAlgebra

/-- Analytic evaluation of Witt-coefficient power series in the actual
completed level. -/
noncomputable def padicCompletedLevelPowerSeriesEval
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    (padicCompletedUnramifiedWittRing p)⟦X⟧ →+*
      (padicCompletedLevelCompleteDVF p n).valuationSubring :=
  PowerSeries.eval₂Hom
    (padicCompletedLevelWittCoefficientHom_continuous p n) hx

/-- Completed-level evaluation sends the power-series variable to the
chosen evaluation point. -/
@[simp]
theorem padicCompletedLevelPowerSeriesEval_X
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    padicCompletedLevelPowerSeriesEval p n x hx PowerSeries.X = x := by
  rw [padicCompletedLevelPowerSeriesEval,
    PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_X]

/-- Completed-level evaluation sends constants through the canonical Witt
coefficient map. -/
@[simp]
theorem padicCompletedLevelPowerSeriesEval_C
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (a : padicCompletedUnramifiedWittRing p) :
    padicCompletedLevelPowerSeriesEval p n x hx (PowerSeries.C a) =
      padicCompletedLevelWittCoefficientHom p n a := by
  rw [padicCompletedLevelPowerSeriesEval,
    PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_C]

/-- On polynomial power series, completed-level analytic evaluation agrees
with ordinary polynomial evaluation. -/
@[simp]
theorem padicCompletedLevelPowerSeriesEval_coe
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (P : Polynomial (padicCompletedUnramifiedWittRing p)) :
    padicCompletedLevelPowerSeriesEval p n x hx
        (P : PowerSeries (padicCompletedUnramifiedWittRing p)) =
      Polynomial.eval₂
        (padicCompletedLevelWittCoefficientHom p n) x P := by
  rw [padicCompletedLevelPowerSeriesEval,
    PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_coe]

/-- Evaluation at a topologically nilpotent completed-level integer is
continuous. -/
theorem padicCompletedLevelPowerSeriesEval_continuous
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    Continuous (padicCompletedLevelPowerSeriesEval p n x hx) := by
  rw [padicCompletedLevelPowerSeriesEval,
    PowerSeries.coe_eval₂Hom]
  exact PowerSeries.continuous_eval₂
    (padicCompletedLevelWittCoefficientHom_continuous p n) hx

/-- Evaluating a Witt-coefficient series with zero constant coefficient
produces another topologically nilpotent completed-level integer. -/
theorem padicCompletedLevelPowerSeriesEval_hasEval
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (f : PowerSeries (padicCompletedUnramifiedWittRing p))
    (hf : PowerSeries.HasSubst f) :
    PowerSeries.HasEval
      (padicCompletedLevelPowerSeriesEval p n x hx f) :=
  hf.hasEval.map
    (padicCompletedLevelPowerSeriesEval_continuous p n x hx)

/-- Completed-level analytic evaluation commutes with one-variable formal
substitution. -/
theorem padicCompletedLevelPowerSeriesEval_subst
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (a f : PowerSeries (padicCompletedUnramifiedWittRing p))
    (ha : PowerSeries.HasSubst a)
    (haEval : PowerSeries.HasEval
      (padicCompletedLevelPowerSeriesEval p n x hx a)) :
    padicCompletedLevelPowerSeriesEval p n x hx
        (PowerSeries.subst a f) =
      padicCompletedLevelPowerSeriesEval p n
        (padicCompletedLevelPowerSeriesEval p n x hx a)
        haEval f := by
  let W := padicCompletedUnramifiedWittRing p
  let S := (padicCompletedLevelCompleteDVF p n).valuationSubring
  simp only [padicCompletedLevelPowerSeriesEval,
    PowerSeries.coe_eval₂Hom]
  change PowerSeries.eval₂ (algebraMap W S) x
      (PowerSeries.subst a f) =
    PowerSeries.eval₂ (algebraMap W S)
      (PowerSeries.eval₂ (algebraMap W S) x a) f
  simpa only [PowerSeries.eval₂, PowerSeries.subst,
    Function.const_apply] using
      (MvPowerSeries.eval₂_subst
        (R := W) (S := W) (T := S)
        (a := fun _ : Unit ↦ a) ha.const
        (PowerSeries.hasEval hx) f)

end LubinTate

end
