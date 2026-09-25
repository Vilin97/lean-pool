/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedLevel
public import Mathlib.RingTheory.AdicCompletion.Topology
/-!
# Coefficient maps and analytic evaluation on completed p-adic levels

This module equips completed Lubin--Tate levels with the direct p-adic
coefficient maps used by polynomial and power-series evaluation.  It also
establishes the exact completed primitive-point torsion relations and the
general injectivity criterion for evaluation with unit linear coefficient.
-/

@[expose] public section

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open SameUniformizer

/-- The discrete Witt-vector coefficient uniformity used for completed evaluation. -/
noncomputable local instance (priority := 50)
    padicCompletedMultiplicativeWittUniformSpace
    (p : ℕ) [Fact p.Prime] :
    UniformSpace (padicCompletedUnramifiedWittRing p) :=
  ⊥

/-- The maximal-ideal adic structure on a completed Lubin--Tate level. -/
noncomputable local instance
    padicCompletedMultiplicativeTargetWithIdeal
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    WithIdeal
      (padicCompletedLevelCompleteDVF p n).valuationSubring where
  i := (padicCompletedLevelCompleteDVF p n).maximalIdeal

/-- Completeness of the completed-level valuation ring for its adic topology. -/
noncomputable local instance
    padicCompletedMultiplicativeTargetCompleteSpace
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    CompleteSpace
      (padicCompletedLevelCompleteDVF p n).valuationSubring := by
  let target := padicCompletedLevelCompleteDVF p n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).1

/-- Separatedness of the completed-level valuation ring for its adic topology. -/
noncomputable local instance
    padicCompletedMultiplicativeTargetT2Space
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    T2Space
      (padicCompletedLevelCompleteDVF p n).valuationSubring := by
  let target := padicCompletedLevelCompleteDVF p n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).2

/-- The completed Lubin--Tate level as an algebra over the original p-adic
base field, through the completed unramified coefficient field. -/
noncomputable instance padicCompletedLevelFieldPadicAlgebra
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Algebra ℚ_[p] (padicCompletedLevelField p n) :=
  ((algebraMap (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n)).comp
    (algebraMap ℚ_[p] (padicCompletedUnramifiedField p))).toAlgebra

instance padicCompletedLevelField_padicScalarTower
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsScalarTower ℚ_[p] (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The canonical coefficient map from the p-adic valuation ring directly
into the field underlying a completed Lubin--Tate level. -/
noncomputable def padicCompletedLevelPadicFieldCoefficientHom
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicLocalField p).valuationSubring →+*
      padicCompletedLevelField p n :=
  ((algebraMap (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n)).comp
    (algebraMap ℚ_[p] (padicCompletedUnramifiedField p))).comp
      (algebraMap (padicLocalField p).valuationSubring ℚ_[p])

/-- The same p-adic coefficient map with codomain restricted to the
valuation ring of the completed level. -/
noncomputable def padicCompletedLevelPadicIntegerCoefficientHom
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicLocalField p).valuationSubring →+*
      (padicCompletedLevelCompleteDVF p n).valuationSubring :=
  (padicCompletedLevelWittCoefficientHom p n).comp
    (padicValuationSubringToCompletedUnramifiedWittRing p)

/-- Coercing the integral p-adic coefficient map to the completed-level
field gives the canonical field-valued coefficient map. -/
@[simp]
theorem padicCompletedLevelPadicIntegerCoefficientHom_coe
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : (padicLocalField p).valuationSubring) :
    ((padicCompletedLevelPadicIntegerCoefficientHom p n a :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
      padicCompletedLevelField p n) =
        padicCompletedLevelPadicFieldCoefficientHom p n a := by
  rw [padicCompletedLevelPadicIntegerCoefficientHom,
    RingHom.comp_apply,
    padicCompletedLevelWittCoefficientHom_apply]
  change
    algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)
        (algebraMap (padicCompletedUnramifiedWittRing p)
          (padicCompletedUnramifiedField p)
          (padicValuationSubringToCompletedUnramifiedWittRing p a)) =
      padicCompletedLevelPadicFieldCoefficientHom p n a
  let z : ℤ_[p] := (padicIntEquivValuationSubring p).symm a
  have ha : padicIntEquivValuationSubring p z = a :=
    (padicIntEquivValuationSubring p).apply_symm_apply a
  rw [← ha]
  rw [show
    padicValuationSubringToCompletedUnramifiedWittRing p
        (padicIntEquivValuationSubring p z) =
      padicIntToCompletedUnramifiedWittRing p z by
    change
      padicIntToCompletedUnramifiedWittRing p
          ((padicIntEquivValuationSubring p).symm
            (padicIntEquivValuationSubring p z)) =
        padicIntToCompletedUnramifiedWittRing p z
    rw [RingEquiv.symm_apply_apply]]
  change
    algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)
        (algebraMap (padicCompletedUnramifiedWittRing p)
          (padicCompletedUnramifiedField p)
          (padicIntToCompletedUnramifiedWittRing p z)) =
      algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)
        (algebraMap ℚ_[p] (padicCompletedUnramifiedField p)
          (algebraMap ℤ_[p] ℚ_[p] z))
  rw [padicCompletedUnramifiedField_algebraMap_padicInt]

/-- Polynomial evaluation through the integral coefficient map agrees,
after coercion, with evaluation through the field coefficient map. -/
theorem padicCompletedLevelPadicIntegerPolynomialEval_coe
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (P : Polynomial (padicLocalField p).valuationSubring) :
    ((Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n) x P :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n) =
      Polynomial.eval₂
        (padicCompletedLevelPadicFieldCoefficientHom p n)
        (x : padicCompletedLevelField p n) P := by
  let target := padicCompletedLevelCompleteDVF p n
  let i : target.valuationSubring →+*
      padicCompletedLevelField p n :=
    target.valuation.valuationSubring.subtype
  have hcomp :
      i.comp (padicCompletedLevelPadicIntegerCoefficientHom p n) =
        padicCompletedLevelPadicFieldCoefficientHom p n := by
    ext a
    exact padicCompletedLevelPadicIntegerCoefficientHom_coe p n a
  change
    i (Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n) x P) =
      Polynomial.eval₂
        (padicCompletedLevelPadicFieldCoefficientHom p n) (i x) P
  rw [Polynomial.hom_eval₂, hcomp]

private theorem padicCompletedPrimitiveRoot_standardPrimitivePolynomial
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Polynomial.eval₂
        (padicCompletedLevelPadicFieldCoefficientHom p n)
        (padicCompletedPrimitiveRoot p n)
        (standardLubinTatePrimitivePolynomial
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) n) =
      0 := by
  have hroot := padicCompletedPrimitiveRoot_isRoot p n
  simpa [Polynomial.IsRoot, padicCompletedPrimitivePolynomial,
    standardLubinTatePrimitivePolynomialOverField,
    padicCompletedLevelPadicFieldCoefficientHom,
    Polynomial.eval_map, Polynomial.eval₂_map] using hroot

/-- The chosen primitive point in the completed level is killed by the
`n + 1`-fold standard p-adic Lubin--Tate iterate. -/
theorem padicCompletedPrimitiveRoot_iterate_succ_eq_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Polynomial.eval₂
        (padicCompletedLevelPadicFieldCoefficientHom p n)
        (padicCompletedPrimitiveRoot p n)
        (standardLubinTatePolynomialIterate
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) (n + 1)) =
      0 := by
  let F := padicLocalField p
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  let φ := padicCompletedLevelPadicFieldCoefficientHom p n
  let x := padicCompletedPrimitiveRoot p n
  have hfactor :=
    congrArg (Polynomial.eval₂ φ x)
      (standardLubinTatePolynomialIterate_succ_factor F π n)
  rw [Polynomial.eval₂_mul,
    padicCompletedPrimitiveRoot_standardPrimitivePolynomial p n,
    mul_zero] at hfactor
  simpa only [F, π, φ, x] using hfactor

/-- The chosen completed primitive point is not killed one level early. -/
theorem padicCompletedPrimitiveRoot_iterate_ne_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Polynomial.eval₂
        (padicCompletedLevelPadicFieldCoefficientHom p n)
        (padicCompletedPrimitiveRoot p n)
        (standardLubinTatePolynomialIterate
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) n) ≠
      0 := by
  let F := padicLocalField p
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  let E := padicCompletedUnramifiedField p
  let L := padicCompletedLevelField p n
  let φK : ℚ_[p] →+* L :=
    (algebraMap E L).comp (algebraMap ℚ_[p] E)
  let φO : F.valuationSubring →+* L :=
    φK.comp (algebraMap F.valuationSubring ℚ_[p])
  let x := padicCompletedPrimitiveRoot p n
  intro hzero
  have hroot := padicCompletedPrimitiveRoot_isRoot p n
  have hrootField :
      Polynomial.eval₂ φK x
          (standardLubinTatePrimitivePolynomialOverField F π n) =
        0 := by
    simpa [Polynomial.IsRoot, padicCompletedPrimitivePolynomial,
      Polynomial.eval_map, Polynomial.eval₂_map, F, π, E, L, φK, x] using
        hroot
  have hequation :
      Polynomial.eval₂ φO x
            (standardLubinTatePolynomialIterate F π n) ^
          (Nat.card F.residueField - 1) +
        φK (π : ℚ_[p]) =
      0 := by
    calc
      _ =
          Polynomial.eval₂ φK x
            (standardLubinTatePrimitivePolynomialOverField F π n) := by
        symm
        exact
          standardLubinTatePrimitivePolynomialOverField_eval₂
            F π φK n x
      _ = 0 := hrootField
  have hzero' :
      Polynomial.eval₂ φO x
          (standardLubinTatePolynomialIterate F π n) =
        0 := by
    simpa only [φO, φK, F, π, E, L, x,
      padicCompletedLevelPadicFieldCoefficientHom] using hzero
  rw [hzero', zero_pow, zero_add] at hequation
  · apply (padicMultiplicativeLubinTateSeries_isUniformizer p).ne_zero
    apply φK.injective
    simpa only [F, π, map_zero] using hequation
  · exact Nat.sub_ne_zero_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField)

/-- Integral form of the exact completed primitive-point torsion
relation at level `n + 1`. -/
theorem padicCompletedPrimitiveRootInteger_iterate_succ_eq_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n)
        (padicCompletedPrimitiveRootInteger p n)
        (standardLubinTatePolynomialIterate
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) (n + 1)) =
      0 := by
  apply Subtype.ext
  change
    ((Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n)
        (padicCompletedPrimitiveRootInteger p n)
        (standardLubinTatePolynomialIterate
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) (n + 1)) :
      (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n) =
      0
  rw [padicCompletedLevelPadicIntegerPolynomialEval_coe]
  exact padicCompletedPrimitiveRoot_iterate_succ_eq_zero p n

/-- The integral completed primitive point is not killed by the
level-`n` standard iterate. -/
theorem padicCompletedPrimitiveRootInteger_iterate_ne_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n)
        (padicCompletedPrimitiveRootInteger p n)
        (standardLubinTatePolynomialIterate
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) n) ≠
      0 := by
  intro hzero
  apply padicCompletedPrimitiveRoot_iterate_ne_zero p n
  have hcoe := congrArg
    (fun z : (padicCompletedLevelCompleteDVF p n).valuationSubring =>
      (z : padicCompletedLevelField p n)) hzero
  simpa [map_zero,
    padicCompletedLevelPadicIntegerPolynomialEval_coe,
    padicCompletedPrimitiveRootInteger_coe] using hcoe

/-- Completed-level power-series evaluation is independent of the proof
that its evaluation point is topologically nilpotent. -/
theorem padicCompletedLevelPowerSeriesEval_congr_point
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    {x y : (padicCompletedLevelCompleteDVF p n).valuationSubring}
    (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
    (hxy : x = y)
    (f : PowerSeries (padicCompletedUnramifiedWittRing p)) :
    padicCompletedLevelPowerSeriesEval p n x hx f =
      padicCompletedLevelPowerSeriesEval p n y hy f := by
  subst y
  rfl

/-- A completed-level power-series evaluation with zero constant
coefficient and a unit linear coefficient is injective on convergent points. -/
theorem
    padicCompletedLevelPowerSeriesEval_injective_of_unitLinearCoefficient
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (f : PowerSeries (padicCompletedUnramifiedWittRing p))
    (hconstant : PowerSeries.constantCoeff f = 0)
    (hlinear : IsUnit (PowerSeries.coeff 1 f))
    {x y : (padicCompletedLevelCompleteDVF p n).valuationSubring}
    (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
    (hxy :
      padicCompletedLevelPowerSeriesEval p n x hx f =
        padicCompletedLevelPowerSeriesEval p n y hy f) :
    x = y := by
  let g := f.substInvOfIsUnit hlinear
  have hf : PowerSeries.HasSubst f :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hconstant
  have hg : PowerSeries.HasSubst g := by
    simpa only [g] using
      (PowerSeries.HasSubst.substInvOfIsUnit f hlinear)
  let xf := padicCompletedLevelPowerSeriesEval p n x hx f
  let yf := padicCompletedLevelPowerSeriesEval p n y hy f
  let hxf : PowerSeries.HasEval xf :=
    padicCompletedLevelPowerSeriesEval_hasEval p n x hx f hf
  let hyf : PowerSeries.HasEval yf :=
    padicCompletedLevelPowerSeriesEval_hasEval p n y hy f hf
  let evalInverse :
      {z : (padicCompletedLevelCompleteDVF p n).valuationSubring //
        PowerSeries.HasEval z} →
        (padicCompletedLevelCompleteDVF p n).valuationSubring :=
    fun z =>
      padicCompletedLevelPowerSeriesEval p n z.1 z.2 g
  let packedX :
      {z : (padicCompletedLevelCompleteDVF p n).valuationSubring //
        PowerSeries.HasEval z} :=
    ⟨xf, hxf⟩
  let packedY :
      {z : (padicCompletedLevelCompleteDVF p n).valuationSubring //
        PowerSeries.HasEval z} :=
    ⟨yf, hyf⟩
  have hpacked : packedX = packedY := by
    apply Subtype.ext
    exact hxy
  have hxback : evalInverse packedX = x := by
    calc
      evalInverse packedX =
          padicCompletedLevelPowerSeriesEval p n x hx
            (PowerSeries.subst f g) := by
        exact
          (padicCompletedLevelPowerSeriesEval_subst p n x hx
            f g hf hxf).symm
      _ =
          padicCompletedLevelPowerSeriesEval p n x hx
            PowerSeries.X := by
        rw [show PowerSeries.subst f g = PowerSeries.X by
          simpa only [g] using
            (PowerSeries.subst_substInvOfIsUnit_left
              f hconstant hlinear)]
      _ = x :=
        padicCompletedLevelPowerSeriesEval_X p n x hx
  have hyback : evalInverse packedY = y := by
    calc
      evalInverse packedY =
          padicCompletedLevelPowerSeriesEval p n y hy
            (PowerSeries.subst f g) := by
        exact
          (padicCompletedLevelPowerSeriesEval_subst p n y hy
            f g hf hyf).symm
      _ =
          padicCompletedLevelPowerSeriesEval p n y hy
            PowerSeries.X := by
        rw [show PowerSeries.subst f g = PowerSeries.X by
          simpa only [g] using
            (PowerSeries.subst_substInvOfIsUnit_left
              f hconstant hlinear)]
      _ = y :=
        padicCompletedLevelPowerSeriesEval_X p n y hy
  exact hxback.symm.trans
    ((congrArg evalInverse hpacked).trans hyback)

end LubinTate

end
