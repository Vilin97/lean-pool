/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.NormalForm

/-!
# Semantic normal forms for the split trace cover

The iterated monic `AdjoinRoot` presentation gives every element of the Kummer top algebra a
unique rectangular coefficient vector.  Composing this representation with the affine and
Laurent comparison maps gives semantic normal forms for trace-cover classes, and evaluation of
those coefficients recovers the comparison-map image exactly.

This does not identify two source classes with the same semantic normal form.  That remaining
injectivity statement is the syntactic quotient-division wall and is kept explicit below.
-/

namespace BGS.Markoff

open Polynomial

noncomputable section

/-- Rectangular coefficients of an element in a two-stage monic `AdjoinRoot` tower. -/
def adjoinRootTowerSemanticNormalForm
    {R : Type*} [CommRing R] (f : R[X]) (hf : f.Monic)
    (g : Polynomial (AdjoinRoot f)) (hg : g.Monic) (z : AdjoinRoot g) :
    Fin f.natDegree × Fin g.natDegree →₀ R :=
  (((AdjoinRoot.powerBasis' hf).basis.smulTower
    (AdjoinRoot.powerBasis' hg).basis).repr z)

/-- Evaluate a rectangular coefficient vector in the two-stage `AdjoinRoot` tower. -/
def adjoinRootTowerSemanticNormalFormEvaluation
    {R : Type*} [CommRing R] (f : R[X]) (hf : f.Monic)
    (g : Polynomial (AdjoinRoot f)) (hg : g.Monic)
    (c : Fin f.natDegree × Fin g.natDegree →₀ R) : AdjoinRoot g :=
  (((AdjoinRoot.powerBasis' hf).basis.smulTower
    (AdjoinRoot.powerBasis' hg).basis).repr.symm c)

@[simp]
theorem adjoinRootTowerSemanticNormalForm_evaluation
    {R : Type*} [CommRing R] (f : R[X]) (hf : f.Monic)
    (g : Polynomial (AdjoinRoot f)) (hg : g.Monic) (z : AdjoinRoot g) :
    adjoinRootTowerSemanticNormalFormEvaluation f hf g hg
        (adjoinRootTowerSemanticNormalForm f hf g hg z) = z := by
  exact LinearEquiv.symm_apply_apply _ z

@[simp]
theorem adjoinRootTowerSemanticNormalForm_evaluation_inverse
    {R : Type*} [CommRing R] (f : R[X]) (hf : f.Monic)
    (g : Polynomial (AdjoinRoot f)) (hg : g.Monic)
    (c : Fin f.natDegree × Fin g.natDegree →₀ R) :
    adjoinRootTowerSemanticNormalForm f hf g hg
        (adjoinRootTowerSemanticNormalFormEvaluation f hf g hg c) = c := by
  exact LinearEquiv.apply_symm_apply _ c

@[simp]
theorem adjoinRootTowerSemanticNormalForm_zero
    {R : Type*} [CommRing R] (f : R[X]) (hf : f.Monic)
    (g : Polynomial (AdjoinRoot f)) (hg : g.Monic) :
    adjoinRootTowerSemanticNormalForm f hf g hg 0 = 0 := by
  exact map_zero _

@[simp]
theorem adjoinRootTowerSemanticNormalFormEvaluation_zero
    {R : Type*} [CommRing R] (f : R[X]) (hf : f.Monic)
    (g : Polynomial (AdjoinRoot f)) (hg : g.Monic) :
    adjoinRootTowerSemanticNormalFormEvaluation f hf g hg 0 = 0 := by
  exact map_zero _

theorem adjoinRootTowerSemanticNormalForm_injective
    {R : Type*} [CommRing R] (f : R[X]) (hf : f.Monic)
    (g : Polynomial (AdjoinRoot f)) (hg : g.Monic) :
    Function.Injective (adjoinRootTowerSemanticNormalForm f hf g hg) :=
  ((AdjoinRoot.powerBasis' hf).basis.smulTower
    (AdjoinRoot.powerBasis' hg).basis).repr.injective

variable {K : Type*} [Field K]

section TraceCover

variable (sigma : K) (hsigma : sigma ≠ 0) (e d : ℕ)
  (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e)

private lemma etaExponent_ne_zero (e : ℕ) (heOdd : Odd e) : e ≠ 0 := by
  rintro rfl
  simp at heOdd

private lemma xiExponent_ne_zero (d : ℕ) (hdOdd : Odd d) : d ≠ 0 := by
  rintro rfl
  simp at hdOdd

/-- Semantic rectangular coefficients of an affine trace-cover class. -/
def splitTraceAffineSemanticNormalForm
    (a : SplitTraceAffineCoordinateRing K sigma d e) :
    Fin (splitTraceEtaKummerPolynomial sigma e).natDegree ×
        Fin (splitTraceXiKummerPolynomial sigma e d).natDegree →₀
      AdjoinRoot (splitTraceBaseKummerPolynomial sigma) :=
  adjoinRootTowerSemanticNormalForm
    (splitTraceEtaKummerPolynomial sigma e)
    (splitTraceEtaKummerPolynomial_monic sigma e
      (etaExponent_ne_zero e heOdd))
    (splitTraceXiKummerPolynomial sigma e d)
    (splitTraceXiKummerPolynomial_monic sigma e d
      (xiExponent_ne_zero d hdOdd))
    (splitTraceAffineToKummerTop sigma hsigma e d heOdd hdOdd hde a)

/-- Evaluating the affine semantic normal form recovers the affine comparison-map image. -/
theorem splitTraceAffineSemanticNormalForm_evaluation
    (a : SplitTraceAffineCoordinateRing K sigma d e) :
    adjoinRootTowerSemanticNormalFormEvaluation
        (splitTraceEtaKummerPolynomial sigma e)
        (splitTraceEtaKummerPolynomial_monic sigma e
          (etaExponent_ne_zero e heOdd))
        (splitTraceXiKummerPolynomial sigma e d)
        (splitTraceXiKummerPolynomial_monic sigma e d
          (xiExponent_ne_zero d hdOdd))
        (splitTraceAffineSemanticNormalForm sigma hsigma e d heOdd hdOdd hde a) =
      splitTraceAffineToKummerTop sigma hsigma e d heOdd hdOdd hde a := by
  exact adjoinRootTowerSemanticNormalForm_evaluation _ _ _ _ _

/-- The affine semantic normal form has zero coefficients exactly when its Kummer image is zero. -/
theorem splitTraceAffineSemanticNormalForm_eq_zero_iff
    (a : SplitTraceAffineCoordinateRing K sigma d e) :
    splitTraceAffineSemanticNormalForm sigma hsigma e d heOdd hdOdd hde a = 0 ↔
      splitTraceAffineToKummerTop sigma hsigma e d heOdd hdOdd hde a = 0 := by
  let f := splitTraceEtaKummerPolynomial sigma e
  let hf := splitTraceEtaKummerPolynomial_monic sigma e (etaExponent_ne_zero e heOdd)
  let g := splitTraceXiKummerPolynomial sigma e d
  let hg := splitTraceXiKummerPolynomial_monic sigma e d (xiExponent_ne_zero d hdOdd)
  change adjoinRootTowerSemanticNormalForm f hf g hg
      (splitTraceAffineToKummerTop sigma hsigma e d heOdd hdOdd hde a) = 0 ↔ _
  constructor
  · intro h
    have hEval := congrArg (adjoinRootTowerSemanticNormalFormEvaluation f hf g hg) h
    simpa only [adjoinRootTowerSemanticNormalForm_evaluation,
      adjoinRootTowerSemanticNormalFormEvaluation_zero] using hEval
  · intro h
    rw [h]
    exact map_zero _

/-- Affine comparison-map injectivity is now exactly injectivity of the semantic coefficient map.
The forward implication is useful once a syntactic quotient reduction proves coefficient-map
injectivity; the converse prevents semantic coordinates from concealing the original wall. -/
theorem splitTraceAffineSemanticNormalForm_injective_iff :
    Function.Injective
        (splitTraceAffineSemanticNormalForm sigma hsigma e d heOdd hdOdd hde) ↔
      Function.Injective
        (splitTraceAffineToKummerTop sigma hsigma e d heOdd hdOdd hde) := by
  let f := splitTraceEtaKummerPolynomial sigma e
  let hf := splitTraceEtaKummerPolynomial_monic sigma e (etaExponent_ne_zero e heOdd)
  let g := splitTraceXiKummerPolynomial sigma e d
  let hg := splitTraceXiKummerPolynomial_monic sigma e d (xiExponent_ne_zero d hdOdd)
  change Function.Injective
      (fun a ↦ adjoinRootTowerSemanticNormalForm f hf g hg
        (splitTraceAffineToKummerTop sigma hsigma e d heOdd hdOdd hde a)) ↔ _
  constructor
  · intro hSemantic a b hab
    apply hSemantic
    exact congrArg (adjoinRootTowerSemanticNormalForm f hf g hg) hab
  · intro hAffine
    exact (adjoinRootTowerSemanticNormalForm_injective f hf g hg).comp hAffine

/-- Semantic rectangular coefficients of a Laurent trace-cover class. -/
def splitTraceLaurentSemanticNormalForm
    (a : SplitTraceLaurentCoordinateRing K sigma d e) :
    Fin (splitTraceEtaKummerPolynomial sigma e).natDegree ×
        Fin (splitTraceXiKummerPolynomial sigma e d).natDegree →₀
      AdjoinRoot (splitTraceBaseKummerPolynomial sigma) := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  exact adjoinRootTowerSemanticNormalForm
    (splitTraceEtaKummerPolynomial sigma e)
    (splitTraceEtaKummerPolynomial_monic sigma e
      (etaExponent_ne_zero e heOdd))
    (splitTraceXiKummerPolynomial sigma e d)
    (splitTraceXiKummerPolynomial_monic sigma e d
      (xiExponent_ne_zero d hdOdd))
    (splitTraceLaurentToKummerTop sigma hsigma e d heOdd hdOdd hde a)

/-- Evaluating the Laurent semantic normal form recovers the Laurent comparison-map image. -/
theorem splitTraceLaurentSemanticNormalForm_evaluation
    (a : SplitTraceLaurentCoordinateRing K sigma d e) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) :=
      ⟨splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd⟩
    letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) :=
      ⟨splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde⟩
    adjoinRootTowerSemanticNormalFormEvaluation
        (splitTraceEtaKummerPolynomial sigma e)
        (splitTraceEtaKummerPolynomial_monic sigma e
          (etaExponent_ne_zero e heOdd))
        (splitTraceXiKummerPolynomial sigma e d)
        (splitTraceXiKummerPolynomial_monic sigma e d
          (xiExponent_ne_zero d hdOdd))
        (splitTraceLaurentSemanticNormalForm sigma hsigma e d heOdd hdOdd hde a) =
      splitTraceLaurentToKummerTop sigma hsigma e d heOdd hdOdd hde a := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  exact adjoinRootTowerSemanticNormalForm_evaluation _ _ _ _ _

/-- Laurent comparison-map injectivity is equivalent to injectivity of its semantic coefficient
map.  Thus localization introduces no new target-side ambiguity; the unsolved source-side task is
still the syntactic quotient normal-form theorem. -/
theorem splitTraceLaurentSemanticNormalForm_injective_iff :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) :=
      ⟨splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd⟩
    letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) :=
      ⟨splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde⟩
    Function.Injective
        (splitTraceLaurentSemanticNormalForm sigma hsigma e d heOdd hdOdd hde) ↔
      Function.Injective
        (splitTraceLaurentToKummerTop sigma hsigma e d heOdd hdOdd hde) := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  let f := splitTraceEtaKummerPolynomial sigma e
  let hf := splitTraceEtaKummerPolynomial_monic sigma e (etaExponent_ne_zero e heOdd)
  let g := splitTraceXiKummerPolynomial sigma e d
  let hg := splitTraceXiKummerPolynomial_monic sigma e d (xiExponent_ne_zero d hdOdd)
  change Function.Injective
      (fun a ↦ adjoinRootTowerSemanticNormalForm f hf g hg
        (splitTraceLaurentToKummerTop sigma hsigma e d heOdd hdOdd hde a)) ↔ _
  constructor
  · intro hSemantic a b hab
    apply hSemantic
    exact congrArg (adjoinRootTowerSemanticNormalForm f hf g hg) hab
  · intro hLaurent
    exact (adjoinRootTowerSemanticNormalForm_injective f hf g hg).comp hLaurent

end TraceCover

end

end BGS.Markoff
