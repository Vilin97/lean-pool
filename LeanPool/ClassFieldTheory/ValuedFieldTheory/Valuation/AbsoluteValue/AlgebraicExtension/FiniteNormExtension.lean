/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.Core
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Completeness
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.ValuationSubring
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Complex
/-!
# Finite-extension norm formula for complete valuations

The nonarchimedean branch uses mathlib's spectral norm.  The archimedean branch
uses the completed Ostrowski theorem, reducing the statement to the
standard `ℝ` and `ℂ` absolute values.
-/

@[expose] public section

noncomputable
section

namespace AlgebraicNumberTheory
namespace Valuations

/-- the finite-degree norm construction, archimedean standard branch: the usual absolute value on
`ℝ`, bundled in the same `AbsoluteValue` API as the rest of the absolute-value construction. -/
private abbrev finiteStandardRealAbsoluteValue : AbsoluteValue ℝ ℝ :=
  NormedField.toAbsoluteValue ℝ

/-- the finite-degree norm construction, archimedean standard branch: the usual absolute value on
`ℂ`. -/
private abbrev finiteStandardComplexAbsoluteValue : AbsoluteValue ℂ ℝ :=
  NormedField.toAbsoluteValue ℂ


/-- Taking a positive `s`-power of an absolute value does not change its
uniformity. -/
private theorem finiteRpowUniformSpaceEq
    {F : Type*} [Field F] (v : AbsoluteValue F ℝ)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    (AbsoluteValue.rpow v s hs0 hs1).uniformSpace =
      v.uniformSpace := by
  apply le_antisymm
  · exact
      ((AbsoluteValue.hasBasis_uniformity
        (AbsoluteValue.rpow v s hs0 hs1)).le_basis_iff
          (AbsoluteValue.hasBasis_uniformity v)).2 (by
        intro ε hε
        refine ⟨ε ^ s, Real.rpow_pos_of_pos hε s, ?_⟩
        intro p hp
        change v (p.2 - p.1) ^ s < ε ^ s at hp
        exact (Real.rpow_lt_rpow_iff (v.nonneg _) (le_of_lt hε) hs0).1 hp)
  · exact
      ((AbsoluteValue.hasBasis_uniformity v).le_basis_iff
        (AbsoluteValue.hasBasis_uniformity
          (AbsoluteValue.rpow v s hs0 hs1))).2 (by
        intro ε hε
        refine ⟨ε ^ s⁻¹, Real.rpow_pos_of_pos hε s⁻¹, ?_⟩
        intro p hp
        change v (p.2 - p.1) < ε ^ s⁻¹ at hp
        change v (p.2 - p.1) ^ s < ε
        have hpow :
            v (p.2 - p.1) ^ s < (ε ^ s⁻¹) ^ s :=
          Real.rpow_lt_rpow (v.nonneg _) hp hs0
        have hεpow : (ε ^ s⁻¹) ^ s = ε := by
          rw [← Real.rpow_mul (le_of_lt hε) s⁻¹ s,
            inv_mul_cancel₀ hs0.ne', Real.rpow_one]
        simpa [hεpow] using hpow)

/-- Completeness is unchanged by taking a positive `s`-power of an absolute
value. -/
private theorem finiteRpowCompleteIff
    {F : Type*} [Field F] (v : AbsoluteValue F ℝ)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    IsCompleteForAbsoluteValue
        (AbsoluteValue.rpow v s hs0 hs1) ↔
      IsCompleteForAbsoluteValue v := by
  dsimp [IsCompleteForAbsoluteValue]
  rw [finiteRpowUniformSpaceEq v s hs0 hs1]

/-- The absolute value underlying a complete normed field is complete. -/
private theorem finiteStandardComplete
    (F : Type*) [NormedField F] [CompleteSpace F] :
    IsCompleteForAbsoluteValue (NormedField.toAbsoluteValue F) := by
  apply (absoluteValueCompleteness_completeSpace_withAbs_iff_complete _).1
  let e : WithAbs (NormedField.toAbsoluteValue F) ≃ᵢ F :=
    { toEquiv := (WithAbs.equiv _).toEquiv
      isometry_toFun := by
        rw [isometry_iff_dist_eq]
        intro x y
        simp only [dist_eq_norm_sub, WithAbs.norm_eq_apply_ofAbs,
          WithAbs.ofAbs_sub]
        rfl }
  exact e.completeSpace

/-- The standard real absolute value is complete. -/
private theorem finiteStandardRealComplete :
    IsCompleteForAbsoluteValue finiteStandardRealAbsoluteValue :=
  finiteStandardComplete ℝ

/-- The standard complex absolute value is complete. -/
private theorem finiteStandardComplexComplete :
    IsCompleteForAbsoluteValue finiteStandardComplexAbsoluteValue :=
  finiteStandardComplete ℂ

/-- The `s`-power of the standard real absolute value is complete. -/
private theorem finiteStandardRealRpowComplete
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    IsCompleteForAbsoluteValue
      (AbsoluteValue.rpow
        finiteStandardRealAbsoluteValue s hs0 hs1) :=
  (finiteRpowCompleteIff
    finiteStandardRealAbsoluteValue s hs0 hs1).2
    finiteStandardRealComplete

/-- The `s`-power of the standard complex absolute value is complete. -/
private theorem finiteStandardComplexRpowComplete
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    IsCompleteForAbsoluteValue
      (AbsoluteValue.rpow
        finiteStandardComplexAbsoluteValue s hs0 hs1) :=
  (finiteRpowCompleteIff
    finiteStandardComplexAbsoluteValue s hs0 hs1).2
    finiteStandardComplexComplete

/-- the finite-degree norm construction, archimedean standard branch: the usual complex absolute
value extends the usual real absolute value. -/
private theorem finiteStandardComplexExtendsReal
    (x : ℝ) :
    finiteStandardComplexAbsoluteValue (algebraMap ℝ ℂ x) =
      finiteStandardRealAbsoluteValue x := by
  change ‖(algebraMap ℝ ℂ x)‖ = ‖x‖
  simp


/-- Completeness is preserved when an absolute value is pulled back along an
algebra equivalence. -/
private theorem finiteCompAlgEquivComplete
    {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] (e : L ≃ₐ[K] E)
    (w : AbsoluteValue E ℝ)
    (hwcomplete : IsCompleteForAbsoluteValue w) :
    IsCompleteForAbsoluteValue
      (AbsoluteValue.compAlgEquiv e w) :=
  (absoluteValueCompleteness_completeSpace_withAbs_iff_complete _).1
    (AbsoluteValue.compAlgEquiv_complete e w
      (completeSpace_withAbs_of_isCompleteForAbsoluteValue w hwcomplete))

/-- In the `ℝ` branch, an absolute value extending the `s`-power of the
standard real absolute value is the `s`-power of the transported standard
absolute value. -/
private theorem finiteRealAlgEquivRealUniqueRpowExtension
    {L : Type*} [Field L] [Algebra ℝ L] (e : L ≃ₐ[ℝ] ℝ)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (w : AbsoluteValue L ℝ)
    (hw : ∀ x : ℝ, w (algebraMap ℝ L x) =
      finiteStandardRealAbsoluteValue x ^ s) :
    w = AbsoluteValue.rpow
      (AbsoluteValue.compAlgEquiv
        e finiteStandardRealAbsoluteValue)
      s hs0 hs1 := by
  ext x
  have hx : x = algebraMap ℝ L (e x) := by
    calc
      x = e.symm (e x) := by simp
      _ = algebraMap ℝ L (e x) := by
        simpa using (AlgEquiv.commutes e.symm (e x))
  rw [hx, hw]
  exact congrArg (fun t : ℝ => t ^ s)
    (AbsoluteValue.compAlgEquiv_extends_apply e
      finiteStandardRealAbsoluteValue finiteStandardRealAbsoluteValue
      (fun x => rfl) (e x)).symm

/-- In the `ℂ` branch over `ℝ`, the `s`-power of the usual complex absolute
value is the unique extension of the `s`-power of the usual real absolute
value. -/
private theorem finiteRealAlgEquivComplexUniqueRpowExtension
    {L : Type*} [Field L] [Algebra ℝ L] (e : L ≃ₐ[ℝ] ℂ)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (w : AbsoluteValue L ℝ)
    (hw : ∀ x : ℝ, w (algebraMap ℝ L x) =
      finiteStandardRealAbsoluteValue x ^ s) :
    w = AbsoluteValue.rpow
      (AbsoluteValue.compAlgEquiv
        e finiteStandardComplexAbsoluteValue)
      s hs0 hs1 := by
  let : Algebra ℝ (WithAbs w) := inferInstance
  let e' : WithAbs w ≃ₐ[ℝ] ℂ :=
    (WithAbs.algEquiv ℝ w).trans e
  have hnorm :
      ∀ r : ℝ, ‖algebraMap ℝ (WithAbs w) r‖ = ‖r‖ ^ s := by
    intro r
    rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.algebraMap_right_apply]
    change w (algebraMap ℝ L r) =
      finiteStandardRealAbsoluteValue r ^ s
    exact hw r
  ext x
  let y : WithAbs w := WithAbs.toAbs w x
  change w x = ‖e x‖ ^ s
  calc
    w x = ‖y‖ := by
      simp [y, WithAbs.norm_eq_apply_ofAbs]
    _ = ‖e'.symm (e' y)‖ := by simp
    _ = ‖e' y‖ ^ s :=
      AlgEquiv.norm_symm_apply_eq_norm_rpow
        (F := WithAbs w) (s := s) hs0 hnorm e' (e' y)
    _ = ‖e x‖ ^ s := by simp [y, e']

/-- Over `ℂ`, an absolute value extending the `s`-power of the usual complex
absolute value is the transported `s`-power. -/
private theorem finiteComplexAlgEquivComplexUniqueRpowExtension
    {L : Type*} [Field L] [Algebra ℂ L] (e : L ≃ₐ[ℂ] ℂ)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (w : AbsoluteValue L ℝ)
    (hw : ∀ z : ℂ, w (algebraMap ℂ L z) =
      finiteStandardComplexAbsoluteValue z ^ s) :
    w = AbsoluteValue.rpow
      (AbsoluteValue.compAlgEquiv
        e finiteStandardComplexAbsoluteValue)
      s hs0 hs1 := by
  ext x
  have hx : x = algebraMap ℂ L (e x) := by
    calc
      x = e.symm (e x) := by simp
      _ = algebraMap ℂ L (e x) := by
        simpa using (AlgEquiv.commutes e.symm (e x))
  rw [hx, hw]
  exact congrArg (fun t : ℝ => t ^ s)
    (AbsoluteValue.compAlgEquiv_extends_apply e
      finiteStandardComplexAbsoluteValue finiteStandardComplexAbsoluteValue
      (fun z => rfl) (e x)).symm

/-- the finite-degree norm construction, archimedean standard branch over `ℝ | ℝ`: the
construction's
finite norm formula in degree one is the usual real absolute value. -/
private theorem finiteNormExtension_real_self_normFormulaValue_eq_standard
    (x : ℝ) :
    finiteExtensionNormFormulaValue (K := ℝ) (L := ℝ)
      finiteStandardRealAbsoluteValue x =
      finiteStandardRealAbsoluteValue x := by
  rw [finiteExtensionNormFormulaValue, Module.finrank_self ℝ]
  simp

/-- the finite-degree norm construction, archimedean standard branch over `ℂ | ℂ`: the
construction's
finite norm formula in degree one is the usual complex absolute value. -/
private theorem finiteNormExtension_complex_self_normFormulaValue_eq_standard
    (z : ℂ) :
    finiteExtensionNormFormulaValue (K := ℂ) (L := ℂ)
      finiteStandardComplexAbsoluteValue z =
      finiteStandardComplexAbsoluteValue z := by
  rw [finiteExtensionNormFormulaValue, Module.finrank_self ℂ]
  simp

/-- the finite-degree norm construction, archimedean standard branch over `ℂ | ℝ`: the
construction's
finite norm formula `|N_{ℂ/ℝ}(z)|^(1/2)` is the usual complex absolute value. -/
private theorem finiteNormExtension_real_complex_normFormulaValue_eq_standard
    (z : ℂ) :
    finiteExtensionNormFormulaValue (K := ℝ) (L := ℂ)
      finiteStandardRealAbsoluteValue z =
      finiteStandardComplexAbsoluteValue z := by
  rw [finiteExtensionNormFormulaValue, Algebra.norm_complex_apply,
    Complex.finrank_real_complex]
  change ‖Complex.normSq z‖ ^ (1 / (2 : ℝ)) = ‖z‖
  rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg z),
    Complex.normSq_eq_norm_sq]
  rw [show (1 / (2 : ℝ)) = ((2 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.pow_rpow_inv_natCast (norm_nonneg z)
    (by norm_num : (2 : ℕ) ≠ 0)

/-- The finite norm formula commutes with taking an `s`-power of the
base absolute value. -/
private theorem finiteNormExtension_finite_normFormulaValue_rpow
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (x : L) :
    finiteExtensionNormFormulaValue
        (AbsoluteValue.rpow v s hs0 hs1) x =
      finiteExtensionNormFormulaValue v x ^ s := by
  rw [finiteExtensionNormFormulaValue, finiteExtensionNormFormulaValue]
  simp only [AbsoluteValue.rpow_apply]
  let a : ℝ := v (Algebra.norm K x)
  have ha : 0 ≤ a := v.nonneg _
  change (a ^ s) ^ (1 / (Module.finrank K L : ℝ)) =
    (a ^ (1 / (Module.finrank K L : ℝ))) ^ s
  rw [← Real.rpow_mul ha s (1 / (Module.finrank K L : ℝ)),
    ← Real.rpow_mul ha (1 / (Module.finrank K L : ℝ)) s]
  rw [mul_comm s (1 / (Module.finrank K L : ℝ))]

/-- The finite norm formula is invariant under algebra equivalence of
the top field. -/
private theorem finiteNormExtension_finite_normFormulaValue_algEquiv
    {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E]
    [FiniteDimensional K L] [FiniteDimensional K E]
    (v : AbsoluteValue K ℝ) (e : L ≃ₐ[K] E) (x : L) :
    finiteExtensionNormFormulaValue v x =
      finiteExtensionNormFormulaValue v (e x) := by
  rw [finiteExtensionNormFormulaValue, finiteExtensionNormFormulaValue]
  rw [Algebra.norm_eq_of_algEquiv e x]
  rw [e.toLinearEquiv.finrank_eq]

/-- the finite-degree norm construction, archimedean `s`-power branch over `ℝ | ℝ`: the finite
norm formula is `|x|^s`. -/
private theorem finiteNormExtension_real_self_normFormulaValue_eq_rpow
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) (x : ℝ) :
    finiteExtensionNormFormulaValue (K := ℝ) (L := ℝ)
      (AbsoluteValue.rpow
        finiteStandardRealAbsoluteValue s hs0 hs1) x =
      finiteStandardRealAbsoluteValue x ^ s := by
  rw [finiteNormExtension_finite_normFormulaValue_rpow]
  rw [finiteNormExtension_real_self_normFormulaValue_eq_standard]

/-- the finite-degree norm construction, archimedean `s`-power branch over `ℂ | ℂ`: the finite
norm formula is `|z|^s`. -/
private theorem finiteNormExtension_complex_self_normFormulaValue_eq_rpow
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) (z : ℂ) :
    finiteExtensionNormFormulaValue (K := ℂ) (L := ℂ)
      (AbsoluteValue.rpow
        finiteStandardComplexAbsoluteValue s hs0 hs1) z =
      finiteStandardComplexAbsoluteValue z ^ s := by
  rw [finiteNormExtension_finite_normFormulaValue_rpow]
  rw [finiteNormExtension_complex_self_normFormulaValue_eq_standard]

/-- the finite-degree norm construction, archimedean `s`-power branch over `ℂ | ℝ`: the finite
norm formula is the `s`-power of the usual complex absolute value. -/
private theorem finiteNormExtension_real_complex_normFormulaValue_eq_rpow
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) (z : ℂ) :
    finiteExtensionNormFormulaValue (K := ℝ) (L := ℂ)
      (AbsoluteValue.rpow
        finiteStandardRealAbsoluteValue s hs0 hs1) z =
      finiteStandardComplexAbsoluteValue z ^ s := by
  rw [finiteNormExtension_finite_normFormulaValue_rpow]
  rw [finiteNormExtension_real_complex_normFormulaValue_eq_standard]

/-- The nontrivial-valuation convention excludes the trivial valuation in the
nontrivial-valuation convention; for the
nonarchimedean spectral branch this supplies the corresponding mathlib
`NontriviallyNormedField` instance on `WithAbs v`. -/
@[reducible] private def finiteWithAbsNontriviallyNormedField
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (hv : v.IsNontrivial) :
    NontriviallyNormedField (WithAbs v) :=
  NontriviallyNormedField.ofNormNeOne
    (by
      rcases hv with ⟨x, hx0, hx1⟩
      refine ⟨WithAbs.toAbs v x, ?_, ?_⟩
      · intro hx
        apply hx0
        simpa using congrArg (WithAbs.equiv v) hx
      · simpa [WithAbs.norm_eq_apply_ofAbs] using hx1)

/-- `WithAbs` is only a type synonym, so algebraicity is transported from the
original base field without adding data. -/
private instance finiteWithAbsAlgebraIsAlgebraic
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (v : AbsoluteValue K ℝ) :
    Algebra.IsAlgebraic (WithAbs v) L := by
  exact Algebra.IsAlgebraic.tower_top
    (K := K) (L := WithAbs v) (A := L)

/-- the real absolute-value classification, translated to the `WithAbs` normed-field structure. -/
private theorem finiteWithAbsIsUltrametricDist
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) :
    IsUltrametricDist (WithAbs v) := by
  refine IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm ?_
  intro x y
  simpa [WithAbs.norm_eq_apply_ofAbs] using
    (LubinTate.Valuations.strong_triangle_of_nonarchimedean v hnonarch
      (WithAbs.equiv v x) (WithAbs.equiv v y))

/-- the finite-degree norm construction, existence branch: the spectral extension restricts to the
given chosen valuation on the base field. -/
private theorem finiteSpectralNormExtendsBase
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ) (x : K) :
    _root_.spectralNorm (WithAbs v) L (algebraMap K L x) = v x := by
  let : Algebra.IsAlgebraic (WithAbs v) L :=
    finiteWithAbsAlgebraIsAlgebraic v
  simpa [WithAbs.algebraMap_left_apply, WithAbs.norm_eq_apply_ofAbs] using
    (_root_.spectralNorm_extends
      (K := WithAbs v) (L := L) ((WithAbs.equiv v).symm x))

/-- the finite-degree norm construction, existence branch: the spectral extension satisfies the
strong triangle inequality in the nonarchimedean case. -/
private theorem finiteSpectralNormStrongTriangle
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) (x y : L) :
    _root_.spectralNorm (WithAbs v) L (x + y) ≤
      max (_root_.spectralNorm (WithAbs v) L x)
        (_root_.spectralNorm (WithAbs v) L y) := by
  let : IsUltrametricDist (WithAbs v) :=
    finiteWithAbsIsUltrametricDist v hnonarch
  let : Algebra.IsAlgebraic (WithAbs v) L :=
    finiteWithAbsAlgebraIsAlgebraic v
  exact _root_.isNonarchimedean_spectralNorm
    (K := WithAbs v) (L := L) x y

/-- the finite-degree norm construction, existence branch: the spectral extension vanishes exactly
at zero. -/
private theorem finiteSpectralNormEqZeroIff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ) (x : L) :
    _root_.spectralNorm (WithAbs v) L x = 0 ↔ x = 0 := by
  let : Algebra.IsAlgebraic (WithAbs v) L :=
    finiteWithAbsAlgebraIsAlgebraic v
  constructor
  · intro hx
    exact _root_.eq_zero_of_map_spectralNorm_eq_zero
      (K := WithAbs v) (L := L) hx
      (Algebra.IsAlgebraic.isAlgebraic x)
  · intro hx
    rw [hx]
    exact _root_.spectralNorm_zero (K := WithAbs v) (L := L)

/-- the finite-degree norm construction, existence branch: multiplicativity of the spectral
extension over an algebraic extension. -/
private theorem finiteSpectralNormMul
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : v.IsNontrivial) (x y : L) :
    _root_.spectralNorm (WithAbs v) L (x * y) =
      _root_.spectralNorm (WithAbs v) L x *
        _root_.spectralNorm (WithAbs v) L y := by
  let : NontriviallyNormedField (WithAbs v) :=
    finiteWithAbsNontriviallyNormedField v hv
  let : Algebra (WithAbs v) L :=
    WithAbs.algebraLeft L v
  let : CompleteSpace (WithAbs v) :=
    completeSpace_withAbs_of_isCompleteForAbsoluteValue v hcomplete
  let : IsUltrametricDist (WithAbs v) :=
    finiteWithAbsIsUltrametricDist v hnonarch
  let : Algebra.IsAlgebraic (WithAbs v) L :=
    finiteWithAbsAlgebraIsAlgebraic v
  simpa [_root_.spectralAlgNorm_def] using
    (_root_.spectralAlgNorm_mul (K := WithAbs v) (L := L) x y)

private theorem finiteBaseIsNonarchimedean
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) :
    IsNonarchimedean (v : K → ℝ) :=
  (LubinTate.Valuations.strong_triangle_iff_isNonarchimedean v).1
    (LubinTate.Valuations.strong_triangle_of_nonarchimedean v hnonarch)

private noncomputable def finiteSpectralExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : v.IsNontrivial) : AbsoluteValue L ℝ :=
  AbsoluteValue.spectralExtension v
    (completeSpace_withAbs_of_isCompleteForAbsoluteValue v hcomplete)
    (finiteBaseIsNonarchimedean v hnonarch) hv

private theorem finiteSpectralExtension_extends_base
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : v.IsNontrivial) (x : K) :
    finiteSpectralExtension (K := K) (L := L)
      v hcomplete hnonarch hv (algebraMap K L x) = v x := by
  simpa [finiteSpectralExtension] using
    (AbsoluteValue.spectralExtension_extends
      (K := K) (L := L) v
      (completeSpace_withAbs_of_isCompleteForAbsoluteValue v hcomplete)
      (finiteBaseIsNonarchimedean v hnonarch) hv x)

/-- Finite-dimensional completeness for the spectral norm. -/
private theorem finiteSpectralNormCompleteSpace
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : v.IsNontrivial) :
    letI : NontriviallyNormedField (WithAbs v) :=
      finiteWithAbsNontriviallyNormedField v hv
    letI : Algebra (WithAbs v) L :=
      WithAbs.algebraLeft L v
    letI : CompleteSpace (WithAbs v) :=
      completeSpace_withAbs_of_isCompleteForAbsoluteValue v hcomplete
    letI : IsUltrametricDist (WithAbs v) :=
      finiteWithAbsIsUltrametricDist v hnonarch
    letI : Algebra.IsAlgebraic (WithAbs v) L :=
      finiteWithAbsAlgebraIsAlgebraic v
    @CompleteSpace L (_root_.spectralNorm.uniformSpace (WithAbs v) L) := by
  let : NontriviallyNormedField (WithAbs v) :=
    finiteWithAbsNontriviallyNormedField v hv
  let : Algebra (WithAbs v) L :=
    WithAbs.algebraLeft L v
  let : CompleteSpace (WithAbs v) :=
    completeSpace_withAbs_of_isCompleteForAbsoluteValue v hcomplete
  let : IsUltrametricDist (WithAbs v) :=
    finiteWithAbsIsUltrametricDist v hnonarch
  let : Algebra.IsAlgebraic (WithAbs v) L :=
    finiteWithAbsAlgebraIsAlgebraic v
  infer_instance

/-- the finite-degree norm construction, finite-extension completeness for the constructed
absolute-value extension. -/
private theorem finiteSpectralExtensionComplete
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : v.IsNontrivial) :
    IsCompleteForAbsoluteValue
      (finiteSpectralExtension (K := K) (L := L)
        v hcomplete hnonarch hv) := by
  let : NontriviallyNormedField (WithAbs v) :=
    finiteWithAbsNontriviallyNormedField v hv
  let : Algebra (WithAbs v) L :=
    WithAbs.algebraLeft L v
  let : CompleteSpace (WithAbs v) :=
    completeSpace_withAbs_of_isCompleteForAbsoluteValue v hcomplete
  let : IsUltrametricDist (WithAbs v) :=
    finiteWithAbsIsUltrametricDist v hnonarch
  let : Algebra.IsAlgebraic (WithAbs v) L :=
    finiteWithAbsAlgebraIsAlgebraic v
  apply (absoluteValueCompleteness_completeSpace_withAbs_iff_complete _).1
  let : NormedField L :=
    _root_.spectralNorm.normedField (WithAbs v) L
  let : CompleteSpace L :=
    finiteSpectralNormCompleteSpace
      (K := K) (L := L) v hcomplete hnonarch hv
  let e :
      WithAbs (finiteSpectralExtension (K := K) (L := L)
        v hcomplete hnonarch hv) ≃ᵢ L :=
    { toEquiv := (WithAbs.equiv _).toEquiv
      isometry_toFun := by
        rw [isometry_iff_dist_eq]
        intro x y
        simp only [dist_eq_norm_sub, WithAbs.norm_eq_apply_ofAbs,
          WithAbs.ofAbs_sub]
        rfl }
  exact e.completeSpace

/-- the finite-degree norm construction, finite norm-formula source: the spectral extension is
computed from the constant coefficient of the minimal polynomial. -/
private theorem finiteSpectralNormEqMinpolyCoeffZeroRpow
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : v.IsNontrivial) (x : L) :
    _root_.spectralNorm (WithAbs v) L x =
      v ((minpoly K x).coeff 0) ^
        (1 / ((minpoly K x).natDegree : ℝ)) := by
  let : NontriviallyNormedField (WithAbs v) :=
    finiteWithAbsNontriviallyNormedField v hv
  let : Algebra (WithAbs v) L :=
    WithAbs.algebraLeft L v
  let : CompleteSpace (WithAbs v) :=
    completeSpace_withAbs_of_isCompleteForAbsoluteValue v hcomplete
  let : IsUltrametricDist (WithAbs v) :=
    finiteWithAbsIsUltrametricDist v hnonarch
  let : Algebra.IsAlgebraic (WithAbs v) L :=
    finiteWithAbsAlgebraIsAlgebraic v
  let : Algebra.IsIntegral K L := Algebra.IsAlgebraic.isIntegral
  have hminpoly :
      (minpoly K x).map (WithAbs.equiv v).symm =
        minpoly (WithAbs v) x := by
    apply minpoly.map_eq_of_equiv_equiv
      (f := (WithAbs.equiv v).symm)
      (g := RingEquiv.refl L)
    ext a
    simp [WithAbs.algebraMap_left_apply]
  have hs :=
    _root_.spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow
      (K := WithAbs v) (L := L) x
  rw [← hminpoly] at hs
  simpa [WithAbs.norm_eq_apply_ofAbs] using hs

/-- the finite-degree norm construction, the same constant-term formula for the constructed
absolute-value extension. -/
private theorem finiteSpectralExtensionEqMinpolyCoeffZeroRpow
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : v.IsNontrivial) (x : L) :
    finiteSpectralExtension (K := K) (L := L)
      v hcomplete hnonarch hv x =
      v ((minpoly K x).coeff 0) ^
        (1 / ((minpoly K x).natDegree : ℝ)) :=
  finiteSpectralNormEqMinpolyCoeffZeroRpow
    v hcomplete hnonarch hv x

/-- the finite-degree norm construction, finite norm-formula source: the absolute value of the
finite-extension norm is the corresponding power of the absolute value of the
constant coefficient of the minimal polynomial. -/
private theorem finiteNormExtension_abs_norm_eq_minpoly_coeff_zero_pow_relfinrank
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (x : L) :
    v (Algebra.norm K x) =
      v ((minpoly K x).coeff 0) ^
        (Module.finrank (IntermediateField.adjoin K ({x} : Set L)) L) := by
  let : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let : Algebra.IsIntegral K L := Algebra.IsAlgebraic.isIntegral
  have hxint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  rw [Algebra.norm_eq_norm_adjoin K x, map_pow]
  have hgen :
      Algebra.norm K (IntermediateField.AdjoinSimple.gen K x) =
        (-1 : K) ^ (minpoly K x).natDegree * (minpoly K x).coeff 0 := by
    simpa [IntermediateField.adjoin.powerBasis_gen,
      IntermediateField.minpoly_gen, IntermediateField.adjoin.powerBasis_dim]
      using
        (Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
          (IntermediateField.adjoin.powerBasis hxint))
  rw [hgen, v.map_mul, v.map_pow, AbsoluteValue.map_neg]
  simp

/-- For a nonnegative real number, taking an `n`th natural power and then the
reciprocal `m*n` real power cancels the `n` factor. -/
private theorem finiteNatPowRpowInvMulCancel
    {a : ℝ} (ha : 0 ≤ a) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (a ^ n) ^ (1 / ((m * n : ℕ) : ℝ)) = a ^ (1 / (m : ℝ)) := by
  by_cases ha0 : a = 0
  · have hmn_ne : ((m * n : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.mul_ne_zero (Nat.ne_of_gt hm) (Nat.ne_of_gt hn)
    have hm_ne : (m : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hm
    rw [ha0, zero_pow (Nat.ne_of_gt hn),
      Real.zero_rpow (one_div_ne_zero hmn_ne),
      Real.zero_rpow (one_div_ne_zero hm_ne)]
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (fun h => ha0 h.symm)
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha_pos.le]
    have hm_ne : (m : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hm
    have hn_ne : (n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hn
    congr 1
    field_simp [hm_ne, hn_ne]
    norm_num [Nat.cast_mul, mul_comm]

/-- Symmetric form of `finiteNatPowRpowInvMulCancel`, cancelling the left
natural-power factor. -/
private theorem finiteNatPowRpowInvMulCancelLeft
    {a : ℝ} (ha : 0 ≤ a) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (a ^ m) ^ (1 / ((m * n : ℕ) : ℝ)) = a ^ (1 / (n : ℝ)) := by
  simpa [Nat.mul_comm] using
    (finiteNatPowRpowInvMulCancel (a := a) ha (m := n) (n := m) hn hm)

/-- the finite-degree norm construction, finite case: the norm formula agrees with the
constructed spectral absolute-value extension. -/
private theorem finiteNormExtension_finite_normFormulaValue_eq_spectralAbsoluteValue
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : v.IsNontrivial) (x : L) :
    finiteExtensionNormFormulaValue v x =
      finiteSpectralExtension (K := K) (L := L)
        v hcomplete hnonarch hv x := by
  let : Algebra.IsIntegral K L := Algebra.IsAlgebraic.isIntegral
  have hxint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  let E : IntermediateField K L := IntermediateField.adjoin K ({x} : Set L)
  let : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional hxint
  let : FiniteDimensional E L := FiniteDimensional.right K E L
  have hd_pos : 0 < (minpoly K x).natDegree :=
    minpoly.natDegree_pos hxint
  have hr_pos : 0 < Module.finrank E L :=
    Module.finrank_pos (R := E) (M := L)
  rw [finiteExtensionNormFormulaValue,
    finiteNormExtension_abs_norm_eq_minpoly_coeff_zero_pow_relfinrank,
    finiteSpectralExtensionEqMinpolyCoeffZeroRpow]
  rw [← Module.finrank_mul_finrank K E L,
    IntermediateField.adjoin.finrank hxint]
  exact finiteNatPowRpowInvMulCancel
    (v.nonneg ((minpoly K x).coeff 0)) hd_pos hr_pos

/-- the finite-degree norm construction, finite case: the finite norm formula inherits the strong
triangle inequality from the spectral extension. -/
theorem finiteNormExtension_finite_normFormulaValue_strong_triangle
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : v.IsNontrivial) (x y : L) :
    finiteExtensionNormFormulaValue v (x + y) ≤
      max (finiteExtensionNormFormulaValue v x)
        (finiteExtensionNormFormulaValue v y) := by
  rw [finiteNormExtension_finite_normFormulaValue_eq_spectralAbsoluteValue
      v hcomplete hnonarch hv (x + y),
    finiteNormExtension_finite_normFormulaValue_eq_spectralAbsoluteValue
      v hcomplete hnonarch hv x,
    finiteNormExtension_finite_normFormulaValue_eq_spectralAbsoluteValue
      v hcomplete hnonarch hv y]
  simpa [finiteSpectralExtension, AbsoluteValue.spectralExtension] using
    finiteSpectralNormStrongTriangle v hnonarch x y

/-- the finite-degree norm construction, finite nonarchimedean branch: the norm formula,
bundled as an absolute value on the finite extension. -/
noncomputable def finiteNormExtensionFiniteNormFormulaAbsoluteValue
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : v.IsNontrivial) : AbsoluteValue L ℝ where
  toFun := finiteExtensionNormFormulaValue v
  map_mul' x y := by
    rw [finiteNormExtension_finite_normFormulaValue_eq_spectralAbsoluteValue
        v hcomplete hnonarch hv (x * y),
      finiteNormExtension_finite_normFormulaValue_eq_spectralAbsoluteValue
        v hcomplete hnonarch hv x,
      finiteNormExtension_finite_normFormulaValue_eq_spectralAbsoluteValue
        v hcomplete hnonarch hv y]
    exact (finiteSpectralExtension (K := K) (L := L)
      v hcomplete hnonarch hv).map_mul x y
  nonneg' x := finiteExtensionNormFormulaValue_nonneg v x
  eq_zero' x := by
    rw [finiteNormExtension_finite_normFormulaValue_eq_spectralAbsoluteValue
      v hcomplete hnonarch hv x]
    exact (finiteSpectralExtension (K := K) (L := L)
      v hcomplete hnonarch hv).eq_zero' x
  add_le' x y := by
    have hstrong :=
      finiteNormExtension_finite_normFormulaValue_strong_triangle
        v hcomplete hnonarch hv x y
    have hx_nonneg : 0 ≤ finiteExtensionNormFormulaValue v x :=
      finiteExtensionNormFormulaValue_nonneg v x
    have hy_nonneg : 0 ≤ finiteExtensionNormFormulaValue v y :=
      finiteExtensionNormFormulaValue_nonneg v y
    exact hstrong.trans
      (max_le
        (le_add_of_nonneg_right hy_nonneg)
        (le_add_of_nonneg_left hx_nonneg))

/-- The bundled finite norm formula is pointwise the function
`x ↦ |N_{L/K}(x)|^(1/[L:K])`. -/
theorem finiteNormExtension_finite_normFormulaAbsoluteValue_apply
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : v.IsNontrivial) (x : L) :
    finiteNormExtensionFiniteNormFormulaAbsoluteValue (K := K) (L := L)
      v hcomplete hnonarch hv x =
      finiteExtensionNormFormulaValue v x :=
  rfl

/-- In the finite case, the norm-formula absolute value agrees with the
spectral extension. -/
private theorem finiteNormExtension_finite_normFormulaAbsoluteValue_eq_spectralAbsoluteValue
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : v.IsNontrivial) :
    finiteNormExtensionFiniteNormFormulaAbsoluteValue (K := K) (L := L)
      v hcomplete hnonarch hv =
      finiteSpectralExtension (K := K) (L := L)
        v hcomplete hnonarch hv := by
  ext x
  exact finiteNormExtension_finite_normFormulaValue_eq_spectralAbsoluteValue
    v hcomplete hnonarch hv x

/-- the finite-degree norm construction, finite case: the norm-formula absolute value restricts to
the given base valuation. -/
theorem finiteNormExtension_finite_normFormulaAbsoluteValue_extends_base
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : v.IsNontrivial) (x : K) :
    finiteNormExtensionFiniteNormFormulaAbsoluteValue (K := K) (L := L)
      v hcomplete hnonarch hv (algebraMap K L x) = v x := by
  rw [finiteNormExtension_finite_normFormulaAbsoluteValue_eq_spectralAbsoluteValue
    v hcomplete hnonarch hv]
  exact finiteSpectralExtension_extends_base
    (K := K) (L := L) v hcomplete hnonarch hv x

/-- the finite-degree norm construction, finite case: the finite extension is complete for the
norm-formula absolute value. -/
theorem finiteNormExtension_finite_normFormulaAbsoluteValue_complete
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : v.IsNontrivial) :
    IsCompleteForAbsoluteValue
      (finiteNormExtensionFiniteNormFormulaAbsoluteValue (K := K) (L := L)
        v hcomplete hnonarch hv) := by
  rw [finiteNormExtension_finite_normFormulaAbsoluteValue_eq_spectralAbsoluteValue
    v hcomplete hnonarch hv]
  exact finiteSpectralExtensionComplete
    (K := K) (L := L) v hcomplete hnonarch hv


/-- the finite-degree norm construction, finite case: the norm-formula absolute value is the unique
absolute-value extension of the complete nonarchimedean base valuation. -/
theorem finiteNormExtension_unique_extension_finite_normFormulaAbsoluteValue
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : v.IsNontrivial)
    (w : AbsoluteValue L ℝ)
    (hw_ext : ∀ x : K, w (algebraMap K L x) = v x) :
    w = finiteNormExtensionFiniteNormFormulaAbsoluteValue (K := K) (L := L)
      v hcomplete hnonarch hv := by
  rw [finiteNormExtension_finite_normFormulaAbsoluteValue_eq_spectralAbsoluteValue
    v hcomplete hnonarch hv]
  simpa [finiteSpectralExtension] using
    (AbsoluteValue.eq_spectralExtension_of_extends
      (K := K) (L := L) v
      (completeSpace_withAbs_of_isCompleteForAbsoluteValue v hcomplete)
      (finiteBaseIsNonarchimedean v hnonarch) hv w hw_ext)

/-- Explicit result package for the finite-degree norm construction, finite nonarchimedean case:
the unique extension is the norm formula and the finite extension is complete. -/
structure FiniteNormExtensionFiniteExtensionResult
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) where
  /-- The distinguished absolute value on the finite extension. -/
  extension : AbsoluteValue L ℝ
  /-- The distinguished absolute value restricts to the given base absolute value. -/
  extends_base : ∀ x : K, extension (algebraMap K L x) = v x
  /-- Every extension of the base absolute value equals the distinguished extension. -/
  unique :
    ∀ w : AbsoluteValue L ℝ,
      (∀ x : K, w (algebraMap K L x) = v x) → w = extension
  /-- The distinguished extension is given by the finite-extension norm formula. -/
  norm_formula : ∀ x : L, extension x = finiteExtensionNormFormulaValue v x
  /-- The distinguished extension is complete. -/
  complete_extension : IsCompleteForAbsoluteValue extension

/-- Finite-extension result packages over the same base absolute value are
unique.  In particular, choosing a package does not affect its public value. -/
theorem FiniteNormExtensionFiniteExtensionResult.ext_unique
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    {v : AbsoluteValue K ℝ}
    (R S : FiniteNormExtensionFiniteExtensionResult (K := K) (L := L) v) :
    R = S := by
  cases R with
  | mk extensionR extendsBaseR uniqueR normFormulaR completeR =>
      cases S with
      | mk extensionS extendsBaseS uniqueS normFormulaS completeS =>
          have hExtension : extensionS = extensionR :=
            uniqueR extensionS extendsBaseS
          subst extensionS
          rfl

/-- the finite-degree norm construction, explicit archimedean finite theorem over `ℝ`: in
finite degree, the unique extension is the norm formula and the extension is
complete. -/
private noncomputable def finiteNormExtension_real_finite_rpow_extension
    {L : Type*} [Field L] [Algebra ℝ L]
    [FiniteDimensional ℝ L]
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    FiniteNormExtensionFiniteExtensionResult (K := ℝ) (L := L)
      (AbsoluteValue.rpow
        finiteStandardRealAbsoluteValue s hs0 hs1) :=
  Classical.choice <| by
    rcases Real.nonempty_algEquiv_or L with hreal | hcomplex
    · rcases hreal with ⟨e⟩
      exact ⟨
        { extension :=
            AbsoluteValue.rpow
              (AbsoluteValue.compAlgEquiv
                e finiteStandardRealAbsoluteValue)
              s hs0 hs1
          extends_base := by
            intro x
            simp only [AbsoluteValue.rpow_apply]
            rw [AbsoluteValue.compAlgEquiv_extends_apply e
              finiteStandardRealAbsoluteValue
              finiteStandardRealAbsoluteValue (fun x => rfl) x]
          unique :=
            finiteRealAlgEquivRealUniqueRpowExtension
              e s hs0 hs1
          norm_formula := by
            intro x
            calc
              AbsoluteValue.rpow
                  (AbsoluteValue.compAlgEquiv
                    e finiteStandardRealAbsoluteValue)
                  s hs0 hs1 x
                  = finiteStandardRealAbsoluteValue (e x) ^ s := rfl
              _ = finiteExtensionNormFormulaValue (K := ℝ) (L := ℝ)
                    (AbsoluteValue.rpow
                      finiteStandardRealAbsoluteValue s hs0 hs1) (e x) := by
                    exact (finiteNormExtension_real_self_normFormulaValue_eq_rpow
                      s hs0 hs1 (e x)).symm
              _ = finiteExtensionNormFormulaValue (K := ℝ) (L := L)
                    (AbsoluteValue.rpow
                      finiteStandardRealAbsoluteValue s hs0 hs1) x := by
                    exact (finiteNormExtension_finite_normFormulaValue_algEquiv
                      (AbsoluteValue.rpow
                        finiteStandardRealAbsoluteValue s hs0 hs1) e x).symm
          complete_extension := by
            exact (finiteRpowCompleteIff
              (AbsoluteValue.compAlgEquiv
                e finiteStandardRealAbsoluteValue)
              s hs0 hs1).2
              (finiteCompAlgEquivComplete e
                finiteStandardRealAbsoluteValue
                finiteStandardRealComplete) }⟩
    · rcases hcomplex with ⟨e⟩
      exact ⟨
        { extension :=
            AbsoluteValue.rpow
              (AbsoluteValue.compAlgEquiv
                e finiteStandardComplexAbsoluteValue)
              s hs0 hs1
          extends_base := by
            intro x
            simp only [AbsoluteValue.rpow_apply]
            rw [AbsoluteValue.compAlgEquiv_extends_apply e
              finiteStandardComplexAbsoluteValue
              finiteStandardRealAbsoluteValue
              finiteStandardComplexExtendsReal x]
          unique :=
            finiteRealAlgEquivComplexUniqueRpowExtension
              e s hs0 hs1
          norm_formula := by
            intro x
            calc
              AbsoluteValue.rpow
                  (AbsoluteValue.compAlgEquiv
                    e finiteStandardComplexAbsoluteValue)
                  s hs0 hs1 x
                  = finiteStandardComplexAbsoluteValue (e x) ^ s := rfl
              _ = finiteExtensionNormFormulaValue (K := ℝ) (L := ℂ)
                    (AbsoluteValue.rpow
                      finiteStandardRealAbsoluteValue s hs0 hs1) (e x) := by
                    exact (finiteNormExtension_real_complex_normFormulaValue_eq_rpow
                      s hs0 hs1 (e x)).symm
              _ = finiteExtensionNormFormulaValue (K := ℝ) (L := L)
                    (AbsoluteValue.rpow
                      finiteStandardRealAbsoluteValue s hs0 hs1) x := by
                    exact (finiteNormExtension_finite_normFormulaValue_algEquiv
                      (AbsoluteValue.rpow
                        finiteStandardRealAbsoluteValue s hs0 hs1) e x).symm
          complete_extension := by
            exact (finiteRpowCompleteIff
              (AbsoluteValue.compAlgEquiv
                e finiteStandardComplexAbsoluteValue)
              s hs0 hs1).2
              (finiteCompAlgEquivComplete e
                finiteStandardComplexAbsoluteValue
                finiteStandardComplexComplete) }⟩

/-- the finite-degree norm construction, explicit archimedean finite theorem over `ℂ`: in
finite degree, the unique extension is the norm formula and the extension is
complete. -/
private noncomputable def finiteNormExtension_complex_finite_rpow_extension
    {L : Type*} [Field L] [Algebra ℂ L]
    [FiniteDimensional ℂ L]
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    FiniteNormExtensionFiniteExtensionResult (K := ℂ) (L := L)
      (AbsoluteValue.rpow
        finiteStandardComplexAbsoluteValue s hs0 hs1) := by
  letI : Algebra.IsIntegral ℂ L := Algebra.IsAlgebraic.isIntegral
  let e0 : ℂ ≃ₐ[ℂ] L :=
    AlgEquiv.ofBijective (Algebra.ofId ℂ L)
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := L))
  let e : L ≃ₐ[ℂ] ℂ := e0.symm
  exact
    { extension :=
        AbsoluteValue.rpow
          (AbsoluteValue.compAlgEquiv
            e finiteStandardComplexAbsoluteValue)
          s hs0 hs1
      extends_base := by
        intro z
        simp only [AbsoluteValue.rpow_apply]
        rw [AbsoluteValue.compAlgEquiv_extends_apply e
          finiteStandardComplexAbsoluteValue
          finiteStandardComplexAbsoluteValue (fun z => rfl) z]
      unique :=
        finiteComplexAlgEquivComplexUniqueRpowExtension
          e s hs0 hs1
      norm_formula := by
        intro x
        calc
          AbsoluteValue.rpow
              (AbsoluteValue.compAlgEquiv
                e finiteStandardComplexAbsoluteValue)
              s hs0 hs1 x
              = finiteStandardComplexAbsoluteValue (e x) ^ s := rfl
          _ = finiteExtensionNormFormulaValue (K := ℂ) (L := ℂ)
                (AbsoluteValue.rpow
                  finiteStandardComplexAbsoluteValue s hs0 hs1) (e x) := by
                exact (finiteNormExtension_complex_self_normFormulaValue_eq_rpow
                  s hs0 hs1 (e x)).symm
          _ = finiteExtensionNormFormulaValue (K := ℂ) (L := L)
                (AbsoluteValue.rpow
                  finiteStandardComplexAbsoluteValue s hs0 hs1) x := by
                exact (finiteNormExtension_finite_normFormulaValue_algEquiv
                  (AbsoluteValue.rpow
                    finiteStandardComplexAbsoluteValue s hs0 hs1) e x).symm
      complete_extension := by
        exact (finiteRpowCompleteIff
          (AbsoluteValue.compAlgEquiv
            e finiteStandardComplexAbsoluteValue)
          s hs0 hs1).2
          (finiteCompAlgEquivComplete e
            finiteStandardComplexAbsoluteValue
            finiteStandardComplexComplete) }

/-- Algebraicity is preserved when the base field is replaced by a ring
equivalent field and the top algebra structure is transported through the same
equivalence. -/
private theorem finiteIsAlgebraicOfBaseRingEquiv
    {K E L : Type*} [Field K] [Field E] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (σ : K ≃+* E) :
    letI : Algebra E K := RingHom.toAlgebra σ.symm.toRingHom
    letI : Algebra E L :=
      RingHom.toAlgebra ((algebraMap K L).comp σ.symm.toRingHom)
    Algebra.IsAlgebraic E L := by
  let : Algebra E K := RingHom.toAlgebra σ.symm.toRingHom
  let : Algebra E L :=
    RingHom.toAlgebra ((algebraMap K L).comp σ.symm.toRingHom)
  have : IsScalarTower E K L :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      simp [RingHom.algebraMap_toAlgebra])
  let e : K ≃ₐ[E] E := AlgEquiv.ofRingEquiv (f := σ) (by
    intro r
    simp [RingHom.algebraMap_toAlgebra])
  have : Algebra.IsAlgebraic E K := e.symm.isAlgebraic
  exact Algebra.IsAlgebraic.trans E K L

/-- Finite-dimensionality is preserved when the base field is replaced by an
equivalent field and the top algebra structure is transported along the same
equivalence. -/
private theorem finiteNormExtension_finiteDimensional_of_base_ringEquiv
    {K E L : Type*} [Field K] [Field E] [Field L] [Algebra K L]
    [FiniteDimensional K L] (σ : K ≃+* E) :
    letI : Algebra E L :=
      RingHom.toAlgebra ((algebraMap K L).comp σ.symm.toRingHom)
    FiniteDimensional E L := by
  let : Algebra E K := RingHom.toAlgebra σ.symm.toRingHom
  let : Algebra E L :=
    RingHom.toAlgebra ((algebraMap K L).comp σ.symm.toRingHom)
  have : IsScalarTower E K L :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      simp [RingHom.algebraMap_toAlgebra])
  let e : K ≃ₐ[E] E := AlgEquiv.ofRingEquiv (f := σ) (by
    intro r
    simp [RingHom.algebraMap_toAlgebra])
  have : Module.Finite E K := Module.Finite.equiv e.symm.toLinearEquiv
  exact FiniteDimensional.trans E K L

/-- The finite norm formula is preserved by replacing the base field by
an equivalent field, provided the two base absolute values correspond under
that equivalence. -/
private theorem finiteNormExtension_finite_normFormulaValue_base_ringEquiv
    {K E L : Type*} [Field K] [Field E] [Field L] [Algebra K L]
    [FiniteDimensional K L] (σ : K ≃+* E)
    (vK : AbsoluteValue K ℝ) (vE : AbsoluteValue E ℝ)
    (hvσ : ∀ x : K, vE (σ x) = vK x)
    (x : L) :
    letI : Algebra E L :=
      RingHom.toAlgebra ((algebraMap K L).comp σ.symm.toRingHom)
    letI : FiniteDimensional E L :=
      finiteNormExtension_finiteDimensional_of_base_ringEquiv (K := K)
        (E := E) (L := L) σ
    finiteExtensionNormFormulaValue (K := E) (L := L) vE x =
      finiteExtensionNormFormulaValue (K := K) (L := L) vK x := by
  let : Algebra E K := RingHom.toAlgebra σ.symm.toRingHom
  let : Algebra E L :=
    RingHom.toAlgebra ((algebraMap K L).comp σ.symm.toRingHom)
  have : IsScalarTower E K L :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      simp [RingHom.algebraMap_toAlgebra])
  let e : K ≃ₐ[E] E := AlgEquiv.ofRingEquiv (f := σ) (by
    intro r
    simp [RingHom.algebraMap_toAlgebra])
  have : Module.Finite E K := Module.Finite.equiv e.symm.toLinearEquiv
  have : FiniteDimensional E L := FiniteDimensional.trans E K L
  have hfinEK : Module.finrank E K = 1 := by
    rw [e.toLinearEquiv.finrank_eq]
    simp
  have hfin : Module.finrank K L = Module.finrank E L := by
    have hmul := Module.finrank_mul_finrank E K L
    rwa [hfinEK, one_mul] at hmul
  have he : (algebraMap E L).comp σ.toRingHom = algebraMap K L := by
    ext x
    simp [RingHom.algebraMap_toAlgebra]
  have hnorm : Algebra.norm E x = σ (Algebra.norm K x) :=
    (Algebra.norm_eq_of_ringEquiv σ he x).symm
  rw [finiteExtensionNormFormulaValue, finiteExtensionNormFormulaValue]
  rw [hnorm, hvσ, ← hfin]


/-- Transport a finite-extension result across an equivalent base field. -/
private noncomputable def finiteNormExtension_finiteExtensionResult_base_ringEquiv
    {K E L : Type*} [Field K] [Field E] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (σ : K ≃+* E) (vK : AbsoluteValue K ℝ) (vE : AbsoluteValue E ℝ)
    (hvσ : ∀ x : K, vE (σ x) = vK x)
    (R :
      letI : Algebra E L :=
        RingHom.toAlgebra ((algebraMap K L).comp σ.symm.toRingHom)
      letI : FiniteDimensional E L :=
        finiteNormExtension_finiteDimensional_of_base_ringEquiv
          (K := K) (E := E) (L := L) σ
      FiniteNormExtensionFiniteExtensionResult (K := E) (L := L) vE) :
    FiniteNormExtensionFiniteExtensionResult (K := K) (L := L) vK := by
  letI : Algebra E L :=
    RingHom.toAlgebra ((algebraMap K L).comp σ.symm.toRingHom)
  letI : FiniteDimensional E L :=
    finiteNormExtension_finiteDimensional_of_base_ringEquiv
      (K := K) (E := E) (L := L) σ
  exact
    { extension := R.extension
      extends_base := by
        intro x
        have hbase := R.extends_base (σ x)
        have hmap :
            algebraMap E L (σ x) = algebraMap K L x := by
          simp [RingHom.algebraMap_toAlgebra]
        calc
          R.extension (algebraMap K L x)
              = R.extension (algebraMap E L (σ x)) := by rw [hmap]
          _ = vE (σ x) := hbase
          _ = vK x := hvσ x
      unique := by
        intro w hw
        apply R.unique w
        intro z
        have hmap :
            algebraMap E L z = algebraMap K L (σ.symm z) := by
          simp [RingHom.algebraMap_toAlgebra]
        calc
          w (algebraMap E L z)
              = w (algebraMap K L (σ.symm z)) := by rw [hmap]
          _ = vK (σ.symm z) := hw (σ.symm z)
          _ = vE z := by
            simpa using (hvσ (σ.symm z)).symm
      norm_formula := by
        intro x
        calc
          R.extension x
              = finiteExtensionNormFormulaValue (K := E) (L := L) vE x :=
                R.norm_formula x
          _ = finiteExtensionNormFormulaValue (K := K) (L := L) vK x := by
                exact finiteNormExtension_finite_normFormulaValue_base_ringEquiv
                  (K := K) (E := E) (L := L) σ vK vE hvσ x
      complete_extension := R.complete_extension }


/-- the finite-degree norm construction, explicit finite nonarchimedean theorem: in finite degree,
the unique extension is `|N_{L/K}(x)|^(1/[L:K])`, and the finite extension is
complete. -/
noncomputable def finiteNormExtensionNonarchimedeanFiniteExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : v.IsNontrivial) :
    FiniteNormExtensionFiniteExtensionResult (K := K) (L := L) v where
  extension :=
    finiteNormExtensionFiniteNormFormulaAbsoluteValue (K := K) (L := L)
      v hcomplete hnonarch hv
  extends_base :=
    finiteNormExtension_finite_normFormulaAbsoluteValue_extends_base
      (K := K) (L := L) v hcomplete hnonarch hv
  unique :=
    finiteNormExtension_unique_extension_finite_normFormulaAbsoluteValue
      (K := K) (L := L) v hcomplete hnonarch hv
  norm_formula :=
    finiteNormExtension_finite_normFormulaAbsoluteValue_apply
      (K := K) (L := L) v hcomplete hnonarch hv
  complete_extension :=
    finiteNormExtension_finite_normFormulaAbsoluteValue_complete
      (K := K) (L := L) v hcomplete hnonarch hv

/-- Explicit archimedean finite-extension theorem: after the archimedean
classification, the finite norm formula and completeness reduce to the standard
`ℝ`/`ℂ` cases. -/
noncomputable def finiteNormExtensionArchimedeanFiniteExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (harch : LubinTate.Valuations.ArchimedeanAbsoluteValue v) :
    FiniteNormExtensionFiniteExtensionResult (K := K) (L := L) v :=
  Classical.choice <| by
  classical
  have harchStandard : ¬ IsNonarchimedean (v : K → ℝ) := by
    intro hnonarch
    exact harch ((AbsoluteValue.isNonarchimedean_iff_bounded_nat v).1 hnonarch)
  let : CharZero K :=
    AbsoluteValue.charZero_of_not_isNonarchimedean v harchStandard
  rcases AbsoluteValue.ostrowski_of_complete v
      (completeSpace_withAbs_of_isCompleteForAbsoluteValue v hcomplete)
      harchStandard with
    ⟨s, hs0, hs1, hbranch⟩
  rcases hbranch with hreal | hcomplex
  · rcases hreal with ⟨σ, hσ⟩
    let : Algebra ℝ K := RingHom.toAlgebra σ.symm.toRingHom
    let : Algebra ℝ L :=
      RingHom.toAlgebra ((algebraMap K L).comp σ.symm.toRingHom)
    have : Algebra.IsAlgebraic ℝ L :=
      finiteIsAlgebraicOfBaseRingEquiv (K := K) (E := ℝ)
        (L := L) σ
    have : FiniteDimensional ℝ L :=
      finiteNormExtension_finiteDimensional_of_base_ringEquiv (K := K) (E := ℝ)
        (L := L) σ
    let R := finiteNormExtension_real_finite_rpow_extension (L := L) s hs0 hs1
    exact ⟨
      finiteNormExtension_finiteExtensionResult_base_ringEquiv
        (K := K) (E := ℝ) (L := L) σ v
        (AbsoluteValue.rpow
          finiteStandardRealAbsoluteValue s hs0 hs1)
        (fun x => (hσ x).symm) R⟩
  · rcases hcomplex with ⟨σ, hσ⟩
    let : Algebra ℂ K := RingHom.toAlgebra σ.symm.toRingHom
    let : Algebra ℂ L :=
      RingHom.toAlgebra ((algebraMap K L).comp σ.symm.toRingHom)
    have : Algebra.IsAlgebraic ℂ L :=
      finiteIsAlgebraicOfBaseRingEquiv (K := K) (E := ℂ)
        (L := L) σ
    have : FiniteDimensional ℂ L :=
      finiteNormExtension_finiteDimensional_of_base_ringEquiv (K := K) (E := ℂ)
        (L := L) σ
    let R := finiteNormExtension_complex_finite_rpow_extension (L := L) s hs0 hs1
    exact ⟨
      finiteNormExtension_finiteExtensionResult_base_ringEquiv
        (K := K) (E := ℂ) (L := L) σ v
        (AbsoluteValue.rpow
          finiteStandardComplexAbsoluteValue s hs0 hs1)
        (fun x => (hσ x).symm) R⟩

/-- the finite-degree norm construction, explicit finite theorem for the nontrivial
valuations: in finite degree the unique extension is the norm formula, and the
finite extension is complete. -/
noncomputable def finiteNormExtensionFiniteExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (hv : v.IsNontrivial) :
    FiniteNormExtensionFiniteExtensionResult (K := K) (L := L) v := by
  by_cases hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v
  · exact finiteNormExtensionNonarchimedeanFiniteExtension
      v hcomplete hnonarch hv
  · exact finiteNormExtensionArchimedeanFiniteExtension
      v hcomplete hnonarch

end Valuations
end AlgebraicNumberTheory

end
