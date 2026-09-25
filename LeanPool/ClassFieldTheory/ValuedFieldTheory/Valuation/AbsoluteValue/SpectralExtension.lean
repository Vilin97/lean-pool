/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Extension
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Nonarchimedean
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
/-!
# Spectral extensions of nonarchimedean absolute values

The spectral norm gives the unique extension of a complete nonarchimedean
absolute value to an algebraic field extension.
-/

@[expose] public section

noncomputable
section

namespace AbsoluteValue

@[reducible] private def spectral_withAbsNontriviallyNormedField
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

/-- Algebraicity is transported across the canonical `WithAbs` base-field
equivalence. -/
private instance withAbsAlgebra_isAlgebraic
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (v : AbsoluteValue K ℝ) :
    Algebra.IsAlgebraic (WithAbs v) L := by
  exact Algebra.IsAlgebraic.tower_top
    (K := K) (L := WithAbs v) (A := L)

/-- The strong triangle inequality on the induced normed-field structure. -/
private theorem withAbs_isUltrametricDist
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : IsNonarchimedean (v : K → ℝ)) :
    IsUltrametricDist (WithAbs v) := by
  refine IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm ?_
  intro x y
  simpa [WithAbs.norm_eq_apply_ofAbs] using
    hnonarch (WithAbs.equiv v x) (WithAbs.equiv v y)

/-- existence branch: the spectral extension restricts to the
given absolute value on the base field. -/
private theorem spectral_spectralNorm_extends_base
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ) (x : K) :
    _root_.spectralNorm (WithAbs v) L (algebraMap K L x) = v x := by
  let : Algebra.IsAlgebraic (WithAbs v) L :=
    withAbsAlgebra_isAlgebraic v
  simpa [WithAbs.algebraMap_left_apply, WithAbs.norm_eq_apply_ofAbs] using
    (_root_.spectralNorm_extends
      (K := WithAbs v) (L := L) ((WithAbs.equiv v).symm x))

/-- existence branch: the spectral extension satisfies the
strong triangle inequality in the nonarchimedean case. -/
private theorem spectral_spectralNorm_strong_triangle
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ)
    (hnonarch : IsNonarchimedean (v : K → ℝ)) (x y : L) :
    _root_.spectralNorm (WithAbs v) L (x + y) ≤
      max (_root_.spectralNorm (WithAbs v) L x)
        (_root_.spectralNorm (WithAbs v) L y) := by
  let : IsUltrametricDist (WithAbs v) :=
    withAbs_isUltrametricDist v hnonarch
  let : Algebra.IsAlgebraic (WithAbs v) L :=
    withAbsAlgebra_isAlgebraic v
  exact _root_.isNonarchimedean_spectralNorm
    (K := WithAbs v) (L := L) x y

/-- existence branch: the spectral extension vanishes exactly
at zero. -/
private theorem spectral_spectralNorm_eq_zero_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ) (x : L) :
    _root_.spectralNorm (WithAbs v) L x = 0 ↔ x = 0 := by
  let : Algebra.IsAlgebraic (WithAbs v) L :=
    withAbsAlgebra_isAlgebraic v
  constructor
  · intro hx
    exact _root_.eq_zero_of_map_spectralNorm_eq_zero
      (K := WithAbs v) (L := L) hx
      (Algebra.IsAlgebraic.isAlgebraic x)
  · intro hx
    rw [hx]
    exact _root_.spectralNorm_zero (K := WithAbs v) (L := L)

/-- existence branch: multiplicativity of the spectral
extension over an algebraic extension. -/
private theorem spectral_spectralNorm_mul
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (hnonarch : IsNonarchimedean (v : K → ℝ))
    (hv : v.IsNontrivial) (x y : L) :
    _root_.spectralNorm (WithAbs v) L (x * y) =
      _root_.spectralNorm (WithAbs v) L x *
        _root_.spectralNorm (WithAbs v) L y := by
  let : NontriviallyNormedField (WithAbs v) :=
    spectral_withAbsNontriviallyNormedField v hv
  let : Algebra (WithAbs v) L :=
    WithAbs.algebraLeft L v
  let : CompleteSpace (WithAbs v) :=
    hcomplete
  let : IsUltrametricDist (WithAbs v) :=
    withAbs_isUltrametricDist v hnonarch
  let : Algebra.IsAlgebraic (WithAbs v) L :=
    withAbsAlgebra_isAlgebraic v
  simpa [_root_.spectralAlgNorm_def] using
    (_root_.spectralAlgNorm_mul (K := WithAbs v) (L := L) x y)

/-- existence branch: the spectral norm, bundled as the unique
nonarchimedean absolute-value extension of the complete base valuation. -/
noncomputable def spectralExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (hnonarch : IsNonarchimedean (v : K → ℝ))
    (hv : v.IsNontrivial) : AbsoluteValue L ℝ where
  toFun := _root_.spectralNorm (WithAbs v) L
  map_mul' x y := by
    exact spectral_spectralNorm_mul (K := K) (L := L)
      v hcomplete hnonarch hv x y
  nonneg' x := _root_.spectralNorm_nonneg (K := WithAbs v) (L := L) x
  eq_zero' x := by
    exact spectral_spectralNorm_eq_zero_iff (K := K) (L := L) v x
  add_le' x y := by
    have hstrong :=
      spectral_spectralNorm_strong_triangle v hnonarch x y
    have hx_nonneg :
        0 ≤ _root_.spectralNorm (WithAbs v) L x :=
      _root_.spectralNorm_nonneg (K := WithAbs v) (L := L) x
    have hy_nonneg :
        0 ≤ _root_.spectralNorm (WithAbs v) L y :=
      _root_.spectralNorm_nonneg (K := WithAbs v) (L := L) y
    exact hstrong.trans
      (max_le
        (le_add_of_nonneg_right hy_nonneg)
        (le_add_of_nonneg_left hx_nonneg))

/-- The absolute-value extension constructed is
nonarchimedean. -/
theorem spectralExtension_isNonarchimedean
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (hnonarch : IsNonarchimedean (v : K → ℝ))
    (hv : v.IsNontrivial) :
    IsNonarchimedean
      (spectralExtension (K := K) (L := L)
        v hcomplete hnonarch hv : L → ℝ) := by
  intro x y
  simpa [spectralExtension] using
    spectral_spectralNorm_strong_triangle v hnonarch x y

/-- The absolute-value extension constructed restricts to
the given base valuation. -/
theorem spectralExtension_extends
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (hnonarch : IsNonarchimedean (v : K → ℝ))
    (hv : v.IsNontrivial) :
    Extends v (spectralExtension (K := K) (L := L)
      v hcomplete hnonarch hv) :=
  spectral_spectralNorm_extends_base v

/-- Pointwise uniqueness of the spectral norm among extending absolute values. -/
private theorem spectral_unique_spectralNorm
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (hnonarch : IsNonarchimedean (v : K → ℝ))
    (hv : v.IsNontrivial)
    (w : AbsoluteValue L ℝ)
    (hw_ext : Extends v w)
    (x : L) :
    w x = _root_.spectralNorm (WithAbs v) L x := by
  let : NontriviallyNormedField (WithAbs v) :=
    spectral_withAbsNontriviallyNormedField v hv
  let : Algebra (WithAbs v) L :=
    WithAbs.algebraLeft L v
  let : CompleteSpace (WithAbs v) :=
    hcomplete
  let : IsUltrametricDist (WithAbs v) :=
    withAbs_isUltrametricDist v hnonarch
  let : Algebra.IsAlgebraic (WithAbs v) L :=
    withAbsAlgebra_isAlgebraic v
  refine _root_.spectralNorm_unique_field_norm_ext
    (K := WithAbs v) (L := L) (f := w) ?_ x
  intro a
  rw [WithAbs.algebraMap_left_apply, hw_ext]
  exact (WithAbs.norm_eq_apply_ofAbs v a).symm

/-- nonarchimedean complete branch: uniqueness of the
absolute-value extension, stated as equality with the constructed extension. -/
theorem eq_spectralExtension_of_extends
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ)
    (hcomplete : CompleteSpace (WithAbs v))
    (hnonarch : IsNonarchimedean (v : K → ℝ))
    (hv : v.IsNontrivial)
    (w : AbsoluteValue L ℝ)
    (hw_ext : Extends v w) :
    w = spectralExtension (K := K) (L := L)
      v hcomplete hnonarch hv := by
  ext x
  exact spectral_unique_spectralNorm
    v hcomplete hnonarch hv w hw_ext x


end AbsoluteValue

end
