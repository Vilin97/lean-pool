/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Lp

/-!
# `ℓ²` of columns as *the* Hilbert–Schmidt space

`HilbertSchmidtLp.lean` proves the bijection between Hilbert–Schmidt operators
`F →L[𝕜] E` and square-summable column families `lp (fun _ : ι => E) 2`.  This
module packages the three facts a consumer of a Hilbert–Schmidt *space* actually
uses:

* `ofLp_injective` — distinct column families give distinct operators;
* `existsUnique_ofLp_iff_summable` — an operator is represented by a unique
  element of `lp` exactly when its column norms are square-summable;
* `norm_sq_eq_tsum_norm_column_sq` — the `ℓ²` norm is the Hilbert–Schmidt norm.

## Why `lp` is the space, and not a new type

The obvious alternative is a subtype `{T : F →L[𝕜] E // IsHilbertSchmidt T}`.
It is the wrong choice: as a subtype of a normed space it inherits the
*operator* norm from Mathlib, and every Hilbert–Schmidt statement then has to
fight that instance.  Carrying `lp` instead means `InnerProductSpace` and
`CompleteSpace` arrive from Mathlib already proved — the expensive half of any
from-scratch development — and only the bijection has to be supplied, which
`HilbertSchmidtLp.lean` did.

No tensor product is constructed anywhere.  The donor realises the same space
as a Hilbert tensor product `conj F ⊗ E`, whose closure was measured at 21,581
lines; the three statements below are what that closure was being paid for.

## Sources

The identification of the Hilbert--Schmidt class with `ℓ²` of columns is standard
(Reed--Simon, *Methods of Modern Mathematical Physics I*; Simon, *Trace Ideals*);
see `ForTauCeti/Analysis/InnerProductSpace/HilbertSchmidtLp.lean`, which carries
the presentation this module packages.

## Provenance

*New.*  The statements are chosen to match the shape of the donor's
`HilbertSchmidtTensor.{toOperator_injective, existsUnique_tensor_iff_summable_columns,
norm_sq_eq_tsum_column_norm_sq}` so that consumers re-point with their proof
structure intact.  The proofs share nothing with the donor's: they are three
short consequences of `ofLp_columns` and `columns_ofLp`, where the donor's go
through the universal property of the tensor product.
-/

public section

open scoped ENNReal NNReal

namespace TauCeti
namespace HilbertSchmidt

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι : Type*} {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Membership of `ℓ²`, stated in the square-summability form the paper
Hilbert–Schmidt predicate uses. -/
theorem memLp_columns_iff_summable (b : HilbertBasis ι 𝕜 F) (T : F →L[𝕜] E) :
    Memℓp (columns b T) 2 ↔ Summable fun i => ‖T (b i)‖ ^ 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  refine summable_congr fun i => ?_
  rw [columns_apply, show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by simp]
  exact Real.rpow_natCast _ 2

omit [CompleteSpace F] in
/-- **Distinct column families give distinct operators.**  Immediate from the
column round trip: `columns b` is a left inverse of `ofLp b`. -/
theorem ofLp_injective (b : HilbertBasis ι 𝕜 F) :
    Function.Injective (ofLp b : lp (fun _ : ι => E) 2 → (F →L[𝕜] E)) := by
  intro f g hfg
  have h : columns b (ofLp b f) = columns b (ofLp b g) := by rw [hfg]
  rw [columns_ofLp, columns_ofLp] at h
  exact lp.ext h

omit [CompleteSpace F] in
/-- **An operator has a unique `ℓ²` representative exactly when it is
Hilbert–Schmidt.**  The forward direction reads the representative off the
round trip; the backward direction builds it out of the columns. -/
theorem existsUnique_ofLp_iff_summable (b : HilbertBasis ι 𝕜 F) (T : F →L[𝕜] E) :
    (∃! f : lp (fun _ : ι => E) 2, ofLp b f = T) ↔ Summable fun i => ‖T (b i)‖ ^ 2 := by
  constructor
  · rintro ⟨f, hf, -⟩
    rw [← memLp_columns_iff_summable b T, ← hf, columns_ofLp]
    exact lp.memℓp f
  · intro hsum
    refine ⟨⟨columns b T, (memLp_columns_iff_summable b T).mpr hsum⟩, ofLp_columns b T _, ?_⟩
    intro g hg
    exact ofLp_injective b (hg.trans (ofLp_columns b T _).symm)

omit [CompleteSpace F] in
/-- **The `ℓ²` norm is the Hilbert–Schmidt norm**: the square of the norm of a
column family is the sum of the squared column norms of the operator it
represents. -/
theorem norm_sq_eq_tsum_norm_column_sq (b : HilbertBasis ι 𝕜 F)
    (f : lp (fun _ : ι => E) 2) :
    ‖f‖ ^ 2 = ∑' i, ‖ofLp b f (b i)‖ ^ 2 := by
  rw [← tsum_sq_eq_norm_sq f]
  refine tsum_congr fun i => ?_
  rw [← columns_apply b (ofLp b f) i, columns_ofLp]

end HilbertSchmidt
end TauCeti
