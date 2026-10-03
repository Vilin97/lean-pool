/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Space

/-!
# Conjugating a Hilbert–Schmidt operator by isometries

`Z ↦ U ∘ Z ∘ V` leaves the Hilbert–Schmidt norm alone when `U` and `V` are
isometries (with `V` invertible).  This is the fact that makes the Sylvester
flow `W t Z = U_A t ∘ Z ∘ (U_B t)⋆` a *unitary* group on the Hilbert–Schmidt
space, and it is proved here in the `ℓ²`-of-columns model.

The left-hand case is termwise trivial: composing with an isometry on the
outside does not change any column norm.  The right-hand case is the same
statement about the adjoint, since `(Z ∘ V)⋆ = V⋆ ∘ Z⋆` and the energy is
adjoint-invariant (`hilbertSchmidtEnergy_adjoint`).  **No basis-independence
argument is needed** — both computations happen in one fixed basis, and the
adjoint step is what moves between the two sides.

This module also supplies the additivity and homogeneity of `ofLp`, which the
bijection of `HilbertSchmidtLp.lean` did not need but any *linear* construction
on the space does.  They are proved by the round trip rather than by
manipulating the defining series.

## Sources

Unitary — and more generally isometric — invariance of the Hilbert--Schmidt norm is
standard (Reed--Simon, *Methods of Modern Mathematical Physics I*; Simon,
*Trace Ideals*).  The two-sided isometric form here is what the Sylvester block
argument needs; no source is followed for its presentation.

## Provenance

*New.*  The donor obtains the same invariance from the tensor factorisation
`U ⊗ conj V` of the conjugation map; nothing of that is used or reproduced.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace TauCeti
namespace HilbertSchmidt

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι : Type*} {E F G : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-! ### `ofLp` is linear -/

omit [CompleteSpace F] in
/-- Two Hilbert–Schmidt operators with the same columns are equal.  This is the
round trip read as a uniqueness statement. -/
theorem eq_of_columns_eq {S T : F →L[𝕜] E} (b : HilbertBasis ι 𝕜 F)
    (hS : Memℓp (columns b S) 2) (hT : Memℓp (columns b T) 2)
    (h : columns b S = columns b T) : S = T := by
  rw [← ofLp_columns b S hS, ← ofLp_columns b T hT]
  congr 1
  exact lp.ext h

omit [CompleteSpace F] in
/-- The column-to-operator map is additive. -/
@[simp] theorem ofLp_add (b : HilbertBasis ι 𝕜 F) (f g : lp (fun _ : ι => E) 2) :
    ofLp b (f + g) = ofLp b f + ofLp b g := by
  refine eq_of_columns_eq b ?_ ?_ ?_
  · rw [columns_ofLp]; exact lp.memℓp _
  · rw [columns_add, columns_ofLp, columns_ofLp]; exact lp.memℓp (f + g)
  · rw [columns_ofLp, columns_add, columns_ofLp, columns_ofLp]; rfl

omit [CompleteSpace F] in
/-- The column-to-operator map is additive on differences.  Stated separately from
`ofLp_add` because the subtraction form is what the convergence arguments use. -/
theorem ofLp_sub (b : HilbertBasis ι 𝕜 F) (f g : lp (fun _ : ι => E) 2) :
    ofLp b (f - g) = ofLp b f - ofLp b g := by
  have h : ofLp b (f - g) + ofLp b g = ofLp b f := by rw [← ofLp_add]; congr 1; abel
  rw [← h]; abel

omit [CompleteSpace F] in
/-- The column-to-operator map is homogeneous. -/
@[simp] theorem ofLp_smul (b : HilbertBasis ι 𝕜 F) (c : 𝕜) (f : lp (fun _ : ι => E) 2) :
    ofLp b (c • f) = c • ofLp b f := by
  refine eq_of_columns_eq b ?_ ?_ ?_
  · rw [columns_ofLp]; exact lp.memℓp _
  · rw [columns_smul, columns_ofLp]; exact lp.memℓp (c • f)
  · rw [columns_ofLp, columns_smul, columns_ofLp]; rfl

/-! ### The energy under composition with isometries -/

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] in
/-- Composing on the **left** with a norm-preserving map leaves the energy
alone: every column norm is individually unchanged. -/
theorem hilbertSchmidtEnergy_isometry_comp (T : F →L[𝕜] E) (b : HilbertBasis ι 𝕜 F)
    (U : E →L[𝕜] G) (hU : ∀ x : E, ‖U x‖ = ‖x‖) :
    (U.comp T).hilbertSchmidtEnergy b = T.hilbertSchmidtEnergy b := by
  simp only [ContinuousLinearMap.hilbertSchmidtEnergy_def]
  refine tsum_congr fun i => ?_
  have hnn : ‖U (T (b i))‖₊ = ‖T (b i)‖₊ := NNReal.coe_injective (hU _)
  rw [ContinuousLinearMap.comp_apply, enorm_eq_nnnorm, enorm_eq_nnnorm, hnn]

/-- Composing on the **right** with a map whose adjoint is norm-preserving
leaves the energy alone.  The proof passes to the adjoint, where the
composition moves to the left. -/
theorem hilbertSchmidtEnergy_comp_isometry (T : F →L[𝕜] E) (b : HilbertBasis ι 𝕜 F)
    (V : F →L[𝕜] F) (hV : ∀ x : F, ‖V.adjoint x‖ = ‖x‖) :
    (T.comp V).hilbertSchmidtEnergy b = T.hilbertSchmidtEnergy b := by
  obtain ⟨w, c, -⟩ := exists_hilbertBasis 𝕜 E
  rw [ContinuousLinearMap.hilbertSchmidtEnergy_adjoint _ b c,
    ContinuousLinearMap.hilbertSchmidtEnergy_adjoint T b c,
    ContinuousLinearMap.adjoint_comp]
  exact hilbertSchmidtEnergy_isometry_comp _ c _ hV

/-! ### The `ℓ²` norm in terms of the energy -/

omit [CompleteSpace F] in
/-- The `ℓ²` norm of a column family is the square root of the Hilbert–Schmidt
energy of the operator it represents.  This is the one place the real-valued
`lp` norm and the `ℝ≥0∞`-valued energy are compared. -/
theorem energy_ofLp (b : HilbertBasis ι 𝕜 F) (f : lp (fun _ : ι => E) 2) :
    (ofLp b f).hilbertSchmidtEnergy b = ENNReal.ofReal (‖f‖ ^ 2) := by
  have hsum : Summable fun i => ‖ofLp b f (b i)‖ ^ 2 := by
    refine (summable_sq f).congr fun i => ?_
    rw [← columns_apply b (ofLp b f) i, columns_ofLp]
  rw [ContinuousLinearMap.hilbertSchmidtEnergy_def, norm_sq_eq_tsum_norm_column_sq b f,
    ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hsum]
  refine tsum_congr fun i => ?_
  rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm,
    ← ENNReal.ofReal_pow (by positivity)]

/-- **Conjugating by isometries is an `ℓ²` isometry.**  This is the unitarity of
the Sylvester flow, before any group structure is introduced. -/
theorem norm_conj_eq (b : HilbertBasis ι 𝕜 F) (f : lp (fun _ : ι => E) 2)
    (U : E →L[𝕜] E) (hU : ∀ x : E, ‖U x‖ = ‖x‖)
    (V : F →L[𝕜] F) (hV : ∀ x : F, ‖V.adjoint x‖ = ‖x‖)
    (g : lp (fun _ : ι => E) 2)
    (hg : ofLp b g = (U.comp (ofLp b f)).comp V) :
    ‖g‖ = ‖f‖ := by
  have hE : (ofLp b g).hilbertSchmidtEnergy b = (ofLp b f).hilbertSchmidtEnergy b := by
    rw [hg, hilbertSchmidtEnergy_comp_isometry _ b V hV,
      hilbertSchmidtEnergy_isometry_comp _ b U hU]
  rw [energy_ofLp, energy_ofLp] at hE
  have := (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).mp hE
  have hnn : (0 : ℝ) ≤ ‖g‖ := norm_nonneg _
  nlinarith [norm_nonneg f, norm_nonneg g]

end HilbertSchmidt
end TauCeti
