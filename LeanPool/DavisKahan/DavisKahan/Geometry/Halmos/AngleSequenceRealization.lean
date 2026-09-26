/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.CompactClassification
public import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.Realization
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.DiagonalSequence
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.PrescribedSequence

/-! # Angle Sequence Realization -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Corollary 3.1: realizing a prescribed angle sequence

`Realization.lean` proves that *every* admissible angle datum is attained by a
concrete pair of subspaces.  This module manufactures the datum that Corollary
3.1's second sentence asks for: given a decreasing sequence of angles

`π/2 ≥ θ₁ ≥ θ₂ ≥ ⋯ → 0`,

the diagonal operators `cos Θ = diag (cos θₙ)` and `sin Θ = diag (sin θₙ)` on
`ℓ²(ℕ, 𝕜)` are an admissible datum with the identity as intertwiner, and the pair
it realizes has exactly the prescribed angles.

## What the sequence hypotheses are for

The *datum* needs no hypothesis on `θ` at all — the Pythagorean identity, the
commutation and the self-adjointness hold coefficientwise for an arbitrary real
sequence.  The three hypotheses of Corollary 3.1 enter only afterwards:

* `0 ≤ θₙ ≤ π/2` and `Antitone θ` make `sin² θₙ` an antitone nonnegative
  sequence, which is what identifies it with a list of approximation numbers;
* `θₙ → 0` makes `sin² θₙ → 0`, which is what makes the block compact.

## Which block is compact

`HalmosAngleDatum.defectBlock_eq` says the realized pair's block
`P (1 - Q) P` is `sin² Θ₀` on the `E`-factor and zero elsewhere.  Since
`θₙ → 0`, that block is compact.  This is the **printed** hypothesis of
Corollary 3.1, and it is the one this construction is proved to satisfy.

The cosine block `P Q P` is `cos² Θ₀` by `HalmosAngleDatum.cosineBlock_eq`, whose
coefficients tend to `1`; that this makes it non-compact once infinitely many
angles are nonzero is commentary here, not something the module proves.  The two
hypotheses are recorded elsewhere as incomparable in infinite dimension, so which
one a construction satisfies has to be said explicitly.

## Sources

Davis, C. and Kahan, W. M., *The rotation of eigenvectors by a perturbation. III*,
SIAM J. Numer. Anal. 7 (1970), Corollary 3.1, second sentence.
-/

namespace TauCeti
namespace DavisKahan

open Filter Topology
open scoped InnerProductSpace

section AngleSequence

variable (𝕜 : Type*) [RCLike 𝕜]

/-- `ℓ²(ℕ, 𝕜)`, the space on which a prescribed angle sequence is realized as a
diagonal pair of angle operators. -/
abbrev AngleSequenceSpace : Type _ := lp (fun _ : ℕ => 𝕜) 2

/-- The ambient Hilbert space of the realized pair: the `L²` direct sum of two
copies of `ℓ²(ℕ, 𝕜)`, read as `P H ⊕ Pᗮ H`. -/
abbrev AngleSequenceAmbient : Type _ :=
  WithLp 2 (AngleSequenceSpace 𝕜 × AngleSequenceSpace 𝕜)

variable (θ : ℕ → ℝ)

/-! ### The diagonal coefficient sequences -/

/-- The coefficients of `cos Θ`. -/
noncomputable def angleCosSeq : ℕ → 𝕜 := fun n => ((Real.cos (θ n) : ℝ) : 𝕜)

/-- The coefficients of `sin Θ`. -/
noncomputable def angleSinSeq : ℕ → 𝕜 := fun n => ((Real.sin (θ n) : ℝ) : 𝕜)

/-- The coefficients of `sin² Θ`, the defect block. -/
noncomputable def angleSinSqSeq : ℕ → 𝕜 := fun n => ((Real.sin (θ n) ^ 2 : ℝ) : 𝕜)

/-- The cosine coefficients are bounded by `1`, which is what makes them a
diagonal operator on `ℓ²`. -/
theorem norm_angleCosSeq_le (n : ℕ) : ‖angleCosSeq 𝕜 θ n‖ ≤ 1 := by
  rw [angleCosSeq, RCLike.norm_ofReal]
  exact Real.abs_cos_le_one _

/-- The sine coefficients are bounded by `1`. -/
theorem norm_angleSinSeq_le (n : ℕ) : ‖angleSinSeq 𝕜 θ n‖ ≤ 1 := by
  rw [angleSinSeq, RCLike.norm_ofReal]
  exact Real.abs_sin_le_one _

/-- The squared sine coefficients are bounded by `1`. -/
theorem norm_angleSinSqSeq_le (n : ℕ) : ‖angleSinSqSeq 𝕜 θ n‖ ≤ 1 := by
  rw [angleSinSqSeq, RCLike.norm_ofReal, abs_of_nonneg (sq_nonneg _)]
  nlinarith [Real.sin_sq_add_cos_sq (θ n), sq_nonneg (Real.cos (θ n))]

/-- The cosine coefficients are real, hence fixed by the star operation; this is
what makes `cos Θ` self-adjoint. -/
theorem conj_angleCosSeq (n : ℕ) :
    (starRingEnd 𝕜) (angleCosSeq 𝕜 θ n) = angleCosSeq 𝕜 θ n := by
  rw [angleCosSeq, RCLike.conj_ofReal]

/-- The sine coefficients are real, hence fixed by the star operation. -/
theorem conj_angleSinSeq (n : ℕ) :
    (starRingEnd 𝕜) (angleSinSeq 𝕜 θ n) = angleSinSeq 𝕜 θ n := by
  rw [angleSinSeq, RCLike.conj_ofReal]

/-! ### The diagonal angle operators -/

/-- `cos Θ` for the prescribed sequence: multiplication by `cos θₙ` on `ℓ²`. -/
noncomputable def angleCosOp :
    AngleSequenceSpace 𝕜 →L[𝕜] AngleSequenceSpace 𝕜 :=
  diagOpLp (angleCosSeq 𝕜 θ) zero_le_one (norm_angleCosSeq_le 𝕜 θ)

/-- `sin Θ` for the prescribed sequence: multiplication by `sin θₙ` on `ℓ²`. -/
noncomputable def angleSinOp :
    AngleSequenceSpace 𝕜 →L[𝕜] AngleSequenceSpace 𝕜 :=
  diagOpLp (angleSinSeq 𝕜 θ) zero_le_one (norm_angleSinSeq_le 𝕜 θ)

/-- `sin² Θ` for the prescribed sequence: multiplication by `sin² θₙ` on `ℓ²`. -/
noncomputable def angleSinSqOp :
    AngleSequenceSpace 𝕜 →L[𝕜] AngleSequenceSpace 𝕜 :=
  diagOpLp (angleSinSqSeq 𝕜 θ) zero_le_one (norm_angleSinSqSeq_le 𝕜 θ)

/-- `cos Θ` multiplies the `n`-th coordinate by `cos θₙ`. -/
@[simp]
theorem angleCosOp_apply (x : AngleSequenceSpace 𝕜) (n : ℕ) :
    (angleCosOp 𝕜 θ x : ∀ _ : ℕ, 𝕜) n = angleCosSeq 𝕜 θ n * x n :=
  diagOpLp_apply _ _ _ x n

/-- `sin Θ` multiplies the `n`-th coordinate by `sin θₙ`. -/
@[simp]
theorem angleSinOp_apply (x : AngleSequenceSpace 𝕜) (n : ℕ) :
    (angleSinOp 𝕜 θ x : ∀ _ : ℕ, 𝕜) n = angleSinSeq 𝕜 θ n * x n :=
  diagOpLp_apply _ _ _ x n

/-- `sin² Θ` multiplies the `n`-th coordinate by `sin² θₙ`. -/
@[simp]
theorem angleSinSqOp_apply (x : AngleSequenceSpace 𝕜) (n : ℕ) :
    (angleSinSqOp 𝕜 θ x : ∀ _ : ℕ, 𝕜) n = angleSinSqSeq 𝕜 θ n * x n :=
  diagOpLp_apply _ _ _ x n

/-- The square of `sin Θ` is the diagonal operator with coefficients `sin² θₙ`. -/
theorem angleSinOp_comp_angleSinOp :
    angleSinOp 𝕜 θ ∘L angleSinOp 𝕜 θ = angleSinSqOp 𝕜 θ := by
  refine ContinuousLinearMap.ext fun x => lp.ext (funext fun n => ?_)
  simp only [ContinuousLinearMap.comp_apply, angleSinOp_apply, angleSinSqOp_apply,
    angleSinSeq, angleSinSqSeq]
  rw [← mul_assoc, ← RCLike.ofReal_mul, sq]

/-! ### The prescribed datum -/

/-- **The angle datum of a prescribed real sequence.**

Both sides carry the same diagonal operators and the intertwiner is the
identity, so this datum realizes a pair whose two angle operators agree
exactly — including the multiplicity at `0`.  No hypothesis on `θ` is needed:
the Pythagorean identity holds coefficientwise for every real number. -/
noncomputable def angleSequenceDatum :
    HalmosAngleDatum 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜) where
  cos₀ := angleCosOp 𝕜 θ
  sin₀ := angleSinOp 𝕜 θ
  cos₁ := angleCosOp 𝕜 θ
  sin₁ := angleSinOp 𝕜 θ
  intertwiner := 1
  isSelfAdjoint_cos₀ := isSelfAdjoint_diagOpLp _ _ _ (conj_angleCosSeq 𝕜 θ)
  isSelfAdjoint_sin₀ := isSelfAdjoint_diagOpLp _ _ _ (conj_angleSinSeq 𝕜 θ)
  isSelfAdjoint_cos₁ := isSelfAdjoint_diagOpLp _ _ _ (conj_angleCosSeq 𝕜 θ)
  isSelfAdjoint_sin₁ := isSelfAdjoint_diagOpLp _ _ _ (conj_angleSinSeq 𝕜 θ)
  commute₀ := by
    refine ContinuousLinearMap.ext fun x => lp.ext (funext fun n => ?_)
    simp only [ContinuousLinearMap.comp_apply, angleCosOp_apply, angleSinOp_apply]
    ring
  commute₁ := by
    refine ContinuousLinearMap.ext fun x => lp.ext (funext fun n => ?_)
    simp only [ContinuousLinearMap.comp_apply, angleCosOp_apply, angleSinOp_apply]
    ring
  pythagoras₀ := by
    refine ContinuousLinearMap.ext fun x => lp.ext (funext fun n => ?_)
    have hone : angleCosSeq 𝕜 θ n * angleCosSeq 𝕜 θ n +
        angleSinSeq 𝕜 θ n * angleSinSeq 𝕜 θ n = 1 := by
      rw [angleCosSeq, angleSinSeq, ← RCLike.ofReal_mul, ← RCLike.ofReal_mul,
        ← RCLike.ofReal_add,
        show Real.cos (θ n) * Real.cos (θ n) + Real.sin (θ n) * Real.sin (θ n) = 1 by
          nlinarith [Real.sin_sq_add_cos_sq (θ n)],
        RCLike.ofReal_one]
    simp only [add_apply, lp.coeFn_add, Pi.add_apply,
      ContinuousLinearMap.comp_apply, angleCosOp_apply, angleSinOp_apply,
      one_apply_eq_self]
    calc angleCosSeq 𝕜 θ n * (angleCosSeq 𝕜 θ n * x n) +
          angleSinSeq 𝕜 θ n * (angleSinSeq 𝕜 θ n * x n)
        = (angleCosSeq 𝕜 θ n * angleCosSeq 𝕜 θ n +
            angleSinSeq 𝕜 θ n * angleSinSeq 𝕜 θ n) * x n := by ring
      _ = x n := by rw [hone, one_mul]
  pythagoras₁ := by
    refine ContinuousLinearMap.ext fun x => lp.ext (funext fun n => ?_)
    have hone : angleCosSeq 𝕜 θ n * angleCosSeq 𝕜 θ n +
        angleSinSeq 𝕜 θ n * angleSinSeq 𝕜 θ n = 1 := by
      rw [angleCosSeq, angleSinSeq, ← RCLike.ofReal_mul, ← RCLike.ofReal_mul,
        ← RCLike.ofReal_add,
        show Real.cos (θ n) * Real.cos (θ n) + Real.sin (θ n) * Real.sin (θ n) = 1 by
          nlinarith [Real.sin_sq_add_cos_sq (θ n)],
        RCLike.ofReal_one]
    simp only [add_apply, lp.coeFn_add, Pi.add_apply,
      ContinuousLinearMap.comp_apply, angleCosOp_apply, angleSinOp_apply,
      one_apply_eq_self]
    calc angleCosSeq 𝕜 θ n * (angleCosSeq 𝕜 θ n * x n) +
          angleSinSeq 𝕜 θ n * (angleSinSeq 𝕜 θ n * x n)
        = (angleCosSeq 𝕜 θ n * angleCosSeq 𝕜 θ n +
            angleSinSeq 𝕜 θ n * angleSinSeq 𝕜 θ n) * x n := by ring
      _ = x n := by rw [hone, one_mul]
  map_cos := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp only [ContinuousLinearMap.comp_apply, one_apply_eq_self]
  map_sin := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp only [ContinuousLinearMap.comp_apply, one_apply_eq_self]
  isometry_on_sin₀ := by
    rw [ContinuousLinearMap.adjoint_one]
    refine ContinuousLinearMap.ext fun x => ?_
    simp only [ContinuousLinearMap.comp_apply, one_apply_eq_self]
  coisometry_on_sin₁ := by
    rw [ContinuousLinearMap.adjoint_one]
    refine ContinuousLinearMap.ext fun x => ?_
    simp only [ContinuousLinearMap.comp_apply, one_apply_eq_self]

/-- The datum's `P`-side sine is the prescribed diagonal operator. -/
@[simp]
theorem angleSequenceDatum_sin₀ : (angleSequenceDatum 𝕜 θ).sin₀ = angleSinOp 𝕜 θ := rfl

/-- The datum's `P`-side cosine is the prescribed diagonal operator. -/
@[simp]
theorem angleSequenceDatum_cos₀ : (angleSequenceDatum 𝕜 θ).cos₀ = angleCosOp 𝕜 θ := rfl

/-- The datum's `Pᗮ`-side sine is the same prescribed diagonal operator. -/
@[simp]
theorem angleSequenceDatum_sin₁ : (angleSequenceDatum 𝕜 θ).sin₁ = angleSinOp 𝕜 θ := rfl

/-- The datum's `Pᗮ`-side cosine is the same prescribed diagonal operator. -/
@[simp]
theorem angleSequenceDatum_cos₁ : (angleSequenceDatum 𝕜 θ).cos₁ = angleCosOp 𝕜 θ := rfl

/-- The realized pair's defect block, `P (1 - Q) P`, where `P` projects onto the
`E`-factor and `Q` onto `(angleSequenceDatum 𝕜 θ).targetSubspace`. -/
noncomputable def angleSequenceDefectBlock :
    AngleSequenceAmbient 𝕜 →L[𝕜] AngleSequenceAmbient 𝕜 :=
  (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜)).starProjection ∘L
    (ContinuousLinearMap.id 𝕜 (AngleSequenceAmbient 𝕜) -
      (angleSequenceDatum 𝕜 θ).targetSubspace.starProjection) ∘L
    (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜)).starProjection

/-- **The defect block of the realized pair is `sin² Θ` on the `E`-factor.**

Immediate from `HalmosAngleDatum.defectBlock_eq` together with the coefficientwise
identity `sin θ · sin θ = sin² θ`. -/
theorem angleSequenceDefectBlock_eq :
    angleSequenceDefectBlock 𝕜 θ =
      modelInl 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜) ∘L angleSinSqOp 𝕜 θ ∘L
        WithLp.fstL 2 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜) := by
  rw [angleSequenceDefectBlock, (angleSequenceDatum 𝕜 θ).defectBlock_eq,
    angleSequenceDatum_sin₀, angleSinOp_comp_angleSinOp]

end AngleSequence
/-! ## Sandwiching by the first factor preserves approximation numbers -/

section Sandwich

variable {𝕜 : Type*} [RCLike 𝕜]
variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace 𝕜 A] [CompleteSpace A]
variable {B : Type*} [NormedAddCommGroup B] [InnerProductSpace 𝕜 B] [CompleteSpace B]

omit [CompleteSpace A] [CompleteSpace B] in
/-- An operator on the first factor, extended by zero to `A ⊕₂ B`, keeps every
approximation number: both directions are a sandwich between the two contractions
`modelInl` and `WithLp.fstL`. -/
theorem approximationNumber_modelInl_comp_fstL (T : A →L[𝕜] A) (n : ℕ) :
    (modelInl 𝕜 A B ∘L T ∘L WithLp.fstL 2 𝕜 A B).approximationNumber n =
      T.approximationNumber n := by
  have hfactor : T = WithLp.fstL 2 𝕜 A B ∘L
      (modelInl 𝕜 A B ∘L T ∘L WithLp.fstL 2 𝕜 A B) ∘L modelInl 𝕜 A B := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp only [ContinuousLinearMap.comp_apply]
    rfl
  refine le_antisymm ?_ ?_
  · exact ApproximationNumber.approximationNumber_comp_contractions_le
      (modelInl 𝕜 A B) (T := T) (WithLp.fstL 2 𝕜 A B)
      norm_modelInl_le_one norm_fstL_le_one n
  · conv_lhs => rw [hfactor]
    exact ApproximationNumber.approximationNumber_comp_contractions_le
      (WithLp.fstL 2 𝕜 A B)
      (T := modelInl 𝕜 A B ∘L T ∘L WithLp.fstL 2 𝕜 A B) (modelInl 𝕜 A B)
      norm_fstL_le_one norm_modelInl_le_one n

omit [CompleteSpace A] [CompleteSpace B] in
/-- An operator on the first factor, extended by zero, stays compact. -/
theorem isCompactOperator_modelInl_comp_fstL {T : A →L[𝕜] A} (h : IsCompactOperator T) :
    IsCompactOperator (modelInl 𝕜 A B ∘L T ∘L WithLp.fstL 2 𝕜 A B) :=
  (h.comp_clm (WithLp.fstL 2 𝕜 A B)).clm_comp (modelInl 𝕜 A B)

end Sandwich

/-! ## The defect block of an arbitrary realized pair -/

section GeneralDefect

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **A realized pair's defect block is compact as soon as `sin² Θ₀` is.** -/
theorem isCompactOperator_halmosDefectBlock (d : HalmosAngleDatum 𝕜 E F)
    (h : IsCompactOperator (d.sin₀ ∘L d.sin₀)) :
    IsCompactOperator
      ((sourceSubspace 𝕜 E F).starProjection ∘L
        (ContinuousLinearMap.id 𝕜 (WithLp 2 (E × F)) -
          d.targetSubspace.starProjection) ∘L
        (sourceSubspace 𝕜 E F).starProjection) := by
  rw [d.defectBlock_eq]
  exact isCompactOperator_modelInl_comp_fstL h

/-- **A realized pair's defect block has exactly the approximation numbers of
`sin² Θ₀`.**  This is what turns a prescribed angle sequence into a prescribed
angle eigenvalue list. -/
theorem approximationNumber_halmosDefectBlock (d : HalmosAngleDatum 𝕜 E F) (n : ℕ) :
    ((sourceSubspace 𝕜 E F).starProjection ∘L
        (ContinuousLinearMap.id 𝕜 (WithLp 2 (E × F)) -
          d.targetSubspace.starProjection) ∘L
        (sourceSubspace 𝕜 E F).starProjection).approximationNumber n =
      (d.sin₀ ∘L d.sin₀).approximationNumber n := by
  rw [d.defectBlock_eq, approximationNumber_modelInl_comp_fstL]

end GeneralDefect

section Analysis

variable {𝕜 : Type*} [RCLike 𝕜] {θ : ℕ → ℝ}

/-- Under the corollary's hypotheses the defect coefficients are antitone. -/
theorem antitone_norm_angleSinSqSeq (hθ0 : ∀ n, 0 ≤ θ n)
    (hθ2 : ∀ n, θ n ≤ Real.pi / 2) (hanti : Antitone θ) :
    Antitone fun n => ‖angleSinSqSeq 𝕜 θ n‖ := by
  intro m n hmn
  have hsin : ∀ k, 0 ≤ Real.sin (θ k) := fun k =>
    Real.sin_nonneg_of_nonneg_of_le_pi (hθ0 k)
      ((hθ2 k).trans (by linarith [Real.pi_pos]))
  have hle : Real.sin (θ n) ≤ Real.sin (θ m) := by
    refine Real.sin_le_sin_of_le_of_le_pi_div_two ?_ (hθ2 m) (hanti hmn)
    linarith [hθ0 n, Real.pi_pos]
  simp only [angleSinSqSeq, RCLike.norm_ofReal]
  rw [abs_of_nonneg (sq_nonneg (Real.sin (θ n))),
    abs_of_nonneg (sq_nonneg (Real.sin (θ m)))]
  exact pow_le_pow_left₀ (hsin n) hle 2

/-- Under the corollary's hypotheses the defect coefficients tend to `0`. -/
theorem tendsto_angleSinSqSeq (hlim : Tendsto θ atTop (nhds 0)) :
    Tendsto (angleSinSqSeq 𝕜 θ) atTop (nhds 0) := by
  have hreal : Tendsto (fun n => Real.sin (θ n) ^ 2) atTop (nhds 0) := by
    have h1 : Tendsto (fun n => Real.sin (θ n)) atTop (nhds 0) := by
      have h := (Real.continuous_sin.tendsto 0).comp hlim
      simpa [Function.comp_def] using h
    simpa using h1.pow 2
  have hcast : Tendsto (fun r : ℝ => ((r : ℝ) : 𝕜)) (nhds 0) (nhds 0) := by
    simpa using (RCLike.continuous_ofReal (K := 𝕜)).tendsto 0
  exact hcast.comp hreal

/-- `sin² Θ` is a compact operator when the prescribed angles tend to `0`. -/
theorem isCompactOperator_angleSinSqOp (hlim : Tendsto θ atTop (nhds 0)) :
    IsCompactOperator (angleSinSqOp 𝕜 θ) :=
  isCompactOperator_diagOpLp _ _ _ (tendsto_angleSinSqSeq hlim)

/-- The approximation numbers of `sin² Θ` are the prescribed `sin² θₙ`. -/
theorem approximationNumber_angleSinSqOp (hθ0 : ∀ n, 0 ≤ θ n)
    (hθ2 : ∀ n, θ n ≤ Real.pi / 2) (hanti : Antitone θ) (n : ℕ) :
    (angleSinSqOp 𝕜 θ).approximationNumber n = Real.sin (θ n) ^ 2 := by
  rw [angleSinSqOp,
    approximationNumber_diagOpLp _ _ _ (antitone_norm_angleSinSqSeq hθ0 hθ2 hanti) n,
    angleSinSqSeq, RCLike.norm_ofReal, abs_of_nonneg (sq_nonneg (Real.sin (θ n)))]

/-- **The defect block is compact** — the printed hypothesis of Corollary 3.1. -/
theorem isCompactOperator_angleSequenceDefectBlock
    (hlim : Tendsto θ atTop (nhds 0)) :
    IsCompactOperator (angleSequenceDefectBlock 𝕜 θ) := by
  rw [angleSequenceDefectBlock]
  refine isCompactOperator_halmosDefectBlock _ ?_
  rw [angleSequenceDatum_sin₀, angleSinOp_comp_angleSinOp]
  exact isCompactOperator_angleSinSqOp hlim

/-- **The realized pair's angle list is exactly the prescribed one.**

The `n`-th approximation number of the defect block is `sin² θₙ`, and `θ ↦ sin² θ`
is strictly monotone on `[0, π/2]`, so this is the paper's decreasing angle
sequence, reparametrized without loss. -/
theorem approximationNumber_angleSequenceDefectBlock (hθ0 : ∀ n, 0 ≤ θ n)
    (hθ2 : ∀ n, θ n ≤ Real.pi / 2) (hanti : Antitone θ) (n : ℕ) :
    (angleSequenceDefectBlock 𝕜 θ).approximationNumber n = Real.sin (θ n) ^ 2 := by
  rw [angleSequenceDefectBlock, approximationNumber_halmosDefectBlock,
    angleSequenceDatum_sin₀, angleSinOp_comp_angleSinOp,
    approximationNumber_angleSinSqOp hθ0 hθ2 hanti]

end Analysis


/-! ## Prescribed angle-`0` multiplicities

Corollary 3.1 allows an eigenvalue `0` of arbitrary — and independently chosen —
multiplicity on each side, on top of the sequence.  `trivialHalmosAngleDatum`
realizes that eigenvalue alone, on an arbitrary pair of spaces, and
`HalmosAngleDatum.prod` adds the two data. -/

section ZeroMultiplicity

variable (𝕜 : Type*) [RCLike 𝕜] (θ : ℕ → ℝ)
variable (Z₀ : Type*) [NormedAddCommGroup Z₀] [InnerProductSpace 𝕜 Z₀] [CompleteSpace Z₀]
variable (Z₁ : Type*) [NormedAddCommGroup Z₁] [InnerProductSpace 𝕜 Z₁] [CompleteSpace Z₁]

/-- **The datum realizing a prescribed angle sequence together with prescribed
angle-`0` multiplicities.**  `Z₀` is the extra angle-`0` space on the `P`-side and
`Z₁` the one on the `Pᗮ`-side; the two are arbitrary and unrelated. -/
noncomputable def angleSequenceZeroDatum :
    HalmosAngleDatum 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
      (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁)) :=
  (angleSequenceDatum 𝕜 θ).prod (trivialHalmosAngleDatum 𝕜 Z₀ Z₁)

/-- Its `P`-side sine is the sequence's, extended by zero over `Z₀`. -/
@[simp]
theorem angleSequenceZeroDatum_sin₀ :
    (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).sin₀ =
      blockMap (angleSinOp 𝕜 θ) (0 : Z₀ →L[𝕜] Z₀) := rfl

/-- Its `Pᗮ`-side sine is the sequence's, extended by zero over `Z₁`. -/
@[simp]
theorem angleSequenceZeroDatum_sin₁ :
    (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).sin₁ =
      blockMap (angleSinOp 𝕜 θ) (0 : Z₁ →L[𝕜] Z₁) := rfl

/-- `sin² Θ₀` for the combined datum factors through the sequence's `ℓ²`: the
angle-`0` summand contributes nothing to the defect. -/
theorem angleSequenceZeroDatum_sin₀_sq :
    (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).sin₀ ∘L (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).sin₀ =
      modelInl 𝕜 (AngleSequenceSpace 𝕜) Z₀ ∘L angleSinSqOp 𝕜 θ ∘L
        WithLp.fstL 2 𝕜 (AngleSequenceSpace 𝕜) Z₀ := by
  rw [angleSequenceZeroDatum_sin₀, blockMap_comp, angleSinOp_comp_angleSinOp,
    ContinuousLinearMap.zero_comp, blockMap_zero_right]

/-- **The defect block of the pair with prescribed angle-`0` multiplicities is
compact** — the printed hypothesis of Corollary 3.1, unaffected by the extra
angle-`0` summands. -/
theorem isCompactOperator_angleSequenceZeroDefectBlock
    (hlim : Tendsto θ atTop (nhds 0)) :
    IsCompactOperator
      ((sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
            (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))).starProjection ∘L
        (ContinuousLinearMap.id 𝕜
            (WithLp 2 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀) ×
              WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))) -
          (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).targetSubspace.starProjection) ∘L
        (sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
            (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))).starProjection) := by
  refine isCompactOperator_halmosDefectBlock _ ?_
  rw [angleSequenceZeroDatum_sin₀_sq]
  exact isCompactOperator_modelInl_comp_fstL (isCompactOperator_angleSinSqOp hlim)

/-- **The angle list of that pair is exactly the prescribed sequence.**  The
angle-`0` summands are invisible to the approximation numbers. -/
theorem approximationNumber_angleSequenceZeroDefectBlock (hθ0 : ∀ n, 0 ≤ θ n)
    (hθ2 : ∀ n, θ n ≤ Real.pi / 2) (hanti : Antitone θ) (n : ℕ) :
    ((sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
            (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))).starProjection ∘L
        (ContinuousLinearMap.id 𝕜
            (WithLp 2 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀) ×
              WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))) -
          (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).targetSubspace.starProjection) ∘L
        (sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
            (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))).starProjection).approximationNumber n =
      Real.sin (θ n) ^ 2 := by
  rw [approximationNumber_halmosDefectBlock, angleSequenceZeroDatum_sin₀_sq,
    approximationNumber_modelInl_comp_fstL, approximationNumber_angleSinSqOp hθ0 hθ2 hanti]

end ZeroMultiplicity

section ZeroKernel

variable {𝕜 : Type*} [RCLike 𝕜] {θ : ℕ → ℝ}

/-- `sin Θ` is injective exactly where no prescribed angle has vanishing sine. -/
theorem angleSinOp_eq_zero_iff (hsin : ∀ n, Real.sin (θ n) ≠ 0)
    (x : AngleSequenceSpace 𝕜) : angleSinOp 𝕜 θ x = 0 ↔ x = 0 := by
  refine ⟨fun hx => lp.ext (funext fun n => ?_), fun hx => by rw [hx, map_zero]⟩
  have h := congrArg (fun w : AngleSequenceSpace 𝕜 => (w : ∀ _ : ℕ, 𝕜) n) hx
  simp only [angleSinOp_apply, lp.coeFn_zero, Pi.zero_apply] at h
  have hne : angleSinSeq 𝕜 θ n ≠ 0 := by
    simp only [angleSinSeq, ne_eq, RCLike.ofReal_eq_zero]
    exact hsin n
  have hx0 : (x : ∀ _ : ℕ, 𝕜) n = 0 := (mul_eq_zero.mp h).resolve_left hne
  simpa using hx0

/-- The prescribed angles have nonvanishing sine when none of them is `0`. -/
theorem sin_ne_zero_of_ne_zero (hθ0 : ∀ n, 0 ≤ θ n) (hθ2 : ∀ n, θ n ≤ Real.pi / 2)
    (hne : ∀ n, θ n ≠ 0) (n : ℕ) : Real.sin (θ n) ≠ 0 :=
  ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
    (lt_of_le_of_ne (hθ0 n) (Ne.symm (hne n)))
    (lt_of_le_of_lt (hθ2 n) (by linarith [Real.pi_pos])))

/-- `cos Θ` is injective exactly where no prescribed angle has vanishing cosine. -/
theorem angleCosOp_eq_zero_iff (hcos : ∀ n, Real.cos (θ n) ≠ 0)
    (x : AngleSequenceSpace 𝕜) : angleCosOp 𝕜 θ x = 0 ↔ x = 0 := by
  refine ⟨fun hx => lp.ext (funext fun n => ?_), fun hx => by rw [hx, map_zero]⟩
  have h := congrArg (fun w : AngleSequenceSpace 𝕜 => (w : ∀ _ : ℕ, 𝕜) n) hx
  simp only [angleCosOp_apply, lp.coeFn_zero, Pi.zero_apply] at h
  have hne : angleCosSeq 𝕜 θ n ≠ 0 := by
    simp only [angleCosSeq, ne_eq, RCLike.ofReal_eq_zero]
    exact hcos n
  have hx0 : (x : ∀ _ : ℕ, 𝕜) n = 0 := (mul_eq_zero.mp h).resolve_left hne
  simpa using hx0

/-- The prescribed angles have nonvanishing cosine when none of them is `π / 2`.

This is the angle-`π/2` counterpart of `sin_ne_zero_of_ne_zero`: it is what makes the
crossed defect `U ⊓ Vᗮ` of the realized pair trivial. -/
theorem cos_ne_zero_of_lt_pi_div_two (hθ0 : ∀ n, 0 ≤ θ n)
    (hθ2 : ∀ n, θ n < Real.pi / 2) (n : ℕ) : Real.cos (θ n) ≠ 0 :=
  ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ0 n, Real.pi_pos], hθ2 n⟩)

variable (𝕜 θ)

/-- **The kernel of `sin Θ` is trivial** when no prescribed angle is `0`. -/
theorem ker_angleSinOp_eq_bot (hθ0 : ∀ n, 0 ≤ θ n) (hθ2 : ∀ n, θ n ≤ Real.pi / 2)
    (hne : ∀ n, θ n ≠ 0) :
    LinearMap.ker
        (angleSinOp 𝕜 θ : AngleSequenceSpace 𝕜 →ₗ[𝕜] AngleSequenceSpace 𝕜) = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx
  exact (angleSinOp_eq_zero_iff (sin_ne_zero_of_ne_zero hθ0 hθ2 hne) x).mp hx

/-- **The kernel of `cos Θ` is trivial** when no prescribed angle is `π / 2`. -/
theorem ker_angleCosOp_eq_bot (hθ0 : ∀ n, 0 ≤ θ n) (hθ2 : ∀ n, θ n < Real.pi / 2) :
    LinearMap.ker
        (angleCosOp 𝕜 θ : AngleSequenceSpace 𝕜 →ₗ[𝕜] AngleSequenceSpace 𝕜) = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx
  exact (angleCosOp_eq_zero_iff (cos_ne_zero_of_lt_pi_div_two hθ0 hθ2) x).mp hx

/-- **The kernel of `sin Θ` extended by zero over `Z` is exactly `Z`**, provided the
prescribed sequence itself has no zero angle.  This is the angle-`0` eigenspace of
the combined datum, on either side. -/
theorem ker_blockMap_angleSinOp (hθ0 : ∀ n, 0 ≤ θ n)
    (hθ2 : ∀ n, θ n ≤ Real.pi / 2) (hne : ∀ n, θ n ≠ 0)
    (Z : Type*) [NormedAddCommGroup Z] [InnerProductSpace 𝕜 Z] :
    LinearMap.ker ((blockMap (angleSinOp 𝕜 θ) (0 : Z →L[𝕜] Z)) :
        WithLp 2 (AngleSequenceSpace 𝕜 × Z) →ₗ[𝕜]
          WithLp 2 (AngleSequenceSpace 𝕜 × Z)) =
      Submodule.map
        (modelInr 𝕜 (AngleSequenceSpace 𝕜) Z :
          Z →ₗ[𝕜] WithLp 2 (AngleSequenceSpace 𝕜 × Z)) ⊤ := by
  have hsin := sin_ne_zero_of_ne_zero hθ0 hθ2 hne
  ext z
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, Submodule.mem_map,
    Submodule.mem_top, true_and, blockMap_apply, zero_apply]
  constructor
  · intro hz
    have hfst : angleSinOp 𝕜 θ (WithLp.ofLp z).1 = 0 :=
      congrArg (fun w : WithLp 2 (AngleSequenceSpace 𝕜 × Z) => (WithLp.ofLp w).1) hz
    exact ⟨(WithLp.ofLp z).2,
      (eq_modelInr_of_fst_eq_zero ((angleSinOp_eq_zero_iff hsin _).mp hfst)).symm⟩
  · rintro ⟨y, rfl⟩
    rw [show (WithLp.ofLp (modelInr 𝕜 (AngleSequenceSpace 𝕜) Z y)).1 = 0 from rfl,
      map_zero]
    rfl

end ZeroKernel

/-! ## The realized pair's generic invariant

The realization computes the angle list of the *ambient* defect block `P (1 - Q) P`,
while the classification's invariant is the eigenvalue list of the *generic* cosine block
of the pair `(U, Vᗮ)`.  Once no prescribed angle is `0` or `π/2` the realized pair puts no
mass on any of the four elementary Halmos summands, so
`compactAngleEigenvalueList_genericCosineBlock_eq_ambient` identifies the two lists. -/

section GenericInvariant

/-- **The realized pair's generic invariant is the prescribed angle list.**

The classifying invariant of Corollary 3.1's defect-block form, evaluated on the pair
realized by `angleSequenceDatum`, is `n ↦ sin² θₙ`.  Grounded by `:=` on the realization
sentence's approximation-number computation and on
`approximationNumber_genericCosineBlock_eq_ambient`; no angle mathematics is redone.

The strict bounds `0 < θₙ < π/2` are what make the four elementary Halmos summands vanish,
which is the hypothesis of that bridge. -/
theorem compactAngleEigenvalueList_genericCosineBlock_angleSequenceDatum
    (𝕜 : Type*) [RCLike 𝕜] (θ : ℕ → ℝ)
    (hθ0 : ∀ n, 0 < θ n) (hθ2 : ∀ n, θ n < Real.pi / 2) (hanti : Antitone θ) :
    compactAngleEigenvalueList
        (genericCosineBlock
          (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
          ((angleSequenceDatum 𝕜 θ).targetSubspace)ᗮ) =
      fun n => Real.sin (θ n) ^ 2 := by
  have hθ0' : ∀ n, 0 ≤ θ n := fun n => (hθ0 n).le
  have hθ2' : ∀ n, θ n ≤ Real.pi / 2 := fun n => (hθ2 n).le
  have hne : ∀ n, θ n ≠ 0 := fun n => (hθ0 n).ne'
  have hsin : LinearMap.ker
      ((angleSinOp 𝕜 θ : AngleSequenceSpace 𝕜 →L[𝕜] AngleSequenceSpace 𝕜) :
        AngleSequenceSpace 𝕜 →ₗ[𝕜] AngleSequenceSpace 𝕜) = ⊥ :=
    ker_angleSinOp_eq_bot 𝕜 θ hθ0' hθ2' hne
  have hcos : LinearMap.ker
      ((angleCosOp 𝕜 θ : AngleSequenceSpace 𝕜 →L[𝕜] AngleSequenceSpace 𝕜) :
        AngleSequenceSpace 𝕜 →ₗ[𝕜] AngleSequenceSpace 𝕜) = ⊥ :=
    ker_angleCosOp_eq_bot 𝕜 θ hθ0' hθ2
  -- The four elementary Halmos summands of the realized pair are trivial.
  have hcommon : halmosCommonPart
      (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
      (angleSequenceDatum 𝕜 θ).targetSubspace = ⊥ := by
    rw [show halmosCommonPart
        (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
        (angleSequenceDatum 𝕜 θ).targetSubspace = _ from
      (angleSequenceDatum 𝕜 θ).halmosCommonPart_eq,
      angleSequenceDatum_sin₀, hsin, Submodule.map_bot]
  have hsource : halmosSourceDefect
      (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
      (angleSequenceDatum 𝕜 θ).targetSubspace = ⊥ := by
    rw [show halmosSourceDefect
        (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
        (angleSequenceDatum 𝕜 θ).targetSubspace = _ from
      (angleSequenceDatum 𝕜 θ).halmosSourceDefect_eq,
      angleSequenceDatum_cos₀, hcos, Submodule.map_bot]
  have htarget : halmosTargetDefect
      (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
      (angleSequenceDatum 𝕜 θ).targetSubspace = ⊥ := by
    rw [show halmosTargetDefect
        (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
        (angleSequenceDatum 𝕜 θ).targetSubspace = _ from
      (angleSequenceDatum 𝕜 θ).halmosTargetDefect_eq,
      angleSequenceDatum_cos₁, hcos, Submodule.map_bot]
  have hexterior : halmosExteriorPart
      (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
      (angleSequenceDatum 𝕜 θ).targetSubspace = ⊥ := by
    rw [show halmosExteriorPart
        (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
        (angleSequenceDatum 𝕜 θ).targetSubspace = _ from
      (angleSequenceDatum 𝕜 θ).halmosExteriorPart_eq,
      angleSequenceDatum_sin₁, hsin, Submodule.map_bot]
  have htriv : halmosTrivialPart
      (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
      ((angleSequenceDatum 𝕜 θ).targetSubspace)ᗮ = ⊥ := by
    rw [halmosTrivialPart_orthogonal_right, show halmosTrivialPart
        (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
        (angleSequenceDatum 𝕜 θ).targetSubspace =
      (halmosCommonPart _ _ ⊔ halmosSourceDefect _ _) ⊔
        (halmosTargetDefect _ _ ⊔ halmosExteriorPart _ _) from rfl,
      hcommon, hsource, htarget, hexterior, bot_sup_eq, bot_sup_eq]
  -- The bridge, then the realization's own computation of the ambient list.
  rw [compactAngleEigenvalueList_genericCosineBlock_eq_ambient _ _ htriv,
    Submodule.starProjection_orthogonal (angleSequenceDatum 𝕜 θ).targetSubspace]
  exact funext fun n =>
    approximationNumber_angleSequenceDefectBlock hθ0' hθ2' hanti n

end GenericInvariant

end DavisKahan
end TauCeti
