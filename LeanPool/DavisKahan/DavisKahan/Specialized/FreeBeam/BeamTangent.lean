/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamSection9
import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63Unbounded
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.NumericalBounds
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.RealLowerBound

/-! # Beam Tangent -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Section 9, equations (9.5)--(9.7): the tangent refinement, on the genuine operator

`BeamSection9` proved the two Rayleigh--Ritz inputs for the free-beam example —
the compression form bound `beamRitz_form_le`, the residual norm
`norm_beamRitzResidual_le`, and the perturbed spectral gap
`beamPerturbed_specProjection_Ioo_eq_zero`.  This module bundles them into the
`BoundedCompressionTrialBlock` the unbounded Theorem 6.3 consumes and reads off the
paper's tangent envelope.

The endpoint is `beamTanTheta_le`:

    ‖tan Θ₀‖ ≤ tangentThetaExactBound ε

for the genuine perturbed beam `A + ε t`, its exact low spectral subspace, and the
affine trial subspace — no certificate record, no hypothesis beyond `0 < ε < 100`.
Feeding it to `DavisKahan1970.Section9.equation_9_6` produces the printed decimal.

## The residual is the recentered one

The trial block's residual is `(1 - P_Z) ∘ (A + ε t)|_Z`, whose Gram matrix is the
*recentered* `orthogonalResidualGram ε = (ε²/30)[[1,-1],[-1,1]]` rather than the
initial `residualGram ε`.  That is the whole content of the Rayleigh--Ritz
refinement: the initial residual's top singular value is `|ε|√((11+√76)/30)`, the
recentered one is `|ε|√15/15`, which is smaller by a factor of about 3.9.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Model

open DavisKahan1970.Section9
open TauCeti.DavisKahan.TanTheta
open TauCeti.DavisKahan.TanTheta
open TauCeti.DavisKahan.ExactSinTheta

noncomputable section

/-! ## The Ritz compression as a bounded self-adjoint block -/

/-- The Rayleigh--Ritz compression of the perturbation to the trial subspace. -/
def beamRitzCompression (ε : ℝ) : beamTrial →L[ℂ] beamTrial :=
  beamTrial.orthogonalProjectionOnto ∘L beamResidual ε

/-- The Rayleigh--Ritz compression of the beam operator, in ambient
coordinates. -/
theorem beamRitzCompression_coe (ε : ℝ) (x : beamTrial) :
    ((beamRitzCompression ε x : beamTrial) : BeamL2)
      = beamTrial.starProjection (beamResidual ε x) := rfl

/-- The compression of a self-adjoint operator to a subspace is self-adjoint. -/
theorem beamRitzCompression_isSelfAdjoint (ε : ℝ) :
    IsSelfAdjoint (beamRitzCompression ε) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  have hproj : ∀ u : BeamL2, ∀ z : beamTrial,
      ⟪beamTrial.starProjection u, (z : BeamL2)⟫_ℂ = ⟪u, (z : BeamL2)⟫_ℂ := by
    intro u z
    rw [Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 z.2]
  have hx : ⟪(beamRitzCompression ε x : beamTrial), y⟫_ℂ
      = ⟪beamResidual ε x, (y : BeamL2)⟫_ℂ := by
    rw [Submodule.coe_inner, beamRitzCompression_coe, hproj]
  have hy : ⟪x, (beamRitzCompression ε y : beamTrial)⟫_ℂ
      = ⟪(x : BeamL2), beamResidual ε y⟫_ℂ := by
    rw [Submodule.coe_inner, beamRitzCompression_coe, ← inner_conj_symm, hproj,
      inner_conj_symm]
  show ⟪(beamRitzCompression ε x : beamTrial), y⟫_ℂ
      = ⟪x, (beamRitzCompression ε y : beamTrial)⟫_ℂ
  rw [hx, hy]
  exact beamPerturbation_isSelfAdjoint ε (x : BeamL2) (y : BeamL2)

/-! ## The trial block -/

/-- **The Rayleigh--Ritz trial block of the Section 9 example.**  The trial subspace
is the affine plane, the compression is `beamRitzCompression`, and the residual is
the part of `(A + ε t)|_Z` orthogonal to `Z`. -/
def beamTrialBlock (ε : ℝ) : BoundedCompressionTrialBlock (beamPerturbed ε) beamTrial where
  domain_le := fun _ hy => beamTrial_le_domain hy
  operator := beamRitzCompression ε
  operator_selfAdjoint := beamRitzCompression_isSelfAdjoint ε
  operator_apply x := by
    rw [beamRitzCompression_coe]
    congr 1
    have hker : beamOperator ⟨(x : BeamL2), beamTrial_le_domain x.2⟩ = 0 :=
      beamOperator_apply_trial x.2 _
    show beamResidual ε x = _
    rw [show (beamPerturbed ε) ⟨(x : BeamL2), beamTrial_le_domain x.2⟩
        = beamOperator ⟨(x : BeamL2), beamTrial_le_domain x.2⟩
          + beamPerturbation ε (x : BeamL2) from rfl, hker, zero_add]
    rfl
  residual := beamResidual ε - beamTrialIncl ∘L beamRitzCompression ε
  residual_apply x := by
    have hker : beamOperator ⟨(x : BeamL2), beamTrial_le_domain x.2⟩ = 0 :=
      beamOperator_apply_trial x.2 _
    rw [show (beamPerturbed ε) ⟨(x : BeamL2), beamTrial_le_domain x.2⟩
        = beamOperator ⟨(x : BeamL2), beamTrial_le_domain x.2⟩
          + beamPerturbation ε (x : BeamL2) from rfl, hker, zero_add]
    rfl

/-- Evaluating the trial block's residual. -/
theorem beamTrialBlock_residual_apply (ε : ℝ) (x : beamTrial) :
    (beamTrialBlock ε).residual x
      = beamResidual ε x - beamTrial.starProjection (beamResidual ε x) := rfl

/-- **The recentered residual norm.**  `norm_beamRitzResidual_le` in operator form. -/
theorem norm_beamTrialBlock_residual_le (ε : ℝ) :
    ‖(beamTrialBlock ε).residual‖ ≤ orthogonalResidualSingularValue ε := by
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ ?_
  · unfold orthogonalResidualSingularValue
    positivity
  · intro x
    rw [beamTrialBlock_residual_apply]
    exact norm_beamRitzResidual_le ε x

/-- The compression form bound, in the shape the trial block's consumer takes. -/
theorem beamTrialBlock_compression_form_le (ε : ℝ) (hε : 0 ≤ ε) (z : beamTrial) :
    RCLike.re ⟪(beamTrialBlock ε).operator z, z⟫_ℂ ≤ ritzHigh ε * ‖z‖ ^ 2 := by
  have hz : ⟪(beamTrialBlock ε).operator z, z⟫_ℂ = ⟪beamResidual ε z, (z : BeamL2)⟫_ℂ := by
    rw [Submodule.coe_inner]
    show ⟪beamTrial.starProjection (beamResidual ε z), (z : BeamL2)⟫_ℂ = _
    rw [Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 z.2]
  rw [hz]
  exact beamRitz_form_le ε hε z

/-! ### The trial block's residual is exactly rank one

`orthogonalResidualGram ε = (ε²/30) [[1, -1], [-1, 1]]` has rank one, so the second
approximation number of the Rayleigh--Ritz residual vanishes and its two-term Ky Fan
gauge equals its operator norm.  This is what the 2-norm half of equation (9.6) needs
and what the operator-norm half did not: `‖R̂‖₁ = ‖R̂‖₂ = ε/√15` in the paper's
notation. -/

/-- The recentered residual kills the direction `φ₁ + φ₂`. -/
theorem beamTrialBlock_residual_vecOne_add_vecTwo (ε : ℝ) :
    (beamTrialBlock ε).residual (beamTrialVecOne + beamTrialVecTwo) = 0 := by
  rw [beamTrialBlock_residual_apply]
  exact beamRitzResidual_vecOne_add_vecTwo_eq_zero ε

/-- Hence the two residual columns are opposite: the residual has a one-dimensional
range. -/
theorem beamTrialBlock_residual_vecTwo (ε : ℝ) :
    (beamTrialBlock ε).residual beamTrialVecTwo
      = -(beamTrialBlock ε).residual beamTrialVecOne := by
  have h := beamTrialBlock_residual_vecOne_add_vecTwo ε
  rw [map_add] at h
  exact eq_neg_of_add_eq_zero_right h

/-- **The Rayleigh--Ritz residual has rank at most one.** -/
theorem beamTrialBlock_residual_rank_le (ε : ℝ) :
    ((beamTrialBlock ε).residual).rank ≤ (1 : Cardinal) := by
  classical
  have hle : LinearMap.range
      (((beamTrialBlock ε).residual : beamTrial →L[ℂ] BeamL2) : beamTrial →ₗ[ℂ] BeamL2)
      ≤ Submodule.span ℂ
        ({(beamTrialBlock ε).residual beamTrialVecOne} : Set BeamL2) := by
    rintro y ⟨x, rfl⟩
    obtain ⟨α, β, hx⟩ := exists_beamTrialVec_repr x
    refine Submodule.mem_span_singleton.2 ⟨α - β, ?_⟩
    show (α - β) • (beamTrialBlock ε).residual beamTrialVecOne
      = (beamTrialBlock ε).residual x
    rw [hx, map_add, map_smul, map_smul, beamTrialBlock_residual_vecTwo]
    module
  calc ((beamTrialBlock ε).residual).rank
      ≤ Module.rank ℂ (Submodule.span ℂ
          ({(beamTrialBlock ε).residual beamTrialVecOne} : Set BeamL2)) :=
        Submodule.rank_mono hle
    _ ≤ 1 := by
        simpa using rank_span_le ({(beamTrialBlock ε).residual beamTrialVecOne} : Set BeamL2)

/-- **The second approximation number of the Rayleigh--Ritz residual vanishes.**  The
residual is its own rank-one approximant. -/
theorem approximationSingularValue_one_beamTrialBlock_residual_le (ε : ℝ) :
    approximationSingularValue 1 ((beamTrialBlock ε).residual) ≤ 0 := by
  have hrank : ((beamTrialBlock ε).residual).rank ≤ ((1 : ℕ) : Cardinal) := by
    simpa using beamTrialBlock_residual_rank_le ε
  have h := ((beamTrialBlock ε).residual).approximationNumber_le_norm_sub hrank
  rwa [sub_self, norm_zero] at h

/-- **The two-term Ky Fan gauge of the Rayleigh--Ritz residual equals its operator
norm bound.**  This is the paper's `‖R̂‖₁ = ‖R̂‖₂ = ε/√15`. -/
theorem kyFanTwo_beamTrialBlock_residual_le (ε : ℝ) :
    kyFanApproximationGauge 2 ((beamTrialBlock ε).residual)
      ≤ orthogonalResidualSingularValue ε := by
  have h0 : approximationSingularValue 0 ((beamTrialBlock ε).residual)
      ≤ orthogonalResidualSingularValue ε := by
    have hz : approximationSingularValue 0 ((beamTrialBlock ε).residual)
        = ‖(beamTrialBlock ε).residual‖ :=
      ((beamTrialBlock ε).residual).approximationNumber_index_zero
    rw [hz]
    exact norm_beamTrialBlock_residual_le ε
  have h1 := approximationSingularValue_one_beamTrialBlock_residual_le ε
  have hsum : approximationSingularValue 0 ((beamTrialBlock ε).residual)
      + approximationSingularValue 1 ((beamTrialBlock ε).residual)
      ≤ orthogonalResidualSingularValue ε := by linarith
  unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  exact hsum
end

/-! ## Equation (9.6): the tangent envelope for the genuine operator -/

/-- **The largest tangent** of the angles between the affine trial subspace and the
exact low spectral subspace of `A + ε t` -- everything at or below the upper Ritz
value. -/
noncomputable def beamTanTheta (ε : ℝ) : ℝ :=
  ‖theorem63DirectedTangent beamTrial
    (selfAdjointSpectralSubspace (beamPerturbed ε) (beamPerturbed_isSelfAdjoint ε)
      (Set.Iic (ritzHigh ε)) measurableSet_Iic)‖

/-- The upper Ritz value stays below `500` on the paper's parameter range. -/
theorem ritzHigh_lt_five_hundred {ε : ℝ} (hε100 : ε < 100) :
    ritzHigh ε < 500 := by
  have hc : ritzHighCoefficient ≤ 1 := by
    unfold ritzHighCoefficient
    have h3 : Real.sqrt 3 ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 from by
        rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  have hcpos : 0 < ritzHighCoefficient := by
    unfold ritzHighCoefficient
    positivity
  unfold ritzHigh
  nlinarith

/-- **Davis--Kahan 1970, equation (9.6), for the genuine free-beam operator.**

The largest tangent of the angles between the affine trial subspace and the exact
low spectral subspace of `A + ε t` is at most the exact Rayleigh--Ritz envelope
`tangentThetaExactBound ε`.

Everything in the hypothesis list is the paper's: `0 < ε < 100`.  The gap is the
proved `beamPerturbed_specProjection_Ioo_eq_zero`, the compression bound is the
proved `beamRitz_form_le`, and the residual norm is the proved
`norm_beamRitzResidual_le`.  No certificate field appears in the statement. -/
theorem beamTanTheta_le (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanTheta ε ≤ tangentThetaExactBound ε := by
  have hritz : ritzHigh ε < 500 := ritzHigh_lt_five_hundred hε100
  have hδ : (0 : ℝ) < 500 - ritzHigh ε := by linarith
  have hgap : TauCeti.LinearPMap.specProjection (beamPerturbed_isSelfAdjoint ε)
      (Set.Ioo (ritzHigh ε) (ritzHigh ε + (500 - ritzHigh ε))) measurableSet_Ioo = 0 := by
    rw [show ritzHigh ε + (500 - ritzHigh ε) = 500 from by ring]
    exact beamPerturbed_specProjection_Ioo_eq_zero ε hε.le
  -- the operator norm, read as the first Ky Fan gauge
  have hmain := theorem6_3_unbounded_ideal_directedTangent
    (KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) 1 one_pos)
    (beamPerturbed ε) (beamPerturbed_isSelfAdjoint ε) (beamTrialBlock ε) hδ hgap
    (beamTrialBlock_compression_form_le ε hε.le)
    (KyFanDominantIdealFamily.kyFan_mem 1 one_pos _)
  have hgauge := hmain.2
  rw [KyFanDominantIdealFamily.kyFan_gauge, KyFanDominantIdealFamily.kyFan_gauge,
    kyFanApproximationGauge_one, kyFanApproximationGauge_one] at hgauge
  have hchain : (500 - ritzHigh ε) * beamTanTheta ε
      ≤ orthogonalResidualSingularValue ε :=
    le_trans hgauge (norm_beamTrialBlock_residual_le ε)
  have hden : (1 : ℝ) - ritzHighCoefficient / 500 * ε ≠ 0 := by
    have h : ritzHigh ε = ε * ritzHighCoefficient := rfl
    rw [h] at hritz
    intro hzero
    apply absurd hritz
    push Not
    nlinarith [hzero]
  have hbound : tangentThetaExactBound ε
      = orthogonalResidualSingularValue ε / (500 - ritzHigh ε) := by
    unfold tangentThetaExactBound orthogonalResidualSingularValue
    rw [abs_of_pos hε, show ritzHigh ε = ε * ritzHighCoefficient from rfl,
      div_eq_div_iff hden (by
        rw [show ritzHigh ε = ε * ritzHighCoefficient from rfl] at hδ
        exact ne_of_gt hδ)]
    ring
  rw [hbound, le_div_iff₀ hδ]
  linarith [hchain]

/-- **Equation (9.6) as printed.**  The exact envelope, relaxed to the paper's
decimal. -/
theorem beamTanTheta_lt_printed (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanTheta ε
      < ((1291 : ℝ) / 2500000 * ε) / (1 - (7887 : ℝ) / 5000000 * ε) :=
  equation_9_6 ε (beamTanTheta ε) hε hε100 (beamTanTheta_le ε hε hε100)

/-! ## Equation (9.6), second sentence: the same bound in the 2-norm

"The same bound applies to `tan θ₁ + tan θ₂` in the 2-norm."  Nothing changes on the
left of Theorem 6.3 except the ideal gauge, and nothing changes on the right because
the recentered residual is rank one: its second approximation number is zero, so its
two-term Ky Fan gauge is again `ε/√15`. -/

/-- **The two-term Ky Fan sum of the tangents** of the angles between the affine trial
subspace and the exact low spectral subspace of `A + ε t`. -/
noncomputable def beamTanThetaSum (ε : ℝ) : ℝ :=
  kyFanApproximationGauge 2 (theorem63DirectedTangent beamTrial
    (selfAdjointSpectralSubspace (beamPerturbed ε) (beamPerturbed_isSelfAdjoint ε)
      (Set.Iic (ritzHigh ε)) measurableSet_Iic))

/-- **Davis--Kahan 1970, equation (9.6) in the 2-norm, for the genuine free-beam
operator.**

`tan θ₁ + tan θ₂` obeys the *same* exact envelope as `tan θ₁` alone.  The only two
changes from `beamTanTheta_le` are the ideal gauge — `KyFanDominantIdealFamily.kyFan 2`
instead of `kyFan 1` — and the residual bound, which is `kyFanTwo_beamTrialBlock_residual_le`
instead of the operator norm; the latter is available precisely because the recentered
residual Gram matrix is rank one. -/
theorem beamTanThetaSum_le (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanThetaSum ε ≤ tangentThetaExactBound ε := by
  have hritz : ritzHigh ε < 500 := ritzHigh_lt_five_hundred hε100
  have hδ : (0 : ℝ) < 500 - ritzHigh ε := by linarith
  have hgap : TauCeti.LinearPMap.specProjection (beamPerturbed_isSelfAdjoint ε)
      (Set.Ioo (ritzHigh ε) (ritzHigh ε + (500 - ritzHigh ε))) measurableSet_Ioo = 0 := by
    rw [show ritzHigh ε + (500 - ritzHigh ε) = 500 from by ring]
    exact beamPerturbed_specProjection_Ioo_eq_zero ε hε.le
  have hmain := theorem6_3_unbounded_ideal_directedTangent
    (KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) 2 (by norm_num))
    (beamPerturbed ε) (beamPerturbed_isSelfAdjoint ε) (beamTrialBlock ε) hδ hgap
    (beamTrialBlock_compression_form_le ε hε.le)
    (KyFanDominantIdealFamily.kyFan_mem 2 (by norm_num) _)
  have hgauge := hmain.2
  rw [KyFanDominantIdealFamily.kyFan_gauge, KyFanDominantIdealFamily.kyFan_gauge] at hgauge
  have hchain : (500 - ritzHigh ε) * beamTanThetaSum ε
      ≤ orthogonalResidualSingularValue ε :=
    le_trans hgauge (kyFanTwo_beamTrialBlock_residual_le ε)
  have hden : (1 : ℝ) - ritzHighCoefficient / 500 * ε ≠ 0 := by
    have h : ritzHigh ε = ε * ritzHighCoefficient := rfl
    rw [h] at hritz
    intro hzero
    apply absurd hritz
    push Not
    nlinarith [hzero]
  have hbound : tangentThetaExactBound ε
      = orthogonalResidualSingularValue ε / (500 - ritzHigh ε) := by
    unfold tangentThetaExactBound orthogonalResidualSingularValue
    rw [abs_of_pos hε, show ritzHigh ε = ε * ritzHighCoefficient from rfl,
      div_eq_div_iff hden (by
        rw [show ritzHigh ε = ε * ritzHighCoefficient from rfl] at hδ
        exact ne_of_gt hδ)]
    ring
  rw [hbound, le_div_iff₀ hδ]
  linarith [hchain]

/-- **Equation (9.6) in the 2-norm, as printed.** -/
theorem beamTanThetaSum_lt_printed (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanThetaSum ε
      < ((1291 : ℝ) / 2500000 * ε) / (1 - (7887 : ℝ) / 5000000 * ε) :=
  equation_9_6 ε (beamTanThetaSum ε) hε hε100 (beamTanThetaSum_le ε hε hε100)

/-! ## The low spectral subspace is exactly two-dimensional

Equations (9.9)--(9.11) reduce the eigenproblem to a two-by-two Schur complement.
That reduction describes the *actual* eigenvectors only if the perturbed operator
really has exactly two spectral dimensions below `500`, and that is a
Rayleigh--Ritz dimension count: coercivity off the trial subspace caps it at
`dim beamTrial`, the Ritz bound attains the cap.

The one hypothesis the general theorem cannot supply is that the low spectral
range lies inside the domain -- `Set.Iic 500` is unbounded below.  Here it does,
because the perturbed beam is positive: the free beam's form is its bending
energy and the perturbation's symbol is `ε t ≥ 0`. -/

/-- **The perturbed beam is positive.** -/
theorem beamPerturbed_form_nonneg (ε : ℝ) (hε : 0 ≤ ε)
    (x : (beamPerturbed ε).domain) :
    0 ≤ (⟪(beamPerturbed ε) x, (x : BeamL2)⟫_ℂ).re := by
  have hxdom : (x : BeamL2) ∈ beamOperator.domain := x.2
  have hsplit : (beamPerturbed ε) x
      = beamOperator ⟨(x : BeamL2), hxdom⟩ + beamPerturbation ε (x : BeamL2) :=
    rfl
  rw [hsplit, inner_add_left, Complex.add_re]
  have h1 : 0 ≤ (⟪beamOperator ⟨(x : BeamL2), hxdom⟩, (x : BeamL2)⟫_ℂ).re :=
    beamShiftedFormData.beam_nonnegative ⟨(x : BeamL2), hxdom⟩
  have h2 := re_inner_beamPerturbation_nonneg ε hε (x : BeamL2)
  linarith

/-- Every negative real is a resolvent point of the perturbed beam. -/
theorem beamPerturbed_mem_resolventSet_of_neg (ε : ℝ) (hε : 0 ≤ ε)
    {lam : ℝ} (hlam : lam < 0) :
    (lam : ℂ) ∈ TauCeti.LinearPMap.resolventSet (beamPerturbed ε) := by
  refine (TauCeti.LinearPMap.mem_resolventSet_and_norm_le_of_lower_bound
    (beamPerturbed_isSelfAdjoint ε) (c := -lam) (by linarith) ?_).1
  intro x
  rcases eq_or_lt_of_le (norm_nonneg ((x : BeamL2))) with hx0 | hxpos
  · rw [← hx0, mul_zero]
    exact norm_nonneg _
  · have hform := beamPerturbed_form_nonneg ε hε x
    have hCS : (⟪(beamPerturbed ε) x - (lam : ℂ) • (x : BeamL2),
        (x : BeamL2)⟫_ℂ).re
        ≤ ‖(beamPerturbed ε) x - (lam : ℂ) • (x : BeamL2)‖ * ‖(x : BeamL2)‖ := by
      exact re_inner_le_norm (𝕜 := ℂ)
        ((beamPerturbed ε) x - (lam : ℂ) • (x : BeamL2)) ((x : BeamL2))
    have hval : (⟪(beamPerturbed ε) x - (lam : ℂ) • (x : BeamL2),
        (x : BeamL2)⟫_ℂ).re
        = (⟪(beamPerturbed ε) x, (x : BeamL2)⟫_ℂ).re
          - lam * ‖(x : BeamL2)‖ ^ 2 := by
      have hself : ⟪(x : BeamL2), (x : BeamL2)⟫_ℂ = ((‖(x : BeamL2)‖ ^ 2 : ℝ) : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K]
        push_cast
        rfl
      rw [inner_sub_left, Complex.sub_re, inner_smul_left, Complex.conj_ofReal, hself,
        ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [hval] at hCS
    have hsq : -lam * ‖(x : BeamL2)‖ ^ 2
        ≤ ‖(beamPerturbed ε) x - (lam : ℂ) • (x : BeamL2)‖ * ‖(x : BeamL2)‖ := by
      nlinarith [hform, hCS]
    refine le_of_mul_le_mul_right ?_ hxpos
    exact le_trans (le_of_eq (by ring)) hsq

/-- The perturbed beam has no spectral mass below zero. -/
theorem beamPerturbed_specProjection_Iio_zero (ε : ℝ) (hε : 0 ≤ ε) :
    TauCeti.LinearPMap.specProjection (beamPerturbed_isSelfAdjoint ε)
      (Set.Iio 0) measurableSet_Iio = 0 :=
  TauCeti.LinearPMap.specProjection_eq_zero_of_subset_resolventSet
    (beamPerturbed_isSelfAdjoint ε) _ _
    (fun _ hlam => beamPerturbed_mem_resolventSet_of_neg ε hε hlam)

/-- Hence the low spectral range lies inside the domain: it is the spectral range
of the *bounded* set `[0, 500]`. -/
theorem beamPerturbed_specRange_le_domain (ε : ℝ) (hε : 0 ≤ ε)
    {y : BeamL2}
    (hy : y ∈ TauCeti.LinearPMap.specRange (beamPerturbed_isSelfAdjoint ε)
      (Set.Iic 500) measurableSet_Iic) :
    y ∈ (beamPerturbed ε).domain := by
  have hfix : TauCeti.LinearPMap.specProjection (beamPerturbed_isSelfAdjoint ε)
      (Set.Iic 500) measurableSet_Iic y = y :=
    (TauCeti.LinearPMap.mem_specRange_iff _ _ _ _).1 hy
  have hsplit : TauCeti.LinearPMap.specProjection (beamPerturbed_isSelfAdjoint ε)
      (Set.Iic 500) measurableSet_Iic
      = TauCeti.LinearPMap.specProjection (beamPerturbed_isSelfAdjoint ε)
          (Set.Iio 0) measurableSet_Iio
        + TauCeti.LinearPMap.specProjection (beamPerturbed_isSelfAdjoint ε)
          (Set.Icc 0 500) measurableSet_Icc := by
    have hunion := (TauCeti.LinearPMap.spectralPVM (beamPerturbed_isSelfAdjoint ε)).proj_union
      (B₁ := Set.Iio (0 : ℝ)) (B₂ := Set.Icc (0 : ℝ) 500)
      measurableSet_Iio measurableSet_Icc
      (by
        rw [Set.disjoint_left]
        rintro t ht htc
        rw [Set.mem_Iio] at ht
        rw [Set.mem_Icc] at htc
        linarith [htc.1])
    have hset : Set.Iio (0 : ℝ) ∪ Set.Icc 0 500 = Set.Iic 500 := by
      ext t
      simp only [Set.mem_union, Set.mem_Iio, Set.mem_Icc, Set.mem_Iic]
      constructor
      · rintro (h | ⟨-, h⟩)
        · linarith
        · exact h
      · intro h
        rcases lt_or_ge t 0 with h0 | h0
        · exact Or.inl h0
        · exact Or.inr ⟨h0, h⟩
    simp only [TauCeti.LinearPMap.specProjection_def]
    rw [← (TauCeti.LinearPMap.spectralPVM (beamPerturbed_isSelfAdjoint ε)).proj_congr hset
      (measurableSet_Iio.union measurableSet_Icc) measurableSet_Iic, hunion]
  have hy' : TauCeti.LinearPMap.specProjection (beamPerturbed_isSelfAdjoint ε)
      (Set.Icc 0 500) measurableSet_Icc y = y := by
    have h := congrArg (fun T : BeamL2 →L[ℂ] BeamL2 => T y) hsplit
    simp only [add_apply] at h
    rw [beamPerturbed_specProjection_Iio_zero ε hε] at h
    simp only [zero_apply, zero_add] at h
    rw [← h]
    exact hfix
  refine TauCeti.LinearPMap.mem_domain_of_mem_specRange_of_bounded
    (beamPerturbed_isSelfAdjoint ε) _ _ (M := 500) ?_
    ((TauCeti.LinearPMap.mem_specRange_iff _ _ _ _).2 hy')
  intro t ht
  rw [Set.mem_Icc] at ht
  rw [abs_of_nonneg ht.1]
  exact ht.2

/-- **The Rayleigh--Ritz dimension cap for the free beam.**  No finite-dimensional
subspace of the perturbed beam's spectral range below `500` has more dimensions
than the affine trial subspace. -/
theorem beamPerturbed_finrank_le (ε : ℝ) (hε : 0 ≤ ε)
    {W : Submodule ℂ BeamL2} [FiniteDimensional ℂ W]
    (hW : W ≤ TauCeti.LinearPMap.specRange (beamPerturbed_isSelfAdjoint ε)
      (Set.Iic 500) measurableSet_Iic) :
    Module.finrank ℂ W ≤ Module.finrank ℂ beamTrial :=
  TauCeti.LinearPMap.finrank_le_of_le_specRange_Iic (beamPerturbed_isSelfAdjoint ε)
    (β := 1001 / 2) (c := 500) (by norm_num)
    (fun y hy => beamPerturbed_form_ge_of_mem_orthogonal ε hε y hy)
    (fun _ hy => beamPerturbed_specRange_le_domain ε hε hy) hW

/-- **The cap is attained.**  The trial subspace injects into the spectral range
below the upper Ritz value, hence into the one below `500`. -/
theorem beamTrial_finrank_le (ε : ℝ) (hε : 0 ≤ ε)
    {W : Submodule ℂ BeamL2} [FiniteDimensional ℂ W]
    (hW : TauCeti.LinearPMap.specRange (beamPerturbed_isSelfAdjoint ε)
      (Set.Iic (ritzHigh ε)) measurableSet_Iic ≤ W) :
    Module.finrank ℂ beamTrial ≤ Module.finrank ℂ W :=
  TauCeti.LinearPMap.finrank_le_finrank_of_le_specRange_Iic
    (beamPerturbed_isSelfAdjoint ε) (α := ritzHigh ε)
    (fun _ hy => beamTrial_le_domain hy)
    (fun y hy => beamPerturbed_form_le_of_mem_beamTrial ε hε y hy) hW

/-- The affine trial subspace is two-dimensional: the two Ritz vectors are an
orthonormal basis of it. -/
theorem finrank_beamTrial : Module.finrank ℂ beamTrial = 2 := by
  classical
  obtain ⟨h1, h2, h12⟩ := beamTrialVec_orthonormal
  have h21 : ⟪beamTrialVecTwo, beamTrialVecOne⟫_ℂ = 0 := by
    rw [← inner_conj_symm (𝕜 := ℂ) beamTrialVecTwo beamTrialVecOne, h12, map_zero]
  obtain ⟨n1, n2, -⟩ := beamTrial_orthonormal
  have hb1 : (beamTrialVecOne : BeamL2) = centeredAffineLp trialOne := rfl
  have hb2 : (beamTrialVecTwo : BeamL2) = centeredAffineLp trialTwo := rfl
  have hn1 : ‖(beamTrialVecOne : BeamL2)‖ = 1 := by
    rw [hb1]
    nlinarith [n1, norm_nonneg (centeredAffineLp trialOne)]
  have hn2 : ‖(beamTrialVecTwo : BeamL2)‖ = 1 := by
    rw [hb2]
    nlinarith [n2, norm_nonneg (centeredAffineLp trialTwo)]
  have horth : Orthonormal ℂ (![beamTrialVecOne, beamTrialVecTwo] : Fin 2 → beamTrial) := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [h12, h21, hn1, hn2]
  have hrange : Set.range (![beamTrialVecOne, beamTrialVecTwo] : Fin 2 → beamTrial)
      = {beamTrialVecOne, beamTrialVecTwo} := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hspan : ⊤ ≤ Submodule.span ℂ
      (Set.range (![beamTrialVecOne, beamTrialVecTwo] : Fin 2 → beamTrial)) := by
    rw [hrange, beamTrialVec_span_eq_top]
  have hbasis : Module.Basis (Fin 2) ℂ beamTrial :=
    Module.Basis.mk horth.linearIndependent hspan
  rw [Module.finrank_eq_card_basis hbasis]
  simp

/-! ## The direct one-vector bounds following equation (9.8)

Section 9 estimates the angle `φ_k` made by the *single* Ritz vector `e_k` by applying
Theorem 6.3 with the one-dimensional trial space `E₀ = e_k`: then
`A₀ = α̂_k = e_k* (A + ε t) e_k` is the Ritz value itself, the residual is the single column
`r̂_k = (A + ε t) e_k − e_k α̂_k` of norm `ε/√30`, and the gap is `500 − α̂_k`, giving
`tan φ_k < (ε/√30)/(500 − α̂_k)`.  These are sharper than the `sin`-theorem bounds (9.8).

This needs Theorem 6.3 with a **chosen** reducing subspace, not with a spectrum-free
interval: for `k = 1` the interval `(α̂₁, 500)` contains the second Ritz level, so the
operator does have spectrum there.  The chosen subspace is the exact spectral subspace of
`Iic 500`, whose complement carries form at least `500` with no gap hypothesis at all.

The two Ritz vectors are `centeredAffineLp trialOne` and `centeredAffineLp trialTwo`;
`beamRitz_matrix` gives their Ritz values and `beamResidualGram_matrix` their residual
column norms. -/

noncomputable section

open DavisKahan1970.Section9

/-- The exact spectral subspace of the perturbed beam at or below `500`: the reducing
subspace the printed Theorem 6.3 is applied at. -/
abbrev beamLowFiveHundred (ε : ℝ) : Submodule ℂ BeamL2 :=
  selfAdjointSpectralSubspace (beamPerturbed ε) (beamPerturbed_isSelfAdjoint ε)
    (Set.Iic 500) measurableSet_Iic

/-- The line spanned by a trial vector sits inside the trial subspace. -/
theorem span_singleton_le_beamTrial {v : BeamL2} (hv : v ∈ beamTrial) :
    (ℂ ∙ v) ≤ beamTrial :=
  (Submodule.span_singleton_le_iff_mem _ _).mpr hv

/-- On the trial subspace the perturbed beam acts by the perturbation alone: the free beam
annihilates its kernel. -/
theorem beamPerturbed_apply_of_mem_beamTrial (ε : ℝ) {x : BeamL2} (hx : x ∈ beamTrial)
    (h : x ∈ beamOperator.domain) :
    (beamPerturbed ε) ⟨x, h⟩ = beamPerturbation ε x := by
  rw [show (beamPerturbed ε) ⟨x, h⟩
      = beamOperator ⟨x, h⟩ + beamPerturbation ε x from rfl,
    beamOperator_apply_trial hx h, zero_add]

/-- **The one-dimensional Rayleigh--Ritz trial block at a unit Ritz vector.**  The
compression is the scalar `a = ⟪v, ε t v⟫` and the residual is the single Ritz column. -/
def beamColumnBlock (ε : ℝ) (v : BeamL2) (hv : v ∈ beamTrial) (hvnorm : ‖v‖ = 1)
    (a : ℝ) (hform : ⟪v, beamPerturbation ε v⟫_ℂ = ((a : ℝ) : ℂ)) :
    BoundedCompressionTrialBlock (beamPerturbed ε) (ℂ ∙ v) where
  domain_le := fun _ hx => beamTrial_le_domain (span_singleton_le_beamTrial hv hx)
  operator := ((a : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (ℂ ∙ v)
  operator_selfAdjoint := by
    have h1 : IsSelfAdjoint (((a : ℝ) : ℂ)) := by
      show star ((a : ℝ) : ℂ) = ((a : ℝ) : ℂ)
      rw [Complex.star_def, Complex.conj_ofReal]
    have h2 : IsSelfAdjoint (ContinuousLinearMap.id ℂ (ℂ ∙ v)) := by
      rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
      intro x y
      rfl
    exact h1.smul h2
  operator_apply := fun x => by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 x.2
    have hxv : (x : BeamL2) = c • v := hc.symm
    have hmem : (x : BeamL2) ∈ beamTrial := span_singleton_le_beamTrial hv x.2
    show ((a : ℝ) : ℂ) • (x : BeamL2) = _
    rw [beamPerturbed_apply_of_mem_beamTrial ε hmem,
      Submodule.starProjection_unit_singleton ℂ hvnorm, hxv, map_smul,
      inner_smul_right, hform]
    module
  residual := beamPerturbation ε ∘L (ℂ ∙ v).subtypeL - ((a : ℝ) : ℂ) • (ℂ ∙ v).subtypeL
  residual_apply := fun x => by
    have hmem : (x : BeamL2) ∈ beamTrial := span_singleton_le_beamTrial hv x.2
    show beamPerturbation ε (x : BeamL2) - ((a : ℝ) : ℂ) • (x : BeamL2) = _
    rw [beamPerturbed_apply_of_mem_beamTrial ε hmem]
    rfl

/-- The compression form bound for the one-vector block; it is in fact an equality. -/
theorem beamColumnBlock_compression_form (ε : ℝ) (v : BeamL2) (hv : v ∈ beamTrial)
    (hvnorm : ‖v‖ = 1) (a : ℝ) (hform : ⟪v, beamPerturbation ε v⟫_ℂ = ((a : ℝ) : ℂ))
    (z : (ℂ ∙ v)) :
    RCLike.re ⟪(beamColumnBlock ε v hv hvnorm a hform).operator z, z⟫_ℂ
      ≤ a * ‖z‖ ^ 2 := by
  have hop : (beamColumnBlock ε v hv hvnorm a hform).operator z = ((a : ℝ) : ℂ) • z := rfl
  rw [hop, inner_smul_left, Complex.conj_ofReal, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

/-- **The one-vector residual is the single Ritz column.** -/
theorem norm_beamColumnBlock_residual_le (ε : ℝ) (v : BeamL2) (hv : v ∈ beamTrial)
    (hvnorm : ‖v‖ = 1) (a : ℝ) (hform : ⟪v, beamPerturbation ε v⟫_ℂ = ((a : ℝ) : ℂ))
    (hcol : ‖beamPerturbation ε v - ((a : ℝ) : ℂ) • v‖
      ≤ orthogonalResidualColumnNorm ε) :
    ‖(beamColumnBlock ε v hv hvnorm a hform).residual‖
      ≤ orthogonalResidualColumnNorm ε := by
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ ?_
  · unfold orthogonalResidualColumnNorm
    positivity
  · intro x
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 x.2
    have hxv : (x : BeamL2) = c • v := hc.symm
    have hres : (beamColumnBlock ε v hv hvnorm a hform).residual x
        = c • (beamPerturbation ε v - ((a : ℝ) : ℂ) • v) := by
      show beamPerturbation ε (x : BeamL2) - ((a : ℝ) : ℂ) • (x : BeamL2) = _
      rw [hxv, map_smul]
      module
    have hnormx : ‖x‖ = ‖c‖ := by
      have : ‖x‖ = ‖(x : BeamL2)‖ := rfl
      rw [this, hxv, norm_smul, hvnorm, mul_one]
    rw [hres, norm_smul, hnormx, mul_comm]
    exact mul_le_mul_of_nonneg_right hcol (norm_nonneg c)

/-- **Theorem 6.3 at a single Ritz vector.**  The printed one-vector estimate: the largest
tangent between the line `ℂ ∙ v` and the exact low spectral subspace of `A + ε t` is at
most the single residual column norm divided by the gap `500 − a`. -/
theorem beamColumn_tangent_le (ε : ℝ) (v : BeamL2) (hv : v ∈ beamTrial)
    (hvnorm : ‖v‖ = 1) (a : ℝ) (hform : ⟪v, beamPerturbation ε v⟫_ℂ = ((a : ℝ) : ℂ))
    (ha : a < 500)
    (hcol : ‖beamPerturbation ε v - ((a : ℝ) : ℂ) • v‖
      ≤ orthogonalResidualColumnNorm ε) :
    (500 - a) * ‖theorem63DirectedTangent (ℂ ∙ v) (beamLowFiveHundred ε)‖
      ≤ orthogonalResidualColumnNorm ε := by
  have hδ : (0 : ℝ) < 500 - a := by linarith
  have hUnwanted : ∀ y ∈ (beamLowFiveHundred ε)ᗮ,
      ∀ hy : y ∈ (beamPerturbed ε).domain,
      (a + (500 - a)) * ‖y‖ ^ 2
        ≤ RCLike.re ⟪(beamPerturbed ε) ⟨y, hy⟩, y⟫_ℂ := by
    intro y hy hydom
    rw [show a + (500 - a) = (500 : ℝ) from by ring]
    exact le_re_inner_of_mem_orthogonal_selfAdjointSpectralSubspace_Iic
      (beamPerturbed ε) (beamPerturbed_isSelfAdjoint ε) y hy hydom
  have hmain := theorem6_3_unbounded_ideal_directedTangent_of_reducing
    (KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) 1 one_pos)
    (beamPerturbed ε) (beamColumnBlock ε v hv hvnorm a hform) (beamLowFiveHundred ε) hδ
    (orthogonal_selfAdjointSpectralSubspace_starProjection_mem_domain (beamPerturbed ε)
      (beamPerturbed_isSelfAdjoint ε) (Set.Iic 500) measurableSet_Iic)
    (selfAdjoint_apply_orthogonal_selfAdjointSpectralSubspace_starProjection
      (beamPerturbed ε) (beamPerturbed_isSelfAdjoint ε) (Set.Iic 500) measurableSet_Iic)
    (beamColumnBlock_compression_form ε v hv hvnorm a hform) hUnwanted
    (KyFanDominantIdealFamily.kyFan_mem 1 one_pos _)
  have hgauge := hmain.2
  rw [KyFanDominantIdealFamily.kyFan_gauge, KyFanDominantIdealFamily.kyFan_gauge,
    kyFanApproximationGauge_one, kyFanApproximationGauge_one] at hgauge
  exact hgauge.trans (norm_beamColumnBlock_residual_le ε v hv hvnorm a hform hcol)

/-- The tangent of the angle between a single Ritz vector and the exact low spectral
subspace of `A + ε t`. -/
def beamTanPhi (ε : ℝ) (v : BeamL2) : ℝ :=
  ‖theorem63DirectedTangent (ℂ ∙ v) (beamLowFiveHundred ε)‖

/-! ### The two residual columns

Each Ritz column `r̂_k = ε t e_k − e_k α̂_k` has norm exactly `ε/√30`, half the recentered
singular value squared.  The computation is `‖r̂_k‖² = ⟪ε t e_k, ε t e_k⟫ − α̂_k²`, i.e. the
diagonal entry of the initial residual Gram matrix recentered by the Ritz value; the
radical content is `√75 = 5√3`. -/

/-- `√75 = 5√3`, the one radical identity the column norms need. -/
theorem sqrt_seventyFive : Real.sqrt 75 = 5 * Real.sqrt 3 := by
  rw [show (75 : ℝ) = 5 ^ 2 * 3 from by norm_num, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by norm_num)]

/-- The residual column at a unit Ritz vector, squared: the Gram diagonal entry
recentered by the Ritz value. -/
theorem norm_beamColumnResidual_sq (ε : ℝ) (v : BeamL2) (hvnorm : ‖v‖ = 1) (a g : ℝ)
    (hform : ⟪v, beamPerturbation ε v⟫_ℂ = ((a : ℝ) : ℂ))
    (hgram : ⟪beamPerturbation ε v, beamPerturbation ε v⟫_ℂ = ((g : ℝ) : ℂ)) :
    ‖beamPerturbation ε v - ((a : ℝ) : ℂ) • v‖ ^ 2 = g - a ^ 2 := by
  have hP : ‖beamPerturbation ε v‖ ^ 2 = g := by
    have h := hgram
    rw [inner_self_eq_norm_sq_to_K] at h
    have h2 : ((‖beamPerturbation ε v‖ ^ 2 : ℝ) : ℂ) = ((g : ℝ) : ℂ) := by
      push_cast
      exact h
    exact Complex.ofReal_inj.mp h2
  have hcross : RCLike.re ⟪beamPerturbation ε v, ((a : ℝ) : ℂ) • v⟫_ℂ = a ^ 2 := by
    rw [inner_smul_right, ← inner_conj_symm, hform]
    simp [Complex.conj_ofReal]
    ring
  rw [norm_sub_sq (𝕜 := ℂ), hP, hcross, norm_smul, hvnorm]
  simp
  ring

/-- The lower Ritz column has the printed norm `ε/√30`. -/
theorem norm_beamColumnResidual_low (ε : ℝ) :
    ‖beamPerturbation ε (centeredAffineLp trialOne)
        - ((ritzLow ε : ℝ) : ℂ) • centeredAffineLp trialOne‖
      = orthogonalResidualColumnNorm ε := by
  obtain ⟨r00, -, -⟩ := beamRitz_matrix ε
  obtain ⟨g00, -, -⟩ := beamResidualGram_matrix ε
  obtain ⟨n1, -, -⟩ := beamTrial_orthonormal
  have hvnorm : ‖centeredAffineLp trialOne‖ = 1 := by
    nlinarith [norm_nonneg (centeredAffineLp trialOne), n1]
  have hsq := norm_beamColumnResidual_sq ε (centeredAffineLp trialOne) hvnorm
    (ritzLow ε) ((residualGram ε).a₀₀) r00 g00
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hval : (residualGram ε).a₀₀ - ritzLow ε ^ 2 = ε ^ 2 / 30 := by
    unfold residualGram ritzLow ritzLowCoefficient
    dsimp only
    rw [sqrt_seventyFive]
    nlinarith [hs3]
  rw [hval] at hsq
  have hcol := orthogonalResidualColumnNorm_sq ε
  have hnn : (0 : ℝ) ≤ orthogonalResidualColumnNorm ε := by
    unfold orthogonalResidualColumnNorm
    positivity
  rw [← Real.sqrt_sq (norm_nonneg _), hsq, ← hcol, Real.sqrt_sq hnn]

/-- The upper Ritz column has the same printed norm `ε/√30`. -/
theorem norm_beamColumnResidual_high (ε : ℝ) :
    ‖beamPerturbation ε (centeredAffineLp trialTwo)
        - ((ritzHigh ε : ℝ) : ℂ) • centeredAffineLp trialTwo‖
      = orthogonalResidualColumnNorm ε := by
  obtain ⟨-, -, r11⟩ := beamRitz_matrix ε
  obtain ⟨-, -, g11⟩ := beamResidualGram_matrix ε
  obtain ⟨-, n2, -⟩ := beamTrial_orthonormal
  have hvnorm : ‖centeredAffineLp trialTwo‖ = 1 := by
    nlinarith [norm_nonneg (centeredAffineLp trialTwo), n2]
  have hsq := norm_beamColumnResidual_sq ε (centeredAffineLp trialTwo) hvnorm
    (ritzHigh ε) ((residualGram ε).a₁₁) r11 g11
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hval : (residualGram ε).a₁₁ - ritzHigh ε ^ 2 = ε ^ 2 / 30 := by
    unfold residualGram ritzHigh ritzHighCoefficient
    dsimp only
    rw [sqrt_seventyFive]
    nlinarith [hs3]
  rw [hval] at hsq
  have hcol := orthogonalResidualColumnNorm_sq ε
  have hnn : (0 : ℝ) ≤ orthogonalResidualColumnNorm ε := by
    unfold orthogonalResidualColumnNorm
    positivity
  rw [← Real.sqrt_sq (norm_nonneg _), hsq, ← hcol, Real.sqrt_sq hnn]

/-! ### The two direct bounds

`tan φ_k ≤ (ε/√30)/(500 − α̂_k)`, for the genuine perturbed beam, its exact low spectral
subspace, and each of the two Ritz vectors.  Feeding these to
`direct_lower_individual_vector_bound` / `direct_upper_individual_vector_bound` produces the
printed decimals. -/

/-- The lower Ritz value stays below `500` on the paper's parameter range. -/
theorem ritzLow_lt_five_hundred {ε : ℝ} (hε : 0 < ε) (hε100 : ε < 100) :
    ritzLow ε < 500 := by
  have h3 : Real.sqrt 3 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 from by
      rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h3' : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hc : ritzLowCoefficient ≤ 1 := by
    unfold ritzLowCoefficient
    linarith
  have hcpos : (0 : ℝ) ≤ ritzLowCoefficient := by
    unfold ritzLowCoefficient
    linarith
  unfold ritzLow
  nlinarith

/-- **The direct one-vector bound at the lower Ritz vector, for the genuine beam.**  This
is the paper's `tan φ₁ < (ε/√30)/(500 − α̂₁)`, with `α̂₁ = ritzLow ε`. -/
theorem beamTanPhi_low_le (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanPhi ε (centeredAffineLp trialOne) ≤ lowerIndividualTangentExactBound ε := by
  have hritz : ritzLow ε < 500 := ritzLow_lt_five_hundred hε hε100
  have hδ : (0 : ℝ) < 500 - ritzLow ε := by linarith
  obtain ⟨r00, -, -⟩ := beamRitz_matrix ε
  obtain ⟨n1, -, -⟩ := beamTrial_orthonormal
  have hvnorm : ‖centeredAffineLp trialOne‖ = 1 := by
    nlinarith [norm_nonneg (centeredAffineLp trialOne), n1]
  have hchain := beamColumn_tangent_le ε (centeredAffineLp trialOne)
    (centeredAffineLp_mem_beamTrial _) hvnorm (ritzLow ε) r00 hritz
    (le_of_eq (norm_beamColumnResidual_low ε))
  have hden : (1 : ℝ) - ritzLowCoefficient / 500 * ε ≠ 0 := by
    have h : ritzLow ε = ε * ritzLowCoefficient := rfl
    rw [h] at hritz
    intro hzero
    apply absurd hritz
    push Not
    nlinarith [hzero]
  have hbound : lowerIndividualTangentExactBound ε
      = orthogonalResidualColumnNorm ε / (500 - ritzLow ε) := by
    unfold lowerIndividualTangentExactBound orthogonalResidualColumnNorm
    rw [abs_of_pos hε, show ritzLow ε = ε * ritzLowCoefficient from rfl,
      div_eq_div_iff hden (by
        rw [show ritzLow ε = ε * ritzLowCoefficient from rfl] at hδ
        exact ne_of_gt hδ)]
    ring
  unfold beamTanPhi
  rw [hbound, le_div_iff₀ hδ]
  linarith [hchain]

/-- **The direct one-vector bound at the upper Ritz vector, for the genuine beam.** -/
theorem beamTanPhi_high_le (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanPhi ε (centeredAffineLp trialTwo) ≤ upperIndividualTangentExactBound ε := by
  have hritz : ritzHigh ε < 500 := ritzHigh_lt_five_hundred hε100
  have hδ : (0 : ℝ) < 500 - ritzHigh ε := by linarith
  obtain ⟨-, -, r11⟩ := beamRitz_matrix ε
  obtain ⟨-, n2, -⟩ := beamTrial_orthonormal
  have hvnorm : ‖centeredAffineLp trialTwo‖ = 1 := by
    nlinarith [norm_nonneg (centeredAffineLp trialTwo), n2]
  have hchain := beamColumn_tangent_le ε (centeredAffineLp trialTwo)
    (centeredAffineLp_mem_beamTrial _) hvnorm (ritzHigh ε) r11 hritz
    (le_of_eq (norm_beamColumnResidual_high ε))
  have hden : (1 : ℝ) - ritzHighCoefficient / 500 * ε ≠ 0 := by
    have h : ritzHigh ε = ε * ritzHighCoefficient := rfl
    rw [h] at hritz
    intro hzero
    apply absurd hritz
    push Not
    nlinarith [hzero]
  have hbound : upperIndividualTangentExactBound ε
      = orthogonalResidualColumnNorm ε / (500 - ritzHigh ε) := by
    unfold upperIndividualTangentExactBound orthogonalResidualColumnNorm
    rw [abs_of_pos hε, show ritzHigh ε = ε * ritzHighCoefficient from rfl,
      div_eq_div_iff hden (by
        rw [show ritzHigh ε = ε * ritzHighCoefficient from rfl] at hδ
        exact ne_of_gt hδ)]
    ring
  unfold beamTanPhi
  rw [hbound, le_div_iff₀ hδ]
  linarith [hchain]

/-- **The printed sharper lower-Ritz-vector bound**, about the genuine beam rather than a
free real. -/
theorem beamTanPhi_low_lt_printed (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanPhi ε (centeredAffineLp trialOne)
      < ((913 : ℝ) / 2500000 * ε) / (1 - (4227 : ℝ) / 10000000 * ε) :=
  direct_lower_individual_vector_bound ε _ hε hε100 (beamTanPhi_low_le ε hε hε100)

/-- **The printed sharper upper-Ritz-vector bound**, about the genuine beam rather than a
free real. -/
theorem beamTanPhi_high_lt_printed (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanPhi ε (centeredAffineLp trialTwo)
      < ((913 : ℝ) / 2500000 * ε) / (1 - (7887 : ℝ) / 5000000 * ε) :=
  direct_upper_individual_vector_bound ε _ hε hε100 (beamTanPhi_high_le ε hε hε100)

end

end Model
end FreeBeam
end DavisKahan
end TauCeti
