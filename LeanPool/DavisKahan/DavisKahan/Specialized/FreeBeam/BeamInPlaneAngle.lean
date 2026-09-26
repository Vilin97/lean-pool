/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module


public import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamEigenbasis
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.IndividualAngles

/-! # Beam In Plane Angle -/

@[expose] public section

open TauCeti.DavisKahan.Angle


/-!
# Section 9, equations (9.9)--(9.11): the in-plane angle

`BeamEigenbasis.lean` supplies the eigenbasis of the perturbed free beam below
`500`, the *lower* block of equation (9.9), and the out-of-plane tangent bound
`beam_tan_eta_le`.  What was missing there is the *upper* block and the in-plane
rotation `psi`.  This file supplies both and closes the individual-eigenvector
estimate of Section 9 for the genuine operator `A + ε t`.

## The route

Write `e₁, e₂` for the two orthonormal Ritz vectors, `α̂₁ = ritzLow ε` and
`α̂₂ = ritzHigh ε` for the Ritz values, `γ = α̂₂ - α̂₁ = ε √3 / 3` for the Ritz
gap, and `r_j` for the Rayleigh--Ritz residual column at `e_j`.  Let `f` be a
unit eigenvector of `A + ε t` with eigenvalue `lam`, `x = P f` its trial
coordinate, `y = f - x` its complementary coordinate, and `d_j = α̂_j - lam`.

1. **The two-coordinate identity** (`beam_ritz_coordinate_identity`).  Testing
   the eigenvalue equation against `e_j` and using symmetry of the operator gives
   the exact pair `d_j ⟪e_j, x⟫ = -⟪r_j, y⟫`.  Because the recentered residual
   Gram matrix is exactly rank one, `r₁ + r₂ = 0`
   (`beamRitzColumnMap_vecTwo`), so both coordinates are governed by the single
   scalar `ρ = ⟪r₁, y⟫`.
2. **The Schur coefficient** (`beam_ritz_scalar_data`).  Consequently
   `B x = (⟪e₁,x⟫ - ⟪e₂,x⟫) r₁`, and the two Schur estimates of
   `Section9/SchurComplement.lean` — which never invert anything — give
   `0 ≤ S` and `30 (β - lam) S ≤ ‖⟪e₁,x⟫ - ⟪e₂,x⟫‖² ε²`, with `β = 1001/2` the
   form lower bound on the complement and `S = -re ⟪B x, y⟫`.  The
   division-free form of `u = 1/d₁ + 1/d₂` is the identity
   `d₁ d₂ ‖c‖² = (d₁ + d₂) S` (`two_coordinate_schur_identity`).
3. **The bound** (`inplane_ratio_bound`).  Writing `p ≥ q` for the two Ritz
   coordinates of `x` in decreasing order, `tan psi = q / p` and
   `tan (2 psi) / 2 = p q / (p² - q²)`, and the two facts above force
   `p q / (p² - q²) ≤ γ / (10 (β - lam)) = (√3/30) ε / (β - lam)`.  The printed
   coefficient `halfTanTwoPsiCoefficient = √3/30` comes out exactly, with no
   slack spent: the rank-one residual shifts both diagonal entries of the
   reduced matrix equally, so the reduced gap is still `γ`.
4. **The branch.**  Since `d₂ = d₁ + γ`, the sign of the Schur coefficient alone
   decides which Ritz vector the eigenvector is near, and puts the in-plane
   angle below `pi / 4` at that vector.  No angle theorem, no Theorem 8.1 and no
   eigenvalue lower bound is used.

`beam_individual_angle_le` records, for a single exact eigenvector below
`1001/2`, both the branch and the bound: either `lam ≤ ritzLow ε` and the lower
Ritz vector is within the `√7 / 10` envelope, or `ritzLow ε < lam` and the upper
one is.  `beam_individual_angle_le_printed` restates that with the printed
denominator `500 - lam`, and `beamLowEigenvector_ritz_pairing` turns it into the
printed **pairing**: of the two exact eigenvectors of `A + ε t` below `500`, the
one with the smaller eigenvalue is inside the envelope of the lower Ritz vector
and the one with the larger eigenvalue inside the envelope of the upper one.
That step needs only the branch information together with the observation that
two orthonormal vectors cannot both sit within `pi / 4` of one unit vector.

No resolvent is constructed anywhere in this file.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Model

open DavisKahan1970.Section9

noncomputable section
/-- **The Rayleigh--Ritz residual column map.**  It sends a trial vector `v` to the
part of `(A + ε t) v` orthogonal to the trial subspace. -/
def beamRitzColumnMap (ε : ℝ) : beamTrial →L[ℂ] BeamL2 :=
  (ContinuousLinearMap.id ℂ BeamL2 - beamTrial.starProjection) ∘L beamResidual ε

/-- The residual column map, unfolded. -/
theorem beamRitzColumnMap_apply (ε : ℝ) (v : beamTrial) :
    beamRitzColumnMap ε v
      = beamResidual ε v - beamTrial.starProjection (beamResidual ε v) := rfl

/-- **The two residual columns are opposite.**  This is the exact rank-one
structure of the recentered residual Gram matrix. -/
theorem beamRitzColumnMap_vecTwo (ε : ℝ) :
    beamRitzColumnMap ε beamTrialVecTwo = -beamRitzColumnMap ε beamTrialVecOne := by
  have h : beamRitzColumnMap ε beamTrialVecOne + beamRitzColumnMap ε beamTrialVecTwo = 0 := by
    rw [← map_add]
    exact beamRitzResidual_vecOne_add_vecTwo_eq_zero ε
  linear_combination (norm := module) h

/-- The residual column has squared norm at most `ε ^ 2 / 30`. -/
theorem norm_beamRitzColumnMap_vecOne_sq_le (ε : ℝ) :
    ‖beamRitzColumnMap ε beamTrialVecOne‖ ^ 2 ≤ ε ^ 2 / 30 := by
  have h := norm_beamRitzResidual_sq_le ε 1 0
  rw [one_smul, zero_smul, add_zero] at h
  rw [beamRitzColumnMap_apply]
  simpa using h

/-- The first Ritz vector is an eigenvector of the Ritz compression, with
eigenvalue `ritzLow ε`. -/
theorem beam_ritz_compression_vecOne (ε : ℝ) (z : beamTrial) :
    ⟪beamResidual ε beamTrialVecOne, (z : BeamL2)⟫_ℂ
      = ((ritzLow ε : ℝ) : ℂ) * ⟪(beamTrialVecOne : BeamL2), (z : BeamL2)⟫_ℂ := by
  obtain ⟨c, d, hz⟩ := exists_beamTrialVec_repr z
  subst hz
  obtain ⟨q1, q2, q12, q21⟩ := inner_beamTrialLp
  obtain ⟨m00, m01, m10, m11⟩ := beamResidual_inner_trial ε
  have m10' : ⟪beamResidual ε beamTrialVecOne, centeredAffineLp trialOne⟫_ℂ
      = ((ritzLow ε : ℝ) : ℂ) := by
    rw [← inner_conj_symm (𝕜 := ℂ) (beamResidual ε beamTrialVecOne)
      (centeredAffineLp trialOne), m00, Complex.conj_ofReal]
  have m11' : ⟪beamResidual ε beamTrialVecOne, centeredAffineLp trialTwo⟫_ℂ = 0 := by
    rw [← inner_conj_symm (𝕜 := ℂ) (beamResidual ε beamTrialVecOne)
      (centeredAffineLp trialTwo), m10, map_zero]
  have hzc : ((c • beamTrialVecOne + d • beamTrialVecTwo : beamTrial) : BeamL2)
      = c • centeredAffineLp trialOne + d • centeredAffineLp trialTwo := rfl
  have hv : ((beamTrialVecOne : beamTrial) : BeamL2) = centeredAffineLp trialOne := rfl
  rw [hzc, hv]
  simp only [inner_add_right, inner_smul_right, m10', m11', q1, q12]
  ring

/-- The second Ritz vector is an eigenvector of the Ritz compression, with
eigenvalue `ritzHigh ε`. -/
theorem beam_ritz_compression_vecTwo (ε : ℝ) (z : beamTrial) :
    ⟪beamResidual ε beamTrialVecTwo, (z : BeamL2)⟫_ℂ
      = ((ritzHigh ε : ℝ) : ℂ) * ⟪(beamTrialVecTwo : BeamL2), (z : BeamL2)⟫_ℂ := by
  obtain ⟨c, d, hz⟩ := exists_beamTrialVec_repr z
  subst hz
  obtain ⟨q1, q2, q12, q21⟩ := inner_beamTrialLp
  obtain ⟨m00, m01, m10, m11⟩ := beamResidual_inner_trial ε
  have m01' : ⟪beamResidual ε beamTrialVecTwo, centeredAffineLp trialOne⟫_ℂ = 0 := by
    rw [← inner_conj_symm (𝕜 := ℂ) (beamResidual ε beamTrialVecTwo)
      (centeredAffineLp trialOne), m01, map_zero]
  have m22' : ⟪beamResidual ε beamTrialVecTwo, centeredAffineLp trialTwo⟫_ℂ
      = ((ritzHigh ε : ℝ) : ℂ) := by
    rw [← inner_conj_symm (𝕜 := ℂ) (beamResidual ε beamTrialVecTwo)
      (centeredAffineLp trialTwo), m11, Complex.conj_ofReal]
  have hzc : ((c • beamTrialVecOne + d • beamTrialVecTwo : beamTrial) : BeamL2)
      = c • centeredAffineLp trialOne + d • centeredAffineLp trialTwo := rfl
  have hv : ((beamTrialVecTwo : beamTrial) : BeamL2) = centeredAffineLp trialTwo := rfl
  rw [hzc, hv]
  simp only [inner_add_right, inner_smul_right, m01', m22', q2, q21]
  ring

/-- **Equation (9.9), upper block: the two-coordinate identity.**

Testing the exact eigenvalue equation `(A + ε t) f = lam f` against a Ritz
vector `v` that diagonalises the Ritz compression with value `α` gives the
*exact* scalar relation

`(α - lam) ⟪v, f⟫ = - ⟪r, f - P f⟫`,

where `r` is the Rayleigh--Ritz residual column at `v`.  Nothing is inverted and
no approximation is made: this is symmetry of the operator plus the splitting of
`f` along `beamTrial ⊕ beamTrialᗮ`. -/
theorem beam_ritz_coordinate_identity (ε : ℝ) {f : BeamL2} {lam : ℝ}
    (hfdom : f ∈ (beamPerturbed ε).domain)
    (hf : (beamPerturbed ε) ⟨f, hfdom⟩ = ((lam : ℝ) : ℂ) • f)
    (v : beamTrial) {α : ℝ}
    (hcomp : ∀ z : beamTrial, ⟪beamResidual ε v, (z : BeamL2)⟫_ℂ
      = ((α : ℝ) : ℂ) * ⟪(v : BeamL2), (z : BeamL2)⟫_ℂ) :
    ((α - lam : ℝ) : ℂ) * ⟪(v : BeamL2), f⟫_ℂ
      = -⟪beamRitzColumnMap ε v, f - beamTrial.starProjection f⟫_ℂ := by
  have hvmem : (v : BeamL2) ∈ beamTrial := v.2
  have hvdom : (v : BeamL2) ∈ (beamPerturbed ε).domain := beamTrial_le_domain hvmem
  have hy : f - beamTrial.starProjection f ∈ beamTrialᗮ :=
    Submodule.sub_starProjection_mem_orthogonal f
  have hsym : ⟪(beamPerturbed ε) ⟨(v : BeamL2), hvdom⟩, f⟫_ℂ
      = ⟪(v : BeamL2), (beamPerturbed ε) ⟨f, hfdom⟩⟫_ℂ :=
    (TauCeti.LinearPMap.isSymmetric_of_isSelfAdjoint
      (beamPerturbed_isSelfAdjoint ε)) ⟨(v : BeamL2), hvdom⟩ ⟨f, hfdom⟩
  rw [beamPerturbed_apply_of_mem_beamTrial ε hvmem hvdom, hf, inner_smul_right] at hsym
  have hR : beamPerturbation ε (v : BeamL2) = beamResidual ε v := rfl
  rw [hR] at hsym
  have hsplit : ⟪beamResidual ε v, f⟫_ℂ
      = ⟪beamResidual ε v, (beamTrial.starProjection f)⟫_ℂ
        + ⟪beamResidual ε v, f - beamTrial.starProjection f⟫_ℂ := by
    rw [← inner_add_right]
    congr 1
    abel
  have hvf : ⟪(v : BeamL2), (beamTrial.starProjection f)⟫_ℂ = ⟪(v : BeamL2), f⟫_ℂ := by
    have h0 : ⟪(v : BeamL2), f - beamTrial.starProjection f⟫_ℂ = 0 := hy _ hvmem
    rw [inner_sub_right] at h0
    exact (sub_eq_zero.1 h0).symm
  have hx : ⟪beamResidual ε v, (beamTrial.starProjection f)⟫_ℂ
      = ((α : ℝ) : ℂ) * ⟪(v : BeamL2), f⟫_ℂ := by
    rw [hcomp ⟨beamTrial.starProjection f, beamTrial.starProjection_apply_mem f⟩]
    change ((α : ℝ) : ℂ) * ⟪(v : BeamL2), (beamTrial.starProjection f)⟫_ℂ = _
    rw [hvf]
  have hproj : ⟪beamTrial.starProjection (beamResidual ε v),
      f - beamTrial.starProjection f⟫_ℂ = 0 :=
    hy _ (beamTrial.starProjection_apply_mem _)
  have hcol : ⟪beamResidual ε v, f - beamTrial.starProjection f⟫_ℂ
      = ⟪beamRitzColumnMap ε v, f - beamTrial.starProjection f⟫_ℂ := by
    rw [beamRitzColumnMap_apply, inner_sub_left, hproj, sub_zero]
  rw [hsplit, hx, hcol] at hsym
  push_cast
  linear_combination hsym

/-- The orthogonal projection onto the trial subspace in Ritz coordinates. -/
theorem beamTrial_starProjection_eq (f : BeamL2) :
    beamTrial.starProjection f
      = ⟪centeredAffineLp trialOne, f⟫_ℂ • centeredAffineLp trialOne
        + ⟪centeredAffineLp trialTwo, f⟫_ℂ • centeredAffineLp trialTwo := by
  obtain ⟨c, d, hz⟩ :=
    exists_beamTrialVec_repr ⟨beamTrial.starProjection f, beamTrial.starProjection_apply_mem f⟩
  have hzc : beamTrial.starProjection f
      = c • centeredAffineLp trialOne + d • centeredAffineLp trialTwo :=
    congrArg (fun z : beamTrial => (z : BeamL2)) hz
  obtain ⟨q1, q2, q12, q21⟩ := inner_beamTrialLp
  have hy : f - beamTrial.starProjection f ∈ beamTrialᗮ :=
    Submodule.sub_starProjection_mem_orthogonal f
  have hc : ⟪centeredAffineLp trialOne, f⟫_ℂ = c := by
    have h0 : ⟪centeredAffineLp trialOne, f - beamTrial.starProjection f⟫_ℂ = 0 :=
      hy _ (centeredAffineLp_mem_beamTrial _)
    rw [inner_sub_right, hzc] at h0
    simp only [inner_add_right, inner_smul_right, q1, q12] at h0
    have := sub_eq_zero.1 h0
    rw [this]; ring
  have hd : ⟪centeredAffineLp trialTwo, f⟫_ℂ = d := by
    have h0 : ⟪centeredAffineLp trialTwo, f - beamTrial.starProjection f⟫_ℂ = 0 :=
      hy _ (centeredAffineLp_mem_beamTrial _)
    rw [inner_sub_right, hzc] at h0
    simp only [inner_add_right, inner_smul_right, q2, q21] at h0
    have := sub_eq_zero.1 h0
    rw [this]; ring
  rw [hc, hd, hzc]

/-- The squared norm of the trial coordinate in Ritz coordinates. -/
theorem norm_beamTrial_starProjection_sq (f : BeamL2) :
    ‖beamTrial.starProjection f‖ ^ 2
      = ‖⟪centeredAffineLp trialOne, f⟫_ℂ‖ ^ 2 + ‖⟪centeredAffineLp trialTwo, f⟫_ℂ‖ ^ 2 := by
  have h := norm_sq_beamTrialVec_comb ⟪centeredAffineLp trialOne, f⟫_ℂ
    ⟪centeredAffineLp trialTwo, f⟫_ℂ
  have hcoe : ((⟪centeredAffineLp trialOne, f⟫_ℂ • beamTrialVecOne
        + ⟪centeredAffineLp trialTwo, f⟫_ℂ • beamTrialVecTwo : beamTrial) : BeamL2)
      = ⟪centeredAffineLp trialOne, f⟫_ℂ • centeredAffineLp trialOne
        + ⟪centeredAffineLp trialTwo, f⟫_ℂ • centeredAffineLp trialTwo := rfl
  rw [← h]
  rw [beamTrial_starProjection_eq f, ← hcoe]
  rfl

/-- The residual column at the trial coordinate is a multiple of the first column. -/
theorem beam_residual_at_starProjection (ε : ℝ) (f : BeamL2) :
    beamPerturbation ε (beamTrial.starProjection f)
        - beamTrial.starProjection (beamPerturbation ε (beamTrial.starProjection f))
      = (⟪centeredAffineLp trialOne, f⟫_ℂ - ⟪centeredAffineLp trialTwo, f⟫_ℂ)
          • beamRitzColumnMap ε beamTrialVecOne := by
  have hsub : (⟨beamTrial.starProjection f, beamTrial.starProjection_apply_mem f⟩ : beamTrial)
      = ⟪centeredAffineLp trialOne, f⟫_ℂ • beamTrialVecOne
        + ⟪centeredAffineLp trialTwo, f⟫_ℂ • beamTrialVecTwo := by
    apply Subtype.ext
    exact beamTrial_starProjection_eq f
  have hlhs : beamPerturbation ε (beamTrial.starProjection f)
      - beamTrial.starProjection (beamPerturbation ε (beamTrial.starProjection f))
      = beamRitzColumnMap ε
          ⟨beamTrial.starProjection f, beamTrial.starProjection_apply_mem f⟩ := rfl
  rw [hlhs, hsub, map_add, map_smul, map_smul, beamRitzColumnMap_vecTwo]
  module

/-- Testing against a trial vector does not see the complementary coordinate. -/
theorem inner_beamTrial_starProjection {e : BeamL2} (he : e ∈ beamTrial) (f : BeamL2) :
    ⟪e, beamTrial.starProjection f⟫_ℂ = ⟪e, f⟫_ℂ := by
  have hy : f - beamTrial.starProjection f ∈ beamTrialᗮ :=
    Submodule.sub_starProjection_mem_orthogonal f
  have h0 : ⟪e, f - beamTrial.starProjection f⟫_ℂ = 0 := hy _ he
  rw [inner_sub_right] at h0
  exact (sub_eq_zero.1 h0).symm

/-- The individual-angle envelope from the two Ritz coordinates. -/
theorem beam_angle_of_ritz_coordinates {ε : ℝ} (hε : 0 ≤ ε) {f : BeamL2}
    (hfn : ‖f‖ = 1) (hPf : beamTrial.starProjection f ≠ 0)
    {e : BeamL2} (he : e ∈ beamTrial) (hen : ‖e‖ = 1)
    {p q den : ℝ} (hq : 0 ≤ q) (hqp : q < p)
    (hp : ‖⟪e, f⟫_ℂ‖ = p)
    (hnorm : ‖beamTrial.starProjection f‖ = Real.sqrt (p ^ 2 + q ^ 2))
    (hden : 0 < den)
    (hpsi : p * q / (p ^ 2 - q ^ 2) ≤ halfTanTwoPsiCoefficient * ε / den)
    (htaneta : Real.tan (Real.arccos ‖beamTrial.starProjection f‖)
      ≤ tanEtaCoefficient * ε / den) :
    Real.arccos ‖⟪e, f⟫_ℂ‖ ≤ Real.sqrt 7 / 10 * ε / den := by
  have hPfnorm : 0 < ‖beamTrial.starProjection f‖ := norm_pos_iff.2 hPf
  have hs : 0 < Real.sqrt (p ^ 2 + q ^ 2) := by rw [← hnorm]; exact hPfnorm
  have hg : ‖⟪e, ((‖beamTrial.starProjection f‖ : ℝ) : ℂ)⁻¹
        • beamTrial.starProjection f⟫_ℂ‖ = p / Real.sqrt (p ^ 2 + q ^ 2) := by
    rw [inner_smul_right, norm_mul, inner_beamTrial_starProjection he, hp, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hPfnorm, hnorm]
    ring
  have hmain := individual_angle_le_exact_envelope_of_subspace (𝕜 := ℂ) beamTrial he hen hfn hPf
    (g := ((‖beamTrial.starProjection f‖ : ℝ) : ℂ)⁻¹ • beamTrial.starProjection f) rfl
    hden hε (by rw [hg]; exact arccos_ratio_lt_pi_div_four hq hqp)
    (by rw [hg, half_tan_two_arccos_ratio hq hqp]; exact hpsi) htaneta
  exact hmain

/-- **The scalar consequence of the two-coordinate identity.**

If `d₁ a = -ρ` and `d₂ b = ρ` then the coefficient `a - b` of the residual
column and the Schur coefficient `-re (conj (a - b) ρ)` satisfy the exact
identity `d₁ d₂ ‖a - b‖² = (d₁ + d₂) · (Schur coefficient)`.  This is the step
that replaces `u = 1/d₁ + 1/d₂` by a division-free equation. -/
theorem two_coordinate_schur_identity {d₁ d₂ : ℝ} {a b ρ : ℂ}
    (hA : ((d₁ : ℝ) : ℂ) * a = -ρ) (hB : ((d₂ : ℝ) : ℂ) * b = ρ) :
    d₁ * d₂ * ‖a - b‖ ^ 2
      = (d₁ + d₂) * (-RCLike.re ((starRingEnd ℂ) (a - b) * ρ)) := by
  have hcc : (starRingEnd ℂ) (a - b) * (a - b) = ((‖a - b‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hcomplex : ((d₁ : ℂ) * (d₂ : ℂ)) * (a - b) = -((d₁ : ℂ) + (d₂ : ℂ)) * ρ := by
    linear_combination (d₂ : ℂ) * hA - (d₁ : ℂ) * hB
  have h2 : ((d₁ : ℂ) * (d₂ : ℂ)) * ((‖a - b‖ ^ 2 : ℝ) : ℂ)
      = -((d₁ : ℂ) + (d₂ : ℂ)) * ((starRingEnd ℂ) (a - b) * ρ) := by
    linear_combination (starRingEnd ℂ) (a - b) * hcomplex - ((d₁ : ℂ) * (d₂ : ℂ)) * hcc
  have h3 := congrArg Complex.re h2
  change d₁ * d₂ * ‖a - b‖ ^ 2 = (d₁ + d₂) * (-Complex.re _)
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im] at h3 ⊢
  linarith [h3]

/-- **The scalar data of the Ritz coordinates of an exact eigenvector.** -/
theorem beam_ritz_scalar_data (ε : ℝ) (hε : 0 < ε) {f : BeamL2} {lam : ℝ}
    (hfdom : f ∈ (beamPerturbed ε).domain)
    (hf : (beamPerturbed ε) ⟨f, hfdom⟩ = ((lam : ℝ) : ℂ) • f)
    (hlam : lam < 1001 / 2) (hfn : ‖f‖ = 1) :
    ∃ R S C : ℝ, 0 ≤ R ∧ 0 ≤ S ∧ 0 < C ∧
      |ritzLow ε - lam| * ‖⟪centeredAffineLp trialOne, f⟫_ℂ‖ = R ∧
      |ritzHigh ε - lam| * ‖⟪centeredAffineLp trialTwo, f⟫_ℂ‖ = R ∧
      (ritzLow ε - lam) * (ritzHigh ε - lam) * C
        = ((ritzLow ε - lam) + (ritzHigh ε - lam)) * S ∧
      30 * ((1001 : ℝ) / 2 - lam) * S ≤ C * ε ^ 2 := by
  have hε0 : (0 : ℝ) ≤ ε := hε.le
  have hβ : (0 : ℝ) < 1001 / 2 - lam := by linarith
  have hgap : (ritzHigh ε - lam) - (ritzLow ε - lam) = ε * (Real.sqrt 3 / 3) := by
    have := ritzHigh_sub_ritzLow ε; linarith
  have hγpos : 0 < ε * (Real.sqrt 3 / 3) := by
    have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    positivity
  have hA : ((ritzLow ε - lam : ℝ) : ℂ) * ⟪centeredAffineLp trialOne, f⟫_ℂ
      = -⟪beamRitzColumnMap ε beamTrialVecOne, f - beamTrial.starProjection f⟫_ℂ :=
    beam_ritz_coordinate_identity ε hfdom hf beamTrialVecOne (beam_ritz_compression_vecOne ε)
  have hB0 : ((ritzHigh ε - lam : ℝ) : ℂ) * ⟪centeredAffineLp trialTwo, f⟫_ℂ
      = -⟪beamRitzColumnMap ε beamTrialVecTwo, f - beamTrial.starProjection f⟫_ℂ :=
    beam_ritz_coordinate_identity ε hfdom hf beamTrialVecTwo (beam_ritz_compression_vecTwo ε)
  have hB : ((ritzHigh ε - lam : ℝ) : ℂ) * ⟪centeredAffineLp trialTwo, f⟫_ℂ
      = ⟪beamRitzColumnMap ε beamTrialVecOne, f - beamTrial.starProjection f⟫_ℂ := by
    rw [hB0, beamRitzColumnMap_vecTwo, inner_neg_left, neg_neg]
  have hBx := beam_residual_at_starProjection ε f
  have hPfne : beamTrial.starProjection f ≠ 0 :=
    beam_starProjection_ne_zero ε hε0 hfdom hf hlam hfn
  have hcne : ⟪centeredAffineLp trialOne, f⟫_ℂ - ⟪centeredAffineLp trialTwo, f⟫_ℂ ≠ 0 := by
    intro h0
    have hBx0 : beamPerturbation ε (beamTrial.starProjection f)
        - beamTrial.starProjection (beamPerturbation ε (beamTrial.starProjection f)) = 0 := by
      rw [hBx, h0, zero_smul]
    have hy0 : f - beamTrial.starProjection f = 0 :=
      lower_coordinate_eq_zero_of_residual_eq_zero (𝕜 := ℂ)
        (beam_lower_block_equation ε hfdom hf)
        (beam_lower_block_form_ge ε hε0 f hfdom) hlam hBx0
    have hρ0 : ⟪beamRitzColumnMap ε beamTrialVecOne, f - beamTrial.starProjection f⟫_ℂ = 0 := by
      rw [hy0, inner_zero_right]
    rw [hρ0, neg_zero] at hA
    rw [hρ0] at hB
    have heq : ⟪centeredAffineLp trialOne, f⟫_ℂ = ⟪centeredAffineLp trialTwo, f⟫_ℂ :=
      sub_eq_zero.1 h0
    have hane : ⟪centeredAffineLp trialOne, f⟫_ℂ = 0 := by
      by_contra hne
      have h1 : ((ritzLow ε - lam : ℝ) : ℂ) = 0 := by
        rcases mul_eq_zero.1 hA with h | h
        · exact h
        · exact absurd h hne
      have h2 : ((ritzHigh ε - lam : ℝ) : ℂ) = 0 := by
        rw [heq] at hne
        rcases mul_eq_zero.1 hB with h | h
        · exact h
        · exact absurd h hne
      have h1' : ritzLow ε - lam = 0 := by exact_mod_cast h1
      have h2' : ritzHigh ε - lam = 0 := by exact_mod_cast h2
      linarith
    have hbne : ⟪centeredAffineLp trialTwo, f⟫_ℂ = 0 := by rw [← heq]; exact hane
    exact hPfne (by rw [beamTrial_starProjection_eq f, hane, hbne, zero_smul, zero_smul, add_zero])
  have hSre : RCLike.re (inner ℂ (beamPerturbation ε (beamTrial.starProjection f)
        - beamTrial.starProjection (beamPerturbation ε (beamTrial.starProjection f)))
      (f - beamTrial.starProjection f))
      = RCLike.re ((starRingEnd ℂ)
          (⟪centeredAffineLp trialOne, f⟫_ℂ - ⟪centeredAffineLp trialTwo, f⟫_ℂ)
        * ⟪beamRitzColumnMap ε beamTrialVecOne, f - beamTrial.starProjection f⟫_ℂ) := by
    rw [hBx, inner_smul_left]
  refine ⟨‖⟪beamRitzColumnMap ε beamTrialVecOne, f - beamTrial.starProjection f⟫_ℂ‖,
    -RCLike.re (inner ℂ (beamPerturbation ε (beamTrial.starProjection f)
        - beamTrial.starProjection (beamPerturbation ε (beamTrial.starProjection f)))
      (f - beamTrial.starProjection f)),
    ‖⟪centeredAffineLp trialOne, f⟫_ℂ - ⟪centeredAffineLp trialTwo, f⟫_ℂ‖ ^ 2,
    norm_nonneg _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact schurCoefficient_nonneg (𝕜 := ℂ) (beam_lower_block_equation ε hfdom hf)
      (beam_lower_block_form_ge ε hε0 f hfdom) hlam
  · exact pow_pos (norm_pos_iff.2 hcne) 2
  · have h := congrArg (fun z : ℂ => ‖z‖) hA
    simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  · have h := congrArg (fun z : ℂ => ‖z‖) hB
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  · rw [hSre]
    exact two_coordinate_schur_identity hA hB
  · have hSle := schurCoefficient_le (𝕜 := ℂ) (beam_lower_block_equation ε hfdom hf)
      (beam_lower_block_form_ge ε hε0 f hfdom) hlam
    have hnormBx : ‖beamPerturbation ε (beamTrial.starProjection f)
        - beamTrial.starProjection (beamPerturbation ε (beamTrial.starProjection f))‖ ^ 2
        = ‖⟪centeredAffineLp trialOne, f⟫_ℂ - ⟪centeredAffineLp trialTwo, f⟫_ℂ‖ ^ 2
          * ‖beamRitzColumnMap ε beamTrialVecOne‖ ^ 2 := by
      rw [hBx, norm_smul]
      ring
    rw [hnormBx] at hSle
    have hr := norm_beamRitzColumnMap_vecOne_sq_le ε
    nlinarith [sq_nonneg ‖⟪centeredAffineLp trialOne, f⟫_ℂ - ⟪centeredAffineLp trialTwo, f⟫_ℂ‖,
      norm_nonneg ‖beamRitzColumnMap ε beamTrialVecOne‖]

/-- The scalar core of the in-plane angle bound. -/
theorem inplane_ratio_bound {βp γ m M p q R : ℝ}
    (hβ : 0 < βp) (hγ : 0 < γ) (hm : 0 ≤ m) (hmM : m < M)
    (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h1 : m * p = R) (h2 : M * q = R)
    (hpos : 0 < p ^ 2 + q ^ 2)
    (hcore : 10 * βp * (m * M) ≤ γ * ((M - m) * (M + m))) :
    q < p ∧ p * q / (p ^ 2 - q ^ 2) ≤ γ / (10 * βp) := by
  have hM : 0 < M := lt_of_le_of_lt hm hmM
  rcases eq_or_lt_of_le hm with hm0 | hm0
  · have hR0 : R = 0 := by rw [← h1, ← hm0]; ring
    have hq0 : q = 0 := by
      have h := h2
      rw [hR0] at h
      exact (mul_eq_zero.1 h).resolve_left (ne_of_gt hM)
    have hp0 : 0 < p := by
      rcases eq_or_lt_of_le hp with h | h
      · exfalso; rw [← h, hq0] at hpos; norm_num at hpos
      · exact h
    refine ⟨by rw [hq0]; exact hp0, ?_⟩
    rw [hq0, mul_zero, zero_pow (by norm_num), sub_zero, zero_div]
    positivity
  · have hRne : R ≠ 0 := by
      intro h
      rw [h] at h1 h2
      have hp0 : p = 0 := (mul_eq_zero.1 h1).resolve_left (ne_of_gt hm0)
      have hq0 : q = 0 := (mul_eq_zero.1 h2).resolve_left (ne_of_gt hM)
      rw [hp0, hq0] at hpos
      norm_num at hpos
    have hppos : 0 < p := by
      rcases eq_or_lt_of_le hp with h | h
      · exfalso; rw [← h, mul_zero] at h1; exact hRne h1.symm
      · exact h
    have hqpos : 0 < q := by
      rcases eq_or_lt_of_le hq with h | h
      · exfalso; rw [← h, mul_zero] at h2; exact hRne h2.symm
      · exact h
    have hmq : M * q = m * p := by rw [h1, h2]
    have hqp : q < p := by nlinarith
    have hsq : 0 < p ^ 2 - q ^ 2 := by nlinarith
    refine ⟨hqp, ?_⟩
    rw [div_le_div_iff₀ hsq (by positivity)]
    have hmM2 : 0 < m ^ 2 * M ^ 2 := by positivity
    have e1 : (p * q * (10 * βp)) * (m ^ 2 * M ^ 2) = 10 * βp * (m * M) * R ^ 2 := by
      linear_combination (10 * βp * m * M * (M * q)) * h1 + (10 * βp * m * M * R) * h2
    have e2 : (γ * (p ^ 2 - q ^ 2)) * (m ^ 2 * M ^ 2)
        = γ * ((M - m) * (M + m)) * R ^ 2 := by
      linear_combination (γ * M ^ 2 * (m * p + R)) * h1 - (γ * m ^ 2 * (M * q + R)) * h2
    have key : (p * q * (10 * βp)) * (m ^ 2 * M ^ 2)
        ≤ (γ * (p ^ 2 - q ^ 2)) * (m ^ 2 * M ^ 2) := by
      rw [e1, e2]
      nlinarith [sq_nonneg R]
    exact le_of_mul_le_mul_right key hmM2

/-- The Schur-complement gap inequality, on the branch where the two shifted Ritz
values have nonnegative sum. -/
theorem schur_gap_bound_of_sum_nonneg {βp γ ε d₁ d₂ C S : ℝ} (hC : 0 < C) (hεγ : ε ^ 2 = 3 * γ ^ 2)
    (hprod : d₁ * d₂ * C = (d₁ + d₂) * S)
    (hSb : 30 * βp * S ≤ C * ε ^ 2) (hsum : 0 ≤ d₁ + d₂) :
    10 * βp * (d₁ * d₂) ≤ γ ^ 2 * (d₁ + d₂) := by
  have h5 : 30 * βp * (d₁ * d₂ * C) = (d₁ + d₂) * (30 * βp * S) := by rw [hprod]; ring
  have h6 : (d₁ + d₂) * (30 * βp * S) ≤ (d₁ + d₂) * (C * ε ^ 2) :=
    mul_le_mul_of_nonneg_left hSb hsum
  have h7 : (d₁ + d₂) * (C * ε ^ 2) = 3 * ((d₁ + d₂) * (C * γ ^ 2)) := by rw [hεγ]; ring
  have hkey : (10 * βp * (d₁ * d₂)) * C ≤ (γ ^ 2 * (d₁ + d₂)) * C := by linarith
  exact le_of_mul_le_mul_right hkey hC

/-- The Schur-complement gap inequality, on the branch where the two shifted Ritz
values have nonpositive sum. -/
theorem schur_gap_bound_of_sum_nonpos {βp γ ε d₁ d₂ C S : ℝ} (hC : 0 < C) (hεγ : ε ^ 2 = 3 * γ ^ 2)
    (hprod : d₁ * d₂ * C = (d₁ + d₂) * S)
    (hSb : 30 * βp * S ≤ C * ε ^ 2) (hsum : d₁ + d₂ ≤ 0) :
    γ ^ 2 * (d₁ + d₂) ≤ 10 * βp * (d₁ * d₂) := by
  have h5 : 30 * βp * (d₁ * d₂ * C) = (d₁ + d₂) * (30 * βp * S) := by rw [hprod]; ring
  have h6 : (d₁ + d₂) * (C * ε ^ 2) ≤ (d₁ + d₂) * (30 * βp * S) := by
    nlinarith [mul_nonneg (neg_nonneg.2 hsum) (sub_nonneg.2 hSb)]
  have h7 : (d₁ + d₂) * (C * ε ^ 2) = 3 * ((d₁ + d₂) * (C * γ ^ 2)) := by rw [hεγ]; ring
  have hkey : (γ ^ 2 * (d₁ + d₂)) * C ≤ (10 * βp * (d₁ * d₂)) * C := by linarith
  exact le_of_mul_le_mul_right hkey hC
/-- **The individual eigenvector angle bound for the genuine perturbed beam.**

Which Ritz vector the eigenvector is near is decided by the position of the
eigenvalue relative to the *lower* Ritz value, and by nothing else: the sign of
the Schur coefficient selects the branch. -/
theorem beam_individual_angle_le (ε : ℝ) (hε : 0 < ε) {f : BeamL2} {lam : ℝ}
    (hfdom : f ∈ (beamPerturbed ε).domain)
    (hf : (beamPerturbed ε) ⟨f, hfdom⟩ = ((lam : ℝ) : ℂ) • f)
    (hlam : lam < 1001 / 2) (hfn : ‖f‖ = 1) :
    (lam ≤ ritzLow ε ∧ Real.arccos ‖⟪centeredAffineLp trialOne, f⟫_ℂ‖
        ≤ Real.sqrt 7 / 10 * ε / ((1001 : ℝ) / 2 - lam))
      ∨ (ritzLow ε < lam ∧ Real.arccos ‖⟪centeredAffineLp trialTwo, f⟫_ℂ‖
        ≤ Real.sqrt 7 / 10 * ε / ((1001 : ℝ) / 2 - lam)) := by
  obtain ⟨R, S, C, hR, hS, hC, hG1, hG2, hprod, hSb⟩ :=
    beam_ritz_scalar_data ε hε hfdom hf hlam hfn
  have hε0 : (0 : ℝ) ≤ ε := hε.le
  have hβ : (0 : ℝ) < 1001 / 2 - lam := by linarith
  have hgap : (ritzHigh ε - lam) - (ritzLow ε - lam) = ε * (Real.sqrt 3 / 3) := by
    have := ritzHigh_sub_ritzLow ε; linarith
  have hγ : 0 < ε * (Real.sqrt 3 / 3) := by
    have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    positivity
  have hεγ : ε ^ 2 = 3 * (ε * (Real.sqrt 3 / 3)) ^ 2 := by
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith
  have hPfne : beamTrial.starProjection f ≠ 0 :=
    beam_starProjection_ne_zero ε hε0 hfdom hf hlam hfn
  have hPfpos : 0 < ‖beamTrial.starProjection f‖ := norm_pos_iff.2 hPfne
  have hnormsq := norm_beamTrial_starProjection_sq f
  have hpos : 0 < ‖⟪centeredAffineLp trialOne, f⟫_ℂ‖ ^ 2
      + ‖⟪centeredAffineLp trialTwo, f⟫_ℂ‖ ^ 2 := by
    rw [← hnormsq]; positivity
  have hnormeq : ‖beamTrial.starProjection f‖
      = Real.sqrt (‖⟪centeredAffineLp trialOne, f⟫_ℂ‖ ^ 2
        + ‖⟪centeredAffineLp trialTwo, f⟫_ℂ‖ ^ 2) := by
    rw [← hnormsq, Real.sqrt_sq (norm_nonneg _)]
  have hcoeff : ε * (Real.sqrt 3 / 3) / (10 * ((1001 : ℝ) / 2 - lam))
      = halfTanTwoPsiCoefficient * ε / ((1001 : ℝ) / 2 - lam) := by
    unfold halfTanTwoPsiCoefficient
    field_simp
    ring
  have hetabound : Real.tan (Real.arccos ‖beamTrial.starProjection f‖)
      ≤ tanEtaCoefficient * ε / ((1001 : ℝ) / 2 - lam) := by
    have h := beam_tan_eta_le ε hε0 hfdom hf hlam hfn
    have hσ : orthogonalResidualSingularValue ε = tanEtaCoefficient * ε := by
      unfold orthogonalResidualSingularValue tanEtaCoefficient
      rw [abs_of_nonneg hε0]; ring
    rwa [hσ] at h
  have hone : ‖centeredAffineLp trialOne‖ = 1 := by
    obtain ⟨n1, -, -⟩ := beamTrial_orthonormal
    nlinarith [norm_nonneg (centeredAffineLp trialOne)]
  have htwo : ‖centeredAffineLp trialTwo‖ = 1 := by
    obtain ⟨-, n2, -⟩ := beamTrial_orthonormal
    nlinarith [norm_nonneg (centeredAffineLp trialTwo)]
  by_cases hd1 : 0 ≤ ritzLow ε - lam
  · -- the eigenvalue is at or below the lower Ritz value: pair with the first Ritz vector
    have hd2 : 0 < ritzHigh ε - lam := by linarith
    have hmM : ritzLow ε - lam < ritzHigh ε - lam := by linarith
    have h1 : (ritzLow ε - lam) * ‖⟪centeredAffineLp trialOne, f⟫_ℂ‖ = R := by
      rw [← hG1, abs_of_nonneg hd1]
    have h2 : (ritzHigh ε - lam) * ‖⟪centeredAffineLp trialTwo, f⟫_ℂ‖ = R := by
      rw [← hG2, abs_of_nonneg hd2.le]
    have hsum : 0 ≤ (ritzLow ε - lam) + (ritzHigh ε - lam) := by linarith
    have hbase := schur_gap_bound_of_sum_nonneg (γ := ε * (Real.sqrt 3 / 3)) hC hεγ hprod hSb hsum
    have hcore : 10 * ((1001 : ℝ) / 2 - lam) * ((ritzLow ε - lam) * (ritzHigh ε - lam))
        ≤ ε * (Real.sqrt 3 / 3)
          * (((ritzHigh ε - lam) - (ritzLow ε - lam))
            * ((ritzHigh ε - lam) + (ritzLow ε - lam))) := by
      rw [hgap]
      linarith
    obtain ⟨hqp, hratio⟩ := inplane_ratio_bound hβ hγ hd1 hmM (norm_nonneg _) (norm_nonneg _)
      h1 h2 hpos hcore
    refine Or.inl ⟨by linarith, ?_⟩
    refine beam_angle_of_ritz_coordinates hε0 hfn hPfne (centeredAffineLp_mem_beamTrial _) hone
      (norm_nonneg _) hqp rfl hnormeq hβ ?_ ?_
    · rw [← hcoeff]; exact hratio
    · exact hetabound
  · -- the eigenvalue is above the lower Ritz value: pair with the second Ritz vector
    replace hd1 : ritzLow ε - lam < 0 := not_le.1 hd1
    have hd2 : 0 ≤ ritzHigh ε - lam := by
      by_contra hcon0
      have hcon : ritzHigh ε - lam < 0 := not_le.1 hcon0
      have hp1 : 0 < (ritzLow ε - lam) * (ritzHigh ε - lam) := mul_pos_of_neg_of_neg hd1 hcon
      have hp2 : 0 < (ritzLow ε - lam) * (ritzHigh ε - lam) * C := mul_pos hp1 hC
      have hp3 : 0 ≤ (-((ritzLow ε - lam) + (ritzHigh ε - lam))) * S :=
        mul_nonneg (by linarith) hS
      linarith [hprod]
    have hsum' : (ritzLow ε - lam) + (ritzHigh ε - lam) < 0 := by
      rcases eq_or_lt_of_le hd2 with h | h
      · linarith
      · by_contra hcon0
        have hcon : 0 ≤ (ritzLow ε - lam) + (ritzHigh ε - lam) := not_lt.1 hcon0
        have hp1 : (ritzLow ε - lam) * (ritzHigh ε - lam) < 0 := mul_neg_of_neg_of_pos hd1 h
        have hp2 : (ritzLow ε - lam) * (ritzHigh ε - lam) * C < 0 := mul_neg_of_neg_of_pos hp1 hC
        have hp3 : 0 ≤ ((ritzLow ε - lam) + (ritzHigh ε - lam)) * S := mul_nonneg hcon hS
        linarith [hprod]
    have hsum : (ritzLow ε - lam) + (ritzHigh ε - lam) ≤ 0 := hsum'.le
    have hmM : ritzHigh ε - lam < -(ritzLow ε - lam) := by linarith
    have h1 : (ritzHigh ε - lam) * ‖⟪centeredAffineLp trialTwo, f⟫_ℂ‖ = R := by
      rw [← hG2, abs_of_nonneg hd2]
    have h2 : (-(ritzLow ε - lam)) * ‖⟪centeredAffineLp trialOne, f⟫_ℂ‖ = R := by
      rw [← hG1, abs_of_neg hd1]
    have hbase := schur_gap_bound_of_sum_nonpos (γ := ε * (Real.sqrt 3 / 3)) hC hεγ hprod hSb hsum
    have hcore : 10 * ((1001 : ℝ) / 2 - lam) * ((ritzHigh ε - lam) * (-(ritzLow ε - lam)))
        ≤ ε * (Real.sqrt 3 / 3)
          * ((-(ritzLow ε - lam) - (ritzHigh ε - lam))
            * (-(ritzLow ε - lam) + (ritzHigh ε - lam))) := by
      have hg2 : -(ritzLow ε - lam) + (ritzHigh ε - lam) = ε * (Real.sqrt 3 / 3) := by
        linarith
      rw [hg2]
      linarith [hbase]
    obtain ⟨hqp, hratio⟩ := inplane_ratio_bound hβ hγ hd2 hmM (norm_nonneg _) (norm_nonneg _)
      h1 h2 (by linarith) hcore
    refine Or.inr ⟨by linarith, ?_⟩
    refine beam_angle_of_ritz_coordinates hε0 hfn hPfne (centeredAffineLp_mem_beamTrial _) htwo
      (norm_nonneg _) hqp rfl ?_ hβ ?_ ?_
    · rw [hnormeq, add_comm]
    · rw [← hcoeff]; exact hratio
    · exact hetabound

/-! ## The printed Section 9 statement

Equations (9.9)--(9.11) are printed with the denominator `500 - lambda_k`.  The
form lower bound available on `beamTrialᗮ` is the sharp free-beam gap `1001/2`,
so the bound proved above is strictly better; the printed statement follows. -/

/-- **The printed individual-eigenvector bound of Section 9.**  Some Ritz vector
is within `(√7 / 10) ε / (500 - lam)` of every exact eigenvector below `500`. -/
theorem beam_individual_angle_le_printed (ε : ℝ) (hε : 0 < ε) {f : BeamL2} {lam : ℝ}
    (hfdom : f ∈ (beamPerturbed ε).domain)
    (hf : (beamPerturbed ε) ⟨f, hfdom⟩ = ((lam : ℝ) : ℂ) • f)
    (hlam : lam < 500) (hfn : ‖f‖ = 1) :
    (lam ≤ ritzLow ε ∧ Real.arccos ‖⟪centeredAffineLp trialOne, f⟫_ℂ‖
        ≤ Real.sqrt 7 / 10 * ε / (500 - lam))
      ∨ (ritzLow ε < lam ∧ Real.arccos ‖⟪centeredAffineLp trialTwo, f⟫_ℂ‖
        ≤ Real.sqrt 7 / 10 * ε / (500 - lam)) := by
  have hmono : Real.sqrt 7 / 10 * ε / ((1001 : ℝ) / 2 - lam)
      ≤ Real.sqrt 7 / 10 * ε / (500 - lam) := by
    have h0 : (0 : ℝ) ≤ Real.sqrt 7 / 10 * ε := by positivity
    gcongr
    linarith
  rcases beam_individual_angle_le ε hε hfdom hf (by linarith) hfn with ⟨hb, h⟩ | ⟨hb, h⟩
  · exact Or.inl ⟨hb, h.trans hmono⟩
  · exact Or.inr ⟨hb, h.trans hmono⟩

/-- **The printed bound at the two exact eigenvectors of the perturbed beam.**
Each of the two eigenvectors of `A + ε t` below `500` is within
`(√7 / 10) ε / (500 - lambda_k)` of one of the two Ritz vectors. -/
theorem beamLowEigenvector_individual_angle_le (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100)
    (k : Fin 2) :
    (beamLowEigenvalue ε hε.le hε100 k ≤ ritzLow ε
        ∧ Real.arccos ‖⟪centeredAffineLp trialOne, beamLowEigenvector ε hε.le hε100 k⟫_ℂ‖
          ≤ Real.sqrt 7 / 10 * ε / (500 - beamLowEigenvalue ε hε.le hε100 k))
      ∨ (ritzLow ε < beamLowEigenvalue ε hε.le hε100 k
        ∧ Real.arccos ‖⟪centeredAffineLp trialTwo, beamLowEigenvector ε hε.le hε100 k⟫_ℂ‖
          ≤ Real.sqrt 7 / 10 * ε / (500 - beamLowEigenvalue ε hε.le hε100 k)) :=
  beam_individual_angle_le_printed ε hε (beamLowEigenvector_mem_domain ε hε.le hε100 k)
    (beamPerturbed_apply_beamLowEigenvector ε hε.le hε100 k)
    (beamLowEigenvalue_lt_five_hundred ε hε.le hε100 k)
    (norm_beamLowEigenvector ε hε.le hε100 k)


/-! ## The pairing of eigenvectors with Ritz vectors -/

/-- **No eigenvalue of the perturbed beam below `1001/2` exceeds the upper Ritz
value.**  This is a by-product of the sign analysis: the Schur coefficient is
nonnegative, and an eigenvalue above both Ritz values would make it negative. -/
theorem beam_eigenvalue_le_ritzHigh (ε : ℝ) (hε : 0 < ε) {f : BeamL2} {lam : ℝ}
    (hfdom : f ∈ (beamPerturbed ε).domain)
    (hf : (beamPerturbed ε) ⟨f, hfdom⟩ = ((lam : ℝ) : ℂ) • f)
    (hlam : lam < 1001 / 2) (hfn : ‖f‖ = 1) :
    lam ≤ ritzHigh ε := by
  obtain ⟨R, S, C, hR, hS, hC, hG1, hG2, hprod, hSb⟩ :=
    beam_ritz_scalar_data ε hε hfdom hf hlam hfn
  have hgap : ritzHigh ε - ritzLow ε = ε * (Real.sqrt 3 / 3) := ritzHigh_sub_ritzLow ε
  have hγ : 0 < ε * (Real.sqrt 3 / 3) := by
    have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    positivity
  by_cases hd1 : 0 ≤ ritzLow ε - lam
  · linarith
  · replace hd1 : ritzLow ε - lam < 0 := not_le.1 hd1
    by_contra hcon0
    have hcon : ritzHigh ε - lam < 0 := by
      have := not_le.1 hcon0
      linarith
    have hp1 : 0 < (ritzLow ε - lam) * (ritzHigh ε - lam) := mul_pos_of_neg_of_neg hd1 hcon
    have hp2 : 0 < (ritzLow ε - lam) * (ritzHigh ε - lam) * C := mul_pos hp1 hC
    have hp3 : 0 ≤ (-((ritzLow ε - lam) + (ritzHigh ε - lam))) * S :=
      mul_nonneg (by linarith) hS
    linarith [hprod]

/-- The printed individual-angle envelope is comfortably below `pi / 4` on the
whole range `0 < ε < 100` of the example. -/
theorem beam_individual_envelope_lt_pi_div_four (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100)
    {lam : ℝ} (hlam : lam ≤ ritzHigh ε) :
    Real.sqrt 7 / 10 * ε / (500 - lam) < Real.pi / 4 := by
  have hs3 : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  have hs7 : Real.sqrt 7 ≤ 3 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 7 by norm_num), Real.sqrt_nonneg 7]
  have hrh : ritzHigh ε ≤ 5 * ε / 6 := by
    unfold ritzHigh ritzHighCoefficient
    nlinarith [hε.le]
  have hden : (400 : ℝ) < 500 - lam := by linarith
  have hkey : Real.sqrt 7 / 10 * ε / (500 - lam) < 3 / 4 := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith [Real.sqrt_nonneg 7]
  linarith [Real.pi_gt_three]

/-- **Two orthonormal eigenvectors cannot both be within `pi / 4` of one unit
vector.**  This is Bessel's inequality: two cosines above `√2 / 2` would have
squares summing to more than one. -/
theorem beamLowEigenvector_not_both_near (ε : ℝ) (hε : 0 ≤ ε) (hε100 : ε < 100)
    {e : BeamL2} (hen : ‖e‖ = 1) {j k : Fin 2} (hjk : j ≠ k)
    (hj : Real.arccos ‖⟪e, beamLowEigenvector ε hε hε100 j⟫_ℂ‖ < Real.pi / 4)
    (hk : Real.arccos ‖⟪e, beamLowEigenvector ε hε hε100 k⟫_ℂ‖ < Real.pi / 4) : False := by
  have key : ∀ i : Fin 2, Real.arccos ‖⟪e, beamLowEigenvector ε hε hε100 i⟫_ℂ‖ < Real.pi / 4 →
      1 / 2 < ‖⟪e, beamLowEigenvector ε hε hε100 i⟫_ℂ‖ ^ 2 := by
    intro i hi
    have hle : ‖⟪e, beamLowEigenvector ε hε hε100 i⟫_ℂ‖ ≤ 1 := by
      have := norm_inner_le_norm (𝕜 := ℂ) e (beamLowEigenvector ε hε hε100 i)
      rw [hen, norm_beamLowEigenvector ε hε hε100 i] at this
      simpa using this
    have hcos : Real.cos (Real.pi / 4)
        < Real.cos (Real.arccos ‖⟪e, beamLowEigenvector ε hε hε100 i⟫_ℂ‖) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (Real.arccos_nonneg _)
        (by linarith [Real.pi_pos]) hi
    rw [Real.cos_arccos (by linarith [norm_nonneg (⟪e, beamLowEigenvector ε hε hε100 i⟫_ℂ)]) hle,
      Real.cos_pi_div_four] at hcos
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hb := (beamLowEigenvector_orthonormal ε hε hε100).sum_inner_products_le
    (s := ({j, k} : Finset (Fin 2))) e
  rw [hen, Finset.sum_pair hjk] at hb
  have hsym : ∀ i : Fin 2, ‖⟪beamLowEigenvector ε hε hε100 i, e⟫_ℂ‖
      = ‖⟪e, beamLowEigenvector ε hε hε100 i⟫_ℂ‖ := fun i => norm_inner_symm _ _
  rw [hsym j, hsym k] at hb
  have kj := key j hj
  have kk := key k hk
  norm_num at hb
  linarith

/-- **The eigenvector-to-Ritz-vector pairing, in eigenvalue order.**

The two exact eigenvectors of `A + ε t` below `500` are matched to *different*
Ritz vectors, and the matching is the one the paper prints: the eigenvector with
the smaller eigenvalue is within `(√7 / 10) ε / (500 - lambda)` of the lower Ritz
vector and the one with the larger eigenvalue is within the same envelope of the
upper Ritz vector.

The two ingredients are the branch information carried by
`beamLowEigenvector_individual_angle_le` -- the branch is decided by the position
of the eigenvalue relative to `ritzLow ε` -- and the fact that two orthonormal
vectors cannot both sit within `pi / 4` of one unit vector.  No eigenvalue lower
bound, no angle theorem and no external comparison result is used.

**The eigenvalue placement is part of the conclusion, not just of the proof.**  The surviving
branch is the one where the smaller eigenvalue sits at or below `ritzLow ε` and the larger one
strictly above it, and that placement is what lets Section 9 read the lower envelope at the
*lower* Ritz value.  Davis and Kahan print two different denominators for the two vectors --
`omega_1 < 0.00053 eps / (1 - 0.00043 eps)` against `omega_2 < 0.00053 eps / (1 - 0.0016 eps)`
-- and without `lambda_j <= ritzLow eps` only the weaker of the two is available for both. -/
theorem beamLowEigenvector_ritz_pairing (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100)
    {j k : Fin 2} (hjk : j ≠ k)
    (hle : beamLowEigenvalue ε hε.le hε100 j ≤ beamLowEigenvalue ε hε.le hε100 k) :
    beamLowEigenvalue ε hε.le hε100 j ≤ ritzLow ε
      ∧ ritzLow ε < beamLowEigenvalue ε hε.le hε100 k
      ∧ Real.arccos ‖⟪centeredAffineLp trialOne, beamLowEigenvector ε hε.le hε100 j⟫_ℂ‖
        ≤ Real.sqrt 7 / 10 * ε / (500 - beamLowEigenvalue ε hε.le hε100 j)
      ∧ Real.arccos ‖⟪centeredAffineLp trialTwo, beamLowEigenvector ε hε.le hε100 k⟫_ℂ‖
        ≤ Real.sqrt 7 / 10 * ε / (500 - beamLowEigenvalue ε hε.le hε100 k) := by
  have hone : ‖centeredAffineLp trialOne‖ = 1 := by
    obtain ⟨n1, -, -⟩ := beamTrial_orthonormal
    nlinarith [norm_nonneg (centeredAffineLp trialOne)]
  have htwo : ‖centeredAffineLp trialTwo‖ = 1 := by
    obtain ⟨-, n2, -⟩ := beamTrial_orthonormal
    nlinarith [norm_nonneg (centeredAffineLp trialTwo)]
  have hb : ∀ i : Fin 2, Real.sqrt 7 / 10 * ε / (500 - beamLowEigenvalue ε hε.le hε100 i)
      < Real.pi / 4 := by
    intro i
    refine beam_individual_envelope_lt_pi_div_four ε hε hε100 ?_
    exact beam_eigenvalue_le_ritzHigh ε hε (beamLowEigenvector_mem_domain ε hε.le hε100 i)
      (beamPerturbed_apply_beamLowEigenvector ε hε.le hε100 i)
      (by linarith [beamLowEigenvalue_lt_five_hundred ε hε.le hε100 i])
      (norm_beamLowEigenvector ε hε.le hε100 i)
  rcases beamLowEigenvector_individual_angle_le ε hε hε100 j with ⟨bj, aj⟩ | ⟨bj, aj⟩ <;>
    rcases beamLowEigenvector_individual_angle_le ε hε hε100 k with ⟨bk, ak⟩ | ⟨bk, ak⟩
  · exact (beamLowEigenvector_not_both_near ε hε.le hε100 hone hjk
      (lt_of_le_of_lt aj (hb j)) (lt_of_le_of_lt ak (hb k))).elim
  · exact ⟨bj, bk, aj, ak⟩
  · exact absurd hle (not_le.2 (by linarith))
  · exact (beamLowEigenvector_not_both_near ε hε.le hε100 htwo hjk
      (lt_of_le_of_lt aj (hb j)) (lt_of_le_of_lt ak (hb k))).elim

end

end Model
end FreeBeam
end DavisKahan
end TauCeti
