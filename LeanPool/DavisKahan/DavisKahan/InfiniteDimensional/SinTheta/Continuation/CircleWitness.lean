/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module


public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.CircleRieszIntegral
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.CircleContour
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.CentralBand
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.SharpDiagonalResolvents
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.SharpSchurComplement
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.Riccati.ContinuationWitnessOrientedBlocks

/-! # Circle Witness -/

@[expose] public section

open TauCeti.DavisKahan.Angle


/-!
# A separating circle as a spectral continuation witness

The continuation stack consumes a `SpectralContinuationWitness`: a closed
contour that separates the selected part of the spectrum uniformly along the
affine path `t ↦ A + t E`, together with a positive spectral margin.  This
module builds one from a circle.

`CircleContinuationData` packages what a circle has to supply -- a center, a
radius, a uniform margin, pathwise separation of the real spectrum, and a
uniform resolvent bound on the circle -- and
`spectralContinuationWitnessOfCircle` turns that into the witness, with the
endpoint projections identified as the genuine bounded self-adjoint spectral
projections and the projection variation controlled by the resolvent bound.

The second half constructs the data.  Given a spectral gap of width `d` around
an interval `[left, right]` and an off-diagonal perturbation with `‖E‖ < d / 2`,
the *canonical gap circle* -- centered at `(left + right) / 2` with radius
`(right - left + d) / 2` -- separates the spectrum along the whole path with the
uniform margin `(d / 2 - ‖E‖) / 2`.  The proof of the margin is a Schur
complement estimate: at a point of the canonical circle both diagonal blocks of
the path operator are invertible with resolvent bounded by `delta⁻¹`, the
off-diagonal blocks are bounded by `t ‖E‖ < delta`, so the Schur product has
norm below one and the block operator is invertible there.

Nothing here is specific to Davis--Kahan 1970; the Section 8 source theorems
consume it.
-/

open scoped InnerProductSpace
open Set Filter

namespace TauCeti
namespace DavisKahanExt

open DavisKahan
open TauCeti.DavisKahan.Foundation
open TauCeti.DavisKahan.RieszCircle

universe u v

section ContinuationBridge

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {A E : H →L[ℂ] H} {s : Set ℝ}

omit [CompleteSpace H] in
/-- Every point of the affine self-adjoint path is self-adjoint: the real
parameter is conjugation-fixed. -/
theorem operatorPath_isSelfAdjointOperator
    {A E : H →L[ℂ] H} (hA : A.IsSymmetric)
    (hE : E.IsSymmetric) (t : ℝ) :
    (operatorPath A E t).IsSymmetric :=
  hA.add (hE.smul (Complex.conj_ofReal t))

/-- Circle data sufficient to construct the continuation witness used by the
existing Section 8 development.  The pencil inverse is taken through the total
`Ring.inverse`, matching the RieszCircle surface. -/
structure CircleContinuationData
    (A E : H →L[ℂ] H) (s : Set ℝ) where
  hA : A.IsSymmetric
  hE : E.IsSymmetric
  hs : MeasurableSet s
  /-- The real center of the circle selecting the continued spectral subspace. -/
  center : ℝ
  /-- The radius of the circle selecting the continued spectral subspace. -/
  radius : ℝ
  /-- The uniform positive margin used to bound resolvents along the circle. -/
  margin : ℝ
  margin_pos : 0 < margin
  separates : ∀ t (_ht : t ∈ Set.Icc (0 : ℝ) 1),
    CircleSeparatesRealSpectrum (operatorPath A E t)
      (operatorPath_isSelfAdjointOperator hA hE t) s center radius
  inverse_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius →
      ‖Ring.inverse (z • (1 : H →L[ℂ] H) - operatorPath A E t)‖ ≤ margin⁻¹

omit [CompleteSpace H] in
/-- Every circle point lies on the sphere of the circle contour. -/
theorem circleContour_path_norm_sub_center
    (D : CircleContinuationData A E s) (x : unitInterval) :
    ‖(CircleContour.circleContour (D.center : ℂ) D.radius).path x -
        (D.center : ℂ)‖ = D.radius := by
  change ‖circleMap (D.center : ℂ) D.radius (2 * Real.pi * (x : ℝ)) -
      (D.center : ℂ)‖ = D.radius
  simpa [mem_sphere_iff_norm] using
    circleMap_mem_sphere (D.center : ℂ)
      (D.separates 0 ⟨le_rfl, zero_le_one⟩).radius_pos.le
      (2 * Real.pi * (x : ℝ))

/-- A common separating circle constructs the canonical spectral continuation
witness consumed by the Section 8 branch-selection stack.  The pathwise
separating contours are the circle contours of `CircleContour`, and the
uniform margin comes from the common resolvent bound through the
Neumann-series estimate. -/
noncomputable def spectralContinuationWitnessOfCircle
    (D : CircleContinuationData A E s) :
    SpectralContinuationWitness A E s where
  contour := CircleContour.circleContour (D.center : ℂ) D.radius
  separating := fun t ht =>
    CircleContour.circleSeparatingContour (operatorPath A E t)
      (operatorPath_isSelfAdjointOperator D.hA D.hE t) D.hs
      (D.separates t ht)
  geometric_eq := fun _t _ht => rfl
  margin := D.margin
  margin_pos := D.margin_pos
  spectrum_separated := by
    intro t ht x lam hlam
    have hzc := circleContour_path_norm_sub_center D x
    have hznot : (CircleContour.circleContour (D.center : ℂ) D.radius).path x ∉
        spectrum ℂ (operatorPath A E t) :=
      (D.separates t ht).contour_resolvent _ hzc
    have hb := D.inverse_bound t ht _ hzc
    exact CircleContour.margin_le_norm_sub_of_inverse_bound
      D.margin_pos hznot hb hlam

/-- The source and target selected projections of the witness are the genuine
bounded self-adjoint spectral projections. -/
theorem spectralContinuationWitness_of_circle_endpoints
    (D : CircleContinuationData A E s) :
    (spectralContinuationWitnessOfCircle
        D).sourceSelectedSpectralSubspace.starProjection =
        boundedSelfAdjointSpectralProjection A D.hA s D.hs ∧
      (spectralContinuationWitnessOfCircle
          D).targetSelectedSpectralSubspace.starProjection =
        boundedSelfAdjointSpectralProjection (A + E)
          (D.hA.add D.hE) s D.hs := by
  constructor
  · exact (boundedSelfAdjointSpectralProjection_eq_starProjection
      A D.hA s D.hs).symm
  · exact (boundedSelfAdjointSpectralProjection_eq_starProjection
      (A + E) (D.hA.add D.hE) s D.hs).symm

/-- Quantitative projection variation obtained from the common-circle
resolvent bound. -/
theorem selectedBranchProjectionLipschitzConstant_of_circle
    (D : CircleContinuationData A E s) :
    selectedBranchProjectionLipschitzConstant
      (spectralContinuationWitnessOfCircle D).contour E D.margin ≤
        D.radius * ‖E‖ / D.margin ^ 2 := by
  have hr : (0 : ℝ) ≤ D.radius :=
    (D.separates 0 ⟨le_rfl, zero_le_one⟩).radius_pos.le
  apply le_of_eq
  unfold selectedBranchProjectionLipschitzConstant
  have hlen : (spectralContinuationWitnessOfCircle D).contour.contourLength =
      2 * Real.pi * D.radius :=
    CircleContour.circleContour_contourLength _ hr
  have hnorm : ‖rieszNormalization‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_rieszNormalization, norm_inv]
    have h2pi : ‖((2 : ℂ) * Real.pi * Complex.I)‖ = 2 * Real.pi := by
      simp [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    rw [h2pi]
  rw [hlen, hnorm]
  have hm : (D.margin : ℝ) ≠ 0 := D.margin_pos.ne'
  field_simp


/-- Every point on the canonical finite-gap circle is at distance at least
`d / 2` from the selected interval. -/
theorem canonicalGapCircle_distance_interval
    {left right d : ℝ} (_hlr : left ≤ right) {z : ℂ}
    (hz : ‖z - (((left + right) / 2 : ℝ) : ℂ)‖ =
      (right - left + d) / 2)
    {lam : ℝ} (hlam : lam ∈ Set.Icc left right) :
    d / 2 ≤ ‖z - (lam : ℂ)‖ := by
  have hcenter :
      ‖(lam : ℂ) - (((left + right) / 2 : ℝ) : ℂ)‖ ≤
        (right - left) / 2 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hlam.1, hlam.2]
  have hdecomp :
      z - (((left + right) / 2 : ℝ) : ℂ) =
        (z - (lam : ℂ)) +
          ((lam : ℂ) - (((left + right) / 2 : ℝ) : ℂ)) := by
    ring
  have htri :
      ‖z - (((left + right) / 2 : ℝ) : ℂ)‖ ≤
        ‖z - (lam : ℂ)‖ +
          ‖(lam : ℂ) - (((left + right) / 2 : ℝ) : ℂ)‖ := by
    rw [hdecomp]
    exact norm_add_le _ _
  rw [hz] at htri
  linarith

/-- Every point on the canonical finite-gap circle is at distance at least
`d / 2` from the complementary exterior. -/
theorem canonicalGapCircle_distance_exterior
    {left right d : ℝ} (hlr : left ≤ right) (hd0 : 0 ≤ d) {z : ℂ}
    (hz : ‖z - (((left + right) / 2 : ℝ) : ℂ)‖ =
      (right - left + d) / 2)
    {lam : ℝ} (hlam : lam ≤ left - d ∨ right + d ≤ lam) :
    d / 2 ≤ ‖z - (lam : ℂ)‖ := by
  have hfar :
      (right - left + d) / 2 + d / 2 ≤
        ‖(lam : ℂ) - (((left + right) / 2 : ℝ) : ℂ)‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rcases hlam with hlam | hlam
    · have hsign : lam - (left + right) / 2 ≤ 0 := by
        linarith
      rw [abs_of_nonpos hsign]
      linarith
    · have hsign : 0 ≤ lam - (left + right) / 2 := by
        linarith
      rw [abs_of_nonneg hsign]
      linarith
  have hdecomp :
      (lam : ℂ) - (((left + right) / 2 : ℝ) : ℂ) =
        ((lam : ℂ) - z) +
          (z - (((left + right) / 2 : ℝ) : ℂ)) := by
    ring
  have htri :
      ‖(lam : ℂ) - (((left + right) / 2 : ℝ) : ℂ)‖ ≤
        ‖(lam : ℂ) - z‖ +
          ‖z - (((left + right) / 2 : ℝ) : ℂ)‖ := by
    rw [hdecomp]
    exact norm_add_le _ _
  rw [hz] at htri
  have hdist : d / 2 ≤ ‖(lam : ℂ) - z‖ := by
    linarith
  simpa only [norm_sub_rev] using hdist

/-- The real points strictly inside the canonical finite-gap circle are
exactly the interval enlarged by `d / 2` on both sides. -/
theorem canonicalGapCircle_inside_iff
    {left right d x : ℝ} :
    ‖(x : ℂ) - (((left + right) / 2 : ℝ) : ℂ)‖ <
        (right - left + d) / 2 ↔
      x ∈ Set.Ioo (left - d / 2) (right + d / 2) := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor <;> linarith
  · rintro ⟨hlo, hhi⟩
    constructor <;> linarith

/-- The Schur criterion excludes any real point that remains closer than the
chosen margin to the canonical finite-gap circle. -/
theorem canonicalGapCircle_margin_le_realSpectrum
    (hA : A.IsSymmetric) (hE : E.IsSymmetric)
    {U : Submodule ℂ H} [U.HasOrthogonalProjection]
    (_hU : A.Reduces U) (_hoff : Submodule.IsOffDiagonal U E)
    {d left right : ℝ} (hd : 0 < d) (hlr : left ≤ right)
    (hdiag : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      ∀ hpath : (operatorPath A E t).IsSymmetric,
      ∀ z : ℂ, ∀ delta0 delta1 : ℝ,
        0 < delta0 → 0 < delta1 →
        (∀ lam ∈ Set.Icc left right,
          delta0 ≤ ‖z - (lam : ℂ)‖) →
        (∀ lam ∈ {x : ℝ | x ≤ left - d ∨ right + d ≤ x},
          delta1 ≤ ‖z - (lam : ℂ)‖) →
        let Ht := subspaceBlockOperatorData (operatorPath A E t) U hpath
        InResolventSet Ht.A0 z ∧
        ‖resolventOperator Ht.A0 z‖ ≤ delta0⁻¹ ∧
        InResolventSet Ht.A1 z ∧
        ‖resolventOperator Ht.A1 z‖ ≤ delta1⁻¹ ∧
        ‖Ht.B01‖ ≤ t * ‖E‖ ∧
        ‖Ht.B10‖ ≤ t * ‖E‖)
    (hsmall : ‖E‖ < d / 2)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    {z : ℂ}
    (hz : ‖z - (((left + right) / 2 : ℝ) : ℂ)‖ =
      (right - left + d) / 2)
    {lam : ℝ} (hlam : lam ∈ realSpectrum (operatorPath A E t)) :
    (d / 2 - ‖E‖) / 2 ≤ ‖z - (lam : ℂ)‖ := by
  let : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let : CompleteSpace (Uᗮ : Submodule ℂ H) :=
    (Uᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let margin : ℝ := (d / 2 - ‖E‖) / 2
  let delta : ℝ := d / 2 - margin
  have hmargin : 0 < margin := by
    dsimp only [margin]
    linarith
  have hdelta : 0 < delta := by
    dsimp only [delta, margin]
    linarith [norm_nonneg E]
  have htd : t * ‖E‖ < delta := by
    have htE : t * ‖E‖ ≤ ‖E‖ := by
      nlinarith [ht.1, ht.2, norm_nonneg E]
    dsimp only [delta, margin]
    linarith
  by_contra hnot
  rw [not_le] at hnot
  have hsep0 : ∀ mu ∈ Set.Icc left right,
      delta ≤ ‖(lam : ℂ) - (mu : ℂ)‖ := by
    intro mu hmu
    have hcircle := canonicalGapCircle_distance_interval hlr hz hmu
    have htri : ‖z - (mu : ℂ)‖ ≤
        ‖z - (lam : ℂ)‖ + ‖(lam : ℂ) - (mu : ℂ)‖ := by
      calc
        ‖z - (mu : ℂ)‖ =
            ‖(z - (lam : ℂ)) + ((lam : ℂ) - (mu : ℂ))‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    dsimp only [delta, margin]
    linarith
  have hsep1 : ∀ mu ∈ {x : ℝ | x ≤ left - d ∨ right + d ≤ x},
      delta ≤ ‖(lam : ℂ) - (mu : ℂ)‖ := by
    intro mu hmu
    have hcircle := canonicalGapCircle_distance_exterior hlr hd.le hz hmu
    have htri : ‖z - (mu : ℂ)‖ ≤
        ‖z - (lam : ℂ)‖ + ‖(lam : ℂ) - (mu : ℂ)‖ := by
      calc
        ‖z - (mu : ℂ)‖ =
            ‖(z - (lam : ℂ)) + ((lam : ℂ) - (mu : ℂ))‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    dsimp only [delta, margin]
    linarith
  let hpath := operatorPath_isSelfAdjointOperator hA hE t
  let Ht := subspaceBlockOperatorData (operatorPath A E t) U hpath
  obtain ⟨h0, hR0, h1, hR1, hB01, hB10⟩ :=
    hdiag t ht hpath (lam : ℂ) delta delta hdelta hdelta hsep0 hsep1
  have hq0 : 0 ≤ t * ‖E‖ := mul_nonneg ht.1 (norm_nonneg E)
  have hratio0 : 0 ≤ delta⁻¹ * (t * ‖E‖) :=
    mul_nonneg (inv_nonneg.mpr hdelta.le) hq0
  have hratio1 : delta⁻¹ * (t * ‖E‖) < 1 := by
    rw [inv_mul_eq_div]
    exact (div_lt_one hdelta).2 htd
  let R0 : U →L[ℂ] U := resolventOperator Ht.A0 (lam : ℂ)
  let R1 : Uᗮ →L[ℂ] Uᗮ := resolventOperator Ht.A1 (lam : ℂ)
  have hR0' : ‖R0‖ ≤ delta⁻¹ := by
    simpa only [R0] using hR0
  have hR1' : ‖R1‖ ≤ delta⁻¹ := by
    simpa only [R1] using hR1
  have hdeltaInv : 0 ≤ delta⁻¹ := inv_nonneg.mpr hdelta.le
  have hprod :
      ‖(((R1 ∘L Ht.B10) ∘L R0) ∘L Ht.B01)‖ < 1 := by
    have hcomp1 :
        ‖(((R1 ∘L Ht.B10) ∘L R0) ∘L Ht.B01)‖ ≤
          ‖((R1 ∘L Ht.B10) ∘L R0)‖ * ‖Ht.B01‖ :=
      ContinuousLinearMap.opNorm_comp_le
        ((R1 ∘L Ht.B10) ∘L R0) Ht.B01
    have hcomp2 :
        ‖((R1 ∘L Ht.B10) ∘L R0)‖ ≤
          ‖R1 ∘L Ht.B10‖ * ‖R0‖ :=
      ContinuousLinearMap.opNorm_comp_le (R1 ∘L Ht.B10) R0
    have hcomp3 :
        ‖R1 ∘L Ht.B10‖ ≤ ‖R1‖ * ‖Ht.B10‖ :=
      ContinuousLinearMap.opNorm_comp_le R1 Ht.B10
    have hpair :
        ‖R1‖ * ‖Ht.B10‖ ≤ delta⁻¹ * (t * ‖E‖) :=
      mul_le_mul hR1' hB10 (norm_nonneg Ht.B10) hdeltaInv
    have htriple :
        (‖R1‖ * ‖Ht.B10‖) * ‖R0‖ ≤
          (delta⁻¹ * (t * ‖E‖)) * delta⁻¹ :=
      mul_le_mul hpair hR0' (norm_nonneg R0) hratio0
    have hfour :
        ((‖R1‖ * ‖Ht.B10‖) * ‖R0‖) * ‖Ht.B01‖ ≤
          ((delta⁻¹ * (t * ‖E‖)) * delta⁻¹) * (t * ‖E‖) :=
      mul_le_mul htriple hB01 (norm_nonneg Ht.B01)
        (mul_nonneg hratio0 hdeltaInv)
    have hnorm :
        ‖(((R1 ∘L Ht.B10) ∘L R0) ∘L Ht.B01)‖ ≤
          delta⁻¹ * (t * ‖E‖) * delta⁻¹ * (t * ‖E‖) := by
      calc
        ‖(((R1 ∘L Ht.B10) ∘L R0) ∘L Ht.B01)‖
            ≤ ‖((R1 ∘L Ht.B10) ∘L R0)‖ * ‖Ht.B01‖ := hcomp1
        _ ≤ (‖R1 ∘L Ht.B10‖ * ‖R0‖) * ‖Ht.B01‖ :=
          mul_le_mul_of_nonneg_right hcomp2 (norm_nonneg Ht.B01)
        _ ≤ ((‖R1‖ * ‖Ht.B10‖) * ‖R0‖) * ‖Ht.B01‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcomp3 (norm_nonneg R0))
            (norm_nonneg Ht.B01)
        _ ≤ delta⁻¹ * (t * ‖E‖) * delta⁻¹ * (t * ‖E‖) := hfour
    calc
      ‖(((R1 ∘L Ht.B10) ∘L R0) ∘L Ht.B01)‖
          ≤ delta⁻¹ * (t * ‖E‖) * delta⁻¹ * (t * ‖E‖) := hnorm
      _ = (delta⁻¹ * (t * ‖E‖)) ^ 2 := by ring
      _ < 1 := by nlinarith
  have hblock : InResolventSet (blockOperator Ht) (lam : ℂ) := by
    simpa only [R0, R1, ContinuousLinearMap.comp_assoc] using
      blockOperator_inResolventSet_of_schur_norm_lt_one
        Ht (lam : ℂ) h0 h1 hprod
  have hnotBlock : (lam : ℂ) ∉ spectrum ℂ (blockOperator Ht) :=
    not_mem_spectrum_of_inResolventSet (blockOperator Ht) hblock
  have hspec := spectrum_subspaceBlockOperatorData
    (operatorPath A E t) U hpath
  have hnotAmbient : (lam : ℂ) ∉ spectrum ℂ (operatorPath A E t) := by
    rw [hspec]
    exact hnotBlock
  exact hnotAmbient hlam

/-- The printed perturbation half-gap condition produces a single common
circle, a uniform spectral margin, and hence the continuation datum used by
Section 8. -/
theorem exists_circleContinuationData_of_offDiagonal_halfGap
    (hA : A.IsSymmetric) (hE : E.IsSymmetric)
    {U : Submodule ℂ H} [U.HasOrthogonalProjection]
    (hU : A.Reduces U) (hoff : Submodule.IsOffDiagonal U E)
    {d : ℝ} (hd : 0 < d)
    (hfinite : FiniteGapConfiguration A U d)
    (hsmall : ‖E‖ < d / 2) :
    ∃ left right : ℝ, left ≤ right ∧
      Nonempty (CircleContinuationData A E
        (Set.Ioo (left - d / 2) (right + d / 2))) := by
  let : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let : CompleteSpace (Uᗮ : Submodule ℂ H) :=
    (Uᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  obtain ⟨left, right, hlr, hdiag⟩ :=
    hfinite.exists_operatorPath_diagonalResolventData A E U hU hoff
  let center : ℝ := (left + right) / 2
  let radius : ℝ := (right - left + d) / 2
  let margin : ℝ := (d / 2 - ‖E‖) / 2
  have hradius : 0 < radius := by
    dsimp only [radius]
    linarith
  have hmargin : 0 < margin := by
    dsimp only [margin]
    linarith
  have huniform : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius →
      ∀ lam ∈ realSpectrum (operatorPath A E t),
        margin ≤ ‖z - (lam : ℂ)‖ := by
    intro t ht z hz lam hlam
    exact canonicalGapCircle_margin_le_realSpectrum hA hE hU hoff hd hlr
      hdiag hsmall ht (by simpa only [center, radius] using hz) hlam
  refine ⟨left, right, hlr, ⟨?_⟩⟩
  refine
    { hA := hA
      hE := hE
      hs := measurableSet_Ioo
      center := center
      radius := radius
      margin := margin
      margin_pos := hmargin
      separates := ?_
      inverse_bound := ?_ }
  · intro t ht
    have hpath := operatorPath_isSelfAdjointOperator hA hE t
    refine
      { radius_pos := hradius
        contour_resolvent := ?_
        inside_iff_mem := ?_ }
    · intro z hz
      have hsep : ∀ lam ∈ realSpectrum (operatorPath A E t),
          margin ≤ ‖z - (lam : ℂ)‖ :=
        huniform t ht z hz
      have hres := complex_inResolventSet_of_distance
        (operatorPath A E t) hpath z margin hmargin hsep
      exact not_mem_spectrum_of_inResolventSet (operatorPath A E t) hres
    · intro x _hx
      simpa only [center, radius] using
        (canonicalGapCircle_inside_iff (left := left) (right := right)
          (d := d) (x := x))
  · intro t ht z hz
    have hpath := operatorPath_isSelfAdjointOperator hA hE t
    have hsep : ∀ lam ∈ realSpectrum (operatorPath A E t),
        margin ≤ ‖z - (lam : ℂ)‖ :=
      huniform t ht z hz
    have hres := complex_inResolventSet_and_norm_resolvent_le_inv_distance
      (operatorPath A E t) hpath z margin hmargin hsep
    rw [norm_ringInverse_pencil_eq_norm_resolventOperator
      (operatorPath A E t) hres.1]
    exact hres.2

/-- Source-facing continuation witness obtained directly from the finite-gap,
off-diagonal, and perturbation half-gap hypotheses. -/
theorem exists_spectralContinuationWitness_of_offDiagonal_halfGap
    (hA : A.IsSymmetric) (hE : E.IsSymmetric)
    {U : Submodule ℂ H} [U.HasOrthogonalProjection]
    (hU : A.Reduces U) (hoff : Submodule.IsOffDiagonal U E)
    {d : ℝ} (hd : 0 < d)
    (hfinite : FiniteGapConfiguration A U d)
    (hsmall : ‖E‖ < d / 2) :
    ∃ left right : ℝ, left ≤ right ∧
      Nonempty (SpectralContinuationWitness A E
        (Set.Ioo (left - d / 2) (right + d / 2))) := by
  obtain ⟨left, right, hlr, ⟨D⟩⟩ :=
    exists_circleContinuationData_of_offDiagonal_halfGap
      hA hE hU hoff hd hfinite hsmall
  exact ⟨left, right, hlr, ⟨spectralContinuationWitnessOfCircle D⟩⟩

end ContinuationBridge

/-! ## The affine path, its spectral gap, and the canonical separating circle

The construction above takes a `CircleContinuationData` as given.  This last
section builds one from a spectral gap: if the real spectrum of `T` lies in
`[l, r] ∪ gapExterior l r d`, then the canonical gap circle -- centered at
`gapCenter l r` with radius `(r - l + d) / 2` -- separates the real spectrum and
selects exactly the central band, with every circle point at distance at least
`d / 2` from the spectrum.  A self-adjoint perturbation of norm below `d / 2`
shrinks both gaps by its norm and leaves them nonempty, which is what makes the
same circle work along the whole path.
-/

section Path

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The real spectrum of a self-adjoint operator splits over a reducing
decomposition. -/
theorem realSpectrum_subset_union_of_reduces
    {T : H →L[ℂ] H} (hT : T.IsSymmetric) {U : Submodule ℂ H}
    [U.HasOrthogonalProjection] (hU : T.Reduces U) {p q : Set ℝ}
    (h0 : SpectrumIn T U p) (h1 : SpectrumIn T Uᗮ q) :
    realSpectrum T ⊆ p ∪ q := by
  let : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let : CompleteSpace (Uᗮ : Submodule ℂ H) :=
    (Uᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  rw [realSpectrum_eq_union_compressions_of_reduces T U hT hU]
  rintro x (hx | hx)
  · exact Or.inl (h0.subset (by
      rwa [realSpectrum_compressOperator_eq_restrictedSpectrum T U h0.invariant] at hx))
  · exact Or.inr (h1.subset (by
      rwa [realSpectrum_compressOperator_eq_restrictedSpectrum T Uᗮ h1.invariant] at hx))

omit [CompleteSpace H] in
/-- A real scalar multiple of a complex-linear operator is the multiple by the
corresponding complex scalar. -/
theorem real_smul_eq_complex_smul (t : ℝ) (E : H →L[ℂ] H) :
    (t • E : H →L[ℂ] H) = ((t : ℂ)) • E := by
  ext x
  simp [Complex.coe_smul]

omit [CompleteSpace H] in
/-- Every point of the affine path `A + t E` with real `t` is self-adjoint. -/
theorem isSelfAdjointOperator_path {A E : H →L[ℂ] H}
    (hA : A.IsSymmetric) (hE : E.IsSymmetric) (t : ℝ) :
    (A + t • E).IsSymmetric := by
  rw [real_smul_eq_complex_smul]
  exact operatorPath_isSelfAdjointOperator hA hE t

/-- **The two gaps survive a small self-adjoint perturbation.**  Both open gaps
shrink by `gam` on each side, and they stay nonempty precisely because
`gam < delta / 2`.  This is the printed step
"`A(σ)`, being a perturbation of bound norm at most `γ`, has spectrum disjoint
from `(β - δ + γ, β - γ)`", proved by the Neumann series. -/
theorem realSpectrum_add_subset_of_gap
    {T K : H →L[ℂ] H} (hT : T.IsSymmetric)
    {alpha beta delta gam : ℝ} (hab : beta ≤ alpha) (_hdelta : 0 < delta)
    (hgam : 0 ≤ gam) (_hgamlt : gam < delta / 2) (hK : ‖K‖ ≤ gam)
    (hgap : realSpectrum T ⊆ Set.Icc beta alpha ∪ gapExterior beta alpha delta) :
    realSpectrum (T + K) ⊆
      Set.Icc (beta - gam) (alpha + gam) ∪
        gapExterior (beta - gam) (alpha + gam) (delta - 2 * gam) := by
  intro lam hlam
  by_contra hnot
  rw [Set.mem_union] at hnot
  have h1 : lam ∉ Set.Icc (beta - gam) (alpha + gam) := fun h => hnot (Or.inl h)
  have h2 : lam ∉ gapExterior (beta - gam) (alpha + gam) (delta - 2 * gam) :=
    fun h => hnot (Or.inr h)
  have h2' : beta - delta + gam < lam ∧ lam < alpha + delta - gam := by
    constructor
    · by_contra hcon
      exact h2 (Or.inl (by simp only [not_lt] at hcon; linarith))
    · by_contra hcon
      exact h2 (Or.inr (by simp only [not_lt] at hcon; linarith))
  have h1' : lam < beta - gam ∨ alpha + gam < lam := by
    rcases lt_or_ge lam (beta - gam) with h | h
    · exact Or.inl h
    · exact Or.inr (by
        by_contra hcon
        exact h1 ⟨h, le_of_not_gt hcon⟩)
  -- the ambient spectrum lies below `beta - delta` or above `beta`, and dually
  have hnorm : ∀ mu : ℝ, ‖((lam : ℝ) : ℂ) - ((mu : ℝ) : ℂ)‖ = |lam - mu| := by
    intro mu
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hcontra : ∀ m : ℝ, 0 < m → gam < m →
      (∀ mu ∈ realSpectrum T, m ≤ |lam - mu|) → False := by
    intro m hm hgm hsep
    have hsep' : ∀ mu ∈ realSpectrum T, m ≤ ‖((lam : ℝ) : ℂ) - ((mu : ℝ) : ℂ)‖ := by
      intro mu hmu; rw [hnorm]; exact hsep mu hmu
    exact notMem_spectrum_add_of_realSpectrum_dist hT hm hsep'
      (lt_of_le_of_lt hK hgm) hlam
  rcases h1' with hlow | hhigh
  · refine hcontra (min (beta - lam) (lam - (beta - delta))) ?_ ?_ ?_
    · exact lt_min (by linarith) (by linarith)
    · exact lt_min (by linarith) (by linarith)
    · intro mu hmu
      rcases hgap hmu with hin | hout
      · have : beta ≤ mu := hin.1
        rw [abs_of_nonpos (by linarith)]
        exact le_trans (min_le_left _ _) (by linarith)
      · rcases hout with hle | hge
        · rw [abs_of_nonneg (by linarith)]
          exact le_trans (min_le_right _ _) (by linarith)
        · rw [abs_of_nonpos (by linarith)]
          exact le_trans (min_le_left _ _) (by linarith)
  · refine hcontra (min (lam - alpha) (alpha + delta - lam)) ?_ ?_ ?_
    · exact lt_min (by linarith) (by linarith)
    · exact lt_min (by linarith) (by linarith)
    · intro mu hmu
      rcases hgap hmu with hin | hout
      · have : mu ≤ alpha := hin.2
        rw [abs_of_nonneg (by linarith)]
        exact le_trans (min_le_left _ _) (by linarith)
      · rcases hout with hle | hge
        · rw [abs_of_nonneg (by linarith)]
          exact le_trans (min_le_left _ _) (by linarith)
        · rw [abs_of_nonpos (by linarith)]
          exact le_trans (min_le_right _ _) (by linarith)

omit [CompleteSpace H] in
/-- Every point of the canonical gap circle is at distance at least `d / 2`
from the real spectrum. -/
theorem margin_le_dist_of_gap
    {T : H →L[ℂ] H} {l r d : ℝ} (hlr : l ≤ r) (hd : 0 < d)
    (hgap : realSpectrum T ⊆ Set.Icc l r ∪ gapExterior l r d)
    {z : ℂ} (hz : ‖z - ((gapCenter l r : ℝ) : ℂ)‖ = (r - l + d) / 2)
    {lam : ℝ} (hlam : lam ∈ realSpectrum T) :
    d / 2 ≤ ‖z - (lam : ℂ)‖ := by
  rw [gapCenter] at hz
  rcases hgap hlam with hin | hout
  · exact canonicalGapCircle_distance_interval hlr hz hin
  · exact canonicalGapCircle_distance_exterior hlr hd.le hz hout

/-- The canonical gap circle separates the real spectrum, selecting exactly the
central band. -/
theorem circleSeparates_of_gap
    {T : H →L[ℂ] H} (hT : T.IsSymmetric) {l r d : ℝ}
    (hlr : l ≤ r) (hd : 0 < d)
    (hgap : realSpectrum T ⊆ Set.Icc l r ∪ gapExterior l r d) :
    CircleSeparatesRealSpectrum T hT (centralBand l r d) (gapCenter l r)
      ((r - l + d) / 2) where
  radius_pos := by linarith
  contour_resolvent := by
    intro z hz
    exact not_mem_spectrum_of_inResolventSet T
      (complex_inResolventSet_of_distance T hT z (d / 2) (by linarith)
        fun lam hlam => margin_le_dist_of_gap hlr hd hgap hz hlam)
  inside_iff_mem := by
    intro x _
    rw [gapCenter]
    exact canonicalGapCircle_inside_iff (left := l) (right := r) (d := d) (x := x)

end Path

end DavisKahanExt
end TauCeti
