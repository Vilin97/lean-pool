/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.SpectralGapFormBounds
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.TanTwoTheta.OffDiagonalSpectralRepulsion
import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.DirectRotation
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.OperatorAngle
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SpectralOrder

/-! # Theorem81 -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Theorem 8.1, from the printed hypotheses

The Section 8 configuration is the `tan 2Theta` one:

* `A` is self-adjoint and the subspace `P` reduces it;
* the `P` block is below `alpha` and the `Pᗮ` block is above `alpha + delta`;
* `H` is self-adjoint and *fully* off-diagonal with respect to `P`.

Nothing else.  In particular the caller supplies no contour, no continuation
witness, no smallness constant, and no orientation: those are the paper's
conclusions and are proved here.

What the theorem delivers:

* full spectral repulsion for `A + H` -- the open gap `(alpha, alpha+delta)`
  meets no spectrum at all, continuous spectrum included;
* the canonical branch `Q`, the genuine spectral subspace of `A + H` for
  `Iic alpha`, which reduces `A + H` and carries the sharp ordered form bounds
  and the corresponding restricted-spectrum containments;
* `P` and `Q` are *strictly* within a quarter turn -- stronger than the
  printed closed condition `Theta <= pi/4`;
* uniqueness: any reducing subspace of `A + H` satisfying the printed closed
  condition equals `Q`.  So the closed condition and the spectral orientation
  characterize the same subspace, which is the paper's `iff`.

The uniqueness argument is the paper's.  A reducing projection commutes with
`A + H`, hence -- because the gap makes the spectral projection a *continuous*
functional calculus (`boundedSelfAdjointSpectralProjection_Iic_eq_cfcHom`) --
with the branch projection.  So a vector of `M` outside `Q` can be projected
into `M ∩ Qᗮ`, where the strict quarter-angle bound for `Q` and the closed one
for `M` contradict each other.  The companion direction is the same argument
applied to the complements.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open Set
open scoped InnerProductSpace
open DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.Foundation
open TauCeti.SpectralOrder

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-! ### Scalar bookkeeping: the quarter turn -/

/-- The quarter-turn angle: `arcsin (√2 / 2) = π / 4`. -/
theorem arcsin_sqrt_two_div_two : Real.arcsin (Real.sqrt 2 / 2) = Real.pi / 4 :=
  Real.arcsin_eq_of_sin_eq Real.sin_pi_div_four
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

omit [CompleteSpace E] in
/-- The printed closed quarter-angle condition `Theta <= pi/4` is exactly the
projection-gap condition `gap <= sqrt 2 / 2`. -/
theorem maximalAngle_le_pi_div_four_iff (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    maximalAngle U V ≤ Real.pi / 4 ↔ U.projectionGap V ≤ Real.sqrt 2 / 2 := by
  have hmem : Real.pi / 4 ∈ Set.Ico (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  change Real.arcsin (U.projectionGap V) ≤ Real.pi / 4 ↔ _
  rw [Real.arcsin_le_iff_le_sin' hmem, Real.sin_pi_div_four]

/-- The strict quarter-angle condition, in the two equivalent phrasings.

Stated over an arbitrary `RCLike` field, with its own binders: the real
Section 8 descent needs it over `ℝ`, and the identity is pure scalar
bookkeeping about `arcsin`. -/
theorem maximalAngle_lt_pi_div_four_iff {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    maximalAngle U V < Real.pi / 4 ↔ IsQuarterAcute U V := by
  have hmem : Real.pi / 4 ∈ Set.Ioc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  change Real.arcsin (U.projectionGap V) < Real.pi / 4 ↔ _
  rw [Real.arcsin_lt_iff_lt_sin' hmem, Real.sin_pi_div_four]
  rfl

/-! ### The canonical branch -/

/-- The canonical low branch of Theorem 8.1: the genuine spectral subspace of
the perturbed operator for the closed half-line `Iic alpha`. -/
def canonicalLowBranch (B : E →L[ℂ] E) (hB : B.IsSymmetric)
    (alpha : ℝ) : Submodule ℂ E :=
  boundedSelfAdjointSpectralSubspace B hB (Set.Iic alpha) measurableSet_Iic

/-- The canonical low branch is a spectral subspace, hence complemented. -/
instance canonicalLowBranch_hasOrthogonalProjection (B : E →L[ℂ] E)
    (hB : B.IsSymmetric) (alpha : ℝ) :
    (canonicalLowBranch B hB alpha).HasOrthogonalProjection :=
  boundedSelfAdjointSpectralSubspace_hasOrthogonalProjection B hB _ _

/-- The conclusions of Davis--Kahan 1970 Theorem 8.1 about the canonical
branch, stated for an arbitrary complex Hilbert space. -/
structure Theorem81Conclusion (A H : E →L[ℂ] E) (P Q : Submodule ℂ E)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (alpha delta : ℝ) : Prop where
  /-- The open gap contains no spectrum of the perturbed operator. -/
  spectral_repulsion :
    realSpectrum (A + H) ⊆ Set.Iic alpha ∪ Set.Ici (alpha + delta)
  /-- The branch reduces the perturbed operator. -/
  branch_reduces : ContinuousLinearMap.Reduces (A + H) Q
  /-- Sharp upper form bound on the branch. -/
  branch_form_low : ∀ x ∈ Q, RCLike.re ⟪(A + H) x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2
  /-- Sharp lower form bound on its complement. -/
  branch_form_high :
    ∀ x ∈ Qᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪(A + H) x, x⟫_ℂ
  /-- The printed spectral orientation `Lambda 0 <= alpha`. -/
  branch_spectrum_low : SpectrumIn (A + H) Q (Set.Iic alpha)
  /-- The printed spectral orientation `Lambda 1 >= alpha + delta`. -/
  branch_spectrum_high : SpectrumIn (A + H) Qᗮ (Set.Ici (alpha + delta))
  /-- The branch is strictly inside the quarter turn. -/
  quarter_acute : IsQuarterAcute P Q
  /-- Equivalently, in the printed scalar form. -/
  maximal_angle_lt_pi_div_four : maximalAngle P Q < Real.pi / 4

section Theorem81

variable (A H : E →L[ℂ] E) (P : Submodule ℂ E) [P.HasOrthogonalProjection]
variable {alpha delta : ℝ}

/-- **Theorem 8.1, existence half.**  From the printed hypotheses alone. -/
theorem theorem8_1_canonicalBranch
    (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hHP : ∀ x ∈ P, H x ∈ Pᗮ)
    (hHPperp : ∀ x ∈ Pᗮ, H x ∈ P) :
    Theorem81Conclusion A H P
      (canonicalLowBranch (A + H)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hH)) alpha)
      alpha delta := by
  classical
  have hAH : IsSelfAdjoint (A + H) := hA.add hH
  have hAHop : (A + H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hAH
  have hAsym : A.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hPperpperp : (Pᗮ)ᗮ = P := Submodule.orthogonal_orthogonal P
  -- `A` also leaves `Pᗮ` invariant.
  have hAPperp : ∀ x ∈ Pᗮ, A x ∈ Pᗮ := by
    intro x hx
    exact map_mem_orthogonal_of_forall_map_mem hAsym hAP hx
  -- Repulsion, with `Pᗮ` as the high side.
  have hrep : realSpectrum (A + H) ⊆ Set.Iic alpha ∪ Set.Ici (alpha + delta) := by
    refine realSpectrum_add_offDiagonal_subset_exterior_of_form_gap A H Pᗮ hA hH
      hAPperp hPhigh ?_ ?_ ?_
    · intro x hx
      rw [hPperpperp] at hx
      exact hPlow x hx
    · intro x hx
      rw [hPperpperp]
      exact hHPperp x hx
    · intro x hx
      rw [hPperpperp] at hx
      exact hHP x hx
  set Q : Submodule ℂ E := canonicalLowBranch (A + H) hAHop alpha with hQdef
  have hQreduces : ContinuousLinearMap.Reduces (A + H) Q :=
    boundedSelfAdjointSpectralSubspace_reduces (A + H) hAHop (Set.Iic alpha)
      measurableSet_Iic
  have hlow : ∀ x ∈ Q, RCLike.re ⟪(A + H) x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2 := fun x hx =>
    re_inner_le_of_mem_boundedSelfAdjointSpectralSubspace_Iic (A + H) hAHop
      hdelta hrep hx
  have hhigh : ∀ x ∈ Qᗮ,
      (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪(A + H) x, x⟫_ℂ := fun x hx =>
    le_re_inner_of_mem_boundedSelfAdjointSpectralSubspace_Iic_orthogonal (A + H)
      hAHop hdelta hrep hx
  have hQperpperp : (Qᗮ)ᗮ = Q := Submodule.orthogonal_orthogonal Q
  -- The strict quarter-angle branch, via the complementary pair.
  have hquarterPerp : IsQuarterAcute Pᗮ Qᗮ := by
    refine isQuarterAcute_of_orderedFormGap A H Pᗮ Qᗮ hA hH hAPperp
      ?_ (by linarith) hPhigh ?_ ?_ ?_ ?_ ?_
    · intro x hx
      exact hQreduces.2 x hx
    · intro x hx
      rw [hPperpperp] at hx
      exact hPlow x hx
    · exact hhigh
    · intro x hx
      rw [hQperpperp] at hx
      exact hlow x hx
    · intro x hx
      rw [hPperpperp]
      exact hHPperp x hx
    · intro x hx
      rw [hPperpperp] at hx
      exact hHP x hx
  have hquarter : IsQuarterAcute P Q := by
    have h : Pᗮ.projectionGap Qᗮ = P.projectionGap Q :=
      TauCeti.DavisKahan.subspaceGap_orthogonal P Q
    change P.projectionGap Q < Real.sqrt 2 / 2
    rw [← h]
    exact hquarterPerp
  refine
    { spectral_repulsion := hrep
      branch_reduces := hQreduces
      branch_form_low := hlow
      branch_form_high := hhigh
      branch_spectrum_low := spectrumIn_Iic_of_re_inner_le hQreduces.1 hlow
      branch_spectrum_high := spectrumIn_Ici_of_le_re_inner hQreduces.2 hhigh
      quarter_acute := hquarter
      maximal_angle_lt_pi_div_four :=
        (maximalAngle_lt_pi_div_four_iff P Q).2 hquarter }

end Theorem81

/-! ### The closed quarter-angle cone -/

omit [CompleteSpace E] in
/-- A pair within the *closed* quarter turn puts every vector of the second
subspace inside the closed quarter-angle cone around the first. -/
theorem sqrt_two_div_two_mul_norm_le_norm_starProjection
    {P M : Submodule ℂ E} [P.HasOrthogonalProjection] [M.HasOrthogonalProjection]
    (hgap : P.projectionGap M ≤ Real.sqrt 2 / 2) {y : E} (hy : y ∈ M) :
    Real.sqrt 2 / 2 * ‖y‖ ≤ ‖P.starProjection y‖ := by
  have hMy : M.starProjection y = y := Submodule.starProjection_eq_self_iff.mpr hy
  have heq : Pᗮ.starProjection y = (M.starProjection - P.starProjection) y := by
    rw [Submodule.starProjection_orthogonal_apply]
    simp only [sub_apply, hMy]
  have hbound : ‖Pᗮ.starProjection y‖ ≤ Real.sqrt 2 / 2 * ‖y‖ := by
    rw [heq]
    calc ‖(M.starProjection - P.starProjection) y‖
        ≤ ‖M.starProjection - P.starProjection‖ * ‖y‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = P.projectionGap M * ‖y‖ := by
          rw [show ‖M.starProjection - P.starProjection‖ =
            ‖P.starProjection - M.starProjection‖ from norm_sub_rev _ _]
          rfl
      _ ≤ Real.sqrt 2 / 2 * ‖y‖ :=
          mul_le_mul_of_nonneg_right hgap (norm_nonneg y)
  have hpyth : ‖y‖ ^ 2 = ‖P.starProjection y‖ ^ 2 + ‖Pᗮ.starProjection y‖ ^ 2 :=
    Submodule.norm_sq_eq_add_norm_sq_starProjection y P
  have hsq : (Real.sqrt 2 / 2) ^ 2 = (1 : ℝ) / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  nlinarith [norm_nonneg (P.starProjection y), norm_nonneg (Pᗮ.starProjection y),
    norm_nonneg y, hbound, hpyth, hsq, Real.sqrt_nonneg 2]

omit [CompleteSpace E] in
/-- A pair strictly inside the quarter turn puts every nonzero vector of the
complement of the second subspace strictly outside the cone. -/
theorem norm_starProjection_lt_of_mem_orthogonal
    {P Q : Submodule ℂ E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hq : IsQuarterAcute P Q) {y : E} (hy : y ∈ Qᗮ) (hy0 : y ≠ 0) :
    ‖P.starProjection y‖ < Real.sqrt 2 / 2 * ‖y‖ := by
  have hQy : Q.starProjection y = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff Q).mpr hy
  have heq : P.starProjection y = (P.starProjection - Q.starProjection) y := by
    simp only [sub_apply, hQy, sub_zero]
  rw [heq]
  calc ‖(P.starProjection - Q.starProjection) y‖
      ≤ P.projectionGap Q * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
    _ < Real.sqrt 2 / 2 * ‖y‖ :=
        mul_lt_mul_of_pos_right hq (norm_pos_iff.mpr hy0)

/-! ### Uniqueness of the branch -/

section Uniqueness

variable (A H : E →L[ℂ] E) (P : Submodule ℂ E) [P.HasOrthogonalProjection]
variable {alpha delta : ℝ}

/-- **Theorem 8.1, uniqueness half.**  A reducing subspace of the perturbed
operator satisfying the printed *closed* quarter-angle condition is the
canonical branch.  Nothing beyond the printed hypotheses is assumed. -/
theorem theorem8_1_eq_canonicalBranch_of_maximalAngle_le
    (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hHP : ∀ x ∈ P, H x ∈ Pᗮ)
    (hHPperp : ∀ x ∈ Pᗮ, H x ∈ P)
    (M : Submodule ℂ E) [M.HasOrthogonalProjection]
    (hMreduces : ContinuousLinearMap.Reduces (A + H) M)
    (hMangle : maximalAngle P M ≤ Real.pi / 4) :
    M = canonicalLowBranch (A + H)
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hH)) alpha := by
  classical
  have hAH : IsSelfAdjoint (A + H) := hA.add hH
  have hAHop : (A + H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hAH
  have hconc := theorem8_1_canonicalBranch A H P hdelta hA hH hAP hPlow hPhigh hHP hHPperp
  set Q : Submodule ℂ E := canonicalLowBranch (A + H) hAHop alpha with hQdef
  have hquarter : IsQuarterAcute P Q := hconc.quarter_acute
  have hquarterPerp : IsQuarterAcute Pᗮ Qᗮ := by
    change Pᗮ.projectionGap Qᗮ < Real.sqrt 2 / 2
    rw [TauCeti.DavisKahan.subspaceGap_orthogonal P Q]
    exact hquarter
  have hgapM : P.projectionGap M ≤ Real.sqrt 2 / 2 :=
    (maximalAngle_le_pi_div_four_iff P M).1 hMangle
  have hgapMperp : Pᗮ.projectionGap Mᗮ ≤ Real.sqrt 2 / 2 := by
    rw [TauCeti.DavisKahan.subspaceGap_orthogonal P M]
    exact hgapM
  -- the branch projection
  set F : E →L[ℂ] E :=
    boundedSelfAdjointSpectralProjection (A + H) hAHop (Set.Iic alpha)
      measurableSet_Iic with hFdef
  have hFstar : F = Q.starProjection :=
    boundedSelfAdjointSpectralProjection_eq_starProjection (A + H) hAHop
      (Set.Iic alpha) measurableSet_Iic
  -- a reducing projection commutes with the branch projection
  have hcommT : Commute (A + H) M.starProjection := by
    change (A + H) * M.starProjection = M.starProjection * (A + H)
    refine ContinuousLinearMap.ext fun x => ?_
    exact (ContinuousLinearMap.starProjection_apply_comm_of_reduces
      (A + H) M hMreduces x).symm
  have hcommF : Commute F M.starProjection := by
    rw [hFdef, boundedSelfAdjointSpectralProjection_Iic_eq_cfcHom (A + H) hAHop
      hdelta hconc.spectral_repulsion]
    exact IsSelfAdjoint.commute_cfcHom hAH.isStarNormal hAH hcommT _
  have hcommApply : ∀ x : E, F (M.starProjection x) = M.starProjection (F x) := by
    intro x
    exact congrArg (fun T : E →L[ℂ] E => T x) hcommF
  refine le_antisymm ?_ ?_
  · -- `M ≤ Q`
    intro y hy
    have hMy : M.starProjection y = y := Submodule.starProjection_eq_self_iff.mpr hy
    set u : E := Qᗮ.starProjection y with hudef
    have huQperp : u ∈ Qᗮ := Qᗮ.starProjection_apply_mem y
    have huM : u ∈ M := by
      have hu : u = y - F y := by
        rw [hudef, hFstar, Submodule.starProjection_orthogonal_apply]
      have : M.starProjection u = u := by
        rw [hu, map_sub, hMy, ← hcommApply y, hMy]
      exact this ▸ M.starProjection_apply_mem u
    have hu0 : u = 0 := by
      by_contra hne
      have h1 := sqrt_two_div_two_mul_norm_le_norm_starProjection hgapM huM
      have h2 := norm_starProjection_lt_of_mem_orthogonal hquarter huQperp hne
      linarith
    have hy' : y = Q.starProjection y := by
      rw [hudef, Submodule.starProjection_orthogonal_apply] at hu0
      exact sub_eq_zero.mp hu0
    exact hy' ▸ Q.starProjection_apply_mem y
  · -- `Q ≤ M`
    intro w hw
    have hFw : F w = w := by
      rw [hFstar]
      exact Submodule.starProjection_eq_self_iff.mpr hw
    set v : E := Mᗮ.starProjection w with hvdef
    have hvMperp : v ∈ Mᗮ := Mᗮ.starProjection_apply_mem w
    have hvQ : v ∈ Q := by
      have hv : v = w - M.starProjection w := by
        rw [hvdef, Submodule.starProjection_orthogonal_apply]
      have hFv : F v = v := by
        rw [hv, map_sub, hFw, hcommApply w, hFw]
      rw [hFstar] at hFv
      exact hFv ▸ Q.starProjection_apply_mem v
    have hv0 : v = 0 := by
      by_contra hne
      have h1 := sqrt_two_div_two_mul_norm_le_norm_starProjection hgapMperp hvMperp
      have h2 := norm_starProjection_lt_of_mem_orthogonal hquarterPerp
        (by rw [Submodule.orthogonal_orthogonal]; exact hvQ) hne
      linarith
    have hw' : w = M.starProjection w := by
      rw [hvdef, Submodule.starProjection_orthogonal_apply] at hv0
      exact sub_eq_zero.mp hv0
    exact hw' ▸ M.starProjection_apply_mem w

/-- **Theorem 8.1, the printed characterization.**  For a reducing subspace of
the perturbed operator, the closed quarter-angle condition and the spectral
orientation `Lambda 0 <= alpha`, `Lambda 1 >= alpha + delta` are equivalent.

Both directions are proved from the printed hypotheses; neither is assumed. -/
theorem theorem8_1_maximalAngle_le_iff_spectrumIn
    (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hHP : ∀ x ∈ P, H x ∈ Pᗮ)
    (hHPperp : ∀ x ∈ Pᗮ, H x ∈ P)
    (M : Submodule ℂ E) [M.HasOrthogonalProjection]
    (hMreduces : ContinuousLinearMap.Reduces (A + H) M) :
    maximalAngle P M ≤ Real.pi / 4 ↔
      (SpectrumIn (A + H) M (Set.Iic alpha) ∧
        SpectrumIn (A + H) Mᗮ (Set.Ici (alpha + delta))) := by
  classical
  have hAH : IsSelfAdjoint (A + H) := hA.add hH
  have hAHsym : (A + H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hAH
  have hAHop : (A + H).IsSymmetric := hAHsym
  have hconc := theorem8_1_canonicalBranch A H P hdelta hA hH hAP hPlow hPhigh hHP hHPperp
  have hPperpperp : (Pᗮ)ᗮ = P := Submodule.orthogonal_orthogonal P
  have hAsym : A.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hAPperp : ∀ x ∈ Pᗮ, A x ∈ Pᗮ := fun x hx =>
    map_mem_orthogonal_of_forall_map_mem hAsym hAP hx
  constructor
  · intro hangle
    have hMQ : M = canonicalLowBranch (A + H) hAHop alpha :=
      theorem8_1_eq_canonicalBranch_of_maximalAngle_le A H P hdelta hA hH hAP hPlow
        hPhigh hHP hHPperp M hMreduces hangle
    subst hMQ
    exact ⟨hconc.branch_spectrum_low, hconc.branch_spectrum_high⟩
  · rintro ⟨hMlow, hMhigh⟩
    let : CompleteSpace M :=
      completeSpace_coe_iff_isComplete.mpr M.isComplete_coe_of_hasOrthogonalProjection
    let : CompleteSpace (Mᗮ : Submodule ℂ E) :=
      completeSpace_coe_iff_isComplete.mpr
        Mᗮ.isComplete_coe_of_hasOrthogonalProjection
    -- restricted spectra give the ordered form bounds
    have hformLow : ∀ x ∈ M, RCLike.re ⟪(A + H) x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2 := by
      intro x hx
      refine re_inner_le_on_subspace_of_restriction_spectrum_subset_Iic
        hAHsym hMreduces.1 ?_ hx
      rw [← realSpectrum_eq_spectrum_real]
      intro r hr
      exact hMlow.2 ⟨hMreduces.1, hr⟩
    have hformHigh : ∀ x ∈ Mᗮ,
        (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪(A + H) x, x⟫_ℂ := by
      intro x hx
      refine le_re_inner_on_subspace_of_restriction_spectrum_subset_Ici
        hAHsym hMreduces.2 ?_ hx
      rw [← realSpectrum_eq_spectrum_real]
      intro r hr
      exact hMhigh.2 ⟨hMreduces.2, hr⟩
    have hMperpperp : (Mᗮ)ᗮ = M := Submodule.orthogonal_orthogonal M
    have hquarterPerp : IsQuarterAcute Pᗮ Mᗮ := by
      refine isQuarterAcute_of_orderedFormGap A H Pᗮ Mᗮ hA hH hAPperp
        ?_ (by linarith) hPhigh ?_ hformHigh ?_ ?_ ?_
      · intro x hx
        exact hMreduces.2 x hx
      · intro x hx
        rw [hPperpperp] at hx
        exact hPlow x hx
      · intro x hx
        rw [hMperpperp] at hx
        exact hformLow x hx
      · intro x hx
        rw [hPperpperp]
        exact hHPperp x hx
      · intro x hx
        rw [hPperpperp] at hx
        exact hHP x hx
    have hquarter : IsQuarterAcute P M := by
      change P.projectionGap M < Real.sqrt 2 / 2
      rw [← TauCeti.DavisKahan.subspaceGap_orthogonal P M]
      exact hquarterPerp
    exact le_of_lt ((maximalAngle_lt_pi_div_four_iff P M).2 hquarter)

end Uniqueness


end

/-! ### Paper-facing names

Theorem 8.1 states three things, and the printed section refers to them
separately, so each has its own source-numbered name. -/

/-- **Davis--Kahan 1970, Theorem 8.1: existence of the canonical branch.**
Takes only the printed hypotheses. -/
alias theorem8_1 := theorem8_1_canonicalBranch

/-- **Davis--Kahan 1970, Theorem 8.1: the printed characterization.** -/
alias theorem8_1_characterization := theorem8_1_maximalAngle_le_iff_spectrumIn

/-- **Davis--Kahan 1970, Theorem 8.1: uniqueness of the branch.** -/
alias theorem8_1_uniqueness := theorem8_1_eq_canonicalBranch_of_maximalAngle_le


end Section8
end DavisKahan1970
end TauCeti
