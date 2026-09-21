/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.PartIII
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section5BanachSylvester
import LeanPool.DavisKahan.ForTauCeti.Analysis.Normed.Operator.SylvesterBoundedInverse
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.GeneralSinTheta
import LeanPool.DavisKahan.DavisKahan.Alternative.All
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.All
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.All
import LeanPool.DavisKahan.DavisKahan.Geometry.All
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.All
import LeanPool.DavisKahan.DavisKahan.Riccati.All
import LeanPool.DavisKahan.DavisKahan.SinTheta.All
import LeanPool.DavisKahan.DavisKahan.Specialized.All
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.All
import LeanPool.DavisKahan.DavisKahan.Sylvester.All
import LeanPool.DavisKahan.DavisKahan.TanTheta.All
import LeanPool.DavisKahan.DavisKahan.TanTwoTheta.All

/-! # Part IIIPresentation -/

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970 Part III, presented as one theorem package

This module gives the whole Part III package paper-facing names in one place,
so that a reader who wants the printed results, rather than the modules they
are proved in, has a single import.  The stable finite results remain
available through `PartIII`.

Every alias below is proved: each resolves to a declaration that depends on
nothing beyond the three foundational assumptions Mathlib itself uses.  Results
that are still open are named separately, in `DavisKahan.PartIII`, so that
importing this file cannot pull an unproved result into a production build.

The mathematical dependency order is recorded in
`dev/davis-kahan-1970-full-sine-theta-proof-manuscript-2026-07-19.md`.
-/

namespace TauCeti
namespace DavisKahan1970

/-! ## Canonical single-angle target

The unqualified source role belongs to the generalized unbounded theorem; the
declaration that holds it is `sinTheta_generalized_bundled_complex`.  The
bounded aliases below are specializations and implementation seams. -/

/-! ## Sylvester engine -/
alias bounded_sylvester_neumann_solution :=
  DavisKahan.Sylvester.sylvesterNeumannSolution_eq

/-! ## Single-angle theorems -/
alias sinTheta_unbounded_opNorm_complex :=
  DavisKahan.ExactSinTheta.sinTheta_unbounded_opNorm
alias unbounded_sylvester_intervalExterior_opNorm :=
  DavisKahan.Sylvester.norm_sylvester_le_of_intervalExterior
alias unbounded_sylvester_exteriorInterval_opNorm :=
  DavisKahan.Sylvester.norm_sylvester_le_of_exteriorInterval
alias sinTheta_unbounded_idealFamily_complex :=
  DavisKahan.ExactSinTheta.sinTheta_unbounded_gauge
alias sinTheta_unbounded_spectrumGap_opNorm_complex :=
  DavisKahan.sinTheta_unbounded_opNorm_of_spectrum_gap
alias unbounded_boundedPerturbation_sinTheta_spectralSubspaces :=
  DavisKahan.sinTheta_addBounded_spectralSubspaces_opNorm_of_intervalExterior
alias unbounded_boundedPerturbation_sinTheta_directedGap :=
  DavisKahan.sinTheta_addBounded_directedGap_of_intervalExterior
alias unbounded_boundedPerturbation_sinTheta_spectralProjections :=
  DavisKahan.sinTheta_addBounded_spectralProjection_sub_opNorm_of_spectrum_gap
alias unbounded_spectralRestriction_formBounds :=
  DavisKahan.selfAdjointSpectralRestriction_semibounded_of_subset_Icc
alias unbounded_spectralRestriction_spectrum_exterior :=
  DavisKahan.selfAdjointSpectralRestriction_spectrum_avoids_open_of_inter_eq_empty
alias sinTheta_unbounded_spectrumGap_idealFamily_complex :=
  DavisKahan.sinTheta_unbounded_gauge_of_spectrum_gap
alias unbounded_sylvester_exteriorInterval_uiNorm :=
  DavisKahan.Sylvester.mem_and_gauge_le_of_exteriorLeft_intervalRight
alias unbounded_sylvester_intervalExterior_uiNorm :=
  DavisKahan.Sylvester.mem_and_gauge_le_of_boundedLeft_exteriorRight
alias unbounded_boundedRealization_of_spectrum_Icc :=
  DavisKahan.ExactSinTheta.exists_boundedRealization_of_spectrum_subset_Icc
alias unbounded_semibounded_of_spectrum_Icc :=
  DavisKahan.semibounded_of_spectrum_subset_Icc
alias unbounded_sylvester_exteriorInterval_uiNorm_of_spectra :=
  DavisKahan.unbounded_sylvester_mem_and_gauge_le_of_spectra_exteriorLeft_intervalRight
alias unbounded_sylvester_intervalExterior_uiNorm_of_spectra :=
  DavisKahan.unbounded_sylvester_mem_and_gauge_le_of_spectra_intervalLeft_exteriorRight
alias real_sinTheta_symmetric_of_restriction_spectra :=
  TauCeti.SpectralOrder.opNorm_starProjection_sub_le_of_restriction_spectra
alias real_upperFormBound_of_spectrum :=
  TauCeti.SpectralOrder.upperFormBoundOn_top_of_spectrum_subset_Iic
alias bounded_sinAngleOperatorC_norm := DavisKahan.Angle.norm_sinAngleOperatorC
alias bounded_directedSinAngleOperatorC_norm :=
  DavisKahan.Angle.norm_directedSinAngleOperatorC
alias bounded_angle_pythagoras :=
  DavisKahan.Angle.directedSinAngleOperatorC_sq_add_directedCosAngleOperatorC_sq
alias bounded_angle_commute :=
  DavisKahan.Angle.commute_directedSinAngleOperatorC_directedCosAngleOperatorC
alias boundedDirectedSinTwoAngleOperatorC := DavisKahan.Angle.directedSinTwoAngleOperatorC
alias bounded_directedSinTwoAngleOperatorC_norm_le :=
  DavisKahan.Angle.norm_directedSinTwoAngleOperatorC_le
alias bounded_cosAngle_coercive :=
  DavisKahan.Angle.norm_directedCosAngleOperatorC_apply_ge
alias bounded_cosAngle_injective_of_acute :=
  DavisKahan.Angle.directedCosAngleOperatorC_eq_zero_imp_of_acute
alias bounded_cosAngleExtended_invertible :=
  DavisKahan.Angle.cosAngleExtendedC_ker_bot_range_top
alias boundedDirectedTanAngleOperatorC := DavisKahan.Angle.directedTanAngleOperatorC
alias bounded_tanAngle_defining_identity :=
  DavisKahan.Angle.directedTanAngleOperatorC_comp_cosAngleExtendedC
alias boundedCosTwoAngleOperatorC := DavisKahan.Angle.cosTwoAngleOperatorC
alias bounded_cosTwoAngle_coercive :=
  DavisKahan.Angle.norm_cosTwoAngleOperatorC_apply_ge
alias bounded_cosTwoAngleExtended_invertible :=
  DavisKahan.Angle.cosTwoAngleExtendedC_ker_bot_range_top
alias boundedDirectedTanTwoAngleOperatorC := DavisKahan.Angle.directedTanTwoAngleOperatorC
alias bounded_tanTwoAngle_defining_identity :=
  DavisKahan.Angle.directedTanTwoAngleOperatorC_comp_cosTwoAngleExtendedC
alias bounded_tanAngle_norm_le := DavisKahan.Angle.norm_directedTanAngleOperatorC_le
alias bounded_tanTheta_perVector := DavisKahanExt.tan_theta_le'
alias bounded_sinTwoAngle_norm_eq :=
  DavisKahan.Angle.norm_directedSinTwoAngleOperatorC

/-! ## Direct rotation -/
alias complexDirectRotation :=
  DavisKahan.spectraDirectRotation
alias complex_directRotation_sq :=
  DavisKahan.spectraDirectRotation_sq
alias complex_directRotation_reversal :=
  DavisKahan.spectraDirectRotation_reversal
alias complex_directRotation_unique :=
  DavisKahan.spectraDirectRotation_unique
alias complex_directRotation_minimal :=
  DavisKahan.spectraDirectRotation_minimal

/-! ### Proposition 3.3, both directions

The square identity `W² = J_V J_U` alone does not characterise `W`: a unitary
has many square roots.  Proposition 3.3 says `W` is the **principal** one, and
these four aliases carry that word.

* `complex_directRotation_hermitianPart` is the forward half — the Hermitian
  part of `W` is `2|S|`, hence positive, so `W`'s spectrum avoids the closed
  left half-plane.
* `complex_directRotation_principal_of_sq` is the converse, and in the acute
  case it is *stronger* than the printed statement: no crossed-intersection
  mapping condition is needed, because on an acute pair a nonnegative-real-part
  unitary square root of the reflection product is already forced to be `W`.

The diagonal-block aliases belong to Proposition 3.1, whose characterisation
clause is "positivity of its diagonal blocks": both compressions of `W` to `U`
and to `Uᗮ` are the positive Halmos cosine `|S|`. -/
alias complex_directRotation_hermitianPart :=
  DavisKahan.spectraDirectRotation_add_star_eq_two_smul_absoluteValue
alias complex_directRotation_principal_of_sq :=
  DavisKahan.spectraDirectRotation_unique_of_sq
alias complex_directRotation_diagonalBlock :=
  DavisKahan.projection_mul_spectraDirectRotation_mul_projection
alias complex_directRotation_complementaryDiagonalBlock :=
  DavisKahan.complementaryProjection_mul_spectraDirectRotation_mul_complementaryProjection

/-! ### Proposition 3.1, the characterisation clause

The two aliases above *compute* the diagonal blocks of the direct rotation.
Proposition 3.1 also asserts the converse — that positivity of those two blocks
**characterises** it — and that direction is strictly stronger than
`complex_directRotation_unique`, which assumes `0 ≤ re ⟪W x, x⟫` for every `x`.
Nonnegativity of the two compressions constrains the numerical range on `U` and
on `Uᗮ` separately and says nothing at all about a mixed vector.

What closes the gap is the printed hypothesis that `W` carries the pair
`(U, Uᗮ)` onto `(V, Vᗮ)`.  Combined with `W² = J_V J_U` that forces
`J_U W J_U = W*`, so the Hermitian part of `W` commutes with `J_U` and its
quadratic form splits over `U ⊕ Uᗮ` with **no cross term** — at which point two
separate sign conditions do add up.

* `complex_directRotation_reflectionConjugate` is that structural identity.
* `complex_directRotation_of_diagonalBlocks` is the characterisation direction.
* `complex_directRotation_iff_diagonalBlocks` is Proposition 3.1's
  characterisation clause as a biconditional. -/
alias complex_directRotation_reflectionConjugate :=
  DavisKahan.reflection_conjugate_eq_star_of_sq_of_intertwines
alias complex_directRotation_of_diagonalBlocks :=
  DavisKahan.spectraDirectRotation_unique_of_diagonalBlocks
alias complex_directRotation_iff_diagonalBlocks :=
  DavisKahan.eq_spectraDirectRotation_iff_diagonalBlocks_nonneg

/-! ### Proposition 3.1's third clause, from the printed hypotheses

The three aliases immediately above put equation (3.8), `W² = J_V J_U`, on the left of the
implication.  The printed clause (c) does not: it says the direct rotation "is characterized
by property (i) alone", property (i) of Definition 3.1 being `C₀ ≥ 0` and `C₁ ≥ 0`.  Since
(3.8) is derived at (3.6)--(3.7) from (i) *and* (ii), assuming it assumes part of the
conclusion.  These four names carry the printed hypotheses only — unitary, `W P_U = P_V W`,
and the two diagonal blocks positive — and derive (3.8) rather than assume it.

Property (i) is positivity of the blocks as *operators*, which over `ℂ` is the single
condition `∀ x ∈ U, 0 ≤ ⟪W x, x⟫` in the order on `ℂ` and over `ℝ` is `IsPositive` of the
compression, symmetry included.  Nonnegative *real part* is not enough once (3.8) is
dropped: `diag (i, 1)` on `ℂ²` with `U = V = ℂ ⬝ e₀`, and the plane rotation by `π/3` on
`ℝ⁴` with `U = V = span (e₀, e₁)`, are the two counterexamples. -/
alias complex_directRotation_reflectionConjugate_of_positiveDiagonalBlocks :=
  DavisKahan.reflection_conjugate_eq_star_of_intertwines_of_diagonalBlocks_pos
alias complex_directRotation_of_positiveDiagonalBlocks :=
  DavisKahan.spectraDirectRotation_unique_of_diagonalBlocks_pos
alias complex_directRotation_iff_positiveDiagonalBlocks :=
  DavisKahan.eq_spectraDirectRotation_iff_diagonalBlocks_pos
alias real_directRotation_of_positiveDiagonalBlocks :=
  DavisKahan.directRotationR_unique_of_diagonalBlocks_pos
alias real_directRotation_iff_positiveDiagonalBlocks :=
  DavisKahan.eq_directRotationR_iff_diagonalBlocks_pos

/-! ### Section 3 over a **real** Hilbert space of arbitrary dimension

Standing assumption 1 of the paper is "real or complex", and the `complex_*`
names above are all `InnerProductSpace ℂ`.  These are the same clauses over `ℝ`,
in arbitrary dimension, proved in `DavisKahan/Geometry/Polar/DirectRotationReal.lean`
by descent from the complexification: the complexified intertwiner is
conjugation-fixed, so its modulus is, so the polar factor is, so the direct
rotation of a complexified pair **is** the complexification of a bounded real
operator. -/
alias realDirectRotation := DavisKahan.directRotationR
alias real_directRotation_orthogonal :=
  DavisKahan.directRotationR_mem_unitary
alias real_directRotation_intertwines :=
  DavisKahan.directRotationR_intertwines
alias real_directRotation_maps_subspace :=
  DavisKahan.directRotationR_maps_subspace
alias real_directRotation_maps_orthogonalComplement :=
  DavisKahan.directRotationR_maps_orthogonalComplement
alias real_directRotation_sq := DavisKahan.directRotationR_sq
alias real_directRotation_hermitianPart :=
  DavisKahan.directRotationR_add_star
alias real_directRotation_diagonalBlock :=
  DavisKahan.projection_mul_directRotationR_mul_projection
alias real_directRotation_complementaryDiagonalBlock :=
  DavisKahan.complementaryProjection_mul_directRotationR_mul_complementaryProjection
alias real_directRotation_principal_of_sq :=
  DavisKahan.directRotationR_unique_of_sq
alias real_directRotation_of_diagonalBlocks :=
  DavisKahan.directRotationR_unique_of_diagonalBlocks
alias real_directRotation_iff_diagonalBlocks :=
  DavisKahan.eq_directRotationR_iff_diagonalBlocks_nonneg
alias real_directRotation_reversal :=
  DavisKahan.directRotationR_reversal

/-! ## Graph and Riccati theory -/
/-! ### Theorem 5.1 at source generality

The repository's other Sylvester lower bounds assume a Hilbert space, because
they are proved through coercivity or through the spectral theorem.  Theorem 5.1
is a **Banach**-space statement about *any compatible operator norm*, and needs
neither: `A X = C + X B` plus a left inverse gives `X = A⁻¹C + A⁻¹XB`, and one
multiplication by `ρ + δ` cancels `ρ‖X‖` from both sides.  The Neumann series
is what produces a solution; it is not what bounds one.

`banach_sylvester_lower_bound_uiNorm` carries the "any compatible operator norm"
clause literally: it is stated for an arbitrary size function subject to exactly
subadditivity and the two one-sided ideal bounds, which is also what a
symmetric-norm-ideal gauge supplies. -/
alias banach_sylvester_lower_bound :=
  TauCeti.ContinuousLinearMap.norm_le_of_sylvester_of_leftInverse
alias banach_sylvester_lower_bound_uiNorm :=
  TauCeti.ContinuousLinearMap.opNorm_le_of_sylvester_of_leftInverse
/-- Source-facing bounded Theorem 5.1 with the paper's literal two-sided inverse hypothesis. -/
alias banach_sylvester_lower_bound_exact :=
  DavisKahan1970.theorem5_1_banach_sylvester_exact
alias banach_sylvester_lower_bound_interchanged :=
  DavisKahan1970.theorem5_1_banach_sylvester_interchanged
/-- Source-facing `A`/`B` interchange remark with a literal two-sided inverse of `B`. -/
alias banach_sylvester_lower_bound_interchanged_exact :=
  DavisKahan1970.theorem5_1_banach_sylvester_interchanged_exact
alias banach_sylvester_lower_bound_unboundedA :=
  DavisKahan1970.theorem5_1_banach_sylvester_unboundedA

/-! ## Graph and Riccati theory (continued) -/
alias bounded_coercive_isUnit :=
  TauCeti.ContinuousLinearMap.isUnit_of_coercive
alias bounded_one_add_star_mul_self_isUnit :=
  TauCeti.ContinuousLinearMap.isUnit_one_add_star_mul_self
alias bounded_positive_cauchy_schwarz :=
  TauCeti.ContinuousLinearMap.norm_apply_sq_le_of_positive
alias bounded_inverse_defect_norm :=
  TauCeti.ContinuousLinearMap.norm_one_sub_inverse_one_add

/-! ## Unbounded and form theorems -/
alias unbounded_boundedPerturbation_selfAdjoint_spectra :=
  DavisKahan.addBounded_isSelfAdjoint
alias unboundedSpectralRestriction :=
  DavisKahan.selfAdjointSpectralRestriction
alias unbounded_spectralRestriction_selfAdjoint :=
  DavisKahan.selfAdjointSpectralRestriction_isSelfAdjoint
alias unbounded_sinTheta_boundedPerturbation_blockEmbeddings :=
  DavisKahan.sinTheta_addBounded_opNorm_of_spectrum_gap_isometric
alias unbounded_sinTheta_boundedPerturbation_spectralSubspaces :=
  DavisKahan.sinTheta_addBounded_spectralSubspaces_opNorm_of_spectrum_gap

/-! ## Continuation, ideal, and sharpness package -/

end DavisKahan1970
end TauCeti
