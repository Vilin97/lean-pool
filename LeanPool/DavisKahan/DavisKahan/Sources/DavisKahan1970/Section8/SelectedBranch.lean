/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module


public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.WitnessGraph
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.Riccati.ContinuationWitnessOrientedBlocks

/-! # Selected Branch -/

@[expose] public section

open TauCeti.DavisKahan.Angle


/-!
# Davis--Kahan 1970, Section 8: the continuation-selected branch

The double-angle estimates alone do not identify which side of the
quarter-turn pole contains the intended perturbed spectral subspace.  This
module exposes the admission-free part of the Section 8 argument already
available in the continuation stack:

* the endpoint is a canonical spectral subspace of `A + V`;
* it reduces the perturbed operator;
* it is unitarily transported from the source selected spectral subspace;
* a quantitative common-contour bound places it strictly below `pi / 4`;
* oriented half-line placement excludes the open gap from the full spectrum.

Constructing the common separating contour from the exact hypotheses of
Theorems 8.1 and 8.2 remains a separate bridge.  The operator-order,
ordered-eigenvalue, and symmetric-gauge refinements in Theorem 8.1 are also not
asserted here.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open Set
open scoped InnerProductSpace
open DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.Foundation

universe v

section SelectedBranch

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {A V : H →L[ℂ] H} {s : Set ℝ}

/-- The core continuation-selected branch conclusions used by Section 8. -/
structure SelectedBranchConclusion
    (C : SpectralContinuationWitness A V s) : Prop where
  /-- The endpoint selected spectral subspace reduces `A + V`. -/
  target_reduces : ContinuousLinearMap.Reduces (A + V) C.targetSelectedSpectralSubspace
  /-- The source and target selected spectral subspaces are connected by a
  unitary intertwining their orthogonal projections. -/
  unitary_transport : ∃ W : H →L[ℂ] H,
    TauCeti.LinearPMap.IsUnitaryOperator W ∧
      W ∘L C.sourceSelectedSpectralSubspace.starProjection =
        C.targetSelectedSpectralSubspace.starProjection ∘L W
  /-- The selected endpoint is on the strict quarter-acute branch. -/
  quarter_acute : IsQuarterAcute C.sourceSelectedSpectralSubspace
    C.targetSelectedSpectralSubspace
  /-- Equivalent scalar form of the strict branch conclusion. -/
  maximal_angle_lt_pi_div_four :
    maximalAngle C.sourceSelectedSpectralSubspace
      C.targetSelectedSpectralSubspace < Real.pi / 4

/-- A quantitative continuation witness selects a branch whose maximal angle
is strictly below `pi / 4`. -/
theorem maximalAngle_selectedSpectralSubspaces_lt_pi_div_four
    (C : SpectralContinuationWitness A V s)
    (hsmall : selectedBranchProjectionLipschitzConstant
      C.contour V C.margin < Real.sqrt 2 / 2) :
    maximalAngle C.sourceSelectedSpectralSubspace
      C.targetSelectedSpectralSubspace < Real.pi / 4 := by
  let X : H →L[ℂ] H := C.selectedEndpointAngularOperator hsmall
  have hX : IsAngularOperator C.sourceSelectedSpectralSubspace X := by
    simpa only [X] using C.selectedEndpointAngularOperator_isAngularOperator hsmall
  have hnorm : ‖X‖ < 1 := by
    simpa only [X] using C.norm_selectedEndpointAngularOperator_lt_one hsmall
  have hangle :=
    (norm_angularOperator_lt_one_iff C.sourceSelectedSpectralSubspace X hX).1 hnorm
  simpa only [X, C.graphSubspace_selectedEndpointAngularOperator hsmall] using hangle

/-- Assemble the admission-free branch-selection conclusions from one
quantitatively small continuation witness. -/
theorem selectedBranchConclusion_of_contour_bound
    (C : SpectralContinuationWitness A V s)
    (hsmall : selectedBranchProjectionLipschitzConstant
      C.contour V C.margin < Real.sqrt 2 / 2) :
    SelectedBranchConclusion C := by
  refine
    { target_reduces := C.targetSelectedSpectralSubspace_reduces
      unitary_transport := C.exists_unitary_transport_selectedSpectralSubspaces
      quarter_acute := C.selectedSpectralSubspaces_isQuarterAcute_of_contour_bound hsmall
      maximal_angle_lt_pi_div_four := ?_ }
  exact maximalAngle_selectedSpectralSubspaces_lt_pi_div_four C hsmall

/-- Oriented placement of the continuation-selected branch gives the genuine
spectral-repulsion conclusions currently proved in the infinite-dimensional
bounded development. -/
structure OrientedSpectralRepulsionConclusion
    (C : SpectralContinuationWitness A V s) (a b d : ℝ) : Prop where
  /-- The selected branch lies on the lower side. -/
  selected_below : SpectrumIn (A + V) C.targetSelectedSpectralSubspace
    (Set.Iic a)
  /-- Its orthogonal complement lies on the upper side. -/
  complement_above : SpectrumIn (A + V) C.targetSelectedSpectralSubspaceᗮ
    (Set.Ici b)
  /-- The declared half-lines have separation at least `d`. -/
  ordered_gap : a + d ≤ b
  /-- No point of the full perturbed spectrum lies in `(a,b)`. -/
  full_spectrum_exterior :
    realSpectrum (A + V) ⊆ Set.Iic a ∪ Set.Ici b
  /-- The actual selected and complementary restricted spectra are separated
  pointwise by at least `d`. -/
  selected_spectra_separated :
    SpectraSeparated (A + V) C.targetSelectedSpectralSubspace
      (A + V) C.targetSelectedSpectralSubspaceᗮ d

/-- Package the exact spectral exclusion and restricted-spectrum separation
already available from oriented branch placement. -/
theorem orientedSpectralRepulsionConclusion
    (C : SpectralContinuationWitness A V s) {a b d : ℝ}
    (hgap : a + d ≤ b)
    (h0 : SpectrumIn (A + V) C.targetSelectedSpectralSubspace (Set.Iic a))
    (h1 : SpectrumIn (A + V) C.targetSelectedSpectralSubspaceᗮ (Set.Ici b)) :
    OrientedSpectralRepulsionConclusion C a b d := by
  refine
    { selected_below := h0
      complement_above := h1
      ordered_gap := hgap
      full_spectrum_exterior := ?_
      selected_spectra_separated := ?_ }
  · exact C.realSpectrum_add_subset_exterior_of_target_branch h0 h1
  · exact C.targetSelectedSpectraSeparated_of_halfLines hgap h0 h1

/-- The strongest Section 8.1 core currently assembled without the unresolved
operator-order and finite symmetric-gauge refinements. -/
structure Theorem81CoreConclusion
    (C : SpectralContinuationWitness A V s) (a b d : ℝ) : Prop where
  branch : SelectedBranchConclusion C
  repulsion : OrientedSpectralRepulsionConclusion C a b d

/-- Assemble branch selection and genuine spectral repulsion.  The hypotheses
make explicit the two seams that a source-complete Theorem 8.1 wrapper must
supply: a sufficiently controlled continuation witness and the correct
orientation of the target spectral branches. -/
theorem theorem81CoreConclusion
    (C : SpectralContinuationWitness A V s) {a b d : ℝ}
    (hsmall : selectedBranchProjectionLipschitzConstant
      C.contour V C.margin < Real.sqrt 2 / 2)
    (hgap : a + d ≤ b)
    (h0 : SpectrumIn (A + V) C.targetSelectedSpectralSubspace (Set.Iic a))
    (h1 : SpectrumIn (A + V) C.targetSelectedSpectralSubspaceᗮ (Set.Ici b)) :
    Theorem81CoreConclusion C a b d :=
  ⟨selectedBranchConclusion_of_contour_bound C hsmall,
    orientedSpectralRepulsionConclusion C hgap h0 h1⟩

end SelectedBranch

end Section8
end DavisKahan1970
end TauCeti
