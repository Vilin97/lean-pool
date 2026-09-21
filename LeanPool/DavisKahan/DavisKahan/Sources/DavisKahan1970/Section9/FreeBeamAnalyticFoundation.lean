/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamCharacteristic
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Analytic foundation boundary for the Section 9 free beam

Mathlib currently has Bessel-potential Sobolev spaces on the full Euclidean
space, but the Section 9 example needs a one-dimensional interval realization
with endpoint traces through order three.  This file makes that missing layer
explicit without hiding it inside an unconstrained numerical certificate.

The structure below records the exact pieces that an interval Sobolev campaign
must construct:

* the maximal fourth-derivative domain;
* four continuous endpoint traces;
* the free-boundary subdomain;
* a closed fourth-derivative graph;
* Green symmetry and self-adjointness;
* compact graph embedding;
* identification of the affine kernel;
* identification of the first positive spectral value with the first positive
  root of the free-beam characteristic equation.

All downstream Section 9 facts are then short consequences of this data.  The
point of the interface is to prevent the differential-operator campaign from
being compressed into unrelated scalar fields.
-/

open scoped InnerProductSpace
open Set

namespace TauCeti
namespace DavisKahan
namespace FreeBeam

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Ambient kernel of a closed operator, represented inside the Hilbert space
rather than inside its bundled domain. -/
noncomputable def partialMapKernel
    (A : H →ₗ.[ℂ] H) : Submodule ℂ H :=
  (LinearMap.ker A.toFun).map A.domain.subtype

/-- Exact interval-Sobolev and spectral data required to realize the free-end
fourth derivative.  Every field has a direct analytic interpretation and can
be attacked independently. -/
structure SobolevTraceFoundation where
  /-- Maximal interval domain carrying four weak derivatives. -/
  maximalDomain : Submodule ℂ H
  /-- Free-end operator domain. -/
  freeDomain : Submodule ℂ H
  /-- The free domain lies in the maximal fourth-derivative domain. -/
  free_le_maximal : freeDomain ≤ maximalDomain
  /-- Fourth weak derivative on the maximal domain. -/
  maximalFourth : maximalDomain →ₗ[ℂ] H
  /-- Fourth derivative restricted to the free domain. -/
  freeFourth : freeDomain →ₗ[ℂ] H
  freeFourth_agrees : ∀ x : freeDomain,
    freeFourth x = maximalFourth ⟨x, free_le_maximal x.property⟩
  /-- Endpoint traces of the second and third weak derivatives. -/
  traceSecondLeft : maximalDomain →ₗ[ℂ] ℂ
  /-- The left endpoint trace of the third weak derivative. -/
  traceThirdLeft : maximalDomain →ₗ[ℂ] ℂ
  /-- The right endpoint trace of the second weak derivative. -/
  traceSecondRight : maximalDomain →ₗ[ℂ] ℂ
  /-- The right endpoint trace of the third weak derivative. -/
  traceThirdRight : maximalDomain →ₗ[ℂ] ℂ
  /-- The free domain is exactly the joint kernel of the four endpoint traces. -/
  mem_freeDomain_iff : ∀ x : maximalDomain,
    (x : H) ∈ freeDomain ↔
      traceSecondLeft x = 0 ∧ traceThirdLeft x = 0 ∧
      traceSecondRight x = 0 ∧ traceThirdRight x = 0
  /-- Density of the free-boundary domain in `L2(0,1)`. -/
  dense_freeDomain : Dense (freeDomain : Set H)
  /-- Closedness of the fourth-derivative graph on the free domain. -/
  closed_freeGraph :
    IsClosed (Set.range fun x : freeDomain => ((x : H), freeFourth x))
  /-- Green identity after the free boundary terms vanish. -/
  green_identity : ∀ x y : freeDomain,
    ⟪freeFourth x, (y : H)⟫_ℂ = ⟪(x : H), freeFourth y⟫_ℂ
  /-- Genuine self-adjointness of the free realization.  A concrete
  construction should derive this from the interval trace theorem and the
  maximal-domain adjoint characterization. -/
  selfAdjoint :
    _root_.IsSelfAdjoint (LinearPMap.mk freeDomain freeFourth)
  /-- Compactness of the graph-domain embedding, stated sequentially to avoid
  assuming a pre-existing graph-norm Banach-space wrapper. -/
  graph_compact : ∀ (x : ℕ → freeDomain),
    (∃ C : ℝ, ∀ n,
      ‖(x n : H)‖ ^ 2 + ‖freeFourth (x n)‖ ^ 2 ≤ C) →
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      CauchySeq (fun n => ((x (phi n) : freeDomain) : H))
  /-- Isometric identification of the zero eigenspace with the affine modes. -/
  affineKernelEquiv :
    EuclideanSpace ℂ (Fin 2) ≃ₗᵢ[ℂ]
      partialMapKernel
        (LinearPMap.mk freeDomain freeFourth)
  /-- First positive free-beam frequency and its characteristic localization. -/
  rootLocalization : PositiveRootLocalization
  /-- First positive spectral value of the free realization.  Because the
  zero eigenspace has multiplicity two, this is the third eigenvalue in the
  indexing used in the paper. -/
  firstPositiveSpectralValue : ℝ
  firstPositiveSpectralValue_eq :
    firstPositiveSpectralValue = rootLocalization.firstPositiveRoot ^ 4
  /-- Positivity of the free fourth derivative, expressed spectrally. -/
  spectrum_nonnegative :
    TauCeti.LinearPMap.realSpectrum (LinearPMap.mk freeDomain freeFourth) ⊆ Set.Ici 0
  /-- Every nonzero spectral value is generated by a positive characteristic
  root.  This is the ODE-to-spectrum bridge. -/
  positive_spectrum_characterization : ∀ lambda : ℝ,
    lambda ∈ TauCeti.LinearPMap.realSpectrum (LinearPMap.mk freeDomain freeFourth) →
    0 < lambda →
    ∃ beta : ℝ, 0 < beta ∧ characteristic beta = 0 ∧ lambda = beta ^ 4

namespace SobolevTraceFoundation

/-- Closed free-beam fourth-derivative operator supplied by the foundation. -/
noncomputable def operator (D : SobolevTraceFoundation (H := H)) :
    H →ₗ.[ℂ] H :=
  { domain := D.freeDomain
    toFun := D.freeFourth }

/-- The realized closed operator has exactly the free domain it was
built from. -/
@[simp] theorem operator_domain (D : SobolevTraceFoundation (H := H)) :
    D.operator.domain = D.freeDomain := rfl

/-- The realized closed operator acts by the fourth-derivative map of the
foundation. -/
@[simp] theorem operator_apply
    (D : SobolevTraceFoundation (H := H)) (x : D.freeDomain) :
    D.operator x = D.freeFourth x := rfl

/-- The free realization is symmetric directly from Green's identity. -/
theorem operator_isSymmetric (D : SobolevTraceFoundation (H := H)) :
    TauCeti.LinearPMap.IsSymmetric D.operator := by
  intro x y
  exact D.green_identity x y

/-- The supplied maximal-domain argument proves genuine self-adjointness. -/
theorem operator_isSelfAdjoint (D : SobolevTraceFoundation (H := H)) :
    _root_.IsSelfAdjoint D.operator := by
  simpa [operator] using D.selfAdjoint

/-- The zero eigenspace has Hilbert dimension two. -/
theorem kernel_equiv_affine (D : SobolevTraceFoundation (H := H)) :
    Nonempty
      (EuclideanSpace ℂ (Fin 2) ≃ₗᵢ[ℂ] partialMapKernel D.operator) := by
  exact ⟨by simpa [operator] using D.affineKernelEquiv⟩

/-- The first positive spectral value, hence the paper's third eigenvalue,
exceeds `500`. -/
theorem firstPositiveSpectralValue_gt_five_hundred
    (D : SobolevTraceFoundation (H := H)) :
    500 < D.firstPositiveSpectralValue := by
  rw [D.firstPositiveSpectralValue_eq]
  exact positive_root_fourth_power_gt_five_hundred D.rootLocalization
    D.rootLocalization.firstPositiveRoot_pos
    D.rootLocalization.firstPositiveRoot_characteristic

/-- Every positive spectral value is above `500`. -/
theorem positive_spectrum_gt_five_hundred
    (D : SobolevTraceFoundation (H := H)) {lambda : ℝ}
    (hlambda : lambda ∈ TauCeti.LinearPMap.realSpectrum D.operator) (hpositive : 0 < lambda) :
    500 < lambda := by
  obtain ⟨beta, hbeta, hroot, rfl⟩ :=
    D.positive_spectrum_characterization lambda hlambda hpositive
  exact positive_root_fourth_power_gt_five_hundred D.rootLocalization
    hbeta hroot

/-- The spectral gap above the affine kernel is at least `500`. -/
theorem spectrum_subset_zero_union_Ioi_five_hundred
    (D : SobolevTraceFoundation (H := H)) :
    TauCeti.LinearPMap.realSpectrum D.operator ⊆ ({0} : Set ℝ) ∪ Set.Ioi 500 := by
  intro lambda hlambda
  by_cases hzero : lambda = 0
  · exact Or.inl hzero
  · have hnonneg : 0 ≤ lambda := by
      exact D.spectrum_nonnegative hlambda
    have hpositive : 0 < lambda := lt_of_le_of_ne hnonneg (Ne.symm hzero)
    exact Or.inr (D.positive_spectrum_gt_five_hundred hlambda hpositive)

end SobolevTraceFoundation

end
end FreeBeam
end DavisKahan
end TauCeti
