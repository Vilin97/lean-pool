/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanCutoffCurlBound
public import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicDerivatives
public import LeanPool.NavierStokesAndEuler.Euler.SolutionDefinitions
import LeanPool.NavierStokesAndEuler.Euler.ClassicalBridge
import LeanPool.NavierStokesAndEuler.Euler.CompactSpatialJets
import LeanPool.NavierStokesAndEuler.Euler.DivCurlRecovery
import LeanPool.NavierStokesAndEuler.Euler.MeanVectorIdentities
import LeanPool.NavierStokesAndEuler.Euler.ScalarEulerVorticity

/-! Uniform spatial derivative energies for a Comparator solution whose
vorticity stays in one compact set on a finite time interval. Ordinary joint
smoothness supplies the compact source bounds, and elliptic recovery supplies
the velocity derivative bounds. -/

@[expose] public section


noncomputable section


open Set MeasureTheory InnerProductSpace Laplacian EulerSmoothLimit EulerVectorCalculus
  EulerMeanHarmonic EulerMeanVectorIdentities EulerMeanCutoffCurl EulerComparatorRecovery
open scoped ContDiff Topology

namespace Euler.EulerExistenceAndSmoothnessR3

variable {u₀ : Space → Space} {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
  (h : EulerExistenceAndSmoothnessR3 u₀ v p)

include h

/-- The literal Laplacian of the velocity is the negative curl of its
vorticity, by solenoidality and the ordinary curl-curl identity. -/
theorem velocity_laplacian_eq_neg_curl_curl (t : ℝ) (ht : 0 ≤ t) :
    Δ (v · t) = -vectorCurl (vectorCurl (v · t)) := by
  have hi := vectorCurl_vectorCurl (v · t) (h.velocity_contDiff t ht)
  have hg : gradient (EulerSmoothLimit.divergence (v · t)) = 0 := by
    rw [show EulerSmoothLimit.divergence (v · t) = (fun _ : Space => (0 : ℝ)) from
      funext (fun x => h.div_free x t ht)]
    funext x
    exact gradient_fun_const x 0
  rw [hg, zero_sub] at hi
  rw [hi, neg_neg]

/-- Locality of curl places the Laplacian support inside the vorticity support. -/
theorem velocity_laplacian_tsupport_subset (t : ℝ) (ht : 0 ≤ t) :
    tsupport (Δ (v · t)) ⊆ tsupport (vectorCurl (v · t)) := by
  rw [h.velocity_laplacian_eq_neg_curl_curl t ht, tsupport_neg]
  exact vectorCurl_support _

/-- Every scalar component of the actual velocity Laplacian remains jointly
smooth through time zero. -/
theorem velocity_laplacian_component_joint_contDiffOn (j : Fin 3) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => Δ (v · z.1) z.2 j)
      (Ici 0 ×ˢ (univ : Set Space)) := by
  have hs : ContDiffOn ℝ ∞ (fun z : ℝ × Space => v z.2 z.1 j)
      (Ici 0 ×ˢ (univ : Set Space)) :=
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp_contDiffOn h.velocity_joint_contDiffOn
  apply (joint_scalar_laplacian_contDiffOn hs).congr
  intro z hz
  exact vector_laplacian_coordinate (v · z.1) (h.velocity_contDiff z.1 hz.1) z.2 j

/-- Common compact support of vorticity and Comparator joint smoothness
uniformly control every scalar coordinate derivative of the Laplacian. -/
theorem laplacian_component_word_energy_uniform_of_commonCompactCurl
    (T : ℝ) (K : Set Space) (hK : IsCompact K)
    (hsupport : ∀ t ∈ Icc (0 : ℝ) T, tsupport (vectorCurl (v · t)) ⊆ K)
    (j : Fin 3) (word : List (Fin 3)) :
    ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) T,
      (∫ x, wordDerivative word (fun y => Δ (v · t) y j) x ^ 2) ≤ B := by
  apply wordDerivative_energy_uniform_of_compact_support
    (fun z : ℝ × Space => Δ (v · z.1) z.2 j) T K hK
  · exact (h.velocity_laplacian_component_joint_contDiffOn j).mono
      (by intro z hz; exact ⟨hz.1.1, hz.2⟩)
  · intro t ht
    exact (tsupport_comp_subset (g := fun q : Space => q j) rfl (Δ (v · t))).trans
      ((h.velocity_laplacian_tsupport_subset t ht.1).trans (hsupport t ht))

/-- A Comparator solution with common compact vorticity support has uniform
energies for all genuine scalar coordinate derivatives of its velocity. -/
theorem component_word_energy_uniform_of_commonCompactCurl
    (T : ℝ) (K : Set Space) (hK : IsCompact K)
    (hsupport : ∀ t ∈ Icc (0 : ℝ) T, tsupport (vectorCurl (v · t)) ⊆ K)
    (j : Fin 3) (word : List (Fin 3)) :
    ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) T,
      (∫ x, wordDerivative word (fun y => v y t j) x ^ 2) ≤ B := by
  let u (t : Icc (0 : ℝ) T) : Space → Space := fun x => v x (t : ℝ)
  have hsource (a : Fin 3) (w : List (Fin 3)) : ∃ B : ℝ,
      ∀ t : Icc (0 : ℝ) T,
        (∫ x, wordDerivative w (fun y => Δ (u t) y a) x ^ 2) ≤ B := by
    obtain ⟨B, hB⟩ := h.laplacian_component_word_energy_uniform_of_commonCompactCurl
      T K hK hsupport a w
    exact ⟨B, fun t => hB t t.property⟩
  have henergy : ∃ B : ℝ, ∀ t : Icc (0 : ℝ) T, (∫ x, ‖u t x‖ ^ 2) ≤ B := by
    obtain ⟨B, hB⟩ := h.globally_bounded_energy
    exact ⟨B, fun t => (hB t t.property.1).le⟩
  obtain ⟨B, hB⟩ := component_wordDerivative_energy_uniform u
    (fun t => h.velocity_contDiff t t.property.1)
    (fun t => h.velocity_memLp t t.property.1)
    (fun t x => h.div_free x t t.property.1)
    (fun t => hK.of_isClosed_subset (isClosed_tsupport _) (hsupport t t.property))
    henergy hsource j word
  exact ⟨B, fun t ht => hB ⟨t, ht⟩⟩

end Euler.EulerExistenceAndSmoothnessR3
