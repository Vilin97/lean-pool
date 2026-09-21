/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNonstandardLocalInterpolation
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNonstandardSourceMaximal
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyStoppingRecursion
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyThreeShiftMaximalAction

/-!
# Local assembly for the Krause--Lacey sparse argument

This module collects the verified *local* ingredients, without making a
global standard/nonstandard classification assumption.  At one stopping
node, the constructed children are `1 / 4`-sparse, the remaining collection
has the source's bounded averages, and the full localized maximal action
satisfies the exact recursive inequality.  Independently, any selected
subcollection of the nonstandard part of that good collection has the
physical-suffix `L²`, `L¹`, and interpolated pairing estimates.

The only additional input in the interpolated conclusion is the genuinely
separate local `p`-mass estimate for the test function.  It is deliberately
left visible rather than being replaced by a purported local oscillatory
estimate.  In particular, the physical cutoff has the source orientation
`ell ≥ k₀ + s` throughout.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyLocalSparseAssembly

open KrauseLaceyBadScale KrauseLaceyStoppingExtraction KrauseLaceyStoppingRecursion

attribute [local instance] Classical.propDecidable

/-- One fully concrete local stopping step together with every currently
verified estimate for its good nonstandard subcollection.  The parameter
`G` and hypothesis `hgpmass` are precisely the separate local `p`-mass
input needed by the threshold interpolation argument; no whole-good-part
analytic estimate is assumed.

The first recursive term remains the actual good-collection pairing.  Its
replacement by the desired sparse form is exactly the remaining local
oscillatory estimate in the Krause--Lacey proof. -/
theorem local_good_nonstandard_sparse_stopping_step
    {S : Finset RealInterval} {f g : ℝ → ℂ}
    (hf : Measurable f) (hfi : Integrable f) (hg : Measurable g) (hgi : Integrable g)
    (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ) (hk₀ : 3 ≤ k₀)
    (scale : RealInterval → ℤ)
    (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hparent : HasDyadicParents S I₀)
    {p a G : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (ha : 0 < a) (hG : 0 ≤ G)
    (hgp : Integrable (fun x ↦ ‖g x‖ ^ p))
    (hgpmass : ∀ I ∈ nonstandardIntervals S f I₀ k₀ s scale ∩
      goodCollection S f g I₀, (∫ x in I.carrier, ‖g x‖ ^ p) ≤ G * I.length) :
    IsSparse (1 / 4) (↑(stoppingStepFamily S f g I₀) : Set RealInterval) ∧
      (∀ I ∈ goodCollection S f g I₀,
        intervalL1Average f I ≤ 10 * intervalL1Average f I₀ ∧
          intervalL1Average g I ≤ 10 * intervalL1Average g I₀) ∧
      (∀ K ∈ stoppingChildren S f g I₀, ∀ x, x ∉ K.carrier →
        localizedTailMaximal (k₀ + s) scale (childCollection S K) f x = 0) ∧
      (∫⁻ x, localizedTailMaximal (k₀ + s) scale S f x * ‖g x‖ₑ) ≤
        (∫⁻ x, localizedTailMaximal (k₀ + s) scale
          (goodCollection S f g I₀) f x * ‖g x‖ₑ) +
          ∑ K ∈ stoppingChildren S f g I₀,
            ∫⁻ x, localizedTailMaximal (k₀ + s) scale
              (childCollection S K) f x * ‖g x‖ₑ ∧
      eLpNorm (nonstandardSourceTailMaximal S f I₀ k₀ s scale
        (nonstandardIntervals S f I₀ k₀ s scale ∩ goodCollection S f g I₀)) 2 volume ≤
        ENNReal.ofReal ((4 * (s : ℝ) + 12) *
          Real.sqrt (nonstandardSignedEnergyBudget f I₀ s) +
          Real.sqrt (badRemovedEnergyBudget f I₀ s)) ∧
      (∫⁻ x, ‖nonstandardSourceTailMaximal S f I₀ k₀ s scale
        (nonstandardIntervals S f I₀ k₀ s scale ∩ goodCollection S f g I₀) x‖ₑ * ‖g x‖ₑ) ≤
        ENNReal.ofReal (80 * positiveDyadicAmplitudeBound * intervalL1Average g I₀ *
          ∫ x, ‖f x‖) ∧
      (∫⁻ x, ‖nonstandardSourceTailMaximal S f I₀ k₀ s scale
        (nonstandardIntervals S f I₀ k₀ s scale ∩ goodCollection S f g I₀) x‖ₑ * ‖g x‖ₑ) ≤
        ENNReal.ofReal ((4 * (s : ℝ) + 12) *
          Real.sqrt (nonstandardSignedEnergyBudget f I₀ s) +
          Real.sqrt (badRemovedEnergyBudget f I₀ s)) *
          (ENNReal.ofReal (a ^ (2 - p)) *
            ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p)) ^ (1 / 2 : ℝ) +
        ENNReal.ofReal (8 * positiveDyadicAmplitudeBound *
          (a ^ (1 - p) * G) * ∫ x, ‖f x‖) := by
  let N : Finset RealInterval :=
    nonstandardIntervals S f I₀ k₀ s scale ∩ goodCollection S f g I₀
  have hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale := by
    exact Finset.inter_subset_left
  have hsource : nonstandardSourceTailMaximal S f I₀ k₀ s scale N =
      badLengthTailMaximal S f I₀ k₀ s scale N := funext
    (nonstandardSourceTailMaximal_eq_badLengthTailMaximal f I₀ k₀ s scale hlam N hN)
  obtain ⟨hsparse, hgood, hchild, hrec⟩ :=
    finite_localized_stopping_step (k₀ + s) scale S hf hg hfi hgi I₀
      hsub hscale hlam
  refine ⟨hsparse, hgood, hchild, hrec, ?_, ?_, ?_⟩
  · exact eLpNorm_nonstandardSourceTailMaximal_le hfi I₀ k₀ s hk₀ scale hlam
      hparent hsub N hN
  · change (∫⁻ x, ‖nonstandardSourceTailMaximal S f I₀ k₀ s scale N x‖ₑ * ‖g x‖ₑ) ≤ _
    rw [hsource]
    exact lintegral_nonstandard_good_pairing_le hfi hgi I₀ k₀ s scale hlam hsub
  · change (∫⁻ x, ‖nonstandardSourceTailMaximal S f I₀ k₀ s scale N x‖ₑ * ‖g x‖ₑ) ≤ _
    rw [hsource]
    exact lintegral_nonstandard_pairing_le_threshold hfi hg hgi hp hp2 ha hG hgp I₀ k₀ s
      hk₀ scale hlam hparent hsub N hN hgpmass

/-- The finite positive global tail is reduced, with no change in its
physical lower cutoff, to the three localized maximal tails that feed the
local stopping theorem above.  This reduction contains no classifier. -/
theorem exists_three_shift_localized_tail_reduction
    (f : L0Infinity) (k₀ s topScale : ℤ) (depths : Finset ℕ) (maxDepth : ℕ)
    (hdepths : ∀ depth ∈ depths, depth ≤ maxDepth) :
    ∃ E : ℕ → Finset ℤ,
      (∀ shift,
        KrauseLaceyThreeShiftGrid.finiteOneShiftMultiscaleFamily topScale depths E shift ⊆
          KrauseLaceyThreeShiftGrid.completeFiniteShiftGridForest topScale shift maxDepth
            (KrauseLaceyThreeShiftGrid.finiteOneShiftMultiscaleAddresses depths E shift)) ∧
      ∀ x,
        KrauseLaceyThreeShiftGrid.finitePositiveGlobalTailMaximal (k₀ + s)
          topScale depths f x ≤
          ∑ shift : Fin 3,
            localizedTailMaximal (k₀ + s)
              (KrauseLaceyThreeShiftGrid.finiteShiftGridScale topScale shift)
              (KrauseLaceyThreeShiftGrid.finiteOneShiftMultiscaleFamily
                topScale depths E shift) f x :=
  KrauseLaceyThreeShiftGrid.exists_threeShiftForests_globalTailMaximal f (k₀ + s)
    topScale depths maxDepth hdepths


end KrauseLaceyLocalSparseAssembly
end QuadraticCarleson
