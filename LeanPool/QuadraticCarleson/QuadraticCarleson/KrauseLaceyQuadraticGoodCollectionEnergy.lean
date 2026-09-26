/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectEnergyAssembly
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyThreeShiftTreeInterface

/-!
# Direct quadratic energy on the actual good collection

This is the concrete wrapper around the abstract direct one-piece estimate.
The selected family is the good collection produced by the genuine
threshold-ten stopping construction inside one complete shifted-grid tree.
Thus laminarity, the exact dyadic length label, and the ordinary `f` average
bound are all discharged from the concrete tree and stopping interfaces.
-/

@[expose] public section

open Function MeasureTheory Set

namespace QuadraticCarleson
namespace KrauseLaceyQuadraticDirectPartition

open KrauseLaceyBadScale KrauseLaceyStoppingExtraction
open KrauseLaceyThreeShiftGrid


noncomputable
section

/-- Classical equality for intervals in the finite shifted-grid energy estimate. -/
local instance : DecidableEq RealInterval := Classical.decEq _
attribute [local instance] Classical.propDecidable

/-- The direct quadratic one-piece estimate for the actual good collection
inside a complete finite shifted-grid tree.

The energy estimate uses the exact gap hypothesis `0 ≤ k + 2 - s`.
The stopping constant is explicitly the source constant `10` multiplying
the parent `f` average. The external tail cutoff is imposed later when
these one-piece estimates are summed.
-/
theorem localizedEnergy_completeFiniteShiftGridTree_goodCollection_le
    (topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ) (q₀ : ℤ)
    (f : L0Infinity)
    {k s : ℤ} (hgap : 0 ≤ k + 2 - s)
    {I : RealInterval}
    (hI : I ∈ goodCollection
      (completeFiniteShiftGridTree topScale shift maxDepth q₀) f 0
        (finiteShiftGridInterval topScale shift 0 q₀))
    (hIk : finiteShiftGridScale topScale shift I = k) :
    localizedEnergy k I
        (smallestScaleInput
          (goodCollection
            (completeFiniteShiftGridTree topScale shift maxDepth q₀) f 0
              (finiteShiftGridInterval topScale shift 0 q₀))
          (finiteShiftGridScale topScale shift) f (k - s)) ≤
      (432 * positiveDyadicAmplitudeBound ^ 2 *
          (10 * intervalL1Average f
            (finiteShiftGridInterval topScale shift 0 q₀)) *
          (2 : ℝ) ^ (-s)) *
        ∫ x in I.centralThird,
          ‖smallestScaleInput
            (goodCollection
              (completeFiniteShiftGridTree topScale shift maxDepth q₀) f 0
                (finiteShiftGridInterval topScale shift 0 q₀))
            (finiteShiftGridScale topScale shift) f (k - s) x‖ := by
  have hroot : ∀ J ∈ completeFiniteShiftGridTree topScale shift maxDepth q₀,
      J.carrier ⊆ (finiteShiftGridInterval topScale shift 0 q₀).carrier :=
    completeFiniteShiftGridTree_subset_root topScale shift maxDepth q₀
  have htreeLam :
      Set.Pairwise
        (↑(completeFiniteShiftGridTree topScale shift maxDepth q₀) :
          Set RealInterval)
        (fun J K ↦ J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨
          Disjoint J.carrier K.carrier) :=
    completeFiniteShiftGridTree_laminar topScale shift maxDepth q₀
  have hgoodLam :
      Set.Pairwise
        (↑(goodCollection
          (completeFiniteShiftGridTree topScale shift maxDepth q₀) f 0
            (finiteShiftGridInterval topScale shift 0 q₀)) : Set RealInterval)
        (fun J K ↦ J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨
          Disjoint J.carrier K.carrier) := by
    apply htreeLam.mono
    intro J hJ
    exact (Finset.mem_filter.mp hJ).1
  have hgoodScale :
      ∀ J ∈ goodCollection
        (completeFiniteShiftGridTree topScale shift maxDepth q₀) f 0
          (finiteShiftGridInterval topScale shift 0 q₀),
        J.length = (2 : ℝ) ^ (finiteShiftGridScale topScale shift J + 2) := by
    intro J hJ
    exact completeFiniteShiftGridTree_length_eq_scale topScale shift maxDepth q₀ J
      ((Finset.mem_filter.mp hJ).1)
  have hM :
      0 ≤ 10 * intervalL1Average f
        (finiteShiftGridInterval topScale shift 0 q₀) := by
    exact mul_nonneg (by norm_num)
      (intervalL1Average_nonneg f (finiteShiftGridInterval topScale shift 0 q₀))
  have hgoodMass :
      ∀ J ∈ goodCollection
        (completeFiniteShiftGridTree topScale shift maxDepth q₀) f 0
          (finiteShiftGridInterval topScale shift 0 q₀),
        (∫ x in J.carrier, ‖f x‖) ≤
          (10 * intervalL1Average f
            (finiteShiftGridInterval topScale shift 0 q₀)) * J.length := by
    intro J hJ
    have havg := goodCollection_averages_le
      (fun K hK ↦ hroot K hK) hJ
    calc
      (∫ x in J.carrier, ‖f x‖) = intervalL1Average f J * J.length :=
        (intervalL1Average_mul_length f J).symm
      _ ≤ (10 * intervalL1Average f
          (finiteShiftGridInterval topScale shift 0 q₀)) * J.length :=
        mul_le_mul_of_nonneg_right havg.1 J.length_pos.le
  have hIscale : I.length = (2 : ℝ) ^ (k + 2) := by
    rw [← hIk]
    exact hgoodScale I hI
  exact localizedEnergy_smallestScaleInput_le hgoodLam
    (finiteShiftGridScale topScale shift) hgoodScale f hgap hM hgoodMass I hI
    hIscale


end
end KrauseLaceyQuadraticDirectPartition
end QuadraticCarleson
