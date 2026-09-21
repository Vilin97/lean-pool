/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliScaleZeroBridge

/-! # Coarse Caccioppoli Scale Zero -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Scale-zero coarse Caccioppoli inequality

This file contains the full scale-zero proof and theorem packages used by the
arbitrary-scale public Caccioppoli interface.

## Audit tag

Claim: assemble the single note-facing scale-zero Caccioppoli package from the
scalar envelope, with all `s,t` dependence displayed in the public RHS.

Downstream target: `coarseCaccioppoliScaleZeroTheory`, consumed by the
arbitrary-scale Caccioppoli interface.  No additional public `*Theory` surface
belongs in this file.
-/

noncomputable section

open scoped ENNReal

/-- Note-facing scale-zero Caccioppoli package.  This is the full public
statement with `m = 0`: the constant is dimension-only, while all `s,t`
dependence is displayed in `boundaryCaccioppoliRHS` and
`interiorCaccioppoliRHS`. -/
structure CoarseCaccioppoliScaleZeroTheory (d : ℕ) [NeZero d] : Prop where
  exists_constant :
    ∃ C : ℝ, 0 < C ∧
      (∀ {Q : TriadicCube d} {a : CoeffFamily d} {s t : ℝ} {x : Vec d}
        (u : BoundaryCaccioppoliDatum Q a x),
        0 < s → 0 < t → s + t < 1 → x ∈ openCubeSet Q → Q.scale = 0 →
          boundaryCaccioppoliCoreEnergy u ≤
            boundaryCaccioppoliRHS C s t u) ∧
      (∀ {Q : TriadicCube d} {a : CoeffFamily d} {s t : ℝ}
        (u : CubeSolution Q a),
        0 < s → 0 < t → s + t < 1 → Q.scale = 0 →
          interiorCaccioppoliCoreEnergy Q a (cubeCenter Q) u ≤
            interiorCaccioppoliRHS C Q a s t u)

/-- Once the one-dimensional scalar envelope is proved, the full note-facing
scale-zero Caccioppoli package follows with no further analytic assumptions. -/
private theorem coarseCaccioppoliScaleZeroTheory_of_scalarEnvelope
    {d : ℕ} [NeZero d]
    (hscalar : CoarseCaccioppoliScaleZeroScalarEnvelope d) :
    CoarseCaccioppoliScaleZeroTheory d := by
  rcases hscalar.exists_constant with ⟨C, hCpos, hboundary, hinterior⟩
  let D : ℝ := (d : ℝ) ^ (2 : ℕ)
  have hd_nat : 1 ≤ d := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne d))
  have hd_one : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_nat
  have hd_pos : 0 < (d : ℝ) := lt_of_lt_of_le zero_lt_one hd_one
  have hD_pos : 0 < D := by
    dsimp [D]
    exact pow_pos hd_pos 2
  have hD_nonneg : 0 ≤ D := hD_pos.le
  refine ⟨⟨D * C, mul_pos hD_pos hCpos, ?_, ?_⟩⟩
  · intro Q a s t x u hs ht hst hx hQscale
    refine
      boundary_publicCoreEnergy_le_publicRHS_of_scale_zero_of_unitStandardExplicitBoundSplit
        (Q := Q) (a := a) (x := x) u hs ht hst hx hQscale ?_
    have hbase := hboundary hs ht hst
    have hmul : D * boundaryCaccioppoliScaleZeroExplicitConstant d s t ≤ D * C :=
      mul_le_mul_of_nonneg_left hbase hD_nonneg
    simpa [D, boundaryCaccioppoliScaleZeroExplicitConstant,
      mul_assoc, mul_left_comm, mul_comm] using hmul
  · intro Q a s t u hs ht hst hQscale
    refine
      interior_centered_publicCoreEnergy_le_publicRHS_of_scale_zero_of_unitStandardExplicitBoundSplit
        (Q := Q) (a := a) u hs ht hst hQscale ?_
    have hbase := hinterior hs ht hst
    have hmul : D * interiorCaccioppoliScaleZeroExplicitConstant d s t ≤ D * C :=
      mul_le_mul_of_nonneg_left hbase hD_nonneg
    simpa [D, interiorCaccioppoliScaleZeroExplicitConstant,
      mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Fully proved note-facing scale-zero Caccioppoli package (`m = 0`). -/
theorem coarseCaccioppoliScaleZeroTheory
    (d : ℕ) [NeZero d] :
    CoarseCaccioppoliScaleZeroTheory d :=
  coarseCaccioppoliScaleZeroTheory_of_scalarEnvelope
    (coarseCaccioppoliScaleZeroScalarEnvelope d)


end

end Ch03
end Book
end Homogenization
