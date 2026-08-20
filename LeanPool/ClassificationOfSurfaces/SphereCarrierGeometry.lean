/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.RepresentativeCarrier

/-!
# Disk geometry for the sphere carrier

The faithful sphere presentation glues two monogons with opposite boundary directions. This file
records the elementary disk geometry needed to map those two cells to opposite hemispheres:
complex conjugation is a self-homeomorphism of every indexed polygon cell, and on a monogon it
turns the reversed boundary parameter back into the forward parameter.

The indexed cells are also compact. The instance is transported through the existing
homeomorphism with the closed unit disk, keeping this fact tied to the actual polygon carrier.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

open Complex
open scoped ComplexConjugate

namespace PolygonCell

/-- Complex conjugation as a self-homeomorphism of an indexed polygon cell. -/
noncomputable def conjHomeomorph (n : ℕ) : PolygonCell n ≃ₜ PolygonCell n where
  toFun z := ⟨conj z.val, by
    simpa only [Metric.mem_closedBall, Complex.dist_eq, sub_zero, Complex.norm_conj]
      using z.property⟩
  invFun z := ⟨conj z.val, by
    simpa only [Metric.mem_closedBall, Complex.dist_eq, sub_zero, Complex.norm_conj]
      using z.property⟩
  left_inv z := by
    apply PolygonCell.ext
    exact Complex.conj_conj z.val
  right_inv z := by
    apply PolygonCell.ext
    exact Complex.conj_conj z.val
  continuous_toFun :=
    continuous_induced_rng.2 (Complex.continuous_conj.comp PolygonCell.continuous_val)
  continuous_invFun :=
    continuous_induced_rng.2 (Complex.continuous_conj.comp PolygonCell.continuous_val)

@[simp]
theorem conjHomeomorph_apply (n : ℕ) (z : PolygonCell n) :
    (conjHomeomorph n z).val = conj z.val :=
  rfl

/-- On a monogon, conjugation changes the reversed boundary parameter into the forward one. -/
theorem conj_side_symm_monogon (t : unitInterval) :
    conj ((side (0 : Fin 1) (unitInterval.symm t) : PolygonCell 1).val) =
      (side (0 : Fin 1) t : PolygonCell 1).val := by
  change conj (Circle.exp (sideAngle (0 : Fin 1) (unitInterval.symm t)) : ℂ) =
    (Circle.exp (sideAngle (0 : Fin 1) t) : ℂ)
  rw [← Circle.coe_inv_eq_conj, ← Circle.exp_neg]
  apply congrArg (fun z : Circle ↦ (z : ℂ))
  apply Circle.exp_eq_exp.mpr
  refine ⟨-1, ?_⟩
  simp only [sideAngle, Fin.val_zero, Nat.cast_one, div_one, Int.cast_neg, Int.cast_one,
    neg_mul, one_mul, unitInterval.coe_symm_eq]
  ring

/-- Every indexed polygon cell is compact through its identification with the closed unit disk. -/
noncomputable instance (n : ℕ) : CompactSpace (PolygonCell n) :=
  (closedUnitDiscHomeomorph n).symm.compactSpace

end PolygonCell

end ClassificationOfSurfaces
end Topology
end LeanEval
