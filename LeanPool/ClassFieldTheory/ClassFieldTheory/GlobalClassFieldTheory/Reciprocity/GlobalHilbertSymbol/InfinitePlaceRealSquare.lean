/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.InfinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
/-!
# Positive global units are local squares at real places

This is the arithmetic input for the positive-radicand branch of the real
infinite-place Hilbert-symbol comparison.
-/

open scoped Classical NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable (K : Type) [Field K] [NumberField K]

omit [NumberField K] in
/-- The canonical real coordinate of a global unit in a real completion is
its real infinite-place embedding. -/
theorem realInfinitePlace_globalUnit_realCoordinate
    (v : InfinitePlace K) (hv : v.IsReal) (b : Kˣ) :
    InfinitePlace.Completion.ringEquivRealOfIsReal hv
        (Units.map (algebraMap K v.Completion).toMonoidHom b :
          v.Completionˣ) =
      InfinitePlace.embedding_of_isReal hv (b : K) := by
  change
    InfinitePlace.Completion.ringEquivRealOfIsReal hv
        (algebraMap K v.Completion (b : K)) =
      InfinitePlace.embedding_of_isReal hv (b : K)
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
  rw [InfinitePlace.Completion.algebraMap_apply]
  rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
  simp only [WithAbs.equiv_apply]

omit [NumberField K] in
/-- A global unit whose image at a real infinite place is positive becomes a
square in the unit group of the completion. -/
theorem realInfinitePlace_globalUnit_mem_squareSubgroup_of_pos
    (v : InfinitePlace K) (hv : v.IsReal) (b : Kˣ)
    (hb : 0 < InfinitePlace.embedding_of_isReal hv (b : K)) :
    Units.map (algebraMap K v.Completion).toMonoidHom b ∈
      (powMonoidHom 2 : v.Completionˣ →* v.Completionˣ).range := by
  let e : v.Completion ≃+* ℝ :=
    InfinitePlace.Completion.ringEquivRealOfIsReal hv
  let eU : v.Completionˣ ≃* ℝˣ :=
    Units.mapEquiv e.toMulEquiv
  let b_v : v.Completionˣ :=
    Units.map (algebraMap K v.Completion).toMonoidHom b
  have hcoord :
      (eU b_v : ℝ) = InfinitePlace.embedding_of_isReal hv (b : K) := by
    exact realInfinitePlace_globalUnit_realCoordinate K v hv b
  have hpos : 0 < (eU b_v : ℝ) := by
    rw [hcoord]
    exact hb
  let t : ℝˣ :=
    Units.mk0 (Real.sqrt (eU b_v : ℝ))
      (ne_of_gt (Real.sqrt_pos.2 hpos))
  let y : v.Completionˣ := eU.symm t
  refine ⟨y, ?_⟩
  rw [powMonoidHom_apply]
  apply eU.injective
  calc
    eU (y ^ 2) = (eU y) ^ 2 := map_pow eU y 2
    _ = t ^ 2 := by rw [eU.apply_symm_apply]
    _ = eU b_v := by
      apply Units.ext
      change Real.sqrt (eU b_v : ℝ) ^ 2 = (eU b_v : ℝ)
      exact Real.sq_sqrt hpos.le

end Reciprocity
end GlobalClassFieldTheory
