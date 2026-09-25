/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.SlabPruning

/-!
# Thickness on fibres of augmented representations

Two points in the same augmented fibre agree on the old representation and
on every added direction. They therefore agree on the whole enlarged space
of fibre-constant affine functionals. A functional distinguishing them lies
outside that space, where maximality supplies thickness after slab pruning.
-/

@[expose] public section

namespace EGZ

variable {p d : ℕ} [Fact p.Prime]

/-- Affine functionals taking the same value at two specified points. -/
def affineFunctionalEqualizer (v w : FpCoord p d) :
    Submodule (ZMod p) (FpCoord p d →ᵃ[ZMod p] ZMod p) where
  carrier := {ξ | ξ v = ξ w}
  zero_mem' := rfl
  add_mem' hξ hη := congrArg₂ (· + ·) hξ hη
  smul_mem' c _ξ hξ := congrArg (c • ·) hξ

namespace DirectionChain

variable {F : ConvexFlag} (R : FpRepresentation p d F) (x : F.Node)
    {k : ℕ} {P : ℕ → (FpCoord p d →ᵃ[ZMod p] ZMod p) → Prop}
    (D : DirectionChain (R.fiberConstantSubmodule x) P k)

/-- Equality on the old fibre and every added direction implies equality on
the final span. -/
theorem eq_on_augmented_fibre {v w : FpCoord p d}
    (hv : v ∈ R.space x) (hw : w ∈ R.space x) (hmap : R.map x v = R.map x w)
    (hdir : ∀ i, i < k → D.direction i v = D.direction i w)
    {ξ : FpCoord p d →ᵃ[ZMod p] ZMod p} (hξ : ξ ∈ D.space k) : ξ v = ξ w := by
  have hle := D.space_le_of_mem (affineFunctionalEqualizer v w)
    (fun η hη ↦ hη v w hv hw hmap) hdir k le_rfl
  exact hle hξ

theorem not_mem_of_augmented_fibre_witness {v w : FpCoord p d}
    (hv : v ∈ R.space x) (hw : w ∈ R.space x) (hmap : R.map x v = R.map x w)
    (hdir : ∀ i, i < k → D.direction i v = D.direction i w)
    {ξ : FpCoord p d →ᵃ[ZMod p] ZMod p} (hξ : ξ v ≠ ξ w) : ξ ∉ D.space k :=
  fun hmem ↦ hξ (D.eq_on_augmented_fibre R x hv hw hmap hdir hmem)

variable {weight : FpCoord p d → ℕ} {t : ℕ → ℕ} {δ : ℝ}

/-- The selected weight is thick in every functional that distinguishes a
pair in an augmented fibre. This is the completeness input for the new node. -/
theorem thick_slabIntersection_of_augmented_fibre
    (D : DirectionChain (R.fiberConstantSubmodule x)
      (fun i ξ ↦ IsThinAlong weight ξ (t (i + 1)) ((3 : ℝ) ^ (i + 1) * δ)) k)
    (hδ : 0 ≤ δ)
    (hmax : ∀ ξ, ξ ∉ D.space k →
      IsThickAlong weight ξ (t (k + 1)) ((3 : ℝ) ^ (k + 1) * δ))
    {v w : FpCoord p d} (hv : v ∈ R.space x) (hw : w ∈ R.space x)
    (hmap : R.map x v = R.map x w)
    (hdir : ∀ i, i < k → D.direction i v = D.direction i w)
    {ξ : FpCoord p d →ᵃ[ZMod p] ZMod p} (hξ : ξ v ≠ ξ w) :
    IsThickAlong (restrictWeight weight (slabIntersection k D.direction t))
      ξ (t (k + 1)) δ :=
  D.thick_slabIntersection_of_maximal hδ hmax ξ
    (D.not_mem_of_augmented_fibre_witness R x hv hw hmap hdir hξ)

end DirectionChain

end EGZ
