/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Interfaces.SchurPackage

/-!
# Block bounds

The two abstract consequences of the Schur interface that drive
hook confinement: an algebra morphism that does not kill the
idempotent of shape `μ` transports the full `(dim μ)²`-dimensional
block (`dim_sq_le_finrank`), and killing a shape kills every shape
containing it (`e_killed_of_contained`), by the branching
containment.  Both are stated against an arbitrary target algebra;
the skein endomorphism algebras are substituted downstream.
-/

@[expose] public section

namespace RS

universe u

namespace SchurPackage

/-- If an algebra morphism does not kill `e μ`, its target has
dimension at least `(dim μ)²`: the block of `μ` embeds. -/
theorem dim_sq_le_finrank (P : SchurPackage.{u}) (μ : YoungDiagram)
    {B : Type u} [Ring B] [Algebra ℂ B] [Module.Finite ℂ B]
    (φ : SymGroupAlgebra μ.card →ₐ[ℂ] B)
    (hne : φ (P.e μ) ≠ 0) :
    P.dim μ ^ 2 ≤ Module.finrank ℂ B := by
  rw [← P.block_rank μ]
  set I := LinearMap.range
      (LinearMap.mulLeft ℂ (charIdempotent (P.dim μ) (P.char μ)))
  have hinj : Function.Injective (φ.toLinearMap.comp I.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, hx⟩ hzero
    obtain ⟨y, rfl⟩ := hx
    have hy : φ (charIdempotent (P.dim μ) (P.char μ) * y) = 0 := by
      simpa [LinearMap.mulLeft_apply] using hzero
    have := P.block_faithful μ B φ hne y hy
    simpa [LinearMap.mulLeft_apply] using this
  exact LinearMap.finrank_le_finrank_of_injective hinj

/-- Killing a shape kills every shape containing it: if `φ`
annihilates `e lam` extended to arity `mu.card`, and `lam ≤ mu`,
then `φ` annihilates `e mu`. -/
theorem e_killed_of_contained (P : SchurPackage.{u})
    {lam mu : YoungDiagram} (hle : lam ≤ mu) (h : lam.card ≤ mu.card)
    {B : Type u} [Ring B] [Algebra ℂ B]
    (φ : SymGroupAlgebra mu.card →ₐ[ℂ] B)
    (hkill : φ (symCast h (P.e lam)) = 0) :
    φ (P.e mu) = 0 := by
  by_contra hne
  apply P.branching lam mu hle h
  have hzero :
      φ (charIdempotent (P.dim mu) (P.char mu) *
        (symCast h (charIdempotent (P.dim lam) (P.char lam)) *
          charIdempotent (P.dim mu) (P.char mu))) = 0 := by
    simp only [map_mul]
    rw [show φ (symCast h (charIdempotent (P.dim lam) (P.char lam))) = 0
        from hkill]
    simp
  have := P.block_faithful mu B φ hne _ hzero
  rw [← mul_assoc] at this
  exact this

end SchurPackage

end RS
