/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

SL₃ action interfaces for the Zhou tensor carrier. Paper: §2. The file keeps
the linear action and quadratic Sp₄ correction as separate reusable layers.
-/
import LeanPool.ConnesRigidity.Construction
import LeanPool.ConnesRigidity.Foundation.LinearAlgebra.QuadraticCocycle

/-!
The paper actions component of the Connes rigidity formalization.
-/

namespace Connes
namespace Construction
namespace PaperKernel

noncomputable section

/--
The `Q` construction used in the Connes rigidity formalization.
-/
abbrev Q := OpenAIPort.ModTwoSymplecticGroup
/--
The `SymplecticIndex` construction used in the Connes rigidity formalization.
-/
abbrev SymplecticIndex := OpenAIPort.SymplecticIndex

/-- The SL₃ action on the polynomial module. Paper: §2. -/
def sl3AAction : SpecialLinear.SL3 →* (A ≃ₗ[k] A) where
  toFun l := (Matrix.SpecialLinearGroup.toLin' l).restrictScalars k
  map_one' := by
    ext a
    simp
  map_mul' l m := by
    ext a
    simp

/-- The diagonal SL₃ action on the tensor square. Paper: §2. -/
def sl3TensorAction (l : SpecialLinear.SL3) :
    TensorAA →ₗ[k] TensorAA :=
  TensorProduct.map (sl3AAction l).toLinearMap (sl3AAction l).toLinearMap

/-- The diagonal SL₃ action restricted to the fixed tensor module. Paper: §2. -/
def sl3CAction (l : SpecialLinear.SL3) : C →ₗ[k] C where
  toFun c :=
    ⟨sl3TensorAction l c, by
      have hcomm := TensorProduct.map_comm
        (sl3AAction l).toLinearMap (sl3AAction l).toLinearMap (c : TensorAA)
      have hc : (TensorProduct.comm k A A) (c : TensorAA) = c := c.property
      rw [hc] at hcomm
      change (TensorProduct.comm k A A)
          ((TensorProduct.map (sl3AAction l).toLinearMap
            (sl3AAction l).toLinearMap) (c : TensorAA)) =
        (TensorProduct.map (sl3AAction l).toLinearMap
          (sl3AAction l).toLinearMap) (c : TensorAA)
      exact hcomm.symm⟩
  map_add' c d := by
    apply Subtype.ext
    change sl3TensorAction l ((c : TensorAA) + (d : TensorAA)) =
      sl3TensorAction l c + sl3TensorAction l d
    simp only [map_add]
  map_smul' a c := by
    apply Subtype.ext
    change sl3TensorAction l (a • (c : TensorAA)) =
      a • sl3TensorAction l c
    simp only [map_smul]

/-- The natural linear action of Q on the finite module. Paper: §2. -/
def qVAction (q : Q) : PaperV ≃ₗ[k] PaperV :=
  { toFun := fun v => q • v
    invFun := fun v => q⁻¹ • v
    left_inv := by intro v; simp [smul_smul]
    right_inv := by intro v; simp [smul_smul]
    map_add' := by intro v w; exact smul_add q v w
    map_smul' := by
      intro a v
      change (q : Matrix SymplecticIndex SymplecticIndex k).mulVec (a • v) =
        a • (q : Matrix SymplecticIndex SymplecticIndex k).mulVec v
      exact Matrix.mulVec_smul _ _ _ }

/-- The Q action homomorphism on the finite module. Paper: §2. -/
def qVActionHom : Q →* (PaperV ≃ₗ[k] PaperV) where
  toFun := qVAction
  map_one' := by
    apply LinearEquiv.ext
    intro v
    simp [qVAction]
  map_mul' p q := by
    apply LinearEquiv.ext
    intro v
    change (p * q : Q) • v = p • (q • v)
    rw [mul_smul]

/-- The contragredient Q action on the finite dual. Paper: §2. -/
def qVStarActionHom : Q →* (VStar ≃ₗ[k] VStar) where
  toFun q := LinearEquiv.dualMap (qVActionHom q⁻¹)
  map_one' := by
    ext f v
    simp
  map_mul' p q := by
    ext f v
    simp [mul_inv_rev]

@[simp] theorem sl3CAction_diagonal (l : SpecialLinear.SL3) (a : A) :
    sl3CAction l (diagonal a) = diagonal (sl3AAction l a) := by
  apply Subtype.ext
  change sl3TensorAction l (a ⊗ₜ[k] a) =
    (sl3AAction l a) ⊗ₜ[k] (sl3AAction l a)
  rfl

/-- Span of square tensors in the tensor square. Paper: §2. -/
def squareSpan : Submodule k TensorAA :=
  Submodule.span k (Set.range fun a : A => a ⊗ₜ[k] a)

/-- The paper's missing spanning statement for the fixed tensor module. Paper: §2. -/
structure SquareSpanData where
  squares_span : ∀ c : C, (c : TensorAA) ∈ squareSpan

/-- The coefficientwise candidate is surjective. Paper: §2. -/
theorem delta_surjective : Function.Surjective delta := by
  intro a
  exact ⟨diagonal a, delta_diagonal a⟩

/-- The coefficientwise candidate intertwines the tensor action on squares. Paper: §2. -/
theorem deltaTensor_equivariant_on_squareSpan
    (l : SpecialLinear.SL3) {x : TensorAA} (hx : x ∈ squareSpan) :
    deltaTensor (sl3TensorAction l x) =
      sl3AAction l (deltaTensor x) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      have hdiag : deltaTensor (a ⊗ₜ[k] a) = a := by
        simpa [delta, diagonal] using delta_diagonal a
      calc
        deltaTensor (sl3TensorAction l (a ⊗ₜ[k] a)) =
            sl3AAction l a := by
          simpa [delta, diagonal, sl3TensorAction] using
            delta_diagonal (sl3AAction l a)
        _ = sl3AAction l (deltaTensor (a ⊗ₜ[k] a)) := by rw [hdiag]
  | zero => simp
  | add x y hx hy ihx ihy =>
      simp only [map_add, ihx, ihy, (sl3AAction l).map_add]
  | smul c x hx ih =>
      simp only [map_smul, ih, (sl3AAction l).map_smul]

/-- The candidate is equivariant once the paper's spanning lemma is supplied. Paper: §2. -/
theorem delta_equivariant_of_squareSpanData (l : SpecialLinear.SL3)
    (data : SquareSpanData) (c : C) :
    delta (sl3CAction l c) = sl3AAction l (delta c) := by
  exact deltaTensor_equivariant_on_squareSpan l (data.squares_span c)

end
end PaperKernel
end Construction
end Connes
