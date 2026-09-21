/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Envelope.MatBraided

/-!
# Rigidity of the matrix envelope

When `C` is a right rigid monoidal preadditive category, the matrix
envelope `Mat_ C` is right rigid: the dual of an object
`M = (ι, X)` is `(ι, fun i => (X i)ᘁ)`, with coevaluation and
evaluation built diagonally from the componentwise cups and caps.
The snake identities reduce to collapsing off-diagonal sums
(all zero by `MonoidalPreadditive`) and applying the base snake
identity at each index.

When `C` is moreover braided, `Mat_ C` is rigid.
-/

noncomputable section

namespace RS

open scoped Classical

open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits CategoryTheory.MonoidalPreadditive

universe v u

variable {C : Type u}

/-! ### Componentwise access lemmas

The `private` access lemmas in `MatBraided.lean` are not visible here,
so we restate the ones we need.  Each is proved by `rfl`. -/

@[simp] private theorem mat_whiskerLeft_apply'
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (X : Mat_ C) {Y Z : Mat_ C} (f :
  Y ⟶ Z)
    (ix : X.ι) (iy : Y.ι) (jx : X.ι) (jz : Z.ι) :
    (X ◁ f) (ix, iy) (jx, jz) = (𝟙 (X : Mat_ C)) ix jx ⊗ₘ f iy jz := rfl

@[simp] private theorem mat_whiskerRight_apply'
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    {X Y : Mat_ C} (f : X ⟶ Y) (Z :
  Mat_ C)
    (ix : X.ι) (iz : Z.ι) (jy : Y.ι) (jz : Z.ι) :
    (f ▷ Z) (ix, iz) (jy, jz) = f ix jy ⊗ₘ (𝟙 (Z : Mat_ C)) iz jz := rfl

@[simp] private theorem mat_assocHom_apply'
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (M N K : Mat_ C)
    (i : M.ι) (j : N.ι) (k : K.ι) (i' : M.ι) (j' : N.ι) (k' : K.ι) :
    (α_ M N K).hom ((i, j), k) (i', (j', k')) =
      if hi : i = i' then if hj : j = j' then if hk : k = k' then
        eqToHom (by subst hi; subst hj; subst hk; rfl) ≫ (α_ (M.X i') (N.X j')
          (K.X k')).hom
      else 0 else 0 else 0 := rfl

@[simp] private theorem mat_assocInv_apply'
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (M N K : Mat_ C)
    (i : M.ι) (j : N.ι) (k : K.ι) (i' : M.ι) (j' : N.ι) (k' : K.ι) :
    (α_ M N K).inv (i, (j, k)) ((i', j'), k') =
      if hi : i = i' then if hj : j = j' then if hk : k = k' then
        eqToHom (by subst hi; subst hj; subst hk; rfl) ≫ (α_ (M.X i') (N.X j')
          (K.X k')).inv
      else 0 else 0 else 0 := rfl

@[simp] private theorem mat_rightUnitorHom_apply'
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (M : Mat_ C) (i : M.ι) (u :
  PUnit) (j : M.ι) :
    (ρ_ M).hom (i, u) j =
      if h : i = j then eqToHom (by subst h; rfl) ≫ (ρ_ (M.X j)).hom else 0
        := rfl

@[simp] private theorem mat_rightUnitorInv_apply'
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (M : Mat_ C) (i : M.ι) (j :
  M.ι) (u : PUnit) :
    (ρ_ M).inv i (j, u) =
      if h : i = j then (ρ_ (M.X i)).inv ≫ eqToHom (by subst h; rfl) else 0
        := rfl

@[simp] private theorem mat_leftUnitorHom_apply'
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (M : Mat_ C) (u : PUnit) (i :
  M.ι) (j : M.ι) :
    (λ_ M).hom (u, i) j =
      if h : i = j then eqToHom (by subst h; rfl) ≫ (λ_ (M.X j)).hom else 0
        := rfl

@[simp] private theorem mat_leftUnitorInv_apply'
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (M : Mat_ C) (i : M.ι) (u :
  PUnit) (j : M.ι) :
    (λ_ M).inv i (u, j) =
      if h : i = j then (λ_ (M.X i)).inv ≫ eqToHom (by subst h; rfl) else 0
        := rfl

/-! ### The dual object -/

/-- The right dual of `M` in `Mat_ C`: same index set, componentwise dual. -/
@[reducible] noncomputable def matRightDualObj
    [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    (M : Mat_ C) : Mat_ C :=
  ⟨M.ι, fun i => (M.X i)ᘁ⟩

/-! ### Coevaluation and evaluation -/

/-- Componentwise coevaluation: diagonal matrix of cups. -/
noncomputable def matCoev [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [RightRigidCategory C]
    (M : Mat_ C) : 𝟙_ (Mat_ C) ⟶ M ⊗ matRightDualObj M :=
  fun _ p => if h : p.1 = p.2 then
    η_ (M.X p.1) ((M.X p.1)ᘁ) ≫
      eqToHom (congr_arg (M.X p.1 ⊗ ·) (congr_arg (fun i => (M.X i)ᘁ) h))
  else 0

/-- Componentwise evaluation: diagonal matrix of caps. -/
noncomputable def matEv [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [RightRigidCategory C]
    (M : Mat_ C) : matRightDualObj M ⊗ M ⟶ 𝟙_ (Mat_ C) :=
  fun p _ => if h : p.1 = p.2 then
    eqToHom (congr_arg (· ⊗ M.X p.2) (congr_arg (fun i => (M.X i)ᘁ) h)) ≫
      ε_ (M.X p.2) ((M.X p.2)ᘁ)
  else 0

/-! ### Entry lemmas for coev/ev -/

private theorem matCoev_apply_diag
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [RightRigidCategory C]
    (M : Mat_ C) (u : PUnit) (i : M.ι) :
    matCoev M u (i, i) = η_ (M.X i) ((M.X i)ᘁ) := by
  simp [matCoev]

private theorem matCoev_apply_off
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [RightRigidCategory C]
    (M : Mat_ C) (u : PUnit) (i j : M.ι) (h : i ≠
  j) :
    matCoev M u (i, j) = 0 :=
  dif_neg h

private theorem matEv_apply_diag
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [RightRigidCategory C]
    (M : Mat_ C) (i : M.ι) (u : PUnit) :
    matEv M (i, i) u = ε_ (M.X i) ((M.X i)ᘁ) := by
  simp [matEv]

private theorem matEv_apply_off
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [RightRigidCategory C]
    (M : Mat_ C) (i j : M.ι) (u : PUnit) (h : i ≠ j)
  :
    matEv M (i, j) u = 0 :=
  dif_neg h

/-! ### The snake identities -/

-- Raised budget: the snake identity is checked entrywise, and the
-- coevaluation contributes a sum over the dual index.
private theorem mat_snake_one
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] [RightRigidCategory C]
    (M : Mat_ C) :
    (matRightDualObj M) ◁ matCoev M ≫ (α_ (matRightDualObj M) M (matRightDualObj
      M)).inv ≫
      matEv M ▷ (matRightDualObj M) =
    (ρ_ (matRightDualObj M)).hom ≫ (λ_ (matRightDualObj M)).inv := by
  apply Mat_.hom_ext
  intro ⟨a, u⟩ ⟨u', b⟩
  -- Expand the two compositions into iterated sums.
  rw [mat_comp_XYZ_apply (matRightDualObj M) M (matRightDualObj M)]
  simp_rw [mat_comp_XY_Z_apply (matRightDualObj M) M (matRightDualObj M)]
  simp only [Preadditive.comp_sum]
  -- Collapse outer sums j=a, k=a, l=a.
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
  · rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
    · rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
      · -- On-diagonal: expand whiskerLeft, simplify id and coev.
        simp only [mat_whiskerLeft_apply', Mat_.id_apply_self]
        rw [matCoev_apply_diag M]
        -- Collapse inner sums to (a,a,a).
        rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
        · rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
          · rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
            · simp only [mat_assocInv_apply', mat_whiskerRight_apply',
                dite_true, eqToHom_refl, id_comp]
              by_cases hab : a = b
              · subst hab
                rw [Mat_.id_apply_self, matEv_apply_diag M]
                simp only [id_tensorHom, tensorHom_id]
                rw [Mat_.comp_apply,
                  Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
                · simp only [mat_rightUnitorHom_apply',
                  mat_leftUnitorInv_apply',
                    eqToHom_refl, id_comp, comp_id]
                  exact ExactPairing.coevaluation_evaluation (M.X a) ((M.X a)ᘁ)
                · intro c _ hc
                  rw [mat_rightUnitorHom_apply', dif_neg (Ne.symm hc),
                    zero_comp]
              · rw [Mat_.id_apply_of_ne _ _ _ hab]
                simp only [tensor_zero, comp_zero]
                rw [Mat_.comp_apply,
                  Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
                · simp only [mat_rightUnitorHom_apply',
                  mat_leftUnitorInv_apply']
                  simp [hab]
                · intro c _ hc
                  rw [mat_rightUnitorHom_apply', dif_neg (Ne.symm hc),
                    zero_comp]
            · intro l' _ hl'
              simp [Ne.symm hl', zero_comp]
          · intro k' _ hk'
            apply Finset.sum_eq_zero; intro l' _
            simp [Ne.symm hk', zero_comp]
        · intro j' _ hj'
          apply Finset.sum_eq_zero; intro k' _
          apply Finset.sum_eq_zero; intro l' _
          simp [Ne.symm hj', zero_comp]
      · -- Off-diagonal: l ≠ a for the matCoev.
        intro l _ hl
        simp only [mat_whiskerLeft_apply', Mat_.id_apply_self]
        rw [matCoev_apply_off M _ _ _ (Ne.symm hl)]
        simp [tensor_zero, zero_comp]
    · -- Off-diagonal: k ≠ a.
      intro k _ hk
      apply Finset.sum_eq_zero; intro l _
      simp only [mat_whiskerLeft_apply', Mat_.id_apply_self]
      by_cases hkl : k = l
      · subst hkl
        rw [matCoev_apply_diag M]
        -- coev is nonzero, but inner ev at (a,k) is 0 since a ≠ k.
        rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
        · rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ _)]
          · rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ _)]
            · simp only [mat_assocInv_apply', mat_whiskerRight_apply',
                dite_true, eqToHom_refl, id_comp]
              rw [matEv_apply_off M _ _ _ (Ne.symm hk)]
              simp [MonoidalPreadditive.zero_tensor]
            · intro l' _ hl'
              simp [Ne.symm hl', zero_comp]
          · intro k' _ hk'
            apply Finset.sum_eq_zero; intro l' _
            simp [Ne.symm hk', zero_comp]
        · intro j' _ hj'
          apply Finset.sum_eq_zero; intro k' _
          apply Finset.sum_eq_zero; intro l' _
          simp [Ne.symm hj', zero_comp]
      · rw [matCoev_apply_off M _ _ _ hkl]
        simp [tensor_zero, zero_comp]
  · -- Off-diagonal: j ≠ a.
    intro j _ hj
    apply Finset.sum_eq_zero; intro k _
    apply Finset.sum_eq_zero; intro l _
    simp only [mat_whiskerLeft_apply']
    rw [Mat_.id_apply_of_ne _ _ _ (Ne.symm hj)]
    simp [MonoidalPreadditive.zero_tensor, zero_comp]

-- As for the first snake identity.
private theorem mat_snake_two
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] [RightRigidCategory C]
    (M : Mat_ C) :
    matCoev M ▷ M ≫ (α_ M (matRightDualObj M) M).hom ≫
      M ◁ matEv M =
    (λ_ M).hom ≫ (ρ_ M).inv := by
  apply Mat_.hom_ext
  intro ⟨u, a⟩ ⟨b, u'⟩
  rw [mat_comp_XY_Z_apply M (matRightDualObj M) M]
  simp_rw [mat_comp_XYZ_apply M (matRightDualObj M) M]
  simp only [Preadditive.comp_sum]
  -- Collapse outer sums j=a, k=a, l=a.
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
  · rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
    · rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
      · -- On-diagonal whiskerRight term.
        simp only [mat_whiskerRight_apply', Mat_.id_apply_self]
        rw [matCoev_apply_diag M]
        -- Collapse inner sum to (a,(a,a)).
        rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
        · rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
          · rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
            · simp only [mat_assocHom_apply', mat_whiskerLeft_apply',
                dite_true, eqToHom_refl, id_comp]
              by_cases hab : a = b
              · subst hab
                rw [Mat_.id_apply_self, matEv_apply_diag M]
                simp only [id_tensorHom, tensorHom_id]
                rw [Mat_.comp_apply,
                  Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
                · simp only [mat_leftUnitorHom_apply',
                  mat_rightUnitorInv_apply',
                    eqToHom_refl, id_comp, comp_id]
                  exact ExactPairing.evaluation_coevaluation (M.X a) ((M.X a)ᘁ)
                · intro c _ hc
                  rw [mat_leftUnitorHom_apply', dif_neg (Ne.symm hc), zero_comp]
              · rw [Mat_.id_apply_of_ne _ _ _ hab]
                rw [MonoidalPreadditive.zero_tensor, comp_zero, comp_zero]
                rw [Mat_.comp_apply,
                  Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
                · simp only [mat_leftUnitorHom_apply',
                  mat_rightUnitorInv_apply']
                  simp [hab]
                · intro c _ hc
                  rw [mat_leftUnitorHom_apply', dif_neg (Ne.symm hc), zero_comp]
            · intro l' _ hl'
              simp [Ne.symm hl', zero_comp]
          · intro k' _ hk'
            apply Finset.sum_eq_zero; intro l' _
            simp [Ne.symm hk', zero_comp]
        · intro j' _ hj'
          apply Finset.sum_eq_zero; intro k' _
          apply Finset.sum_eq_zero; intro l' _
          simp [Ne.symm hj', zero_comp]
      · -- Off-diagonal: l ≠ a for matCoev.
        intro l _ hl
        simp only [mat_whiskerRight_apply']
        rw [Mat_.id_apply_of_ne _ _ _ (Ne.symm hl),
          MonoidalPreadditive.tensor_zero]
        simp only [zero_comp, Finset.sum_const_zero]
    · -- Off-diagonal: k ≠ a.  matCoev M u (a, k) = 0.
      intro k _ hk
      apply Finset.sum_eq_zero; intro l _
      simp only [mat_whiskerRight_apply']
      rw [matCoev_apply_off M _ _ _ (Ne.symm hk)]
      simp [MonoidalPreadditive.zero_tensor, zero_comp]
  · -- Off-diagonal: j ≠ a.
    intro j _ hj
    apply Finset.sum_eq_zero; intro k _
    apply Finset.sum_eq_zero; intro l _
    simp only [mat_whiskerRight_apply']
    by_cases hjk : j = k
    · subst hjk
      by_cases hal : a = l
      · subst hal
        -- j = k, a = l: both factors nonzero, but matEv vanishes since j ≠ a.
        rw [matCoev_apply_diag M, Mat_.id_apply_self]
        rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ _)]
        · rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ _)]
          · rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
            · simp only [mat_assocHom_apply', mat_whiskerLeft_apply',
                dite_true, eqToHom_refl, id_comp]
              rw [matEv_apply_off M _ _ _ hj]
              simp [MonoidalPreadditive.tensor_zero, comp_zero]
            · intro l' _ hl'
              simp [Ne.symm hl', zero_comp]
          · intro k' _ hk'
            apply Finset.sum_eq_zero; intro l' _
            simp [Ne.symm hk', zero_comp]
        · intro j' _ hj'
          apply Finset.sum_eq_zero; intro k' _
          apply Finset.sum_eq_zero; intro l' _
          simp [Ne.symm hj', zero_comp]
      · -- a ≠ l: (𝟙 M) a l = 0.
        rw [Mat_.id_apply_of_ne _ _ _ hal]
        simp [MonoidalPreadditive.tensor_zero, zero_comp]
    · -- j ≠ k: matCoev is 0.
      rw [matCoev_apply_off M _ _ _ hjk]
      simp [MonoidalPreadditive.zero_tensor, zero_comp]

/-! ### The exact pairing and rigidity instances -/

/-- The exact pairing between `M` and its componentwise right dual. -/
noncomputable def matExactPairing
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] [RightRigidCategory C]
    (M : Mat_ C) :
    ExactPairing M (matRightDualObj M) where
  coevaluation' := matCoev M
  evaluation' := matEv M
  coevaluation_evaluation' := mat_snake_one M
  evaluation_coevaluation' := mat_snake_two M

/-- Every object in `Mat_ C` has a right dual. -/
noncomputable instance matHasRightDual
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] [RightRigidCategory C]
    (M : Mat_ C) : HasRightDual M where
  rightDual := matRightDualObj M
  exact := matExactPairing M

/-- `Mat_ C` is right rigid when `C` is right rigid. -/
noncomputable instance matRightRigid
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] [RightRigidCategory C] :
    RightRigidCategory (Mat_ C) where

/-- `Mat_ C` is rigid when `C` is right rigid and braided. -/
noncomputable instance matRigid
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] [RightRigidCategory C]
    [BraidedCategory C] : RigidCategory (Mat_ C) :=
  BraidedCategory.rigidCategoryOfRightRigidCategory

end RS

end
