/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Envelope.MatMonoidal

/-!
# Braided and symmetric structure on the matrix envelope

When `C` is a braided (resp. symmetric) monoidal preadditive category, so is
`Mat_ C`.  The braiding on `Mat_ C` is a "diagonal" matrix carrying the
componentwise braidings of `C`, reindexed by the swap `M.ι × N.ι ↔ N.ι × M.ι`.
-/

@[expose] public section

noncomputable section

namespace RS



open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits CategoryTheory.MonoidalPreadditive

universe v u

variable {C : Type u}

/-! ### Componentwise access to the `Mat_ C` monoidal structure -/

@[simp] private theorem mat_whiskerLeft_apply
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (X : Mat_ C) {Y Z : Mat_ C} (f : Y
  ⟶ Z)
    (ix : X.ι) (iy : Y.ι) (jx : X.ι) (jz : Z.ι) :
    (X ◁ f) (ix, iy) (jx, jz) = (𝟙 (X : Mat_ C)) ix jx ⊗ₘ f iy jz := rfl

@[simp] private theorem mat_whiskerRight_apply
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    {X Y : Mat_ C} (f : X ⟶ Y) (Z :
  Mat_ C)
    (ix : X.ι) (iz : Z.ι) (jy : Y.ι) (jz : Z.ι) :
    (f ▷ Z) (ix, iz) (jy, jz) = f ix jy ⊗ₘ (𝟙 (Z : Mat_ C)) iz jz := rfl

@[simp] private theorem mat_tensorHom_apply
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    {M₁ N₁ M₂ N₂ : Mat_ C}
    (f : M₁ ⟶ N₁) (g : M₂ ⟶ N₂) (i₁ : M₁.ι) (i₂ : M₂.ι) (j₁ : N₁.ι) (j₂ : N₂.ι)
      :
    (f ⊗ₘ g : M₁ ⊗ M₂ ⟶ N₁ ⊗ N₂) (i₁, i₂) (j₁, j₂) = f i₁ j₁ ⊗ₘ g i₂ j₂ := rfl

open scoped Classical in
@[simp] private theorem mat_assocHom_apply
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (M N K : Mat_ C)
    (i : M.ι) (j : N.ι) (k : K.ι) (i' : M.ι) (j' : N.ι) (k' : K.ι) :
    (α_ M N K).hom ((i, j), k) (i', (j', k')) =
      if hi : i = i' then if hj : j = j' then if hk : k = k' then
        eqToHom (by subst hi; subst hj; subst hk; rfl) ≫ (α_ (M.X i') (N.X j')
          (K.X k')).hom
      else 0 else 0 else 0 := rfl

open scoped Classical in
@[simp] private theorem mat_assocInv_apply
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (M N K : Mat_ C)
    (i : M.ι) (j : N.ι) (k : K.ι) (i' : M.ι) (j' : N.ι) (k' : K.ι) :
    (α_ M N K).inv (i, (j, k)) ((i', j'), k') =
      if hi : i = i' then if hj : j = j' then if hk : k = k' then
        eqToHom (by subst hi; subst hj; subst hk; rfl) ≫ (α_ (M.X i') (N.X j')
          (K.X k')).inv
      else 0 else 0 else 0 := rfl

/-! ### Braiding data for `Mat_ C` -/

section Braided

open scoped Classical in
private def matBraidHom [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [BraidedCategory C]
    (M N : Mat_ C) : (M ⊗ N : Mat_ C) ⟶ (N ⊗ M : Mat_ C) :=
  fun (i₁, i₂) (j₁, j₂) =>
    if hi : i₂ = j₁ then
      if hj : i₁ = j₂ then
        eqToHom (by subst hi; subst hj; rfl) ≫ (β_ (M.X j₂) (N.X j₁)).hom
      else 0
    else 0

open scoped Classical in
private def matBraidInv [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [BraidedCategory C]
    (M N : Mat_ C) : (N ⊗ M : Mat_ C) ⟶ (M ⊗ N : Mat_ C) :=
  fun (j₁, j₂) (i₁, i₂) =>
    if hj₁ : j₁ = i₂ then
      if hj₂ : j₂ = i₁ then
        eqToHom (by subst hj₁; subst hj₂; rfl) ≫ (β_ (M.X i₁) (N.X i₂)).inv
      else 0
    else 0

open scoped Classical in
@[simp] private theorem matBraidHom_apply
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [BraidedCategory C]
    (M N : Mat_ C)
    (i₁ : M.ι) (i₂ : N.ι) (j₁ : N.ι) (j₂ : M.ι) :
    matBraidHom M N (i₁, i₂) (j₁, j₂) =
      if hi : i₂ = j₁ then if hj : i₁ = j₂ then
        eqToHom (by subst hi; subst hj; rfl) ≫ (β_ (M.X j₂) (N.X j₁)).hom
      else 0 else 0 := rfl

open scoped Classical in
@[simp] private theorem matBraidInv_apply
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [BraidedCategory C]
    (M N : Mat_ C)
    (j₁ : N.ι) (j₂ : M.ι) (i₁ : M.ι) (i₂ : N.ι) :
    matBraidInv M N (j₁, j₂) (i₁, i₂) =
      if hj₁ : j₁ = i₂ then if hj₂ : j₂ = i₁ then
        eqToHom (by subst hj₁; subst hj₂; rfl) ≫ (β_ (M.X i₁) (N.X i₂)).inv
      else 0 else 0 := rfl

/-! ### Braiding iso -/

-- Raised budget: the matrix identity is checked entrywise, and
-- each entry is a sum over the intermediate index.
private theorem matBraid_hom_inv
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [BraidedCategory C]
    (M N : Mat_ C) :
    matBraidHom M N ≫ matBraidInv M N = 𝟙 _ := by
  apply Mat_.hom_ext; intro ⟨i₁, i₂⟩ ⟨i₁', i₂'⟩
  rw [mat_comp_tensor_apply, Mat_.id_apply]
  simp only [matBraidHom_apply, matBraidInv_apply]
  rw [Finset.sum_eq_single_of_mem i₂ (Finset.mem_univ _)]
  · rw [Finset.sum_eq_single_of_mem i₁ (Finset.mem_univ _)]
    · simp only [dite_true, eqToHom_refl, id_comp]
      by_cases h₁ : i₁ = i₁' <;> by_cases h₂ : i₂ = i₂'
      · subst h₁; subst h₂; simp [Iso.hom_inv_id]
      · have : (i₁, i₂) ≠ (i₁', i₂') := fun h => h₂ (Prod.mk.inj h).2
        simp [h₂, this]
      · have : (i₁, i₂) ≠ (i₁', i₂') := fun h => h₁ (Prod.mk.inj h).1
        simp [h₁, this]
      · have : (i₁, i₂) ≠ (i₁', i₂') := fun h => h₁ (Prod.mk.inj h).1
        simp [h₂, this]
    · intro b _ hb; simp [show ¬(i₁ = b) from Ne.symm hb]
  · intro b _ hb; simp [show ¬(i₂ = b) from Ne.symm hb]

-- As for the other composite.
private theorem matBraid_inv_hom
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [BraidedCategory C]
    (M N : Mat_ C) :
    matBraidInv M N ≫ matBraidHom M N = 𝟙 _ := by
  apply Mat_.hom_ext; intro ⟨j₁, j₂⟩ ⟨j₁', j₂'⟩
  rw [mat_comp_tensor_apply, Mat_.id_apply]
  simp only [matBraidInv_apply, matBraidHom_apply]
  rw [Finset.sum_eq_single_of_mem j₂ (Finset.mem_univ _)]
  · rw [Finset.sum_eq_single_of_mem j₁ (Finset.mem_univ _)]
    · simp only [dite_true, eqToHom_refl, id_comp]
      by_cases h₁ : j₁ = j₁' <;> by_cases h₂ : j₂ = j₂'
      · subst h₁; subst h₂; simp [Iso.inv_hom_id]
      · have : (j₁, j₂) ≠ (j₁', j₂') := fun h => h₂ (Prod.mk.inj h).2
        simp [h₂, this]
      · have : (j₁, j₂) ≠ (j₁', j₂') := fun h => h₁ (Prod.mk.inj h).1
        simp [h₁, this]
      · have : (j₁, j₂) ≠ (j₁', j₂') := fun h => h₁ (Prod.mk.inj h).1
        simp [h₂, this]
    · intro b _ hb; simp [show ¬(j₁ = b) from Ne.symm hb]
  · intro b _ hb; simp [show ¬(j₂ = b) from Ne.symm hb]

private def matBraidIso [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [BraidedCategory C]
    (M N : Mat_ C) : (M ⊗ N : Mat_ C) ≅ (N ⊗ M : Mat_ C)
  where
  hom := matBraidHom M N
  inv := matBraidInv M N
  hom_inv_id := matBraid_hom_inv M N
  inv_hom_id := matBraid_inv_hom M N

/-! ### Braiding naturality -/

-- Raised budget: naturality is checked entrywise, each entry a sum
-- over the intermediate index.
private theorem mat_braiding_naturality_right
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] [BraidedCategory C]
    (X : Mat_ C) {Y Z : Mat_ C}
    (f : Y ⟶ Z) :
    X ◁ f ≫ (matBraidIso X Z).hom = (matBraidIso X Y).hom ≫ f ▷ X := by
  apply Mat_.hom_ext; intro ⟨ix, iy⟩ ⟨jz, jx⟩
  rw [mat_comp_tensor_apply, mat_comp_tensor_apply]
  simp only [mat_whiskerLeft_apply, mat_whiskerRight_apply, Mat_.id_apply,
    matBraidIso, matBraidHom_apply]
  rw [Finset.sum_eq_single_of_mem jx (Finset.mem_univ _)]
  · rw [Finset.sum_eq_single_of_mem jz (Finset.mem_univ _)]
    · rw [Finset.sum_eq_single_of_mem iy (Finset.mem_univ _)]
      · rw [Finset.sum_eq_single_of_mem ix (Finset.mem_univ _)]
        · simp only [dite_true, eqToHom_refl]
          by_cases hx : ix = jx
          · subst hx; simp only [dite_true, eqToHom_refl, id_comp]
            rw [id_tensorHom, tensorHom_id]
            exact BraidedCategory.braiding_naturality_right (X.X ix) (f iy jz)
          · simp [hx]
        · intro b _ hb; simp [show ¬(ix = b) from Ne.symm hb]
      · intro b _ hb; simp [show ¬(iy = b) from Ne.symm hb]
    · intro b _ hb; simp [hb]
  · intro b _ hb; simp [hb]

-- As for the right-hand naturality.
private theorem mat_braiding_naturality_left
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] [BraidedCategory C]
    {X Y : Mat_ C} (f : X ⟶ Y)
    (Z : Mat_ C) :
    f ▷ Z ≫ (matBraidIso Y Z).hom = (matBraidIso X Z).hom ≫ Z ◁ f := by
  apply Mat_.hom_ext; intro ⟨ix, iz⟩ ⟨jz, jy⟩
  rw [mat_comp_tensor_apply, mat_comp_tensor_apply]
  simp only [mat_whiskerLeft_apply, mat_whiskerRight_apply, Mat_.id_apply,
    matBraidIso, matBraidHom_apply]
  rw [Finset.sum_eq_single_of_mem jy (Finset.mem_univ _)]
  · rw [Finset.sum_eq_single_of_mem jz (Finset.mem_univ _)]
    · rw [Finset.sum_eq_single_of_mem iz (Finset.mem_univ _)]
      · rw [Finset.sum_eq_single_of_mem ix (Finset.mem_univ _)]
        · simp only [dite_true, eqToHom_refl]
          by_cases hz : iz = jz
          · subst hz; simp only [dite_true, eqToHom_refl, id_comp]
            rw [tensorHom_id, id_tensorHom]
            exact BraidedCategory.braiding_naturality_left (f ix jy) (Z.X iz)
          · simp [hz]
        · intro b _ hb; simp [show ¬(ix = b) from Ne.symm hb]
      · intro b _ hb; simp [show ¬(iz = b) from Ne.symm hb]
    · intro b _ hb; simp [hb]
  · intro b _ hb; simp [hb]

/-! ### Hexagon identities -/

private theorem mat_comp3_fwd_lhs
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (X Y Z : Mat_ C)
    {A E : Mat_ C}
    (f : A ⟶ X ⊗ (Y ⊗ Z)) (g : X ⊗ (Y ⊗ Z) ⟶ (Y ⊗ Z) ⊗ X) (h : (Y ⊗ Z) ⊗ X ⟶ E)
    (i : A.ι) (e : E.ι) :
    (f ≫ g ≫ h) i e =
      ∑ ax : X.ι, ∑ ay : Y.ι, ∑ az : Z.ι,
      ∑ by_ : Y.ι, ∑ bz : Z.ι, ∑ bx : X.ι,
        f i (ax, (ay, az)) ≫ g (ax, (ay, az)) ((by_, bz), bx) ≫ h ((by_, bz),
          bx) e := by
  rw [mat_comp_XYZ_apply X Y Z]
  congr 1; ext ax; congr 1; ext ay; congr 1; ext az
  rw [mat_comp_XY_Z_apply Y Z X, Preadditive.comp_sum]
  congr 1; ext by_; rw [Preadditive.comp_sum]
  congr 1; ext bz; rw [Preadditive.comp_sum]

private theorem mat_comp3_fwd_rhs
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (X Y Z : Mat_ C)
    {A E : Mat_ C}
    (f : A ⟶ (Y ⊗ X) ⊗ Z) (g : (Y ⊗ X) ⊗ Z ⟶ Y ⊗ (X ⊗ Z)) (h : Y ⊗ (X ⊗ Z) ⟶ E)
    (i : A.ι) (e : E.ι) :
    (f ≫ g ≫ h) i e =
      ∑ cy : Y.ι, ∑ cx : X.ι, ∑ cz : Z.ι,
      ∑ dy : Y.ι, ∑ dx : X.ι, ∑ dz : Z.ι,
        f i ((cy, cx), cz) ≫ g ((cy, cx), cz) (dy, (dx, dz)) ≫ h (dy, (dx, dz))
          e := by
  rw [mat_comp_XY_Z_apply Y X Z]
  congr 1; ext cy; congr 1; ext cx; congr 1; ext cz
  rw [mat_comp_XYZ_apply Y X Z, Preadditive.comp_sum]
  congr 1; ext dy; rw [Preadditive.comp_sum]
  congr 1; ext dx; rw [Preadditive.comp_sum]

private theorem mat_comp3_rev_lhs
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (X Y Z : Mat_ C)
    {A E : Mat_ C}
    (f : A ⟶ (X ⊗ Y) ⊗ Z) (g : (X ⊗ Y) ⊗ Z ⟶ Z ⊗ (X ⊗ Y)) (h : Z ⊗ (X ⊗ Y) ⟶ E)
    (i : A.ι) (e : E.ι) :
    (f ≫ g ≫ h) i e =
      ∑ ax : X.ι, ∑ ay : Y.ι, ∑ az : Z.ι,
      ∑ bz : Z.ι, ∑ bx : X.ι, ∑ by_ : Y.ι,
        f i ((ax, ay), az) ≫ g ((ax, ay), az) (bz, (bx, by_)) ≫ h (bz, (bx,
          by_)) e := by
  rw [mat_comp_XY_Z_apply X Y Z]
  congr 1; ext ax; congr 1; ext ay; congr 1; ext az
  rw [mat_comp_XYZ_apply Z X Y, Preadditive.comp_sum]
  congr 1; ext bz; rw [Preadditive.comp_sum]
  congr 1; ext bx; rw [Preadditive.comp_sum]

private theorem mat_comp3_rev_rhs
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (X Y Z : Mat_ C)
    {A E : Mat_ C}
    (f : A ⟶ X ⊗ (Z ⊗ Y)) (g : X ⊗ (Z ⊗ Y) ⟶ (X ⊗ Z) ⊗ Y) (h : (X ⊗ Z) ⊗ Y ⟶ E)
    (i : A.ι) (e : E.ι) :
    (f ≫ g ≫ h) i e =
      ∑ cx : X.ι, ∑ cz : Z.ι, ∑ cy : Y.ι,
      ∑ dx : X.ι, ∑ dz : Z.ι, ∑ dy : Y.ι,
        f i (cx, (cz, cy)) ≫ g (cx, (cz, cy)) ((dx, dz), dy) ≫ h ((dx, dz), dy)
          e := by
  rw [mat_comp_XYZ_apply X Z Y]
  congr 1; ext cx; congr 1; ext cz; congr 1; ext cy
  rw [mat_comp_XY_Z_apply X Z Y, Preadditive.comp_sum]
  congr 1; ext dx; rw [Preadditive.comp_sum]
  congr 1; ext dz; rw [Preadditive.comp_sum]

-- Raised budget: the hexagon is checked entrywise on a triple
-- index, so three matrix compositions expand.
private theorem mat_hexagon_forward
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] [BraidedCategory C]
    (X Y Z : Mat_ C) :
    (α_ X Y Z).hom ≫ (matBraidIso X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
    (matBraidIso X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (matBraidIso X Z).hom := by
  apply Mat_.hom_ext; intro ⟨⟨ix, iy⟩, iz⟩ ⟨jy, ⟨jz, jx⟩⟩
  rw [mat_comp3_fwd_lhs X Y Z, mat_comp3_fwd_rhs X Y Z]
  simp only [mat_assocHom_apply, matBraidIso, matBraidHom_apply,
    mat_whiskerLeft_apply, mat_whiskerRight_apply, Mat_.id_apply]
  -- LHS: collapse ax=ix, ay=iy, az=iz (from α.hom)
  rw [Finset.sum_eq_single_of_mem ix (Finset.mem_univ _)]
  · rw [Finset.sum_eq_single_of_mem iy (Finset.mem_univ _)]
    · rw [Finset.sum_eq_single_of_mem iz (Finset.mem_univ _)]
      · simp only [dite_true, eqToHom_refl, id_comp]
        -- Braiding: collapse by_=iy, bz=iz, bx=ix
        rw [Finset.sum_eq_single_of_mem iy (Finset.mem_univ _)]
        · rw [Finset.sum_eq_single_of_mem iz (Finset.mem_univ _)]
          · rw [Finset.sum_eq_single_of_mem ix (Finset.mem_univ _)]
            · simp only [dite_true, eqToHom_refl, id_comp]
              -- RHS: collapse cy=iy, cx=ix, cz=iz
              rw [Finset.sum_eq_single_of_mem iy (Finset.mem_univ _)]
              · rw [Finset.sum_eq_single_of_mem ix (Finset.mem_univ _)]
                · rw [Finset.sum_eq_single_of_mem iz (Finset.mem_univ _)]
                  · simp only [dite_true, eqToHom_refl, id_comp]
                    -- α.hom: collapse dy=iy, dx=ix, dz=iz
                    rw [Finset.sum_eq_single_of_mem iy (Finset.mem_univ _)]
                    · rw [Finset.sum_eq_single_of_mem ix (Finset.mem_univ _)]
                      · rw [Finset.sum_eq_single_of_mem iz (Finset.mem_univ _)]
                        · simp only [dite_true, eqToHom_refl, id_comp]
                          by_cases hx : ix = jx <;> by_cases hy : iy = jy <;>
                            by_cases hz : iz = jz
                          · subst hx; subst hy; subst hz
                            simp only [dite_true, eqToHom_refl, id_comp]
                            rw [id_tensorHom, tensorHom_id]
                            exact BraidedCategory.hexagon_forward (X.X ix) (Y.X
                              iy) (Z.X iz)
                          all_goals simp_all
                        · intro b _ hb; simp [Ne.symm hb]
                      · intro b _ hb; simp [Ne.symm hb]
                    · intro b _ hb; simp [Ne.symm hb]
                  · intro b _ hb; simp [Ne.symm hb]
                · intro b _ hb; simp [Ne.symm hb]
              · intro b _ hb; simp [Ne.symm hb]
            · intro b _ hb; simp [Ne.symm hb]
          · intro b _ hb
            have : ¬((iy, iz) = (iy, b)) := fun h => (Ne.symm hb)
              (Prod.mk.inj h).2
            simp [this]
        · intro b _ hb
          apply Finset.sum_eq_zero; intro bz _
          apply Finset.sum_eq_zero; intro bx _
          have : ¬((iy, iz) = (b, bz)) := fun h => (Ne.symm hb)
            (Prod.mk.inj h).1
          simp [this]
      · intro b _ hb; simp [Ne.symm hb]
    · intro b _ hb; simp [Ne.symm hb]
  · intro b _ hb; simp [Ne.symm hb]

-- As for the forward hexagon.
private theorem mat_hexagon_reverse
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] [BraidedCategory C]
    (X Y Z : Mat_ C) :
    (α_ X Y Z).inv ≫ (matBraidIso (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
    X ◁ (matBraidIso Y Z).hom ≫ (α_ X Z Y).inv ≫ (matBraidIso X Z).hom ▷ Y := by
  apply Mat_.hom_ext; intro ⟨ix, ⟨iy, iz⟩⟩ ⟨⟨jz, jx⟩, jy⟩
  rw [mat_comp3_rev_lhs X Y Z, mat_comp3_rev_rhs X Y Z]
  simp only [mat_assocInv_apply, matBraidIso, matBraidHom_apply,
    mat_whiskerLeft_apply, mat_whiskerRight_apply, Mat_.id_apply]
  -- LHS: collapse ax=ix, ay=iy, az=iz (from α.inv)
  rw [Finset.sum_eq_single_of_mem ix (Finset.mem_univ _)]
  · rw [Finset.sum_eq_single_of_mem iy (Finset.mem_univ _)]
    · rw [Finset.sum_eq_single_of_mem iz (Finset.mem_univ _)]
      · simp only [dite_true, eqToHom_refl, id_comp]
        -- Braiding: collapse bz=iz, bx=ix, by_=iy
        rw [Finset.sum_eq_single_of_mem iz (Finset.mem_univ _)]
        · rw [Finset.sum_eq_single_of_mem ix (Finset.mem_univ _)]
          · rw [Finset.sum_eq_single_of_mem iy (Finset.mem_univ _)]
            · simp only [dite_true, eqToHom_refl, id_comp]
              -- RHS: collapse cx=ix, cz=iz, cy=iy
              rw [Finset.sum_eq_single_of_mem ix (Finset.mem_univ _)]
              · rw [Finset.sum_eq_single_of_mem iz (Finset.mem_univ _)]
                · rw [Finset.sum_eq_single_of_mem iy (Finset.mem_univ _)]
                  · simp only [dite_true, eqToHom_refl, id_comp]
                    -- α.inv: collapse dx=ix, dz=iz, dy=iy
                    rw [Finset.sum_eq_single_of_mem ix (Finset.mem_univ _)]
                    · rw [Finset.sum_eq_single_of_mem iz (Finset.mem_univ _)]
                      · rw [Finset.sum_eq_single_of_mem iy (Finset.mem_univ _)]
                        · simp only [dite_true, eqToHom_refl, id_comp]
                          by_cases hx : ix = jx <;> by_cases hy : iy = jy <;>
                            by_cases hz : iz = jz
                          · subst hx; subst hy; subst hz
                            simp only [dite_true, eqToHom_refl, id_comp]
                            rw [id_tensorHom, tensorHom_id]
                            exact BraidedCategory.hexagon_reverse (X.X ix) (Y.X
                              iy) (Z.X iz)
                          all_goals simp_all
                        · intro b _ hb; simp [Ne.symm hb]
                      · intro b _ hb; simp [Ne.symm hb]
                    · intro b _ hb; simp [Ne.symm hb]
                  · intro b _ hb; simp [Ne.symm hb]
                · intro b _ hb; simp [Ne.symm hb]
              · intro b _ hb; simp [Ne.symm hb]
            · intro b _ hb
              have : ¬((ix, iy) = (ix, b)) :=
                fun h => (Ne.symm hb) (Prod.mk.inj h).2
              simp [this]
          · intro b _ hb
            apply Finset.sum_eq_zero; intro by_ _
            have : ¬((ix, iy) = (b, by_)) :=
              fun h => (Ne.symm hb) (Prod.mk.inj h).1
            simp [this]
        · intro b _ hb; simp [Ne.symm hb]
      · intro b _ hb; simp [Ne.symm hb]
    · intro b _ hb; simp [Ne.symm hb]
  · intro b _ hb; simp [Ne.symm hb]

/-! ### `BraidedCategory` instance -/

/-- The matrix category inherits a braiding: the componentwise
braidings, reindexed by the swap of index products. -/
instance matBraided [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] [BraidedCategory C] : BraidedCategory (Mat_ C) where
  braiding := matBraidIso
  braiding_naturality_right := mat_braiding_naturality_right
  braiding_naturality_left := mat_braiding_naturality_left
  hexagon_forward := mat_hexagon_forward
  hexagon_reverse := mat_hexagon_reverse

end Braided

/-! ### `SymmetricCategory` instance -/

section Symmetric

-- Raised budget: symmetry is checked entrywise.
/-- And a symmetric one stays symmetric. -/
instance matSymmetric [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] :
    SymmetricCategory (Mat_ C) where
  symmetry X Y := by
    change matBraidHom X Y ≫ matBraidHom Y X = 𝟙 _
    apply Mat_.hom_ext; intro ⟨ix, iy⟩ ⟨jx, jy⟩
    rw [mat_comp_tensor_apply, Mat_.id_apply]
    simp only [matBraidHom_apply]
    rw [Finset.sum_eq_single_of_mem iy (Finset.mem_univ _)]
    · rw [Finset.sum_eq_single_of_mem ix (Finset.mem_univ _)]
      · simp only [dite_true, eqToHom_refl, id_comp]
        by_cases hx : ix = jx <;> by_cases hy : iy = jy
        · subst hx; subst hy
          simp only [dite_true, eqToHom_refl, id_comp]
          exact SymmetricCategory.symmetry (X.X ix) (Y.X iy)
        · have : (ix, iy) ≠ (jx, jy) := fun h => hy (Prod.mk.inj h).2
          simp [hy, this]
        · have : (ix, iy) ≠ (jx, jy) := fun h => hx (Prod.mk.inj h).1
          simp [hx, this]
        · have : (ix, iy) ≠ (jx, jy) := fun h => hx (Prod.mk.inj h).1
          simp [hy, this]
      · intro b _ hb; simp [show ¬(ix = b) from Ne.symm hb]
    · intro b _ hb; simp [show ¬(iy = b) from Ne.symm hb]

end Symmetric

end RS

end
