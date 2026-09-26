/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Monoidal structure on the matrix envelope

When `C` is a monoidal preadditive category (i.e. a preadditive category with a
monoidal structure such that the tensor product is bilinear on morphisms), the
matrix category `Mat_ C` inherits a monoidal structure:

* **Objects**: `M ⊗ N = (M.ι × N.ι, fun p => M.X p.1 ⊗ N.X p.2)`.
* **Morphisms**: the Kronecker product — entry `(i₁,i₂),(j₁,j₂)` of `f ⊗ₘ g`
  is `f i₁ j₁ ⊗ₘ g i₂ j₂`.
* **Unit**: `(PUnit, fun _ => 𝟙_ C)`.
* **Structural isomorphisms**: diagonal matrices carrying the componentwise
  associators/unitors of `C`, with index-type reindexing by `Equiv.prodAssoc`,
  `Equiv.punitProd`, `Equiv.prodPUnit`.

The interchange law (`tensorHom_comp_tensorHom`) holds because matrix
multiplication turns into iterated sums that factor via `tensor_sum` and
`sum_tensor` (the `MonoidalPreadditive` hypothesis).  The pentagon and triangle
identities reduce componentwise to the corresponding identities in `C`.
-/

@[expose] public section

noncomputable section

namespace RS



open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits CategoryTheory.MonoidalPreadditive

universe v u

variable {C : Type u}

/-! ### Tensor product data on `Mat_ C` -/

/-- Tensor product of objects in `Mat_ C`: index by the product, with
componentwise tensor in `C`. -/
@[reducible] def matTensorObj [Category.{v} C] [MonoidalCategory C]
    (M N : Mat_ C) : Mat_ C :=
  ⟨M.ι × N.ι, fun p => M.X p.1 ⊗ N.X p.2⟩

/-- Tensor product of morphisms in `Mat_ C`: the Kronecker product. -/
def matTensorHom [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    {M₁ N₁ M₂ N₂ : Mat_ C}
    (f : M₁ ⟶ N₁) (g : M₂ ⟶ N₂) : matTensorObj M₁ M₂ ⟶ matTensorObj N₁ N₂ :=
  fun (i₁, i₂) (j₁, j₂) => f i₁ j₁ ⊗ₘ g i₂ j₂

/-- The tensor unit in `Mat_ C`. -/
@[reducible] def matTensorUnit
    [Category.{v} C] [MonoidalCategory C] : Mat_ C := ⟨PUnit, fun _ => 𝟙_ C⟩

/-! ### Structural isomorphisms

The associator and unitors are "diagonal" morphisms: given an equivalence of
index types, the entry at `(i, e i)` is the corresponding structural morphism
of `C`, and all other entries are zero. -/

open scoped Classical in
/-- The associator hom in `Mat_ C`. -/
def matAssocHom [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (M N K : Mat_ C) :
    matTensorObj (matTensorObj M N) K ⟶ matTensorObj M (matTensorObj N K) :=
  fun ((i, j), k) (i', (j', k')) =>
    if hi : i = i' then
      if hj : j = j' then
        if hk : k = k' then
          eqToHom (by subst hi; subst hj; subst hk; rfl) ≫
            (α_ (M.X i') (N.X j') (K.X k')).hom
        else 0
      else 0
    else 0

open scoped Classical in
/-- The associator inv in `Mat_ C`. -/
def matAssocInv [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (M N K : Mat_ C) :
    matTensorObj M (matTensorObj N K) ⟶ matTensorObj (matTensorObj M N) K :=
  fun (i, (j, k)) ((i', j'), k') =>
    if hi : i = i' then
      if hj : j = j' then
        if hk : k = k' then
          eqToHom (by subst hi; subst hj; subst hk; rfl) ≫
            (α_ (M.X i') (N.X j') (K.X k')).inv
        else 0
      else 0
    else 0

open scoped Classical in
/-- The left unitor hom in `Mat_ C`. -/
def matLeftUnitorHom
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (M : Mat_ C) :
    matTensorObj matTensorUnit M ⟶ M :=
  fun ((), i) j =>
    if h : i = j then
      eqToHom (by subst h; rfl) ≫ (λ_ (M.X j)).hom
    else 0

open scoped Classical in
/-- The left unitor inv in `Mat_ C`. -/
def matLeftUnitorInv
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (M : Mat_ C) :
    M ⟶ matTensorObj matTensorUnit M :=
  fun i ((), j) =>
    if h : i = j then
      (λ_ (M.X i)).inv ≫ eqToHom (by subst h; rfl)
    else 0

open scoped Classical in
/-- The right unitor hom in `Mat_ C`. -/
def matRightUnitorHom
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (M : Mat_ C) :
    matTensorObj M matTensorUnit ⟶ M :=
  fun (i, ()) j =>
    if h : i = j then
      eqToHom (by subst h; rfl) ≫ (ρ_ (M.X j)).hom
    else 0

open scoped Classical in
/-- The right unitor inv in `Mat_ C`. -/
def matRightUnitorInv
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (M : Mat_ C) :
    M ⟶ matTensorObj M matTensorUnit :=
  fun i (j, ()) =>
    if h : i = j then
      (ρ_ (M.X i)).inv ≫ eqToHom (by subst h; rfl)
    else 0

/-! ### Isomorphism proofs for the structural morphisms

Diagonal ≫ diagonal collapses to a single summand: all off-diagonal entries
in the intermediate sum vanish.  `Finset.sum_eq_single_of_mem` identifies the
unique nonzero term, and the on-diagonal entry then simplifies. -/

open scoped Classical in
private theorem matAssoc_hom_inv
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (M N K : Mat_ C) :
    matAssocHom M N K ≫ matAssocInv M N K = 𝟙 _ := by
  apply Mat_.hom_ext
  intro ⟨⟨i, j⟩, k⟩ ⟨⟨i', j'⟩, k'⟩
  simp only [Mat_.comp_apply, Mat_.id_apply, matAssocHom, matAssocInv]
  rw [Finset.sum_eq_single_of_mem (i, (j, k)) (Finset.mem_univ _)]
  · -- ═══ On-diagonal term ═══
    simp only [dite_true, eqToHom_refl, id_comp]
    by_cases hi : i = i' <;> by_cases hj : j = j' <;> by_cases hk : k = k'
    · subst hi; subst hj; subst hk
      simp [eqToHom_refl, id_comp, Iso.hom_inv_id]
    all_goals simp_all [Prod.mk.injEq]
  · -- ═══ Off-diagonal terms ═══
    intro ⟨a, b, c⟩ _ hne
    have h : ¬(i = a ∧ j = b ∧ k = c) :=
      by rintro ⟨rfl, rfl, rfl⟩; exact hne rfl
    rcases not_and_or.mp h with h1 | h1
    · simp [h1, zero_comp]
    · rcases not_and_or.mp h1 with h2 | h2
      · simp [h2, zero_comp]
      · simp [h2, zero_comp]

open scoped Classical in
private theorem matAssoc_inv_hom
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (M N K : Mat_ C) :
    matAssocInv M N K ≫ matAssocHom M N K = 𝟙 _ := by
  apply Mat_.hom_ext
  intro ⟨i, j, k⟩ ⟨i', j', k'⟩
  simp only [Mat_.comp_apply, Mat_.id_apply, matAssocInv, matAssocHom]
  rw [Finset.sum_eq_single_of_mem ((i, j), k) (Finset.mem_univ _)]
  · simp only [dite_true, eqToHom_refl, id_comp]
    by_cases hi : i = i' <;> by_cases hj : j = j' <;> by_cases hk : k = k'
    · subst hi; subst hj; subst hk
      simp [eqToHom_refl, id_comp, Iso.inv_hom_id]
    all_goals simp_all [Prod.mk.injEq]
  · intro ⟨⟨a, b⟩, c⟩ _ hne
    have h : ¬(i = a ∧ j = b ∧ k = c) :=
      by rintro ⟨rfl, rfl, rfl⟩; exact hne rfl
    rcases not_and_or.mp h with h1 | h1
    · simp [h1, zero_comp]
    · rcases not_and_or.mp h1 with h2 | h2
      · simp [h2, zero_comp]
      · simp [h2, zero_comp]

open scoped Classical in
private theorem matLeftUnitor_hom_inv
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (M : Mat_ C) :
    matLeftUnitorHom M ≫ matLeftUnitorInv M = 𝟙 _ := by
  apply Mat_.hom_ext
  intro ⟨⟨⟩, i⟩ ⟨⟨⟩, j⟩
  simp only [Mat_.comp_apply, Mat_.id_apply, matLeftUnitorHom, matLeftUnitorInv]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
  · simp only [dite_true, eqToHom_refl, id_comp]
    by_cases h : i = j
    · subst h; simp [eqToHom_refl, comp_id, Iso.hom_inv_id]
    · simp [h, Prod.mk.injEq]
  · intro b _ hb
    have : ¬(i = b) := fun h => hb h.symm
    simp [this, zero_comp]

open scoped Classical in
private theorem matLeftUnitor_inv_hom
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (M : Mat_ C) :
    matLeftUnitorInv M ≫ matLeftUnitorHom M = 𝟙 _ := by
  apply Mat_.hom_ext
  intro i j
  simp only [Mat_.comp_apply, Mat_.id_apply, matLeftUnitorInv, matLeftUnitorHom]
  rw [Finset.sum_eq_single_of_mem ((), i) (Finset.mem_univ _)]
  · simp only [dite_true, eqToHom_refl]
    by_cases h : i = j
    · subst h; simp [eqToHom_refl, id_comp, comp_id, Iso.inv_hom_id]
    · simp [h]
  · intro ⟨⟨⟩, b⟩ _ hb
    have : ¬(i = b) := fun h => hb (by subst h; rfl)
    simp [this, zero_comp]

open scoped Classical in
private theorem matRightUnitor_hom_inv
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (M : Mat_ C) :
    matRightUnitorHom M ≫ matRightUnitorInv M = 𝟙 _ := by
  apply Mat_.hom_ext
  intro ⟨i, ⟨⟩⟩ ⟨j, ⟨⟩⟩
  simp only [Mat_.comp_apply, Mat_.id_apply, matRightUnitorHom,
    matRightUnitorInv]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
  · simp only [dite_true, eqToHom_refl, id_comp]
    by_cases h : i = j
    · subst h; simp [eqToHom_refl, comp_id, Iso.hom_inv_id]
    · simp [h, Prod.mk.injEq]
  · intro b _ hb
    have : ¬(i = b) := fun h => hb h.symm
    simp [this, zero_comp]

open scoped Classical in
private theorem matRightUnitor_inv_hom
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (M : Mat_ C) :
    matRightUnitorInv M ≫ matRightUnitorHom M = 𝟙 _ := by
  apply Mat_.hom_ext
  intro i j
  simp only [Mat_.comp_apply, Mat_.id_apply, matRightUnitorInv,
    matRightUnitorHom]
  rw [Finset.sum_eq_single_of_mem (i, ()) (Finset.mem_univ _)]
  · simp only [dite_true, eqToHom_refl]
    by_cases h : i = j
    · subst h; simp [eqToHom_refl, id_comp, comp_id, Iso.inv_hom_id]
    · simp [h]
  · intro ⟨b, ⟨⟩⟩ _ hb
    have : ¬(i = b) := fun h => hb (by subst h; rfl)
    simp [this, zero_comp]

/-- The associator isomorphism in `Mat_ C`. -/
def matAssociator [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (M N K : Mat_ C) :
    matTensorObj (matTensorObj M N) K ≅ matTensorObj M (matTensorObj N K) where
  hom := matAssocHom M N K
  inv := matAssocInv M N K
  hom_inv_id := by exact matAssoc_hom_inv M N K
  inv_hom_id := by exact matAssoc_inv_hom M N K

/-- The left unitor isomorphism in `Mat_ C`. -/
def matLeftUnitor [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (M : Mat_ C) :
    matTensorObj matTensorUnit M ≅ M where
  hom := matLeftUnitorHom M
  inv := matLeftUnitorInv M
  hom_inv_id := by exact matLeftUnitor_hom_inv M
  inv_hom_id := by exact matLeftUnitor_inv_hom M

/-- The right unitor isomorphism in `Mat_ C`. -/
def matRightUnitor [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    (M : Mat_ C) :
    matTensorObj M matTensorUnit ≅ M where
  hom := matRightUnitorHom M
  inv := matRightUnitorInv M
  hom_inv_id := by exact matRightUnitor_hom_inv M
  inv_hom_id := by exact matRightUnitor_inv_hom M

/-! ### `MonoidalCategoryStruct` instance -/

/-- The monoidal data on the matrix category: index products on
objects, Kronecker products on morphisms. -/
instance matMonoidalStruct
    [Category.{v} C] [Preadditive C] [MonoidalCategory C] :
    MonoidalCategoryStruct (Mat_ C) where
  tensorObj := matTensorObj
  whiskerLeft M _ _ f := matTensorHom (𝟙 M) f
  whiskerRight f N := matTensorHom f (𝟙 N)
  tensorHom := matTensorHom
  tensorUnit := matTensorUnit
  associator := matAssociator
  leftUnitor := matLeftUnitor
  rightUnitor := matRightUnitor

/-! ### `MonoidalCategory` instance

We use `MonoidalCategory.ofTensorHom` which requires proofs of the interchange
law, naturality of structural isomorphisms, and the pentagon and triangle
coherence identities.  Each proof goes pointwise via `Mat_.hom_ext`, collapses
diagonal sums via `Finset.sum_eq_single_of_mem`, and reduces to the
corresponding axiom in `C`. -/

private theorem mat_id_tensorHom_id
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C]
    (M₁ M₂ : Mat_ C) :
    matTensorHom (𝟙 M₁) (𝟙 M₂) = 𝟙 (matTensorObj M₁ M₂) := by
  apply Mat_.hom_ext; intro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [matTensorHom, Mat_.id_apply]
  by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂
  · subst h₁; subst h₂
    simp [eqToHom_refl]
  · simp [h₂, tensor_zero]
  · simp [h₁, MonoidalPreadditive.zero_tensor]
  · simp [h₁, MonoidalPreadditive.zero_tensor]

private theorem mat_tensorHom_comp
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C]
    {M₁ N₁ K₁ M₂ N₂ K₂ : Mat_ C}
    (f₁ : M₁ ⟶ N₁) (f₂ : M₂ ⟶ N₂) (g₁ : N₁ ⟶ K₁) (g₂ : N₂ ⟶ K₂) :
    matTensorHom f₁ f₂ ≫ matTensorHom g₁ g₂ = matTensorHom (f₁ ≫ g₁) (f₂ ≫ g₂)
      := by
  apply Mat_.hom_ext; intro ⟨i₁, i₂⟩ ⟨k₁, k₂⟩
  simp only [Mat_.comp_apply, matTensorHom]
  simp_rw [tensorHom_comp_tensorHom]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [← tensor_sum Finset.univ]
  rw [← sum_tensor Finset.univ]

open scoped Classical in
private theorem mat_associator_naturality
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    {M₁ M₂ M₃ N₁ N₂ N₃ : Mat_ C}
    (f₁ : M₁ ⟶ N₁) (f₂ : M₂ ⟶ N₂) (f₃ : M₃ ⟶ N₃) :
    matTensorHom (matTensorHom f₁ f₂) f₃ ≫ (matAssociator N₁ N₂ N₃).hom =
      (matAssociator M₁ M₂ M₃).hom ≫ matTensorHom f₁ (matTensorHom f₂ f₃) := by
  apply Mat_.hom_ext; intro ⟨⟨i₁, i₂⟩, i₃⟩ ⟨j₁, ⟨j₂, j₃⟩⟩
  simp only [Mat_.comp_apply, matTensorHom, matAssociator, matAssocHom]
  -- ═══ Collapse LHS sum ═══
  rw [Finset.sum_eq_single_of_mem ((j₁, j₂), j₃) (Finset.mem_univ _)]
  · -- ═══ Collapse RHS sum ═══
    rw [Finset.sum_eq_single_of_mem (i₁, (i₂, i₃)) (Finset.mem_univ _)]
    · simp only [dite_true, eqToHom_refl, id_comp]
      exact MonoidalCategory.associator_naturality (f₁ i₁ j₁) (f₂ i₂ j₂) (f₃ i₃
        j₃)
    · intro ⟨a, b, c⟩ _ hne
      have h : ¬(i₁ = a ∧ i₂ = b ∧ i₃ = c) :=
        by rintro ⟨rfl, rfl, rfl⟩; exact hne rfl
      rcases not_and_or.mp h with h1 | h1
      · simp [h1, zero_comp]
      · rcases not_and_or.mp h1 with h2 | h2 <;> simp [h2, zero_comp]
  · intro ⟨⟨a, b⟩, c⟩ _ hne
    have h : ¬(a = j₁ ∧ b = j₂ ∧ c = j₃) :=
      by rintro ⟨rfl, rfl, rfl⟩; exact hne rfl
    rcases not_and_or.mp h with h1 | h1
    · simp [h1]
    · rcases not_and_or.mp h1 with h2 | h2 <;> simp [h2]

open scoped Classical in
private theorem mat_leftUnitor_naturality
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    {M N : Mat_ C} (f : M ⟶ N) :
    matTensorHom (𝟙 matTensorUnit) f ≫ (matLeftUnitor N).hom =
      (matLeftUnitor M).hom ≫ f := by
  apply Mat_.hom_ext; intro ⟨⟨⟩, i⟩ j
  simp only [Mat_.comp_apply, matTensorHom, matLeftUnitor, matLeftUnitorHom]
  -- ═══ Collapse LHS sum over PUnit × N.ι ═══
  rw [Finset.sum_eq_single_of_mem (⟨⟨⟩, j⟩ : PUnit × N.ι) (Finset.mem_univ _)]
  · -- ═══ Collapse RHS sum over M.ι ═══
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
    · simp only [dite_true, eqToHom_refl, id_comp, Mat_.id_apply_self]
      rw [id_tensorHom]; exact leftUnitor_naturality (f i j)
    · intro b _ hb; simp [hb.symm]
  · intro ⟨⟨⟩, b⟩ _ hne
    have : b ≠ j := fun h => hne (by subst h; rfl)
    simp [this]

open scoped Classical in
private theorem mat_rightUnitor_naturality
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    {M N : Mat_ C} (f : M ⟶ N) :
    matTensorHom f (𝟙 matTensorUnit) ≫ (matRightUnitor N).hom =
      (matRightUnitor M).hom ≫ f := by
  apply Mat_.hom_ext; intro ⟨i, ⟨⟩⟩ j
  simp only [Mat_.comp_apply, matTensorHom, matRightUnitor, matRightUnitorHom]
  -- ═══ Collapse LHS sum over N.ι × PUnit ═══
  rw [Finset.sum_eq_single_of_mem (⟨j, ⟨⟩⟩ : N.ι × PUnit) (Finset.mem_univ _)]
  · -- ═══ Collapse RHS sum over M.ι ═══
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
    · simp only [dite_true, eqToHom_refl, id_comp, Mat_.id_apply_self]
      rw [tensorHom_id]; exact rightUnitor_naturality (f i j)
    · intro b _ hb; simp [hb.symm]
  · intro ⟨b, ⟨⟩⟩ _ hne
    have : b ≠ j := fun h => hne (by subst h; rfl)
    simp [this]

/-! ### Pentagon and triangle coherences

Both proofs go pointwise via `Mat_.hom_ext`, fully unfold the structural
morphisms to nested `dite` expressions, use `dite_comp`/`comp_dite`/
`tensor_dite`/`dite_tensor` to push compositions inside the `dite`s,
decompose product sums into iterated sums, and then collapse each sum
via `Finset.sum_dite_irrel` + `Fintype.sum_dite_eq'`.  After all sums are
gone both sides reduce to the corresponding coherence in `C`. -/

-- The pentagon is checked entrywise on a quadruple
-- index, so four matrix compositions expand.
open scoped Classical in
private theorem mat_pentagon
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C]
    (M₁ M₂ M₃ M₄ : Mat_ C) :
    matTensorHom (matAssociator M₁ M₂ M₃).hom (𝟙 M₄) ≫
      (matAssociator M₁ (matTensorObj M₂ M₃) M₄).hom ≫
        matTensorHom (𝟙 M₁) (matAssociator M₂ M₃ M₄).hom =
    (matAssociator (matTensorObj M₁ M₂) M₃ M₄).hom ≫
      (matAssociator M₁ M₂ (matTensorObj M₃ M₄)).hom := by
  apply Mat_.hom_ext
  intro ⟨⟨⟨i₁, i₂⟩, i₃⟩, i₄⟩ ⟨j₁, ⟨j₂, ⟨j₃, j₄⟩⟩⟩
  simp only [Mat_.comp_apply, matAssociator, matTensorHom, matAssocHom,
    Mat_.id_apply]
  -- ═══ Collapse LHS outer sum ═══
  rw [Finset.sum_eq_single_of_mem ((i₁, (i₂, i₃)), i₄) (Finset.mem_univ _)]
  · -- ═══ Simplify surviving outer term ═══
    simp only [dite_true, eqToHom_refl, id_comp]
    -- ═══ Collapse inner LHS sum ═══
    rw [Finset.sum_eq_single_of_mem (i₁, ((i₂, i₃), i₄)) (Finset.mem_univ _)]
    · -- ═══ Collapse RHS sum ═══
      simp only [dite_true, eqToHom_refl, id_comp]
      rw [Finset.sum_eq_single_of_mem ((i₁, i₂), (i₃, i₄)) (Finset.mem_univ _)]
      · -- ═══ On-diagonal: apply C-level pentagon ═══
        simp only [dite_true, eqToHom_refl, id_comp]
        by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
          by_cases h₃ : i₃ = j₃ <;> by_cases h₄ : i₄ = j₄
        · subst h₁; subst h₂; subst h₃; subst h₄
          simp only [dite_true, eqToHom_refl, id_comp]
          rw [id_tensorHom, tensorHom_id]
          exact pentagon (M₁.X i₁) (M₂.X i₂) (M₃.X i₃) (M₄.X i₄)
        all_goals simp_all
      · -- ═══ Off-diagonal RHS ═══
        intro ⟨⟨a, b⟩, ⟨c, d⟩⟩ _ hne
        have h : ¬(i₁ = a ∧ i₂ = b ∧ i₃ = c ∧ i₄ = d) := by
          rintro ⟨rfl, rfl, rfl, rfl⟩; exact hne rfl
        rcases not_and_or.mp h with h1 | h1
        · simp [h1]
        · rcases not_and_or.mp h1 with h2 | h2
          · simp [h2]
          · rcases not_and_or.mp h2 with h3 | h3 <;> simp [h3]
    · -- ═══ Off-diagonal inner LHS ═══
      intro ⟨a, ⟨⟨b, c⟩, d⟩⟩ _ hne
      have : ¬(i₁ = a) ∨ ¬((i₂, i₃) = (b, c)) ∨ ¬(i₄ = d) := by
        by_contra hall; push Not at hall
        exact hne (Prod.ext hall.1.symm (Prod.ext hall.2.1.symm hall.2.2.symm))
      rcases this with h | h | h <;> simp [h, zero_comp]
  · -- ═══ Off-diagonal LHS outer ═══
    intro ⟨⟨a, ⟨b, c⟩⟩, d⟩ _ hne
    have h : ¬(i₁ = a ∧ i₂ = b ∧ i₃ = c ∧ i₄ = d) := by
      rintro ⟨rfl, rfl, rfl, rfl⟩; exact hne rfl
    rcases not_and_or.mp h with h1 | h1
    · simp [h1]
    · rcases not_and_or.mp h1 with h2 | h2
      · simp [h2]
      · rcases not_and_or.mp h2 with h3 | h3 <;> simp [h3]

open scoped Classical in
private theorem mat_triangle
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C]
    (M₁ M₂ : Mat_ C) :
    (matAssociator M₁ matTensorUnit M₂).hom ≫
      matTensorHom (𝟙 M₁) (matLeftUnitor M₂).hom =
    matTensorHom (matRightUnitor M₁).hom (𝟙 M₂) := by
  apply Mat_.hom_ext
  intro ⟨⟨i₁, ⟨⟩⟩, i₂⟩ ⟨j₁, j₂⟩
  simp only [Mat_.comp_apply, matAssociator, matTensorHom, matAssocHom,
    matTensorUnit,
    matLeftUnitor, matLeftUnitorHom, matRightUnitor, matRightUnitorHom,
      Mat_.id_apply]
  -- ═══ Collapse the single composition sum ═══
  rw [Finset.sum_eq_single_of_mem (i₁, (PUnit.unit, i₂)) (Finset.mem_univ _)]
  · -- ═══ On-diagonal: simplify and reduce to C triangle ═══
    simp only [dite_true, eqToHom_refl, id_comp]
    by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂
    · subst h₁; subst h₂
      simp only [dite_true, eqToHom_refl, id_comp]
      rw [id_tensorHom, tensorHom_id]
      exact triangle (M₁.X i₁) (M₂.X i₂)
    all_goals simp_all
  · -- ═══ Off-diagonal ═══
    intro ⟨a, ⟨⟨⟩, b⟩⟩ _ hne
    have h : ¬(i₁ = a ∧ i₂ = b) := by rintro ⟨rfl, rfl⟩; exact hne rfl
    rcases not_and_or.mp h with h1 | h1 <;> simp [h1, zero_comp]

/-- The monoidal structure on `Mat_ C` induced by the componentwise tensor
product and Kronecker product of morphisms. -/
instance matMonoidal [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] : MonoidalCategory (Mat_ C) := by
  exact MonoidalCategory.ofTensorHom
    (id_tensorHom_id := by exact mat_id_tensorHom_id)
    (id_tensorHom := fun _ {_ _} _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := by exact mat_tensorHom_comp)
    (associator_naturality := by exact mat_associator_naturality)
    (leftUnitor_naturality := by exact mat_leftUnitor_naturality)
    (rightUnitor_naturality := by exact mat_rightUnitor_naturality)
    (pentagon := by exact mat_pentagon)
    (triangle := by exact mat_triangle)

/-- Composition through a right-associated triple tensor, entry by
entry. -/
theorem mat_comp_XYZ_apply [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    {A D : Mat_ C} (X Y Z : Mat_ C)
    (f : A ⟶ X ⊗ (Y ⊗ Z)) (g : X ⊗ (Y ⊗ Z) ⟶ D)
    (i : A.ι) (d : D.ι) :
    (f ≫ g) i d = ∑ ax : X.ι, ∑ ay : Y.ι, ∑ az : Z.ι,
      f i (ax, (ay, az)) ≫ g (ax, (ay, az)) d :=
  (Mat_.comp_apply f g i d).trans
    ((Fintype.sum_prod_type _).trans
      (Finset.sum_congr rfl fun _ _ => Fintype.sum_prod_type _))

/-- And through a left-associated one — the two sides of the
pentagon. -/
theorem mat_comp_XY_Z_apply
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    {A D : Mat_ C} (X Y Z : Mat_ C)
    (f : A ⟶ (X ⊗ Y) ⊗ Z) (g : (X ⊗ Y) ⊗ Z ⟶ D)
    (i : A.ι) (d : D.ι) :
    (f ≫ g) i d = ∑ ax : X.ι, ∑ ay : Y.ι, ∑ az : Z.ι,
      f i ((ax, ay), az) ≫ g ((ax, ay), az) d :=
  (Mat_.comp_apply f g i d).trans
    ((Fintype.sum_prod_type _).trans (Fintype.sum_prod_type _))

/-- Composition through a tensor of two objects, entry by entry. -/
theorem mat_comp_tensor_apply
    [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    {A : Mat_ C} {B₁ B₂ : Mat_ C} {D : Mat_ C}
    (f : A ⟶ B₁ ⊗ B₂) (g : B₁ ⊗ B₂ ⟶ D) (i : A.ι) (k : D.ι) :
    (f ≫ g) i k = ∑ j₁ : B₁.ι, ∑ j₂ : B₂.ι,
      f i (j₁, j₂) ≫ g (j₁, j₂) k :=
  (Mat_.comp_apply f g i k).trans (Fintype.sum_prod_type _)

end RS

end
