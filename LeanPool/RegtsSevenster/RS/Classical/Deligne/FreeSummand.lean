/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreeModAdjoint
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.MixShuffle

/-!
# Free summands of free mixed modules

Over an algebra whose unit is a scalar, the free-module functor is
full and faithful on the mixed sums of copies of the tensor unit
and of an odd line, idempotent endomorphisms of those mixed sums
split off further mixed sums, and consequently a direct summand of
a free mixed module is again a free mixed module.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

/-! ## Idempotent complex matrices split -/

section Matrices

/-- An idempotent endomorphism of a finite-dimensional coordinate
space factors through a smaller coordinate space. -/
theorem exists_split_of_linear_idem {n : ℕ}
    (f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) (hf : f ∘ₗ f = f) :
    ∃ (r : ℕ) (s : (Fin r → ℂ) →ₗ[ℂ] (Fin n → ℂ))
      (t : (Fin n → ℂ) →ₗ[ℂ] (Fin r → ℂ)),
      s ∘ₗ t = f ∧ t ∘ₗ s = LinearMap.id := by
  classical
  have hff : ∀ y, f (f y) = f y := fun y =>
    congrFun
      (congrArg (fun g : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) => ⇑g) hf) y
  have hU : ∀ u : LinearMap.range f, f ↑u = ↑u := by
    intro u
    obtain ⟨y, hy⟩ := LinearMap.mem_range.1 u.2
    rw [← hy, hff]
  obtain ⟨r, ⟨b⟩⟩ :
      ∃ r : ℕ,
        Nonempty (Module.Basis (Fin r) ℂ (LinearMap.range f)) :=
    ⟨_, ⟨Module.finBasis ℂ _⟩⟩
  refine ⟨r, (LinearMap.range f).subtype ∘ₗ
      b.equivFun.symm.toLinearMap,
    b.equivFun.toLinearMap ∘ₗ f.rangeRestrict, ?_, ?_⟩
  · refine LinearMap.ext fun x => ?_
    change ((b.equivFun.symm (b.equivFun (f.rangeRestrict x)) :
      LinearMap.range f) : Fin n → ℂ) = f x
    rw [LinearEquiv.symm_apply_apply]
    rfl
  · refine LinearMap.ext fun w => ?_
    have h1 : f.rangeRestrict
        ((b.equivFun.symm w : LinearMap.range f) : Fin n → ℂ)
        = b.equivFun.symm w := Subtype.ext (hU _)
    change b.equivFun (f.rangeRestrict
      ((b.equivFun.symm w : LinearMap.range f) : Fin n → ℂ)) = w
    rw [h1, LinearEquiv.apply_symm_apply]

/-- **An idempotent complex square matrix splits** through a
rectangular pair of matrices. -/
theorem exists_split_of_matrix_idem {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : M * M = M) :
    ∃ (r : ℕ) (S : Matrix (Fin n) (Fin r) ℂ)
      (T : Matrix (Fin r) (Fin n) ℂ), S * T = M ∧ T * S = 1 := by
  obtain ⟨r, s, t, hst, hts⟩ :=
    exists_split_of_linear_idem (Matrix.toLin' M)
      (by rw [← Matrix.toLin'_mul, hM])
  refine ⟨r, LinearMap.toMatrix' s, LinearMap.toMatrix' t, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hst, LinearMap.toMatrix'_toLin']
  · rw [← LinearMap.toMatrix'_comp, hts, LinearMap.toMatrix'_id]

end Matrices

/-! ## Matrix calculus for biproducts -/

section Biprod

variable {D : Type u}

/-- **The matrix of a composite is the product of the matrices.** -/
theorem components_comp [Category.{v} D] [Preadditive D] [HasFiniteBiproducts D]
    {J K M : Type} [Finite J] [Fintype K]
    [Finite M] {f : J → D} {g : K → D} {h : M → D}
    (x : ⨁ f ⟶ ⨁ g) (y : ⨁ g ⟶ ⨁ h) (j : J) (m : M) :
    biproduct.components (x ≫ y) j m =
      ∑ k : K, biproduct.components x j k ≫
        biproduct.components y k m := by
  classical
  let := Fintype.ofFinite J
  let := Fintype.ofFinite M
  have key : x ≫ y = ∑ k : K, (x ≫ biproduct.π g k) ≫
      (biproduct.ι g k ≫ y) := by
    calc x ≫ y
        = x ≫ (∑ k : K, biproduct.π g k ≫ biproduct.ι g k) ≫ y := by
          rw [biproduct.total, Category.id_comp]
      _ = ∑ k : K, (x ≫ biproduct.π g k) ≫ (biproduct.ι g k ≫ y) := by
          rw [Preadditive.sum_comp, Preadditive.comp_sum]
          exact Finset.sum_congr rfl fun k _ => by
            simp only [Category.assoc]
  simp only [biproduct.components, key, Preadditive.comp_sum,
    Preadditive.sum_comp, Category.assoc]

/-- Two maps of biproducts with the same matrix agree. -/
theorem hom_ext_components
    [Category.{v} D] [Preadditive D] [HasFiniteBiproducts D]
    {J K : Type} [Finite J] [Finite K]
    {f : J → D} {g : K → D} (x y : ⨁ f ⟶ ⨁ g)
    (h : ∀ j k, biproduct.components x j k =
      biproduct.components y j k) : x = y := by
  classical
  let := Fintype.ofFinite J
  let := Fintype.ofFinite K
  rw [← biproduct.components_matrix x, ← biproduct.components_matrix y]
  exact congrArg biproduct.matrix (funext fun j => funext fun k => h j k)

/-- The diagonal entries of the identity matrix. -/
theorem components_id_self
    [Category.{v} D] [Preadditive D] [HasFiniteBiproducts D]
    {J : Type} [Finite J]
    {f : J → D} (j : J) :
    biproduct.components (𝟙 (⨁ f)) j j = 𝟙 (f j) := by
  classical
  let := Fintype.ofFinite J
  simp [biproduct.components]

/-- The off-diagonal entries of the identity matrix vanish. -/
theorem components_id_ne
    [Category.{v} D] [Preadditive D] [HasFiniteBiproducts D]
    {J : Type} [Finite J]
    {f : J → D} {j k : J} (h : j ≠ k) :
    biproduct.components (𝟙 (⨁ f)) j k = 0 := by
  classical
  let := Fintype.ofFinite J
  simp [biproduct.components, biproduct.ι_π_ne _ h]

end Biprod

/-! ## Whiskering by the odd line is injective on morphisms -/

section Line

variable {D : Type u}

/-- Whiskering an object twice by the line returns the object. -/
noncomputable def OddLine.rot
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] (L : OddLine D)
    (X : D) : (X ⊗ L.obj) ⊗ L.obj ≅ X :=
  α_ X L.obj L.obj ≪≫ whiskerLeftIso X L.sq ≪≫ ρ_ X

theorem OddLine.rot_hom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] (L : OddLine D)
    (X : D) :
    (L.rot X).hom =
      (α_ X L.obj L.obj).hom ≫ X ◁ L.sq.hom ≫ (ρ_ X).hom :=
  rfl

/-- Whiskering a morphism twice by the line conjugates it. -/
@[reassoc]
theorem OddLine.whiskerRight_rot
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] (L : OddLine D)
    {X Y : D} (f : X ⟶ Y) :
    ((f ▷ L.obj) ▷ L.obj) ≫ (L.rot Y).hom = (L.rot X).hom ≫ f := by
  simp only [rot_hom, Category.assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
    rightUnitor_naturality]

theorem OddLine.whiskerRight_whiskerRight
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] (L : OddLine D)
    {X Y : D} (f : X ⟶ Y) :
    (f ▷ L.obj) ▷ L.obj = (L.rot X).hom ≫ f ≫ (L.rot Y).inv := by
  rw [← Category.assoc, ← L.whiskerRight_rot f, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- Double whiskering by the line is undone by the rotation. -/
theorem OddLine.rot_whiskerRight
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] (L : OddLine D)
    {X Y : D} (f : X ⟶ Y) :
    (L.rot X).inv ≫ ((f ▷ L.obj) ▷ L.obj) ≫ (L.rot Y).hom = f := by
  rw [L.whiskerRight_whiskerRight, Category.assoc,
    Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- **Whiskering by the odd line is injective on morphisms.** -/
theorem OddLine.whiskerRight_injective
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] (L : OddLine D)
    {X Y : D} :
    Function.Injective (fun f : X ⟶ Y => f ▷ L.obj) := by
  intro f g h
  have h' : f ▷ L.obj = g ▷ L.obj := h
  rw [← L.rot_whiskerRight f, ← L.rot_whiskerRight g, h']

/-- A morphism killed by whiskering with the line vanishes. -/
theorem OddLine.eq_zero_of_whiskerRight
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] (L : OddLine D)
    {X Y : D} (f : X ⟶ Y)
    (h : f ▷ L.obj = 0) : f = 0 := by
  refine L.whiskerRight_injective ?_
  change f ▷ L.obj = (0 : X ⟶ Y) ▷ L.obj
  rw [h, MonoidalPreadditive.zero_whiskerRight]

end Line

/-! ## Elementary cancellation helpers -/

section Cancel

variable {D : Type u}

/-- A morphism sandwiched between isomorphisms vanishes only if it
vanishes. -/
theorem eq_zero_of_iso_comp [Category.{v} D] [Preadditive D]
    {W X Y Z : D} (a : W ≅ X) (f : X ⟶ Y)
    (b : Y ≅ Z) (h : a.hom ≫ f ≫ b.hom = 0) : f = 0 := by
  have h2 := congrArg (fun k : W ⟶ Z => a.inv ≫ k ≫ b.inv) h
  simpa using h2

/-- Scalars are determined by their action on a nonzero
morphism. -/
theorem smul_left_cancel_of_ne_zero
    [Category.{v} D] [Preadditive D] [Linear ℂ D]
    {X Y : D} {a b : ℂ} {f : X ⟶ Y}
    (hf : f ≠ 0) (h : a • f = b • f) : a = b := by
  by_contra hne
  refine hf ?_
  have h0 : (a - b) • f = 0 := by rw [sub_smul, h, sub_self]
  have h1 := congrArg (fun z : X ⟶ Y => (a - b)⁻¹ • z) h0
  simpa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hne)] using h1

end Cancel

/-! ## The unit of the free module -/

section Unit

variable {D : Type u}

/-- The unit of the free module on an object, read in the ambient
category. -/
noncomputable def algUnitHom
    [Category.{v} D] [MonoidalCategory D] (R : D) [MonObj R]
    (W : D) : W ⟶ R ⊗ W :=
  (λ_ W).inv ≫ η[R] ▷ W

/-- The unit of the free module is natural. -/
@[reassoc]
theorem algUnitHom_naturality
    [Category.{v} D] [MonoidalCategory D] (R : D) [MonObj R]
    {W W' : D} (k : W ⟶ W') :
    algUnitHom R W ≫ (R ◁ k) = k ≫ algUnitHom R W' := by
  rw [algUnitHom, algUnitHom, Category.assoc, ← whisker_exchange,
    ← leftUnitor_inv_naturality_assoc]

/-- At the tensor unit the free-module unit is the algebra unit. -/
theorem algUnitHom_unit
    [Category.{v} D] [MonoidalCategory D] (R : D) [MonObj R] :
    algUnitHom R (𝟙_ D) ≫ (ρ_ R).hom = η[R] := by
  rw [algUnitHom, Category.assoc, rightUnitor_naturality,
    ← unitors_equal, Iso.inv_hom_id_assoc]

/-- **Postcomposition with the free-module unit is bijective.** -/
def UnitBij [Category.{v} D] [MonoidalCategory D] (R : D) [MonObj R]
    (V W : D) : Prop :=
  Function.Bijective (fun f : V ⟶ W => f ≫ algUnitHom R W)

/-- The bijectivity statement passes to biproducts in the
target. -/
theorem unitBij_biproduct_right
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D] (R : D) [MonObj R]
    {J : Type} [Finite J]
    (V : D) (g : J → D)
    (h : ∀ k, UnitBij R V (g k)) : UnitBij R V (⨁ g) := by
  classical
  let := Fintype.ofFinite J
  constructor
  · intro x y hxy
    have hxy' : x ≫ algUnitHom R (⨁ g) = y ≫ algUnitHom R (⨁ g) := hxy
    refine biproduct.hom_ext _ _ fun k => ?_
    refine (h k).1 ?_
    change (x ≫ biproduct.π g k) ≫ algUnitHom R (g k) =
      (y ≫ biproduct.π g k) ≫ algUnitHom R (g k)
    rw [Category.assoc, Category.assoc, ← algUnitHom_naturality,
      ← Category.assoc, ← Category.assoc, hxy']
  · intro y
    choose f hf using fun k => (h k).2 (y ≫ (R ◁ biproduct.π g k))
    have hf' : ∀ k : J, f k ≫ algUnitHom R (g k) =
        y ≫ (R ◁ biproduct.π g k) := hf
    refine ⟨∑ k : J, f k ≫ biproduct.ι g k, ?_⟩
    change (∑ k : J, f k ≫ biproduct.ι g k) ≫ algUnitHom R (⨁ g) = y
    rw [Preadditive.sum_comp]
    have step : ∀ k : J, (f k ≫ biproduct.ι g k) ≫ algUnitHom R (⨁ g)
        = y ≫ (R ◁ (biproduct.π g k ≫ biproduct.ι g k)) := by
      intro k
      rw [Category.assoc, ← algUnitHom_naturality, ← Category.assoc,
        hf' k, Category.assoc,
        ← MonoidalCategory.whiskerLeft_comp]
    rw [Finset.sum_congr rfl fun k _ => step k,
      ← Preadditive.comp_sum, ← whiskerLeft_sum R Finset.univ
        (fun k : J => biproduct.π g k ≫ biproduct.ι g k),
      biproduct.total, MonoidalCategory.whiskerLeft_id,
      Category.comp_id]

/-- The bijectivity statement passes to biproducts in the
source. -/
theorem unitBij_biproduct_left
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasFiniteBiproducts D] (R : D) [MonObj R]
    {J : Type} [Finite J]
    (f : J → D) (W : D)
    (h : ∀ j, UnitBij R (f j) W) : UnitBij R (⨁ f) W := by
  classical
  let := Fintype.ofFinite J
  constructor
  · intro x y hxy
    have hxy' : x ≫ algUnitHom R W = y ≫ algUnitHom R W := hxy
    refine biproduct.hom_ext' _ _ fun j => ?_
    refine (h j).1 ?_
    change (biproduct.ι f j ≫ x) ≫ algUnitHom R W =
      (biproduct.ι f j ≫ y) ≫ algUnitHom R W
    rw [Category.assoc, Category.assoc, hxy']
  · intro y
    choose g hg using fun j => (h j).2 (biproduct.ι f j ≫ y)
    have hg' : ∀ j : J, g j ≫ algUnitHom R W = biproduct.ι f j ≫ y :=
      hg
    refine ⟨∑ j : J, biproduct.π f j ≫ g j, ?_⟩
    change (∑ j : J, biproduct.π f j ≫ g j) ≫ algUnitHom R W = y
    rw [Preadditive.sum_comp]
    have step : ∀ j : J,
        (biproduct.π f j ≫ g j) ≫ algUnitHom R W =
          (biproduct.π f j ≫ biproduct.ι f j) ≫ y := by
      intro j
      rw [Category.assoc, hg' j, ← Category.assoc]
    rw [Finset.sum_congr rfl fun j _ => step j,
      ← Preadditive.sum_comp, biproduct.total, Category.id_comp]

end Unit

/-! ## The atomic hom-sets -/

section Atoms

variable {D : Type u}

/-- **Endomorphisms of the odd line are scalars** when the
endomorphisms of the tensor unit are. -/
theorem OddLine.hom_line_scalar
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D)
    (hsc : ∀ g : 𝟙_ D ⟶ 𝟙_ D, ∃ c : ℂ, g = c • 𝟙 (𝟙_ D))
    (f : L.obj ⟶ L.obj) : ∃ c : ℂ, f = c • 𝟙 L.obj := by
  obtain ⟨c, hc⟩ := hsc (L.sq.inv ≫ (f ▷ L.obj) ≫ L.sq.hom)
  refine ⟨c, L.whiskerRight_injective ?_⟩
  change f ▷ L.obj = (c • 𝟙 L.obj) ▷ L.obj
  rw [MonoidalLinear.smul_whiskerRight,
    MonoidalCategory.id_whiskerRight]
  refine (Iso.cancel_iso_hom_right _ _ L.sq).mp ?_
  have h1 : (f ▷ L.obj) ≫ L.sq.hom = L.sq.hom ≫ (c • 𝟙 (𝟙_ D)) := by
    rw [← hc, Iso.hom_inv_id_assoc]
  rw [h1, Linear.comp_smul, Category.comp_id, Linear.smul_comp,
    Category.id_comp]

/-- **Maps from the tensor unit to the odd line vanish** when maps
the other way do. -/
theorem OddLine.hom_unit_line_eq_zero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] (L : OddLine D)
    (hLU : ∀ g : L.obj ⟶ 𝟙_ D, g = 0) (f : 𝟙_ D ⟶ L.obj) : f = 0 := by
  refine L.eq_zero_of_whiskerRight f ?_
  exact eq_zero_of_iso_comp (λ_ L.obj).symm _ L.sq (hLU _)

/-- Maps from the tensor unit into the free module on the line
vanish. -/
theorem hom_unit_freeLine_eq_zero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] (L : OddLine D) (R : D)
    (hLR : ∀ f : L.obj ⟶ R, f = 0) (g : 𝟙_ D ⟶ R ⊗ L.obj) :
    g = 0 := by
  refine L.eq_zero_of_whiskerRight g ?_
  exact eq_zero_of_iso_comp (λ_ L.obj).symm _ (L.rot R) (hLR _)

/-- Maps from the line into the free module on the tensor unit
vanish. -/
theorem hom_line_freeUnit_eq_zero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] (L : OddLine D) (R : D)
    (hLR : ∀ f : L.obj ⟶ R, f = 0) (g : L.obj ⟶ R ⊗ 𝟙_ D) :
    g = 0 := by
  refine (Iso.cancel_iso_hom_right _ _ (ρ_ R)).mp ?_
  rw [Limits.zero_comp]
  exact hLR _

/-- The free-module unit at the line, transported through the
rotation, is the algebra unit. -/
theorem algUnitHom_line
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] (L : OddLine D) (R : D) [MonObj R] :
    ((algUnitHom R L.obj) ▷ L.obj) ≫ (L.rot R).hom
      = L.sq.hom ≫ η[R] := by
  have hcoh : ((λ_ L.obj).inv ▷ L.obj)
      ≫ (α_ (𝟙_ D) L.obj L.obj).hom
      = (λ_ (L.obj ⊗ L.obj)).inv := by monoidal
  calc ((algUnitHom R L.obj) ▷ L.obj) ≫ (L.rot R).hom
      = ((λ_ L.obj).inv ▷ L.obj) ≫ (((η[R] ▷ L.obj) ▷ L.obj)
          ≫ (α_ R L.obj L.obj).hom)
          ≫ (R ◁ L.sq.hom) ≫ (ρ_ R).hom := by
        rw [algUnitHom, comp_whiskerRight, L.rot_hom]
        simp only [Category.assoc]
    _ = ((λ_ L.obj).inv ▷ L.obj) ≫ ((α_ (𝟙_ D) L.obj L.obj).hom
          ≫ (η[R] ▷ (L.obj ⊗ L.obj)))
          ≫ (R ◁ L.sq.hom) ≫ (ρ_ R).hom := by
        rw [associator_naturality_left]
    _ = algUnitHom R (L.obj ⊗ L.obj)
          ≫ (R ◁ L.sq.hom) ≫ (ρ_ R).hom := by
        rw [algUnitHom, ← hcoh]
        simp only [Category.assoc]
    _ = L.sq.hom ≫ algUnitHom R (𝟙_ D) ≫ (ρ_ R).hom := by
        rw [← Category.assoc, algUnitHom_naturality, Category.assoc]
    _ = L.sq.hom ≫ η[R] := by rw [algUnitHom_unit]

/-- The free-module unit at the tensor unit is nonzero. -/
theorem algUnitHom_unit_ne_zero
    [Category.{v} D] [MonoidalCategory D] [Preadditive D] (R : D) [MonObj R]
    (hη : η[R] ≠ 0) :
    algUnitHom R (𝟙_ D) ≠ 0 := fun h =>
  hη (by rw [← algUnitHom_unit, h, Limits.zero_comp])

/-- The free-module unit at the line is nonzero. -/
theorem algUnitHom_line_ne_zero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] (L : OddLine D) (R : D)
    [MonObj R]
    (hη : η[R] ≠ 0) :
    algUnitHom R L.obj ≠ 0 := by
  intro h
  refine hη ?_
  have h2 : L.sq.hom ≫ η[R] = 0 := by
    rw [← algUnitHom_line L R, h,
      MonoidalPreadditive.zero_whiskerRight, Limits.zero_comp]
  have h3 := congrArg (fun k : L.obj ⊗ L.obj ⟶ R => L.sq.inv ≫ k) h2
  simpa using h3

/-- **Maps from the line into the free module on the line are
scalar multiples of the unit.** -/
theorem hom_line_freeLine_scalar
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R]
    (halg : ∀ f : 𝟙_ D ⟶ R, ∃ c : ℂ, f = c • η[R])
    (g : L.obj ⟶ R ⊗ L.obj) :
    ∃ c : ℂ, g = c • algUnitHom R L.obj := by
  obtain ⟨c, hc⟩ := halg (L.sq.inv ≫ (g ▷ L.obj) ≫ (L.rot R).hom)
  refine ⟨c, L.whiskerRight_injective ?_⟩
  change g ▷ L.obj = (c • algUnitHom R L.obj) ▷ L.obj
  rw [MonoidalLinear.smul_whiskerRight]
  refine (Iso.cancel_iso_hom_right _ _ (L.rot R)).mp ?_
  have h1 : (g ▷ L.obj) ≫ (L.rot R).hom
      = L.sq.hom ≫ (c • η[R]) := by
    rw [← hc, Iso.hom_inv_id_assoc]
  rw [h1, Linear.smul_comp, algUnitHom_line, Linear.comp_smul]

/-! ## Bijectivity at the atoms -/

/-- The unit-to-unit case. -/
theorem unitBij_unit_unit
    [Category.{v} D] [MonoidalCategory D] [Preadditive D] [Linear ℂ D]
    (R : D) [MonObj R]
    (hsc : ∀ f : 𝟙_ D ⟶ 𝟙_ D, ∃ c : ℂ, f = c • 𝟙 (𝟙_ D))
    (halg : ∀ f : 𝟙_ D ⟶ R, ∃ c : ℂ, f = c • η[R])
    (hη : η[R] ≠ 0) : UnitBij R (𝟙_ D) (𝟙_ D) := by
  constructor
  · intro x y hxy
    have hxy' : x ≫ algUnitHom R (𝟙_ D) = y ≫ algUnitHom R (𝟙_ D) :=
      hxy
    obtain ⟨a, ha⟩ := hsc x
    obtain ⟨b, hb⟩ := hsc y
    have hab : a = b := by
      refine smul_left_cancel_of_ne_zero
        (algUnitHom_unit_ne_zero R hη) ?_
      calc a • algUnitHom R (𝟙_ D)
          = x ≫ algUnitHom R (𝟙_ D) := by
            rw [ha, Linear.smul_comp, Category.id_comp]
        _ = y ≫ algUnitHom R (𝟙_ D) := hxy'
        _ = b • algUnitHom R (𝟙_ D) := by
            rw [hb, Linear.smul_comp, Category.id_comp]
    rw [ha, hb, hab]
  · intro y
    obtain ⟨c, hc⟩ := halg (y ≫ (ρ_ R).hom)
    refine ⟨c • 𝟙 (𝟙_ D), ?_⟩
    change (c • 𝟙 (𝟙_ D)) ≫ algUnitHom R (𝟙_ D) = y
    refine (Iso.cancel_iso_hom_right _ _ (ρ_ R)).mp ?_
    rw [Linear.smul_comp, Category.id_comp, Linear.smul_comp,
      algUnitHom_unit, hc]

/-- The unit-to-line case. -/
theorem unitBij_unit_line
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] (L : OddLine D) (R : D)
    [MonObj R]
    (hLU : ∀ f : L.obj ⟶ 𝟙_ D, f = 0)
    (hLR : ∀ f : L.obj ⟶ R, f = 0) : UnitBij R (𝟙_ D) L.obj := by
  constructor
  · intro x y _
    rw [L.hom_unit_line_eq_zero hLU x, L.hom_unit_line_eq_zero hLU y]
  · intro y
    refine ⟨0, ?_⟩
    change (0 : 𝟙_ D ⟶ L.obj) ≫ algUnitHom R L.obj = y
    rw [Limits.zero_comp]
    exact (hom_unit_freeLine_eq_zero L R hLR y).symm

/-- The line-to-unit case. -/
theorem unitBij_line_unit
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] (L : OddLine D) (R : D) [MonObj R]
    (hLU : ∀ f : L.obj ⟶ 𝟙_ D, f = 0)
    (hLR : ∀ f : L.obj ⟶ R, f = 0) : UnitBij R L.obj (𝟙_ D) := by
  constructor
  · intro x y _
    rw [hLU x, hLU y]
  · intro y
    refine ⟨0, ?_⟩
    change (0 : L.obj ⟶ 𝟙_ D) ≫ algUnitHom R (𝟙_ D) = y
    rw [Limits.zero_comp]
    exact (hom_line_freeUnit_eq_zero L R hLR y).symm

/-- The line-to-line case. -/
theorem unitBij_line_line
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R]
    (hsc : ∀ f : 𝟙_ D ⟶ 𝟙_ D, ∃ c : ℂ, f = c • 𝟙 (𝟙_ D))
    (halg : ∀ f : 𝟙_ D ⟶ R, ∃ c : ℂ, f = c • η[R])
    (hη : η[R] ≠ 0) : UnitBij R L.obj L.obj := by
  constructor
  · intro x y hxy
    have hxy' : x ≫ algUnitHom R L.obj = y ≫ algUnitHom R L.obj := hxy
    obtain ⟨a, ha⟩ := L.hom_line_scalar hsc x
    obtain ⟨b, hb⟩ := L.hom_line_scalar hsc y
    have hab : a = b := by
      refine smul_left_cancel_of_ne_zero
        (algUnitHom_line_ne_zero L R hη) ?_
      calc a • algUnitHom R L.obj = x ≫ algUnitHom R L.obj := by
            rw [ha, Linear.smul_comp, Category.id_comp]
        _ = y ≫ algUnitHom R L.obj := hxy'
        _ = b • algUnitHom R L.obj := by
            rw [hb, Linear.smul_comp, Category.id_comp]
    rw [ha, hb, hab]
  · intro y
    obtain ⟨c, hc⟩ := hom_line_freeLine_scalar L R halg y
    refine ⟨c • 𝟙 L.obj, ?_⟩
    change (c • 𝟙 L.obj) ≫ algUnitHom R L.obj = y
    rw [Linear.smul_comp, Category.id_comp, hc]

/-! ## Bijectivity at the mixed sums -/

/-- Bijectivity at a mixed target follows from the two atoms. -/
theorem unitBij_mix_right
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) (R : D) [MonObj R]
    (V : D)
    (h1 : UnitBij R V (𝟙_ D)) (h2 : UnitBij R V L.obj) (p q : ℕ) :
    UnitBij R V (L.mix p q) := by
  change UnitBij R V (⨁ L.mixFun p q)
  refine unitBij_biproduct_right R V (L.mixFun p q) ?_
  rintro (i | j)
  · exact h1
  · exact h2

/-- **Postcomposition with the free-module unit is bijective on
mixed sums.** -/
theorem unitBij_mix [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasFiniteBiproducts D] (L : OddLine D) (R : D)
    [MonObj R]
    (hsc : ∀ f : 𝟙_ D ⟶ 𝟙_ D, ∃ c : ℂ, f = c • 𝟙 (𝟙_ D))
    (hLU : ∀ f : L.obj ⟶ 𝟙_ D, f = 0)
    (halg : ∀ f : 𝟙_ D ⟶ R, ∃ c : ℂ, f = c • η[R])
    (hLR : ∀ f : L.obj ⟶ R, f = 0)
    (hη : η[R] ≠ 0) (p q p' q' : ℕ) :
    UnitBij R (L.mix p q) (L.mix p' q') := by
  change UnitBij R (⨁ L.mixFun p q) (L.mix p' q')
  refine unitBij_biproduct_left R (L.mixFun p q) (L.mix p' q') ?_
  rintro (i | j)
  · exact unitBij_mix_right L R (𝟙_ D)
      (unitBij_unit_unit R hsc halg hη)
      (unitBij_unit_line L R hLU hLR) p' q'
  · exact unitBij_mix_right L R L.obj
      (unitBij_line_unit L R hLU hLR)
      (unitBij_line_line L R hsc halg hη) p' q'

end Atoms

/-! ## The free-module functor on mixed sums -/

section Fullness

variable {D : Type u}

/-- Base change of a morphism corresponds, under the free–forgetful
adjunction, to postcomposition with the free-module unit. -/
theorem freeModHomEquiv_freeModMap
    [Category.{v} D] [MonoidalCategory D] (R : D) [MonObj R]
    {V W : D} (f : V ⟶ W) :
    freeModHomEquiv R V (freeMod R W) (freeModMap R f)
      = f ≫ algUnitHom R W := by
  change (λ_ V).inv ≫ (η[R] ▷ V) ≫ (R ◁ f) = f ≫ algUnitHom R W
  rw [← Category.assoc]
  exact algUnitHom_naturality R f

/-- **The free-module functor is full on mixed sums.** -/
theorem exists_preimage_freeModMap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasFiniteBiproducts D] (L : OddLine D) (R : D)
    [MonObj R]
    (hsc : ∀ f : 𝟙_ D ⟶ 𝟙_ D, ∃ c : ℂ, f = c • 𝟙 (𝟙_ D))
    (hLU : ∀ f : L.obj ⟶ 𝟙_ D, f = 0)
    (halg : ∀ f : 𝟙_ D ⟶ R, ∃ c : ℂ, f = c • η[R])
    (hLR : ∀ f : L.obj ⟶ R, f = 0)
    (hη : η[R] ≠ 0) (p q p' q' : ℕ)
    (g : freeMod R (L.mix p q) ⟶ freeMod R (L.mix p' q')) :
    ∃ f : L.mix p q ⟶ L.mix p' q', freeModMap R f = g := by
  obtain ⟨f, hf⟩ := (unitBij_mix L R hsc hLU halg hLR hη p q p' q').2
    (freeModHomEquiv R (L.mix p q) (freeMod R (L.mix p' q')) g)
  refine ⟨f, ?_⟩
  refine (freeModHomEquiv R (L.mix p q)
    (freeMod R (L.mix p' q'))).injective ?_
  rw [freeModHomEquiv_freeModMap]
  exact hf

/-- **The free-module functor is faithful on mixed sums.** -/
theorem freeModMap_injective_mix
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasFiniteBiproducts D] (L : OddLine D) (R : D)
    [MonObj R]
    (hsc : ∀ f : 𝟙_ D ⟶ 𝟙_ D, ∃ c : ℂ, f = c • 𝟙 (𝟙_ D))
    (hLU : ∀ f : L.obj ⟶ 𝟙_ D, f = 0)
    (halg : ∀ f : 𝟙_ D ⟶ R, ∃ c : ℂ, f = c • η[R])
    (hLR : ∀ f : L.obj ⟶ R, f = 0)
    (hη : η[R] ≠ 0) (p q p' q' : ℕ) :
    Function.Injective
      (fun f : L.mix p q ⟶ L.mix p' q' => freeModMap R f) := by
  intro f f' h
  have h' : freeModMap R f = freeModMap R f' := h
  refine (unitBij_mix L R hsc hLU halg hLR hη p q p' q').1 ?_
  change f ≫ algUnitHom R (L.mix p' q')
    = f' ≫ algUnitHom R (L.mix p' q')
  rw [← freeModHomEquiv_freeModMap, ← freeModHomEquiv_freeModMap, h']

/-- A nonzero algebra unit forces a nonzero identity on the tensor
unit. -/
theorem id_unit_ne_zero_of_unit
    [Category.{v} D] [MonoidalCategory D] [Preadditive D] (R : D) [MonObj R]
    (hη : η[R] ≠ 0) :
    𝟙 (𝟙_ D) ≠ 0 := fun h =>
  hη (by rw [← Category.id_comp η[R], h, Limits.zero_comp])

end Fullness

/-! ## Idempotents of mixed sums split -/

section Split

variable {D : Type u}

/-- The identity of the line is nonzero as soon as the identity of
the tensor unit is. -/
theorem OddLine.id_line_ne_zero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] (L : OddLine D)
    (hid : 𝟙 (𝟙_ D) ≠ 0) :
    𝟙 L.obj ≠ 0 := by
  intro h
  refine hid ?_
  have h2 : 𝟙 (L.obj ⊗ L.obj) = 0 := by
    rw [← MonoidalCategory.id_whiskerRight, h,
      MonoidalPreadditive.zero_whiskerRight]
  have h3 : 𝟙 (𝟙_ D) = L.sq.inv ≫ 𝟙 (L.obj ⊗ L.obj) ≫ L.sq.hom := by
    rw [Category.id_comp, Iso.inv_hom_id]
  rw [h3, h2, Limits.zero_comp, Limits.comp_zero]

/-- The entries of a block-diagonal matrix on a mixed sum. -/
noncomputable def OddLine.mixEntry
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [Linear ℂ D] (L : OddLine D)
    {p q p' q' : ℕ}
    (A : Matrix (Fin p) (Fin p') ℂ) (B : Matrix (Fin q) (Fin q') ℂ) :
    ∀ (j : Fin p ⊕ Fin q) (k : Fin p' ⊕ Fin q'),
      L.mixFun p q j ⟶ L.mixFun p' q' k
  | Sum.inl i, Sum.inl i' => A i i' • 𝟙 (𝟙_ D)
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr j, Sum.inr j' => B j j' • 𝟙 L.obj

/-- A pair of complex matrices as a morphism of mixed sums. -/
noncomputable def OddLine.mixMat
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [Linear ℂ D] [HasFiniteBiproducts D] (L : OddLine D)
    {p q p' q' : ℕ}
    (A : Matrix (Fin p) (Fin p') ℂ) (B : Matrix (Fin q) (Fin q') ℂ) :
    (⨁ L.mixFun p q) ⟶ (⨁ L.mixFun p' q') :=
  biproduct.matrix (L.mixEntry A B)

theorem OddLine.components_mixMat
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [Linear ℂ D] [HasFiniteBiproducts D] (L : OddLine D)
    {p q p' q' : ℕ}
    (A : Matrix (Fin p) (Fin p') ℂ) (B : Matrix (Fin q) (Fin q') ℂ)
    (j : Fin p ⊕ Fin q) (k : Fin p' ⊕ Fin q') :
    biproduct.components (L.mixMat A B) j k = L.mixEntry A B j k :=
  biproduct.matrix_components _ j k

/-- Scalar multiples of an identity compose by multiplication. -/
theorem sum_smul_id [Category.{v} D] [Preadditive D] [Linear ℂ D]
    {X : D} {J : Type} [Fintype J] (u v : J → ℂ) :
    ∑ x : J, (u x • 𝟙 X) ≫ (v x • 𝟙 X)
      = (∑ x : J, u x * v x) • 𝟙 X := by
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul]

/-- Block-diagonal matrices multiply blockwise. -/
theorem OddLine.mixEntry_comp
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [Linear ℂ D] (L : OddLine D)
    {p q p' q' p'' q'' : ℕ}
    (A : Matrix (Fin p) (Fin p') ℂ) (B : Matrix (Fin q) (Fin q') ℂ)
    (A' : Matrix (Fin p') (Fin p'') ℂ)
    (B' : Matrix (Fin q') (Fin q'') ℂ)
    (j : Fin p ⊕ Fin q) (k : Fin p'' ⊕ Fin q'') :
    ∑ m : Fin p' ⊕ Fin q',
        L.mixEntry A B j m ≫ L.mixEntry A' B' m k
      = L.mixEntry (A * A') (B * B') j k := by
  rcases j with i | jj <;> rcases k with i2 | j2 <;>
    rw [Fintype.sum_sum_type] <;>
    simp only [mixEntry,  Limits.comp_zero,
      Finset.sum_const_zero, add_zero, zero_add, Matrix.mul_apply]
  · exact sum_smul_id _ _
  · refine (congrArg₂ (· + ·) ?_ ?_).trans (zero_add 0)
    · apply Finset.sum_eq_zero
      intro a _
      exact Limits.comp_zero
    · apply Finset.sum_eq_zero
      intro a _
      exact Limits.zero_comp
  · refine (congrArg₂ (· + ·) ?_ ?_).trans (zero_add 0)
    · apply Finset.sum_eq_zero
      intro a _
      exact Limits.zero_comp
    · apply Finset.sum_eq_zero
      intro a _
      exact Limits.comp_zero
  · exact sum_smul_id _ _

/-- Composition of block matrices is matrix multiplication. -/
theorem OddLine.mixMat_comp
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [Linear ℂ D] [HasFiniteBiproducts D] (L : OddLine D)
    {p q p' q' p'' q'' : ℕ}
    (A : Matrix (Fin p) (Fin p') ℂ) (B : Matrix (Fin q) (Fin q') ℂ)
    (A' : Matrix (Fin p') (Fin p'') ℂ)
    (B' : Matrix (Fin q') (Fin q'') ℂ) :
    L.mixMat A B ≫ L.mixMat A' B' = L.mixMat (A * A') (B * B') := by
  refine hom_ext_components _ _ fun j k => ?_
  rw [components_comp]
  simp only [components_mixMat]
  exact L.mixEntry_comp A B A' B' j k

/-- The identity matrices give the identity morphism. -/
theorem OddLine.mixMat_one
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [Linear ℂ D] [HasFiniteBiproducts D] (L : OddLine D)
    (p q : ℕ) :
    L.mixMat (1 : Matrix (Fin p) (Fin p) ℂ)
        (1 : Matrix (Fin q) (Fin q) ℂ) = 𝟙 (⨁ L.mixFun p q) := by
  refine hom_ext_components _ _ fun j k => ?_
  rw [components_mixMat]
  by_cases h : j = k
  · subst h
    rw [components_id_self]
    rcases j with i | jj
    · change (1 : Matrix (Fin p) (Fin p) ℂ) i i • 𝟙 (𝟙_ D) = 𝟙 (𝟙_ D)
      rw [Matrix.one_apply_eq, one_smul]
    · change (1 : Matrix (Fin q) (Fin q) ℂ) jj jj • 𝟙 L.obj = 𝟙 L.obj
      rw [Matrix.one_apply_eq, one_smul]
  · rw [components_id_ne h]
    rcases j with i | jj
    · rcases k with i2 | j2
      · have hne : i ≠ i2 := fun hh => h (by rw [hh])
        change (1 : Matrix (Fin p) (Fin p) ℂ) i i2 • 𝟙 (𝟙_ D) = 0
        rw [Matrix.one_apply_ne hne, zero_smul]
      · rfl
    · rcases k with i2 | j2
      · rfl
      · have hne : jj ≠ j2 := fun hh => h (by rw [hh])
        change (1 : Matrix (Fin q) (Fin q) ℂ) jj j2 • 𝟙 L.obj = 0
        rw [Matrix.one_apply_ne hne, zero_smul]

/-- **Every endomorphism of a mixed sum is a pair of complex
matrices.** -/
theorem OddLine.exists_mixMat
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasFiniteBiproducts D] (L : OddLine D)
    (hsc : ∀ f : 𝟙_ D ⟶ 𝟙_ D, ∃ c : ℂ, f = c • 𝟙 (𝟙_ D))
    (hLU : ∀ f : L.obj ⟶ 𝟙_ D, f = 0)
    {p q : ℕ} (e : (⨁ L.mixFun p q) ⟶ (⨁ L.mixFun p q)) :
    ∃ (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ),
      e = L.mixMat A B := by
  choose A hA using fun i i' : Fin p =>
    hsc (biproduct.components e (Sum.inl i) (Sum.inl i'))
  choose B hB using fun j j' : Fin q =>
    L.hom_line_scalar hsc
      (biproduct.components e (Sum.inr j) (Sum.inr j'))
  refine ⟨A, B, hom_ext_components _ _ fun j k => ?_⟩
  erw [components_mixMat]
  rcases j with i | jj
  · rcases k with i2 | j2
    · exact hA i i2
    · exact L.hom_unit_line_eq_zero hLU _
  · rcases k with i2 | j2
    · exact hLU _
    · exact hB jj j2

/-- The pair of matrices is determined by the morphism. -/
theorem OddLine.mixMat_injective
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [HasFiniteBiproducts D] (L : OddLine D)
    (hid : 𝟙 (𝟙_ D) ≠ 0)
    {p q p' q' : ℕ} {A A' : Matrix (Fin p) (Fin p') ℂ}
    {B B' : Matrix (Fin q) (Fin q') ℂ}
    (h : L.mixMat A B = L.mixMat A' B') : A = A' ∧ B = B' := by
  constructor
  · ext i i'
    have h2 : L.mixEntry A B (Sum.inl i) (Sum.inl i')
        = L.mixEntry A' B' (Sum.inl i) (Sum.inl i') := by
      rw [← L.components_mixMat, ← L.components_mixMat, h]
    exact smul_left_cancel_of_ne_zero hid h2
  · ext j j'
    have h2 : L.mixEntry A B (Sum.inr j) (Sum.inr j')
        = L.mixEntry A' B' (Sum.inr j) (Sum.inr j') := by
      rw [← L.components_mixMat, ← L.components_mixMat, h]
    exact smul_left_cancel_of_ne_zero (L.id_line_ne_zero hid) h2

/-- **An idempotent endomorphism of a mixed sum splits off a mixed
sum.** -/
theorem exists_split_of_idem_mix
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasFiniteBiproducts D] (L : OddLine D)
    (hsc : ∀ f : 𝟙_ D ⟶ 𝟙_ D, ∃ c : ℂ, f = c • 𝟙 (𝟙_ D))
    (hLU : ∀ f : L.obj ⟶ 𝟙_ D, f = 0) (hid : 𝟙 (𝟙_ D) ≠ 0)
    {p q : ℕ} (e : L.mix p q ⟶ L.mix p q) (he : e ≫ e = e) :
    ∃ (p' q' : ℕ) (a : L.mix p' q' ⟶ L.mix p q)
      (b : L.mix p q ⟶ L.mix p' q'),
      a ≫ b = 𝟙 (L.mix p' q') ∧ b ≫ a = e := by
  obtain ⟨A, B, hAB⟩ := L.exists_mixMat hsc hLU e
  have hidem : L.mixMat (A * A) (B * B) = L.mixMat A B := by
    rw [← L.mixMat_comp, ← hAB]
    exact he
  obtain ⟨hAA, hBB⟩ := L.mixMat_injective hid hidem
  obtain ⟨p', S, T, hST, hTS⟩ := exists_split_of_matrix_idem A hAA
  obtain ⟨q', S', T', hST', hTS'⟩ := exists_split_of_matrix_idem B hBB
  have h1 : L.mixMat T T' ≫ L.mixMat S S'
      = 𝟙 (⨁ L.mixFun p' q') := by
    rw [L.mixMat_comp, hTS, hTS']
    exact L.mixMat_one p' q'
  have h2 : L.mixMat S S' ≫ L.mixMat T T' = e := by
    rw [L.mixMat_comp, hST, hST']
    exact hAB.symm
  exact ⟨p', q', L.mixMat T T', L.mixMat S S', h1, h2⟩

end Split

end RS
