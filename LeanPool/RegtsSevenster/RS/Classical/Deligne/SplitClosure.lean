/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.FibreRestrict
import LeanPool.RegtsSevenster.RS.Classical.Deligne.MixShuffleLine

/-!
# The objects split by a fixed algebra

An object is *split* by an algebra when its free module is
isomorphic to the free module on a mixed sum of copies of the unit
and of the odd line.  This file collects the closure properties of
that class: the unit and the odd line are split, and split objects
are closed under zero objects, finite biproducts and tensor
products.

The bookkeeping is entirely at the level of the mixed sums: the
free module functor carries binary biproducts to module biproducts
(`RS.freeModBiprodIso`) and tensor products to relative tensor
products (`RS.freeModTensorIso`), so each closure statement reduces
to an isomorphism of mixed sums in the ambient category, and those
are proved by peeling summands with `RS.OddLine.mixSuccIso` and
`RS.OddLine.mixLineSuccIso`.

The payoff is `RS.splitsOn_of_generator`: an algebra splitting a
tensor generator and its dual splits every embedded object, once
subquotients of split objects are known to be split.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v₂ u₂ v u

section FinBiproduct

variable {D : Type u}

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- The empty biproduct vanishes. -/
theorem isZero_biproductFinZero
    [Category.{v} D] [Preadditive D] [HasFiniteBiproducts D]
    (g : Fin 0 → D) : IsZero (⨁ g) := by
  rw [IsZero.iff_id_eq_zero]
  apply biproduct.hom_ext
  rintro ⟨_, hj⟩
  exact absurd hj (Nat.not_lt_zero _)

/-- The first inclusion misses the shifted projections. -/
@[reassoc]
theorem biproductFin_ι_zero_lift
    [Category.{v} D] [Preadditive D] [HasFiniteBiproducts D]
    {k : ℕ} (g : Fin (k + 1) → D) :
    biproduct.ι g 0 ≫
        (biproduct.lift fun i : Fin k => biproduct.π g i.succ) = 0 := by
  apply biproduct.hom_ext
  intro i
  rw [Category.assoc, biproduct.lift_π, zero_comp,
    biproduct.ι_π_ne _ (Fin.succ_ne_zero i).symm]

/-- A shifted inclusion meets the shifted projections diagonally. -/
@[reassoc]
theorem biproductFin_ι_succ_lift
    [Category.{v} D] [Preadditive D] [HasFiniteBiproducts D]
    {k : ℕ} (g : Fin (k + 1) → D)
    (i : Fin k) :
    biproduct.ι g i.succ ≫
        (biproduct.lift fun i' : Fin k => biproduct.π g i'.succ) =
      biproduct.ι (fun i : Fin k => g i.succ) i := by
  apply biproduct.hom_ext
  intro i'
  rw [Category.assoc, biproduct.lift_π]
  by_cases hii : i = i'
  · subst hii
    rw [biproduct.ι_π_self, biproduct.ι_π_self]
  · rw [biproduct.ι_π_ne _ (fun hh => hii (Fin.succ_inj.mp hh)),
      biproduct.ι_π_ne _ hii]

/-- Peeling the first summand off a biproduct indexed by
`Fin (k + 1)`. -/
noncomputable def biprodPeelFinIso
    [Category.{v} D] [Preadditive D] [HasFiniteBiproducts D]
    {k : ℕ} (g : Fin (k + 1) → D) :
    (⨁ g) ≅ g 0 ⊞ (⨁ fun i : Fin k => g i.succ) where
  hom := biprod.lift (biproduct.π g 0)
    (biproduct.lift fun i : Fin k => biproduct.π g i.succ)
  inv := biprod.desc (biproduct.ι g 0)
    (biproduct.desc fun i : Fin k => biproduct.ι g i.succ)
  hom_inv_id := by
    apply biproduct.hom_ext'
    intro j
    refine Fin.cases ?_ (fun i => ?_) j <;>
      simp [biprod.lift_desc, biproductFin_ι_zero_lift_assoc,
        biproductFin_ι_succ_lift_assoc, Fin.succ_ne_zero]
  inv_hom_id := by
    apply biprod.hom_ext'
    · apply biprod.hom_ext
      · simp
      · simp [biproductFin_ι_zero_lift]
    · apply biproduct.hom_ext'
      intro i
      apply biprod.hom_ext
      · simp [Fin.succ_ne_zero]
      · simp [biproductFin_ι_succ_lift]

end FinBiproduct

/-! ## Mixed sums are closed under biproducts and tensors -/

section Mix

variable {D : Type u}

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- The mixed sum of one unit and no line is the unit. -/
noncomputable def OddLine.mixOneZeroIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) :
    L.mix 1 0 ≅ 𝟙_ D :=
  L.mixSuccIso 0 0 ≪≫ (isoBiprodZero L.isZero_mix_zero).symm

/-- The mixed sum of no unit and one line is the line. -/
noncomputable def OddLine.mixZeroOneIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) :
    L.mix 0 1 ≅ L.obj :=
  L.mixLineSuccIso 0 0 ≪≫ (isoBiprodZero L.isZero_mix_zero).symm

/-- **A biproduct of mixed sums is a mixed sum.** -/
theorem OddLine.exists_mix_biprod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) :
    ∀ p q p' q' : ℕ, ∃ a b : ℕ,
      Nonempty (L.mix p q ⊞ L.mix p' q' ≅ L.mix a b) := by
  intro p
  induction p with
  | zero =>
    intro q
    induction q with
    | zero =>
      intro p' q'
      exact ⟨p', q',
        ⟨(isoZeroBiprod L.isZero_mix_zero).symm⟩⟩
    | succ q ihq =>
      intro p' q'
      obtain ⟨a, b, ⟨e⟩⟩ := ihq p' q'
      exact ⟨a, b + 1,
        ⟨biprod.mapIso (L.mixLineSuccIso 0 q) (Iso.refl _) ≪≫
          biprod.associator _ _ _ ≪≫
          biprod.mapIso (Iso.refl L.obj) e ≪≫
          (L.mixLineSuccIso a b).symm⟩⟩
  | succ p ihp =>
    intro q p' q'
    obtain ⟨a, b, ⟨e⟩⟩ := ihp q p' q'
    exact ⟨a + 1, b,
      ⟨biprod.mapIso (L.mixSuccIso p q) (Iso.refl _) ≪≫
        biprod.associator _ _ _ ≪≫
        biprod.mapIso (Iso.refl (𝟙_ D)) e ≪≫
        (L.mixSuccIso a b).symm⟩⟩

/-- **The line times a mixed sum is a mixed sum**: the line
exchanges the unit summands with the line summands. -/
theorem OddLine.exists_mix_line_tensor
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) :
    ∀ p q : ℕ, ∃ a b : ℕ,
      Nonempty (L.obj ⊗ L.mix p q ≅ L.mix a b) := by
  intro p
  induction p with
  | zero =>
    intro q
    induction q with
    | zero =>
      exact ⟨0, 0,
        ⟨(isZero_whiskerLeft L.obj L.isZero_mix_zero).iso
          L.isZero_mix_zero⟩⟩
    | succ q ihq =>
      obtain ⟨a, b, ⟨e⟩⟩ := ihq
      exact ⟨a + 1, b,
        ⟨whiskerLeftIso L.obj (L.mixLineSuccIso 0 q) ≪≫
          tensorBiprodIso L.obj L.obj (L.mix 0 q) ≪≫
          biprod.mapIso L.sq e ≪≫ (L.mixSuccIso a b).symm⟩⟩
  | succ p ihp =>
    intro q
    obtain ⟨a, b, ⟨e⟩⟩ := ihp q
    exact ⟨a, b + 1,
      ⟨whiskerLeftIso L.obj (L.mixSuccIso p q) ≪≫
        tensorBiprodIso L.obj (𝟙_ D) (L.mix p q) ≪≫
        biprod.mapIso (ρ_ L.obj) e ≪≫
        (L.mixLineSuccIso a b).symm⟩⟩

/-- **A tensor product of mixed sums is a mixed sum.** -/
theorem OddLine.exists_mix_tensor
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) :
    ∀ p q p' q' : ℕ, ∃ a b : ℕ,
      Nonempty (L.mix p q ⊗ L.mix p' q' ≅ L.mix a b) := by
  intro p
  induction p with
  | zero =>
    intro q
    induction q with
    | zero =>
      intro p' q'
      exact ⟨0, 0,
        ⟨(isZero_whiskerRight L.isZero_mix_zero _).iso
          L.isZero_mix_zero⟩⟩
    | succ q ihq =>
      intro p' q'
      obtain ⟨a, b, ⟨e⟩⟩ := ihq p' q'
      obtain ⟨c, d, ⟨f⟩⟩ := L.exists_mix_line_tensor p' q'
      obtain ⟨m, n, ⟨g⟩⟩ := L.exists_mix_biprod c d a b
      exact ⟨m, n,
        ⟨whiskerRightIso (L.mixLineSuccIso 0 q) (L.mix p' q') ≪≫
          biprodTensorIso L.obj (L.mix 0 q) (L.mix p' q') ≪≫
          biprod.mapIso f e ≪≫ g⟩⟩
  | succ p ihp =>
    intro q p' q'
    obtain ⟨a, b, ⟨e⟩⟩ := ihp q p' q'
    obtain ⟨m, n, ⟨g⟩⟩ := L.exists_mix_biprod p' q' a b
    exact ⟨m, n,
      ⟨whiskerRightIso (L.mixSuccIso p q) (L.mix p' q') ≪≫
        biprodTensorIso (𝟙_ D) (L.mix p q) (L.mix p' q') ≪≫
        biprod.mapIso (λ_ (L.mix p' q')) e ≪≫ g⟩⟩

end Mix

/-! ## Split objects -/

section Split

variable {D : Type u}

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- An object is *split* by `R` when its free module is a mixed
sum: a sum of copies of the unit and of the odd line. -/
def IsSplit [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D]
    (L : OddLine D) (R : D) [MonObj R] (Y : D) : Prop :=
  ∃ p q : ℕ, Nonempty (freeMod R Y ≅ freeMod R (L.mix p q))

/-- Splitness transports along an isomorphism. -/
theorem IsSplit.of_iso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] (L : OddLine D) (R : D)
    [MonObj R]
    {Y Z : D} (e : Y ≅ Z) (h : IsSplit L R Y) :
    IsSplit L R Z := by
  obtain ⟨p, q, ⟨f⟩⟩ := h
  exact ⟨p, q, ⟨(freeModMapIso R e).symm ≪≫ f⟩⟩

/-- **The unit is split**: it is the mixed sum of a single unit. -/
theorem isSplit_unit [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] (L : OddLine D) (R : D)
    [MonObj R] : IsSplit L R (𝟙_ D) :=
  ⟨1, 0, ⟨freeModMapIso R L.mixOneZeroIso.symm⟩⟩

/-- **A zero object is split**: it is the empty mixed sum. -/
theorem isSplit_zero [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] (L : OddLine D) (R : D)
    [MonObj R]
    {Y : D} (h : IsZero Y) : IsSplit L R Y :=
  ⟨0, 0, ⟨freeModMapIso R (h.iso L.isZero_mix_zero)⟩⟩

/-- **Split objects are closed under binary biproducts**, the
ranks adding. -/
theorem IsSplit.biprod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] (L : OddLine D) (R : D)
    [MonObj R] [MonoidalPreadditive D]
    {Y Z : D} (hY : IsSplit L R Y)
    (hZ : IsSplit L R Z) : IsSplit L R (Y ⊞ Z) := by
  obtain ⟨p, q, ⟨eY⟩⟩ := hY
  obtain ⟨p', q', ⟨eZ⟩⟩ := hZ
  obtain ⟨a, b, ⟨g⟩⟩ := L.exists_mix_biprod p q p' q'
  exact ⟨a, b, ⟨freeModBiprodIso R Y Z ≪≫
    modBiprodMapIso R _ _ eY eZ ≪≫
    (freeModBiprodIso R (L.mix p q) (L.mix p' q')).symm ≪≫
    freeModMapIso R g⟩⟩

/-- **Split objects are closed under finite biproducts.** -/
theorem IsSplit.biproduct
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] (L : OddLine D) (R : D)
    [MonObj R] [MonoidalPreadditive D] : ∀ (k : ℕ) (g : Fin k → D),
    (∀ t, IsSplit L R (g t)) → IsSplit L R (⨁ g) := by
  intro k
  induction k with
  | zero =>
    exact fun g _ => isSplit_zero L R (isZero_biproductFinZero g)
  | succ k ih =>
    intro g hg
    exact IsSplit.of_iso L R (biprodPeelFinIso g).symm
      (IsSplit.biprod L R (hg 0) (ih _ fun i => hg i.succ))

/-- **Split objects are closed under tensor products**: the free
module functor carries the tensor product to the relative tensor
product, and a tensor product of mixed sums is a mixed sum. -/
theorem IsSplit.tensor
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] (L : OddLine D) (R : D)
    [MonObj R] [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj R]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    {Y Z : D} (hY : IsSplit L R Y)
    (hZ : IsSplit L R Z) : IsSplit L R (Y ⊗ Z) := by
  obtain ⟨p, q, ⟨eY⟩⟩ := hY
  obtain ⟨p', q', ⟨eZ⟩⟩ := hZ
  obtain ⟨a, b, ⟨g⟩⟩ := L.exists_mix_tensor p q p' q'
  exact ⟨a, b, ⟨(freeModTensorIso R Y Z).symm ≪≫
    modTensorMapIso R eY eZ ≪≫
    freeModTensorIso R (L.mix p q) (L.mix p' q') ≪≫
    freeModMapIso R g⟩⟩

/-- **Split objects are closed under tensor powers.** -/
theorem IsSplit.tensorPow
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] (L : OddLine D) (R : D)
    [MonObj R] [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj R]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    {Y : D} (h : IsSplit L R Y) (n : ℕ) :
    IsSplit L R (tensorPow D Y n) := by
  induction n with
  | zero => exact isSplit_unit L R
  | succ n ih => exact IsSplit.tensor L R ih h

end Split

/-! ## The generator splits the embedded category -/

section IndGenerator

variable {C : Type v}

/-- **The embedded tensor powers of a split object are split**:
the embedding is strong monoidal, so it carries the tensor power
downstairs to the tensor power upstairs. -/
theorem isSplit_indOf_tensorPow
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [MonoidalPreadditive (Ind C)] [SymmetricCategory (Ind C)]
    [HasCoequalizers (Ind C)]
    [∀ Z : Ind C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft
      Z)] [HasFiniteBiproducts (Ind C)] (L : OddLine (Ind C)) (𝔸 : Ind C)
    [MonObj 𝔸] [IsCommMonObj 𝔸]
    (X : C)
    (hX : IsSplit L 𝔸 ((indOf : C ⥤ Ind C).obj X)) (n : ℕ) :
    IsSplit L 𝔸 ((indOf : C ⥤ Ind C).obj (tensorPow C X n)) := by
  induction n with
  | zero =>
    exact IsSplit.of_iso L 𝔸 (indOfUnitIso (C := C))
      (isSplit_unit L 𝔸)
  | succ n ih =>
    exact IsSplit.of_iso L 𝔸 (indOfTensorIso (tensorPow C X n) X)
      (IsSplit.tensor L 𝔸 ih hX)

/-- **The embedded mixed tensor powers of a generator are split**,
given that the generator and its dual are. -/
theorem isSplit_indOf_mixedPow
    [SmallCategory C] [MonoidalCategory C] [Abelian C] [RigidCategory C]
    [MonoidalPreadditive (Ind C)] [SymmetricCategory (Ind C)]
    [HasCoequalizers (Ind C)]
    [∀ Z : Ind C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft
      Z)] [HasFiniteBiproducts (Ind C)] (L : OddLine (Ind C)) (𝔸 : Ind C)
    [MonObj 𝔸] [IsCommMonObj 𝔸]
    (X : C)
    (hX : IsSplit L 𝔸 ((indOf : C ⥤ Ind C).obj X))
    (hXd : IsSplit L 𝔸 ((indOf : C ⥤ Ind C).obj (Xᘁ)))
    (a b : ℕ) :
    IsSplit L 𝔸 ((indOf : C ⥤ Ind C).obj (mixedPow C X a b)) := by
  have h : IsSplit L 𝔸 ((indOf : C ⥤ Ind C).obj
      (tensorPow C X a ⊗ tensorPow C (Xᘁ) b)) :=
    IsSplit.of_iso L 𝔸
      (indOfTensorIso (tensorPow C X a) (tensorPow C (Xᘁ) b))
      (IsSplit.tensor L 𝔸
        (isSplit_indOf_tensorPow L 𝔸 X hX a)
        (isSplit_indOf_tensorPow L 𝔸 (Xᘁ) hXd b))
  exact h

/-- **A splitting generator splits the whole embedded category.**
Every object of `C` is a subquotient of a finite biproduct of
mixed tensor powers of the generator; the embedding is additive, so
it carries that biproduct into `Ind C`, where the closure
properties above make it split, and the subquotient hypothesis
finishes.

The subquotient hypothesis is phrased downstairs: for objects `Y`
and `Z` of `C` with `Y` a subquotient of `Z`, splitness of the
embedded `Z` implies splitness of the embedded `Y`. -/
theorem splitsOn_of_generator [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [HasFiniteBiproducts C] [RigidCategory C] [MonoidalPreadditive (Ind C)]
    [SymmetricCategory (Ind C)] [HasCoequalizers (Ind C)]
    [∀ Z : Ind C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft
      Z)] [HasFiniteBiproducts (Ind C)] (L : OddLine (Ind C)) (𝔸 : Ind C)
    [MonObj 𝔸] [IsCommMonObj 𝔸]
    (X : C)
    (hX : IsSplit L 𝔸 ((indOf : C ⥤ Ind C).obj X))
    (hXd : IsSplit L 𝔸 ((indOf : C ⥤ Ind C).obj (Xᘁ)))
    (hsub : ∀ Y Z : C, IsSubquotientOf Y Z →
      IsSplit L 𝔸 ((indOf : C ⥤ Ind C).obj Z) →
      IsSplit L 𝔸 ((indOf : C ⥤ Ind C).obj Y))
    (hgen : TensorGeneratedBy C X) :
    SplitsOn L 𝔸 (indOf : C ⥤ Ind C) := by
  haveI : (indOf (C := C)).Additive := indOf_additive
  intro Y
  obtain ⟨k, ab, hsq⟩ := hgen Y
  show IsSplit L 𝔸 ((indOf : C ⥤ Ind C).obj Y)
  refine hsub Y _ hsq ?_
  refine IsSplit.of_iso L 𝔸
    (((indOf : C ⥤ Ind C).mapBiproduct
      (fun t => mixedPow C X (ab t).1 (ab t).2)).symm) ?_
  exact IsSplit.biproduct L 𝔸 k _
    (fun t => isSplit_indOf_mixedPow L 𝔸 X hX hXd _ _)

end IndGenerator

end RS
