/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperEmbed.Letters

/-!
# The standard super object and the mixed sum

Two letter systems and the conclusion they force.  In an ambient
symmetric ℂ-linear category with an odd invertible line `U` the
mixed biproduct sum `𝟙 ^ ⊕ (p+1) ⊞ U ^ ⊕ (q+1)` carries one; so
does the standard super object of `RS.SuperVect`, whose braiding on
the odd line is `−1`.  A group-algebra element killing the ambient
tensor power has vanishing colour sums by
[Letters.lean](Letters.lean), hence kills the standard super object
as well — contradicting `not_schurKilled_stdSuper`.

* `mixedSumLetters`, `stdSuperLetters`: the two letter systems,
  built from the biproduct insertions and projections
  `sumPowIns`/`sumPowPrj` and from the coordinates of the standard
  super object.
* The `MonoidalPreadditive` and `MonoidalLinear` structures of
  `RS.SuperVect`, and `stdSuper_braiding_neg`: the odd line of
  `RS.SuperVect` is odd.
* `tensorPow_id_ne_zero`: a tensor power of a nonzero unit is
  nonzero.
* `not_schurKilled_sum`: the mixed sum is not Schur-killed at any
  diagram avoiding the cell `(p + 1, q + 1)` — the exact complement
  of `schurKilled_unit_odd`.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

/-! ## The letter system of a mixed biproduct sum

In an ambient category with binary biproducts, the object
`𝟙 ^ ⊕ (p+1) ⊞ U ^ ⊕ (q+1)` carries the evident letter system:
unit letters through the first summand, odd letters through the
second. -/

/-- The parity of a mixed letter label: even on the first summand,
odd on the second. -/
abbrev mixedPar {p q : ℕ} : Fin (p + 1) ⊕ Fin (q + 1) → Bool :=
  fun k => Sum.rec (fun _ => false) (fun _ => true) k

section BiprodLetters

variable {A : Type u}

/-- The inclusion of one copy into an iterated biproduct sum. -/
noncomputable def sumPowIns
    [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    (X : A) : (k : ℕ) → Fin (k + 1) →
    (X ⟶ sumPow X k)
  | 0, _ => 𝟙 X
  | k + 1, i =>
      Fin.lastCases biprod.inr
        (fun j => sumPowIns X k j ≫ biprod.inl) i

/-- The projection onto one copy of an iterated biproduct sum. -/
noncomputable def sumPowPrj
    [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    (X : A) : (k : ℕ) → Fin (k + 1) →
    (sumPow X k ⟶ X)
  | 0, _ => 𝟙 X
  | k + 1, i =>
      Fin.lastCases biprod.snd
        (fun j => biprod.fst ≫ sumPowPrj X k j) i

/-- The recursion of the copy inclusion. -/
theorem sumPowIns_succ [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    (X : A) (k : ℕ) (i : Fin (k + 2)) :
    sumPowIns X (k + 1) i =
      Fin.lastCases biprod.inr
        (fun j => sumPowIns X k j ≫ biprod.inl) i := rfl

/-- The recursion of the copy projection. -/
theorem sumPowPrj_succ [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    (X : A) (k : ℕ) (i : Fin (k + 2)) :
    sumPowPrj X (k + 1) i =
      Fin.lastCases biprod.snd
        (fun j => biprod.fst ≫ sumPowPrj X k j) i := rfl

/-- Sandwich of a first-summand round trip.  Stated at general
objects. -/
private theorem inl_sandwich
    [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    {X P Q : A} (f : X ⟶ P) (g : P ⟶ X)
    (h : f ≫ g = 𝟙 X) :
    (f ≫ (biprod.inl : P ⟶ P ⊞ Q)) ≫ (biprod.fst ≫ g) = 𝟙 X := by
  rw [Category.assoc, biprod.inl_fst_assoc, h]

/-- Sandwich of a vanishing first-summand round trip.  Stated at
general objects. -/
private theorem inl_sandwich_zero
    [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    {X X' P Q : A} (f : X ⟶ P)
    (g : P ⟶ X') (h : f ≫ g = 0) :
    (f ≫ (biprod.inl : P ⟶ P ⊞ Q)) ≫ (biprod.fst ≫ g) = 0 := by
  rw [Category.assoc, biprod.inl_fst_assoc, h]

/-- The second summand misses a first-summand projection.  Stated
at general objects. -/
private theorem inr_miss
    [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    {X' P Q : A} (g : P ⟶ X') :
    (biprod.inr : Q ⟶ P ⊞ Q) ≫ (biprod.fst ≫ g) = 0 := by
  rw [← Category.assoc, biprod.inr_fst, Limits.zero_comp]

/-- The first summand misses the second-summand projection.
Stated at general objects. -/
private theorem inl_miss
    [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    {X P Q : A} (f : X ⟶ P) :
    (f ≫ (biprod.inl : P ⟶ P ⊞ Q)) ≫ biprod.snd = 0 := by
  rw [Category.assoc, biprod.inl_snd, Limits.comp_zero]

/-- A copy's round trip through the sum is the identity. -/
theorem sumPowIns_prj_same
    [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    (X : A) :
    ∀ (k : ℕ) (i : Fin (k + 1)),
      sumPowIns X k i ≫ sumPowPrj X k i = 𝟙 X := by
  intro k
  induction k with
  | zero => intro i; exact Category.id_comp _
  | succ k ih =>
    intro i
    induction i using Fin.lastCases with
    | last =>
      erw [sumPowIns_succ, sumPowPrj_succ, Fin.lastCases_last,
        Fin.lastCases_last]
      exact biprod.inr_snd
    | cast j =>
      erw [sumPowIns_succ, sumPowPrj_succ, Fin.lastCases_castSucc,
        Fin.lastCases_castSucc]
      exact inl_sandwich _ _ (ih j)

/-- Distinct copies' round trips vanish. -/
theorem sumPowIns_prj_ne
    [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    (X : A) :
    ∀ (k : ℕ) {i i' : Fin (k + 1)}, i ≠ i' →
      sumPowIns X k i ≫ sumPowPrj X k i' = 0 := by
  intro k
  induction k with
  | zero =>
    intro i i' hii'
    exact absurd (Fin.ext (by omega)) hii'
  | succ k ih =>
    intro i i' hii'
    induction i using Fin.lastCases with
    | last =>
      induction i' using Fin.lastCases with
      | last => exact absurd rfl hii'
      | cast j' =>
        erw [sumPowIns_succ, sumPowPrj_succ, Fin.lastCases_last,
          Fin.lastCases_castSucc]
        exact inr_miss _
    | cast j =>
      induction i' using Fin.lastCases with
      | last =>
        erw [sumPowIns_succ, sumPowPrj_succ, Fin.lastCases_castSucc,
          Fin.lastCases_last]
        exact inl_miss _
      | cast j' =>
        erw [sumPowIns_succ, sumPowPrj_succ, Fin.lastCases_castSucc,
          Fin.lastCases_castSucc]
        exact inl_sandwich_zero _ _
          (ih (fun h => hii' (congrArg Fin.castSucc h)))

/-- One-step gathering of the summand round trips.  Stated at
general objects. -/
private theorem biprod_gather
    [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    {P Q X : A} {m : ℕ}
    (p : Fin m → (P ⟶ X)) (i : Fin m → (X ⟶ P))
    (htot : (∑ j : Fin m, p j ≫ i j) = 𝟙 P) :
    (∑ j : Fin m, (biprod.fst ≫ p j) ≫ (i j ≫ biprod.inl)) +
        biprod.snd ≫ biprod.inr = 𝟙 (P ⊞ Q) := by
  have h1 : (∑ j : Fin m, ((biprod.fst : P ⊞ Q ⟶ P) ≫ p j) ≫
      (i j ≫ (biprod.inl : P ⟶ P ⊞ Q))) =
      (biprod.fst : P ⊞ Q ⟶ P) ≫ (∑ j : Fin m, p j ≫ i j) ≫
        biprod.inl := by
    rw [Preadditive.sum_comp, Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Category.assoc]
  rw [h1, htot, Category.id_comp]
  exact biprod.total

/-- The copies decompose the identity of the sum. -/
theorem sumPow_total [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    (X : A) :
    ∀ k : ℕ,
      (∑ i : Fin (k + 1), sumPowPrj X k i ≫ sumPowIns X k i) =
        𝟙 (sumPow X k) := by
  intro k
  induction k with
  | zero =>
    change (∑ i : Fin 1, sumPowPrj X 0 i ≫ sumPowIns X 0 i) =
      𝟙 (sumPow X 0)
    rw [Fin.sum_univ_one]
    exact Category.id_comp _
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => by
      erw [sumPowIns_succ, sumPowPrj_succ, Fin.lastCases_castSucc,
        Fin.lastCases_castSucc]]
    erw [sumPowIns_succ, sumPowPrj_succ, Fin.lastCases_last,
      Fin.lastCases_last]
    exact biprod_gather (sumPowPrj X k) (sumPowIns X k) ih

/-- **The letter system of the mixed sum**: `p + 1` unit letters
through the first summand and `q + 1` odd letters through the
second. -/
noncomputable def mixedSumLetters
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A]
    (p q : ℕ) (U : A) :
    MixedLetters (Fin (p + 1) ⊕ Fin (q + 1)) mixedPar U
      (sumPow (𝟙_ A) p ⊞ sumPow U q) where
  ins k :=
    Sum.rec (fun i => sumPowIns (𝟙_ A) p i ≫ biprod.inl)
      (fun j => sumPowIns U q j ≫ biprod.inr) k
  prj k :=
    Sum.rec (fun i => biprod.fst ≫ sumPowPrj (𝟙_ A) p i)
      (fun j => biprod.snd ≫ sumPowPrj U q j) k
  ins_prj k := by
    cases k with
    | inl i =>
      change (sumPowIns (𝟙_ A) p i ≫ biprod.inl) ≫
        (biprod.fst ≫ sumPowPrj (𝟙_ A) p i) = 𝟙 _
      rw [Category.assoc, biprod.inl_fst_assoc]
      exact sumPowIns_prj_same (𝟙_ A) p i
    | inr j =>
      change (sumPowIns U q j ≫ biprod.inr) ≫
        (biprod.snd ≫ sumPowPrj U q j) = 𝟙 _
      rw [Category.assoc, biprod.inr_snd_assoc]
      exact sumPowIns_prj_same U q j
  ins_prj_ne {k k'} hkk' := by
    cases k with
    | inl i =>
      cases k' with
      | inl i' =>
        change (sumPowIns (𝟙_ A) p i ≫ biprod.inl) ≫
          (biprod.fst ≫ sumPowPrj (𝟙_ A) p i') = 0
        rw [Category.assoc, biprod.inl_fst_assoc,
          sumPowIns_prj_ne (𝟙_ A) p
            (fun h => hkk' (congrArg Sum.inl h))]
      | inr j' =>
        change (sumPowIns (𝟙_ A) p i ≫ biprod.inl) ≫
          (biprod.snd ≫ sumPowPrj U q j') = 0
        rw [Category.assoc, biprod.inl_snd_assoc,
          Limits.zero_comp, Limits.comp_zero]
    | inr j =>
      cases k' with
      | inl i' =>
        change (sumPowIns U q j ≫ biprod.inr) ≫
          (biprod.fst ≫ sumPowPrj (𝟙_ A) p i') = 0
        rw [Category.assoc, biprod.inr_fst_assoc,
          Limits.zero_comp, Limits.comp_zero]
      | inr j' =>
        change (sumPowIns U q j ≫ biprod.inr) ≫
          (biprod.snd ≫ sumPowPrj U q j') = 0
        rw [Category.assoc, biprod.inr_snd_assoc,
          sumPowIns_prj_ne U q
            (fun h => hkk' (congrArg Sum.inr h))]
  total := by
    rw [Fintype.sum_sum_type]
    have h1 : (∑ i : Fin (p + 1),
        ((biprod.fst : sumPow (𝟙_ A) p ⊞ sumPow U q ⟶ _) ≫
          sumPowPrj (𝟙_ A) p i) ≫
          (sumPowIns (𝟙_ A) p i ≫
            (biprod.inl : _ ⟶ sumPow (𝟙_ A) p ⊞ sumPow U q))) =
        (biprod.fst : sumPow (𝟙_ A) p ⊞ sumPow U q ⟶ _) ≫
          (𝟙 (sumPow (𝟙_ A) p)) ≫
          (biprod.inl : _ ⟶ sumPow (𝟙_ A) p ⊞ sumPow U q) := by
      rw [← sumPow_total (𝟙_ A) p, Preadditive.sum_comp,
        Preadditive.comp_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Category.assoc]
    have h2 : (∑ j : Fin (q + 1),
        ((biprod.snd : sumPow (𝟙_ A) p ⊞ sumPow U q ⟶ _) ≫
          sumPowPrj U q j) ≫
          (sumPowIns U q j ≫
            (biprod.inr : _ ⟶ sumPow (𝟙_ A) p ⊞ sumPow U q))) =
        (biprod.snd : sumPow (𝟙_ A) p ⊞ sumPow U q ⟶ _) ≫
          (𝟙 (sumPow U q)) ≫
          (biprod.inr : _ ⟶ sumPow (𝟙_ A) p ⊞ sumPow U q) := by
      rw [← sumPow_total U q, Preadditive.sum_comp,
        Preadditive.comp_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Category.assoc]
    change (∑ i : Fin (p + 1),
        ((biprod.fst : sumPow (𝟙_ A) p ⊞ sumPow U q ⟶ _) ≫
          sumPowPrj (𝟙_ A) p i) ≫
          (sumPowIns (𝟙_ A) p i ≫
            (biprod.inl : _ ⟶ sumPow (𝟙_ A) p ⊞ sumPow U q))) +
      (∑ j : Fin (q + 1),
        ((biprod.snd : sumPow (𝟙_ A) p ⊞ sumPow U q ⟶ _) ≫
          sumPowPrj U q j) ≫
          (sumPowIns U q j ≫
            (biprod.inr : _ ⟶ sumPow (𝟙_ A) p ⊞ sumPow U q))) =
      𝟙 (sumPow (𝟙_ A) p ⊞ sumPow U q)
    rw [h1, h2, Category.id_comp, Category.id_comp]
    exact biprod.total

end BiprodLetters

/-! ## Nonvanishing of the odd-line powers -/

section Nonzero

variable {A : Type u}

/-- A zero identity transfers along an isomorphism.  Stated at
general objects. -/
private theorem id_zero_transfer [Category.{v} A] [Preadditive A]
    {X Y : A} (e : X ≅ Y)
    (h : 𝟙 X = 0) : 𝟙 Y = 0 := by
  calc 𝟙 Y = e.inv ≫ 𝟙 X ≫ e.hom := by
        rw [Category.id_comp, e.inv_hom_id]
    _ = 0 := by rw [h, Limits.zero_comp, Limits.comp_zero]

/-- **Powers of an invertible line are nonzero** when the unit is:
tensoring with one more copy of the line is undone through its
self-pairing. -/
theorem tensorPow_id_ne_zero
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A]
    (hone : ¬ Limits.IsZero (𝟙_ A))
    {U : A} (hUU : U ⊗ U ≅ 𝟙_ A) :
    ∀ k : ℕ, 𝟙 (tensorPow A U k) ≠
      (0 : tensorPow A U k ⟶ tensorPow A U k) := by
  intro k
  induction k with
  | zero =>
    intro h
    exact hone ((Limits.IsZero.iff_id_eq_zero (𝟙_ A)).mpr h)
  | succ k ih =>
    intro h
    have h1 : 𝟙 (tensorPow A U (k + 1) ⊗ U) = 0 := by
      rw [← MonoidalCategory.id_whiskerRight, h,
        MonoidalPreadditive.zero_whiskerRight]
    exact ih (id_zero_transfer
      ((α_ (tensorPow A U k) U U) ≪≫
        whiskerLeftIso (tensorPow A U k) hUU ≪≫
        ρ_ (tensorPow A U k)) h1)

end Nonzero

/-! ## The ambient extraction -/

section AmbientSide

variable {A : Type u}

/-- **Extraction in the ambient category**: if the mixed sum is
Schur-killed at a diagram, every colour sum of the block idempotent
vanishes — a purely combinatorial consequence, shared with every
other model. -/
theorem colourSum_eq_zero_of_schurKilled
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] [HasBinaryBiproducts A]
    (P : SchurPackage.{v})
    (hone : ¬ Limits.IsZero (𝟙_ A)) {U : A} (hUU : U ⊗ U ≅ 𝟙_ A)
    (hβ : (β_ U U).hom = -(𝟙 (U ⊗ U))) (p q : ℕ)
    {lam : YoungDiagram}
    (hkill : SchurKilled P (sumPow (𝟙_ A) p ⊞ sumPow U q) lam) :
    ∀ c d : Fin lam.card → Fin (p + 1) ⊕ Fin (q + 1),
      colourSum mixedPar (P.e lam) c d = 0 :=
  fun c d => (mixedSumLetters p q U).colourSum_eq_zero hβ
    (tensorPow_id_ne_zero hone hUU) hkill c d

end AmbientSide

/-! ## Additive and linear monoidal structure of `SuperVect`

The graded tensor product is additive and ℂ-linear in each
argument, componentwise. -/

section SuperVectInstances

open scoped TensorProduct

/-- The parallel pair of zero maps is zero. -/
private theorem prodMap_zero₂ {M₁ M₂ N₁ N₂ : Type*}
    [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    [AddCommGroup N₁] [Module ℂ N₁] [AddCommGroup N₂] [Module ℂ N₂] :
    LinearMap.prodMap (0 : M₁ →ₗ[ℂ] N₁) (0 : M₂ →ₗ[ℂ] N₂) = 0 :=
  LinearMap.ext fun _ => rfl

/-- The parallel pair of sums is the sum of the parallel pairs. -/
private theorem prodMap_add₂ {M₁ M₂ N₁ N₂ : Type*}
    [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    [AddCommGroup N₁] [Module ℂ N₁] [AddCommGroup N₂] [Module ℂ N₂]
    (f f' : M₁ →ₗ[ℂ] N₁) (g g' : M₂ →ₗ[ℂ] N₂) :
    LinearMap.prodMap (f + f') (g + g') =
      LinearMap.prodMap f g + LinearMap.prodMap f' g' :=
  LinearMap.ext fun _ => rfl

/-- The parallel pair of scalings is the scaling of the pair. -/
private theorem prodMap_smul₂ {M₁ M₂ N₁ N₂ : Type*}
    [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    [AddCommGroup N₁] [Module ℂ N₁] [AddCommGroup N₂] [Module ℂ N₂]
    (r : ℂ) (f : M₁ →ₗ[ℂ] N₁) (g : M₂ →ₗ[ℂ] N₂) :
    LinearMap.prodMap (r • f) (r • g) =
      r • LinearMap.prodMap f g :=
  LinearMap.ext fun _ => rfl

/-- `SuperVect` is monoidal preadditive: whiskering is additive. -/
instance : MonoidalPreadditive SuperVect where
  whiskerLeft_zero {X Y Z} := by
    apply SuperVect.hom_ext
    · change LinearMap.prodMap
        (TensorProduct.map LinearMap.id
          (SuperVect.Hom.evenMap (0 : Y ⟶ Z)))
        (TensorProduct.map LinearMap.id
          (SuperVect.Hom.oddMap (0 : Y ⟶ Z))) =
        SuperVect.Hom.evenMap (0 : X ⊗ Y ⟶ X ⊗ Z)
      rw [SuperVect.zero_evenMap, SuperVect.zero_oddMap,
        TensorProduct.map_zero_right, TensorProduct.map_zero_right,
        prodMap_zero₂]
      rfl
    · change LinearMap.prodMap
        (TensorProduct.map LinearMap.id
          (SuperVect.Hom.oddMap (0 : Y ⟶ Z)))
        (TensorProduct.map LinearMap.id
          (SuperVect.Hom.evenMap (0 : Y ⟶ Z))) =
        SuperVect.Hom.oddMap (0 : X ⊗ Y ⟶ X ⊗ Z)
      rw [SuperVect.zero_evenMap, SuperVect.zero_oddMap,
        TensorProduct.map_zero_right, TensorProduct.map_zero_right,
        prodMap_zero₂]
      rfl
  zero_whiskerRight {X Y Z} := by
    apply SuperVect.hom_ext
    · change LinearMap.prodMap
        (TensorProduct.map (SuperVect.Hom.evenMap (0 : Y ⟶ Z))
          LinearMap.id)
        (TensorProduct.map (SuperVect.Hom.oddMap (0 : Y ⟶ Z))
          LinearMap.id) =
        SuperVect.Hom.evenMap (0 : Y ⊗ X ⟶ Z ⊗ X)
      rw [SuperVect.zero_evenMap, SuperVect.zero_oddMap,
        TensorProduct.map_zero_left, TensorProduct.map_zero_left,
        prodMap_zero₂]
      rfl
    · change LinearMap.prodMap
        (TensorProduct.map (SuperVect.Hom.evenMap (0 : Y ⟶ Z))
          LinearMap.id)
        (TensorProduct.map (SuperVect.Hom.oddMap (0 : Y ⟶ Z))
          LinearMap.id) =
        SuperVect.Hom.oddMap (0 : Y ⊗ X ⟶ Z ⊗ X)
      rw [SuperVect.zero_evenMap, SuperVect.zero_oddMap,
        TensorProduct.map_zero_left, TensorProduct.map_zero_left,
        prodMap_zero₂]
      rfl
  whiskerLeft_add {X Y Z} f g := by
    apply SuperVect.hom_ext
    · change LinearMap.prodMap
        (TensorProduct.map LinearMap.id
          (SuperVect.Hom.evenMap (f + g)))
        (TensorProduct.map LinearMap.id
          (SuperVect.Hom.oddMap (f + g))) =
        SuperVect.Hom.evenMap (X ◁ f + X ◁ g)
      rw [SuperVect.add_evenMap, SuperVect.add_oddMap,
        TensorProduct.map_add_right, TensorProduct.map_add_right,
        prodMap_add₂]
      rfl
    · change LinearMap.prodMap
        (TensorProduct.map LinearMap.id
          (SuperVect.Hom.oddMap (f + g)))
        (TensorProduct.map LinearMap.id
          (SuperVect.Hom.evenMap (f + g))) =
        SuperVect.Hom.oddMap (X ◁ f + X ◁ g)
      rw [SuperVect.add_evenMap, SuperVect.add_oddMap,
        TensorProduct.map_add_right, TensorProduct.map_add_right,
        prodMap_add₂]
      rfl
  add_whiskerRight {X Y Z} f g := by
    apply SuperVect.hom_ext
    · change LinearMap.prodMap
        (TensorProduct.map (SuperVect.Hom.evenMap (f + g))
          LinearMap.id)
        (TensorProduct.map (SuperVect.Hom.oddMap (f + g))
          LinearMap.id) =
        SuperVect.Hom.evenMap (f ▷ X + g ▷ X)
      rw [SuperVect.add_evenMap, SuperVect.add_oddMap,
        TensorProduct.map_add_left, TensorProduct.map_add_left,
        prodMap_add₂]
      rfl
    · change LinearMap.prodMap
        (TensorProduct.map (SuperVect.Hom.evenMap (f + g))
          LinearMap.id)
        (TensorProduct.map (SuperVect.Hom.oddMap (f + g))
          LinearMap.id) =
        SuperVect.Hom.oddMap (f ▷ X + g ▷ X)
      rw [SuperVect.add_evenMap, SuperVect.add_oddMap,
        TensorProduct.map_add_left, TensorProduct.map_add_left,
        prodMap_add₂]
      rfl

/-- `SuperVect` is monoidal ℂ-linear: whiskering is ℂ-linear. -/
instance : MonoidalLinear ℂ SuperVect where
  whiskerLeft_smul X Y Z r f := by
    apply SuperVect.hom_ext
    · change LinearMap.prodMap
        (TensorProduct.map LinearMap.id
          (SuperVect.Hom.evenMap (r • f)))
        (TensorProduct.map LinearMap.id
          (SuperVect.Hom.oddMap (r • f))) =
        SuperVect.Hom.evenMap (r • (X ◁ f))
      rw [SuperVect.smul_evenMap, SuperVect.smul_oddMap,
        TensorProduct.map_smul_right, TensorProduct.map_smul_right,
        prodMap_smul₂]
      rfl
    · change LinearMap.prodMap
        (TensorProduct.map LinearMap.id
          (SuperVect.Hom.oddMap (r • f)))
        (TensorProduct.map LinearMap.id
          (SuperVect.Hom.evenMap (r • f))) =
        SuperVect.Hom.oddMap (r • (X ◁ f))
      rw [SuperVect.smul_evenMap, SuperVect.smul_oddMap,
        TensorProduct.map_smul_right, TensorProduct.map_smul_right,
        prodMap_smul₂]
      rfl
  smul_whiskerRight r {Y Z} f X := by
    apply SuperVect.hom_ext
    · change LinearMap.prodMap
        (TensorProduct.map (SuperVect.Hom.evenMap (r • f))
          LinearMap.id)
        (TensorProduct.map (SuperVect.Hom.oddMap (r • f))
          LinearMap.id) =
        SuperVect.Hom.evenMap (r • (f ▷ X))
      rw [SuperVect.smul_evenMap, SuperVect.smul_oddMap,
        TensorProduct.map_smul_left, TensorProduct.map_smul_left,
        prodMap_smul₂]
      rfl
    · change LinearMap.prodMap
        (TensorProduct.map (SuperVect.Hom.evenMap (r • f))
          LinearMap.id)
        (TensorProduct.map (SuperVect.Hom.oddMap (r • f))
          LinearMap.id) =
        SuperVect.Hom.oddMap (r • (f ▷ X))
      rw [SuperVect.smul_evenMap, SuperVect.smul_oddMap,
        TensorProduct.map_smul_left, TensorProduct.map_smul_left,
        prodMap_smul₂]
      rfl

end SuperVectInstances

/-! ## The odd line of `SuperVect`

The standard super object `ℂ^{0|1}` self-braids by `−1`: its even
component is the zero space, and the Koszul sign acts on the
odd square. -/

section OddLine

open scoped TensorProduct

/-- A tensor product with the zero space on the left is trivial. -/
private theorem tensor_zero_left_eq {M : Type*} [AddCommGroup M]
    [Module ℂ M] (z : (Fin 0 → ℂ) ⊗[ℂ] M) : z = 0 := by
  have h0 : (LinearMap.id : (Fin 0 → ℂ) →ₗ[ℂ] (Fin 0 → ℂ)) = 0 :=
    Subsingleton.elim _ _
  calc z = TensorProduct.map LinearMap.id LinearMap.id z := by
        rw [TensorProduct.map_id]
        rfl
    _ = TensorProduct.map 0 LinearMap.id z := by rw [h0]
    _ = 0 := by rw [TensorProduct.map_zero_left]; rfl

/-- A tensor product with the zero space on the right is
trivial. -/
private theorem tensor_zero_right_eq {M : Type*} [AddCommGroup M]
    [Module ℂ M] (z : M ⊗[ℂ] (Fin 0 → ℂ)) : z = 0 := by
  have h0 : (LinearMap.id : (Fin 0 → ℂ) →ₗ[ℂ] (Fin 0 → ℂ)) = 0 :=
    Subsingleton.elim _ _
  calc z = TensorProduct.map LinearMap.id LinearMap.id z := by
        rw [TensorProduct.map_id]
        rfl
    _ = TensorProduct.map LinearMap.id 0 z := by rw [h0]
    _ = 0 := by rw [TensorProduct.map_zero_right]; rfl

/-- The flip on the square of a line is the identity. -/
private theorem comm_line_self (b : (Fin 1 → ℂ) ⊗[ℂ] (Fin 1 → ℂ)) :
    TensorProduct.comm ℂ (Fin 1 → ℂ) (Fin 1 → ℂ) b = b := by
  induction b using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, hx, hy]
  | tmul v w =>
    have hrep : ∀ v : Fin 1 → ℂ,
        v = v 0 • (fun _ => (1 : ℂ)) := by
      intro v
      funext i
      rw [Subsingleton.elim i 0]
      simp
    rw [TensorProduct.comm_tmul, hrep v, hrep w,
      ← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul',
      TensorProduct.tmul_smul, TensorProduct.tmul_smul,
      smul_smul, smul_smul, mul_comm]

/-- **The odd line self-braids by `−1`.** -/
theorem stdSuper_braiding_neg :
    (β_ (stdSuper 0 1) (stdSuper 0 1)).hom =
      -(𝟙 (stdSuper 0 1 ⊗ stdSuper 0 1)) := by
  have hEE : ∀ x y : (Fin 0 → ℂ) ⊗[ℂ] (Fin 0 → ℂ), x = y := by
    intro x y
    rw [tensor_zero_left_eq x, tensor_zero_left_eq y]
  have hEO : ∀ x y : (Fin 0 → ℂ) ⊗[ℂ] (Fin 1 → ℂ), x = y := by
    intro x y
    rw [tensor_zero_left_eq x, tensor_zero_left_eq y]
  have hOE : ∀ x y : (Fin 1 → ℂ) ⊗[ℂ] (Fin 0 → ℂ), x = y := by
    intro x y
    rw [tensor_zero_right_eq x, tensor_zero_right_eq y]
  apply SuperVect.hom_ext
  · apply LinearMap.ext
    rintro ⟨a, b⟩
    change ((TensorProduct.comm ℂ (Fin 0 → ℂ) (Fin 0 → ℂ)) a,
        -((TensorProduct.comm ℂ (Fin 1 → ℂ) (Fin 1 → ℂ)) b)) =
      (-a, -b)
    refine Prod.ext (hEE _ _) ?_
    exact congrArg Neg.neg (comm_line_self b)
  · apply LinearMap.ext
    rintro ⟨x, y⟩
    change ((TensorProduct.comm ℂ (Fin 1 → ℂ) (Fin 0 → ℂ)) y,
        (TensorProduct.comm ℂ (Fin 0 → ℂ) (Fin 1 → ℂ)) x) =
      (-x, -y)
    exact Prod.ext (hEO _ _) (hOE _ _)

end OddLine

/-! ## The letter system of the standard super object

`ℂ^{p+1|q+1}` carries the evident letter system in `SuperVect`:
unit letters along the even coordinates and odd-line letters along
the odd coordinates.  No biproducts are needed — the inclusions and
projections are written down directly. -/

section SuperLetters

/-- The even component, as an additive map of homs. -/
private def evenMapAdd (V W : SuperVect) :
    (V ⟶ W) →+ (V.even →ₗ[ℂ] W.even) where
  toFun f := SuperVect.Hom.evenMap f
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The odd component, as an additive map of homs. -/
private def oddMapAdd (V W : SuperVect) :
    (V ⟶ W) →+ (V.odd →ₗ[ℂ] W.odd) where
  toFun f := SuperVect.Hom.oddMap f
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The inclusion of an even coordinate line. -/
noncomputable def unitIn (p q : ℕ) (i : Fin (p + 1)) :
    𝟙_ SuperVect ⟶ stdSuper (p + 1) (q + 1) where
  evenMap := LinearMap.single ℂ (fun _ => ℂ) i
  oddMap := 0

/-- The projection onto an even coordinate line. -/
noncomputable def unitPrj (p q : ℕ) (i : Fin (p + 1)) :
    stdSuper (p + 1) (q + 1) ⟶ 𝟙_ SuperVect where
  evenMap := LinearMap.proj i
  oddMap := 0

/-- The inclusion of an odd coordinate line. -/
noncomputable def oddIn (p q : ℕ) (j : Fin (q + 1)) :
    stdSuper 0 1 ⟶ stdSuper (p + 1) (q + 1) where
  evenMap := 0
  oddMap :=
    (LinearMap.single ℂ (fun _ => ℂ) j).comp
      (LinearMap.proj (0 : Fin 1))

/-- The projection onto an odd coordinate line. -/
noncomputable def oddPrj (p q : ℕ) (j : Fin (q + 1)) :
    stdSuper (p + 1) (q + 1) ⟶ stdSuper 0 1 where
  evenMap := 0
  oddMap := LinearMap.pi fun _ : Fin 1 => LinearMap.proj j

/-- The letter inclusions of the standard super object. -/
noncomputable def stdIns (p q : ℕ)
    (k : Fin (p + 1) ⊕ Fin (q + 1)) :
    letterObj (stdSuper 0 1) mixedPar k ⟶ stdSuper (p + 1) (q + 1)
    :=
  Sum.rec (fun i => unitIn p q i) (fun j => oddIn p q j) k

/-- The letter projections of the standard super object. -/
noncomputable def stdPrj (p q : ℕ)
    (k : Fin (p + 1) ⊕ Fin (q + 1)) :
    stdSuper (p + 1) (q + 1) ⟶ letterObj (stdSuper 0 1) mixedPar k
    :=
  Sum.rec (fun i => unitPrj p q i) (fun j => oddPrj p q j) k

/-- The letter decomposition of the identity of the standard super
object. -/
private theorem stdSuper_total (p q : ℕ) :
    (∑ k : Fin (p + 1) ⊕ Fin (q + 1),
      (stdPrj p q k ≫ stdIns p q k :
        stdSuper (p + 1) (q + 1) ⟶ stdSuper (p + 1) (q + 1))) =
    𝟙 (stdSuper (p + 1) (q + 1)) := by
  apply SuperVect.hom_ext
  · have h1 : SuperVect.Hom.evenMap
        ((∑ k : Fin (p + 1) ⊕ Fin (q + 1),
          stdPrj p q k ≫ stdIns p q k :
            stdSuper (p + 1) (q + 1) ⟶ stdSuper (p + 1) (q + 1))) =
        ∑ k : Fin (p + 1) ⊕ Fin (q + 1),
          SuperVect.Hom.evenMap (stdPrj p q k ≫ stdIns p q k) :=
      map_sum (evenMapAdd _ _) _ _
    rw [h1, Fintype.sum_sum_type]
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.sum_apply]
    have hA : ∀ i : Fin (p + 1), SuperVect.Hom.evenMap
        (stdPrj p q (Sum.inl i) ≫ stdIns p q (Sum.inl i)) v =
        Pi.single i (v i) := fun i => rfl
    have hB : ∀ j : Fin (q + 1), SuperVect.Hom.evenMap
        (stdPrj p q (Sum.inr j) ≫ stdIns p q (Sum.inr j)) v = 0 :=
      fun j => rfl
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hA i,
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hB j,
      Finset.sum_const, smul_zero, add_zero]
    exact Finset.univ_sum_single v
  · have h1 : SuperVect.Hom.oddMap
        ((∑ k : Fin (p + 1) ⊕ Fin (q + 1),
          stdPrj p q k ≫ stdIns p q k :
            stdSuper (p + 1) (q + 1) ⟶ stdSuper (p + 1) (q + 1))) =
        ∑ k : Fin (p + 1) ⊕ Fin (q + 1),
          SuperVect.Hom.oddMap (stdPrj p q k ≫ stdIns p q k) :=
      map_sum (oddMapAdd _ _) _ _
    rw [h1, Fintype.sum_sum_type]
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.sum_apply]
    have hA : ∀ i : Fin (p + 1), SuperVect.Hom.oddMap
        (stdPrj p q (Sum.inl i) ≫ stdIns p q (Sum.inl i)) v = 0 :=
      fun i => rfl
    have hB : ∀ j : Fin (q + 1), SuperVect.Hom.oddMap
        (stdPrj p q (Sum.inr j) ≫ stdIns p q (Sum.inr j)) v =
        Pi.single j (v j) := fun j => rfl
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hA i,
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hB j,
      Finset.sum_const, smul_zero, zero_add]
    exact Finset.univ_sum_single v

/-- **The letter system of the standard super object.** -/
noncomputable def stdSuperLetters (p q : ℕ) :
    MixedLetters (Fin (p + 1) ⊕ Fin (q + 1)) mixedPar
      (stdSuper 0 1) (stdSuper (p + 1) (q + 1)) where
  ins := stdIns p q
  prj := stdPrj p q
  ins_prj k := by
    cases k with
    | inl i =>
      apply SuperVect.hom_ext
      · change (LinearMap.proj (R := ℂ) (φ := fun _ : Fin (p + 1) => ℂ)
            i).comp (LinearMap.single ℂ (fun _ => ℂ) i) =
          LinearMap.id
        refine LinearMap.ext fun z => ?_
        change Pi.single (M := fun _ : Fin (p + 1) => ℂ) i z i = z
        rw [Pi.single_eq_same]
      · refine LinearMap.ext fun z => ?_
        exact Subsingleton.elim (α := PUnit) _ _
    | inr j =>
      apply SuperVect.hom_ext
      · refine LinearMap.ext fun z => ?_
        exact Subsingleton.elim (α := Fin 0 → ℂ) _ _
      · change (LinearMap.pi fun _ : Fin 1 =>
            LinearMap.proj (R := ℂ) (φ := fun _ : Fin (q + 1) => ℂ) j).comp
          ((LinearMap.single ℂ (fun _ => ℂ) j).comp
            (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0)) =
          LinearMap.id
        refine LinearMap.ext fun v => ?_
        funext i
        change Pi.single (M := fun _ : Fin (q + 1) => ℂ) j (v 0) j =
          v i
        rw [Pi.single_eq_same, Subsingleton.elim i 0]
  ins_prj_ne {k k'} hkk' := by
    cases k with
    | inl i =>
      cases k' with
      | inl i' =>
        apply SuperVect.hom_ext
        · change (LinearMap.proj (R := ℂ) (φ := fun _ : Fin (p + 1) => ℂ)
              i').comp (LinearMap.single ℂ (fun _ => ℂ) i) = 0
          refine LinearMap.ext fun z => ?_
          change Pi.single (M := fun _ : Fin (p + 1) => ℂ) i z i' = 0
          exact Pi.single_eq_of_ne (M := fun _ : Fin (p + 1) => ℂ)
            (fun h => hkk' (congrArg Sum.inl h.symm)) z
        · refine LinearMap.ext fun z => ?_
          exact Subsingleton.elim (α := PUnit) _ _
      | inr j' =>
        apply SuperVect.hom_ext
        · refine LinearMap.ext fun z => ?_
          exact Subsingleton.elim (α := Fin 0 → ℂ) _ _
        · refine LinearMap.ext fun z => ?_
          change (LinearMap.pi fun _ : Fin 1 =>
              LinearMap.proj (R := ℂ)
                (φ := fun _ : Fin (q + 1) => ℂ) j')
            ((0 : PUnit →ₗ[ℂ] (Fin (q + 1) → ℂ)) z) = 0
          erw [LinearMap.zero_apply, map_zero]
    | inr j =>
      cases k' with
      | inl i' =>
        apply SuperVect.hom_ext
        · refine LinearMap.ext fun z => ?_
          change (LinearMap.proj (R := ℂ)
              (φ := fun _ : Fin (p + 1) => ℂ) i')
            ((0 : (Fin 0 → ℂ) →ₗ[ℂ] (Fin (p + 1) → ℂ)) z) = 0
          rfl
        · refine LinearMap.ext fun z => ?_
          exact Subsingleton.elim (α := PUnit) _ _
      | inr j' =>
        apply SuperVect.hom_ext
        · refine LinearMap.ext fun z => ?_
          exact Subsingleton.elim (α := Fin 0 → ℂ) _ _
        · change (LinearMap.pi fun _ : Fin 1 =>
              LinearMap.proj (R := ℂ) (φ := fun _ : Fin (q + 1) => ℂ)
                j').comp
            ((LinearMap.single ℂ (fun _ => ℂ) j).comp
              (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0)) = 0
          refine LinearMap.ext fun v => ?_
          funext i
          change Pi.single (M := fun _ : Fin (q + 1) => ℂ) j (v 0) j'
            = 0
          exact Pi.single_eq_of_ne (M := fun _ : Fin (q + 1) => ℂ)
            (fun h => hkk' (congrArg Sum.inr h.symm)) (v 0)
  total := stdSuper_total p q

/-- **Reconstruction in `SuperVect`**: vanishing colour sums force
the block idempotent to kill the standard super object. -/
theorem schurKilled_stdSuper_of_colourSum (P₀ : SchurPackage.{0})
    (p q : ℕ) {lam : YoungDiagram}
    (hcs : ∀ c d : Fin lam.card → Fin (p + 1) ⊕ Fin (q + 1),
      colourSum mixedPar (P₀.e lam) c d = 0) :
    SchurKilled P₀ (stdSuper (p + 1) (q + 1)) lam :=
  (stdSuperLetters p q).permAlg_eq_zero stdSuper_braiding_neg hcs

end SuperLetters

/-! ## The summit: nonvanishing of the mixed sum

The exact complement of `schurKilled_unit_odd`: at every diagram
avoiding the cell `(p + 1, q + 1)`, the mixed sum survives.  The
ambient extraction pins the colour sums of the block idempotent to
zero, the reconstruction transports this into `SuperVect`, and the
super trace computation of `not_schurKilled_stdSuper` refutes it.
Both Schur packages have the Jacobi–Trudi character, so their block
idempotents coincide and the two worlds speak about the same
group-algebra element. -/

section Summit

variable {A : Type u}

/-- **The nonvanishing half of Deligne 1.9, internally**: in a
nontrivial ambient category, a direct sum of `p + 1` unit copies
and `q + 1` odd-line copies is *not* Schur-killed at any diagram
avoiding the cell `(p + 1, q + 1)`.  Together with
`schurKilled_unit_odd` this characterises the killed diagrams of
the mixed sum exactly. -/
theorem not_schurKilled_sum
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] [HasBinaryBiproducts A]
    (P : SchurPackage.{v})
    (P₀ : SchurPackage.{0}) (hone : ¬ Limits.IsZero (𝟙_ A))
    {U : A} (hUU : U ⊗ U ≅ 𝟙_ A)
    (hβ : (β_ U U).hom = -(𝟙 (U ⊗ U))) (p q : ℕ)
    {lam : YoungDiagram}
    (hcell : ((p + 1, q + 1) : ℕ × ℕ) ∉ lam) :
    ¬ SchurKilled P (sumPow (𝟙_ A) p ⊞ sumPow U q) lam := by
  intro hkill
  have he : P.e lam = P₀.e lam := by
    rw [P.e_eq_nProjector lam, P₀.e_eq_nProjector lam]
  have hcs :=
    colourSum_eq_zero_of_schurKilled P hone hUU hβ p q hkill
  rw [he] at hcs
  exact not_schurKilled_stdSuper P₀ hcell
    (schurKilled_stdSuper_of_colourSum P₀ p q hcs)

end Summit

end RS
