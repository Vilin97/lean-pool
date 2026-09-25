/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperEmbed.Signs

/-!
# Letter systems and the sign transport

A `MixedLetters` system exhibits an object of a monoidal category
as a family of letters, each of them the unit or a fixed odd line.
The tensor power then decomposes into colourings, and a permutation
routes a colouring to its shuffle scaled by the Koszul sign of
[Signs.lean](Signs.lean).  The matrix of the action of the group
algebra is therefore the same in every ambient category carrying
such a system, which is what makes the colour sum an obstruction
that transports; the two systems it is applied to are built in
[Standard.lean](Standard.lean).

* `MixedLetters`: the structure, with the colouring maps
  `colourInto`/`colourFrom`, their orthogonality and their
  completeness `sum_colourFrom_colourInto`.
* `normIso`, `nIn`, `nOut`: the normalised form of a word power and
  the colouring maps through it.
* `nIn_permMor`: the sign transport — a permutation carries a
  normalised colouring to its shuffle, scaled by `parSign`.
* `colourSum`: the colour sum of a group-algebra element, with
  `colourSum_eq_zero` and `permAlg_eq_zero`: an element kills the
  tensor power exactly when its colour sums vanish.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

/-! ## Letter systems

A `MixedLetters` system exhibits an object `M` as a biproduct-style
family of letters, each a monoidal unit (even) or a fixed line `U`
(odd), without asking the ambient category for biproducts: only the
inclusions, projections, orthogonality and completeness are used. -/

section Letters

variable {A : Type u}

/-- The letter object of a label: the line `U` when the label is
odd, the monoidal unit when it is even. -/
abbrev letterObj [Category.{v} A] [MonoidalCategory A]
    (U : A) {K : Type} (par : K → Bool) (k : K) : A :=
  bif par k then U else 𝟙_ A

/-- **A letter system on `M`**: unit and `U`-letters included into
and projected from `M`, orthonormally and completely. -/
structure MixedLetters
    [Category.{v} A] [MonoidalCategory A]
    [Preadditive A] (K : Type) [Fintype K]
    (par : K → Bool) (U M : A) where
  /-- The inclusion of the letter labelled `k`. -/
  ins : (k : K) → (letterObj U par k ⟶ M)
  /-- The projection onto the letter labelled `k`. -/
  prj : (k : K) → (M ⟶ letterObj U par k)
  /-- A letter's round trip through `M` is the identity. -/
  ins_prj : ∀ k, ins k ≫ prj k = 𝟙 (letterObj U par k)
  /-- Distinct letters' round trips vanish. -/
  ins_prj_ne : ∀ {k k' : K}, k ≠ k' → ins k ≫ prj k' = 0
  /-- The projections and inclusions decompose the identity. -/
  total : (∑ k : K, prj k ≫ ins k) = 𝟙 M

namespace MixedLetters

/-- **The inclusion of a colouring**: the fold of the letterwise
inclusions into the tensor power, in slot order. -/
noncomputable def colourInto
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] {K : Type}
    [Fintype K] {par : K → Bool} {U : A} {M : A}
    (S : MixedLetters K par U M) :
    (n : ℕ) → (c : Fin n → K) →
      (wordPow U (𝟙_ A) n (par ∘ c) ⟶ tensorPow A M n)
  | 0, _ => 𝟙 (𝟙_ A)
  | n + 1, c =>
      S.colourInto n (c ∘ Fin.castSucc) ⊗ₘ S.ins (c (Fin.last n))

/-- **The projection onto a colouring**: the fold of the letterwise
projections from the tensor power. -/
noncomputable def colourFrom
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] {K : Type}
    [Fintype K] {par : K → Bool} {U : A} {M : A}
    (S : MixedLetters K par U M) :
    (n : ℕ) → (c : Fin n → K) →
      (tensorPow A M n ⟶ wordPow U (𝟙_ A) n (par ∘ c))
  | 0, _ => 𝟙 (𝟙_ A)
  | n + 1, c =>
      S.colourFrom n (c ∘ Fin.castSucc) ⊗ₘ S.prj (c (Fin.last n))

/-- The defining recursion of `colourInto`. -/
theorem colourInto_succ
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] {K : Type}
    [Fintype K] {par : K → Bool} {U : A} {M : A}
    (S : MixedLetters K par U M) (n : ℕ)
    (c : Fin (n + 1) → K) :
    S.colourInto (n + 1) c =
      S.colourInto n (c ∘ Fin.castSucc) ⊗ₘ S.ins (c (Fin.last n)) :=
  rfl

/-- Sections tensor to a section; stated at general objects. -/
private theorem tensor_section [Category.{v} A] [MonoidalCategory A]
    {P Q R T : A} (f : P ⟶ Q) (g : Q ⟶ P)
    (h : R ⟶ T) (k : T ⟶ R) (hfg : f ≫ g = 𝟙 P) (hhk : h ≫ k = 𝟙 R) :
    (f ⊗ₘ h) ≫ (g ⊗ₘ k) = 𝟙 (P ⊗ R) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom, hfg, hhk,
    MonoidalCategory.id_tensorHom_id]

/-- **Same-colouring round trip**: a colouring included into the
power and projected back is unchanged. -/
theorem colourInto_colourFrom_same
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] {K : Type}
    [Fintype K] {par : K → Bool} {U : A} {M : A}
    (S : MixedLetters K par U M) :
    ∀ (n : ℕ) (c : Fin n → K),
      S.colourInto n c ≫ S.colourFrom n c =
        𝟙 (wordPow U (𝟙_ A) n (par ∘ c)) := by
  intro n
  induction n with
  | zero => intro c; exact Category.id_comp _
  | succ n ih =>
    intro c
    exact tensor_section _ _ _ _ (ih (c ∘ Fin.castSucc))
      (S.ins_prj (c (Fin.last n)))

/-- Two colourings of positive length differ in the last letter or
in the rest. -/
private theorem colour_ne_cases {K : Type}
    {n : ℕ} {c c' : Fin (n + 1) → K}
    (hcc' : c ≠ c') :
    c ∘ Fin.castSucc ≠ c' ∘ Fin.castSucc ∨
      c (Fin.last n) ≠ c' (Fin.last n) := by
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨h1, h2⟩ := hcon
  refine hcc' (funext fun i => ?_)
  induction i using Fin.lastCases with
  | last => exact h2
  | cast j => exact congrFun h1 j

section MonPre

/-- A vanishing first factor kills the tensor. -/
private theorem tensor_zero_fst
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A]
    {P Q R T V W : A}
    (f : P ⟶ Q) (g : Q ⟶ R) (h : T ⟶ V) (k : V ⟶ W)
    (hfg : f ≫ g = 0) : (f ⊗ₘ h) ≫ (g ⊗ₘ k) = 0 := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom, hfg,
    MonoidalPreadditive.zero_tensor]

/-- A vanishing second factor kills the tensor. -/
private theorem tensor_zero_snd
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A]
    {P Q R T V W : A}
    (f : P ⟶ Q) (g : Q ⟶ R) (h : T ⟶ V) (k : V ⟶ W)
    (hhk : h ≫ k = 0) : (f ⊗ₘ h) ≫ (g ⊗ₘ k) = 0 := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom, hhk,
    MonoidalPreadditive.tensor_zero]

/-- **Distinct-colouring round trips vanish.** -/
theorem colourInto_colourFrom_ne
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] {K : Type}
    [Fintype K] {par : K → Bool} {U : A} {M : A} [MonoidalPreadditive A]
    (S : MixedLetters K par U M) :
    ∀ (n : ℕ) {c c' : Fin n → K}, c ≠ c' →
      S.colourInto n c ≫ S.colourFrom n c' = 0 := by
  intro n
  induction n with
  | zero =>
    intro c c' hcc'
    exact absurd (funext fun i => i.elim0) hcc'
  | succ n ih =>
    intro c c' hcc'
    rcases colour_ne_cases hcc' with h | h
    · exact tensor_zero_fst _ _ _ _ (ih h)
    · exact tensor_zero_snd _ _ _ _ (S.ins_prj_ne h)

/-- One colouring's round trip through the full power, split into
the shorter colouring's round trip and the last letter's. -/
private theorem fromInto_snoc
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] {K : Type}
    [Fintype K] {par : K → Bool} {U : A} {M : A}
    (S : MixedLetters K par U M) (n : ℕ)
    (c' : Fin n → K) (k : K) :
    S.colourFrom (n + 1) (Fin.snoc c' k) ≫
        S.colourInto (n + 1) (Fin.snoc c' k) =
      (S.colourFrom n c' ≫ S.colourInto n c') ⊗ₘ
        (S.prj k ≫ S.ins k) := by
  have hw : (Fin.snoc c' k : Fin (n + 1) → K) ∘ Fin.castSucc = c' :=
    Fin.snoc_comp_castSucc
  have hb : (Fin.snoc c' k : Fin (n + 1) → K) (Fin.last n) = k :=
    Fin.snoc_last ..
  have hww : S.colourFrom n (Fin.snoc c' k ∘ Fin.castSucc) ≫
      S.colourInto n (Fin.snoc c' k ∘ Fin.castSucc) =
    S.colourFrom n c' ≫ S.colourInto n c' := by rw [hw]
  have hbb : S.prj ((Fin.snoc c' k : Fin (n + 1) → K) (Fin.last n)) ≫
      S.ins ((Fin.snoc c' k : Fin (n + 1) → K) (Fin.last n)) =
    S.prj k ≫ S.ins k := by rw [hb]
  rw [← hww, ← hbb]
  exact MonoidalCategory.tensorHom_comp_tensorHom (C := A) _ _ _ _

/-- **Completeness of the colouring decomposition**: the round
trips through the colourings sum to the identity of the power. -/
theorem sum_colourFrom_colourInto
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] {K : Type}
    [Fintype K] {par : K → Bool} {U : A} {M : A} [MonoidalPreadditive A]
    (S : MixedLetters K par U M) :
    ∀ n : ℕ,
      (∑ c : Fin n → K, S.colourFrom n c ≫ S.colourInto n c) =
        𝟙 (tensorPow A M n) := by
  intro n
  induction n with
  | zero =>
    rw [Fintype.sum_unique]
    exact Category.id_comp _
  | succ n ih =>
    have e1 : (∑ c : Fin (n + 1) → K,
          S.colourFrom (n + 1) c ≫ S.colourInto (n + 1) c) =
        ∑ p : K × (Fin n → K),
          S.colourFrom (n + 1) (Fin.snoc p.2 p.1) ≫
            S.colourInto (n + 1) (Fin.snoc p.2 p.1) :=
      (Equiv.sum_comp (Fin.snocEquiv fun _ : Fin (n + 1) => K)
        (fun c => S.colourFrom (n + 1) c ≫
          S.colourInto (n + 1) c)).symm
    have e2 : (∑ p : K × (Fin n → K),
          S.colourFrom (n + 1) (Fin.snoc p.2 p.1) ≫
            S.colourInto (n + 1) (Fin.snoc p.2 p.1)) =
        ∑ p : K × (Fin n → K),
          ((S.colourFrom n p.2 ≫ S.colourInto n p.2) ⊗ₘ
              (S.prj p.1 ≫ S.ins p.1) :
            tensorPow A M (n + 1) ⟶ tensorPow A M (n + 1)) :=
      Finset.sum_congr rfl fun p _ => S.fromInto_snoc n p.2 p.1
    have e3 : (∑ p : K × (Fin n → K),
          ((S.colourFrom n p.2 ≫ S.colourInto n p.2) ⊗ₘ
              (S.prj p.1 ≫ S.ins p.1) :
            tensorPow A M (n + 1) ⟶ tensorPow A M (n + 1))) =
        ∑ k : K, ∑ c' : Fin n → K,
          ((S.colourFrom n c' ≫ S.colourInto n c') ⊗ₘ
              (S.prj k ≫ S.ins k) :
            tensorPow A M (n + 1) ⟶ tensorPow A M (n + 1)) :=
      Fintype.sum_prod_type _
    have e4 : ∀ k : K,
        (∑ c' : Fin n → K,
          ((S.colourFrom n c' ≫ S.colourInto n c') ⊗ₘ
              (S.prj k ≫ S.ins k) :
            tensorPow A M (n + 1) ⟶ tensorPow A M (n + 1))) =
        𝟙 (tensorPow A M n) ⊗ₘ (S.prj k ≫ S.ins k) := by
      intro k
      rw [← ih]
      exact (sum_tensor _ _ _).symm
    have e5 : (∑ k : K, ∑ c' : Fin n → K,
          ((S.colourFrom n c' ≫ S.colourInto n c') ⊗ₘ
              (S.prj k ≫ S.ins k) :
            tensorPow A M (n + 1) ⟶ tensorPow A M (n + 1))) =
        ∑ k : K, 𝟙 (tensorPow A M n) ⊗ₘ (S.prj k ≫ S.ins k) :=
      Finset.sum_congr rfl fun k _ => e4 k
    have e6 : (∑ k : K, 𝟙 (tensorPow A M n) ⊗ₘ
          (S.prj k ≫ S.ins k)) =
        𝟙 (tensorPow A M (n + 1)) := by
      rw [← tensor_sum, S.total, MonoidalCategory.id_tensorHom_id]
      rfl
    exact e1.trans (e2.trans (e3.trans (e5.trans e6)))

end MonPre

end MixedLetters

end Letters

/-! ## Normalising word powers

Every word power of `U` and the unit normalises, by unitors alone,
to the pure power of `U` counted by the word.  Reading the
colouring inclusions and projections through this normal form
confines every transport to powers of `U` indexed by counts. -/

section Norm

variable {A : Type u}

/-- Absorbing one letter into a power of `U`: a `U`-letter extends
the power, a unit letter is stripped by the right unitor. -/
noncomputable def tailIso [Category.{v} A] [MonoidalCategory A]
    (U : A) (k : ℕ) : (b : Bool) →
    (tensorPow A U k ⊗ (bif b then U else 𝟙_ A) ≅
      tensorPow A U (k + (bif b then 1 else 0)))
  | true => Iso.refl (tensorPow A U (k + 1))
  | false => ρ_ (tensorPow A U k)

/-- **The normalisation of a word power**: strip the unit letters
by unitors, leaving the power of `U` of the word's count. -/
noncomputable def normIso [Category.{v} A] [MonoidalCategory A]
    (U : A) : (n : ℕ) → (w : Fin n → Bool) →
    (wordPow U (𝟙_ A) n w ≅ tensorPow A U (popCount w))
  | 0, w => eqToIso (congrArg (tensorPow A U) (popCount_nil w).symm)
  | n + 1, w =>
      whiskerRightIso (normIso U n (w ∘ Fin.castSucc))
          (bif w (Fin.last n) then U else 𝟙_ A) ≪≫
        tailIso U (popCount (w ∘ Fin.castSucc)) (w (Fin.last n)) ≪≫
        eqToIso (congrArg (tensorPow A U) (popCount_succ w).symm)

end Norm

section NormMaps

variable {A : Type u}

/-- The recursion of the normalisation, inverse side. -/
private theorem normIso_inv_succ [Category.{v} A] [MonoidalCategory A]
    (U : A) {n : ℕ}
    (w : Fin (n + 1) → Bool) :
    (normIso U (n + 1) w).inv =
      eqToHom (congrArg (tensorPow A U) (popCount_succ w)) ≫
        (tailIso U (popCount (w ∘ Fin.castSucc)) (w (Fin.last n))).inv ≫
        ((normIso U n (w ∘ Fin.castSucc)).inv ▷
          (bif w (Fin.last n) then U else 𝟙_ A)) := by
  change (whiskerRightIso (normIso U n (w ∘ Fin.castSucc)) _ ≪≫
      tailIso U (popCount (w ∘ Fin.castSucc)) (w (Fin.last n)) ≪≫
      eqToIso (congrArg (tensorPow A U) (popCount_succ w).symm)).inv = _
  simp only [Iso.trans_inv, whiskerRightIso_inv, eqToIso.inv,
    Category.assoc]

/-- The recursion of the normalisation, hom side. -/
private theorem normIso_hom_succ [Category.{v} A] [MonoidalCategory A]
    (U : A) {n : ℕ}
    (w : Fin (n + 1) → Bool) :
    (normIso U (n + 1) w).hom =
      ((normIso U n (w ∘ Fin.castSucc)).hom ▷
          (bif w (Fin.last n) then U else 𝟙_ A)) ≫
        (tailIso U (popCount (w ∘ Fin.castSucc)) (w (Fin.last n))).hom ≫
        eqToHom (congrArg (tensorPow A U) (popCount_succ w).symm) := by
  change (whiskerRightIso (normIso U n (w ∘ Fin.castSucc)) _ ≪≫
      tailIso U (popCount (w ∘ Fin.castSucc)) (w (Fin.last n)) ≪≫
      eqToIso (congrArg (tensorPow A U) (popCount_succ w).symm)).hom = _
  simp only [Iso.trans_hom, whiskerRightIso_hom, eqToIso.hom]

/-- A whisker followed by a tensor merges on the first factor.
Stated at general objects. -/
private theorem whisker_then_tensor [Category.{v} A] [MonoidalCategory A]
    {P Q R T V : A}
    (f : P ⟶ Q) (g : Q ⟶ R) (h : T ⟶ V) :
    (f ▷ T) ≫ (g ⊗ₘ h) = (f ≫ g) ⊗ₘ h := by
  rw [← MonoidalCategory.tensorHom_id f T,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]

/-- Gluing a whisker-ended factorisation onto a tensor.  Stated at
general objects. -/
private theorem split_glue [Category.{v} A] [MonoidalCategory A]
    {W X P P' L Q Q' : A}
    (E : W ⟶ X) (T : X ⟶ P ⊗ L) (N : P ⟶ P') (I : P' ⟶ Q)
    (J : L ⟶ Q') :
    (E ≫ T ≫ (N ▷ L)) ≫ (I ⊗ₘ J) = E ≫ T ≫ ((N ≫ I) ⊗ₘ J) := by
  simp only [Category.assoc]
  rw [whisker_then_tensor]

/-- A tensor followed by a whisker merges on the first factor.
Stated at general objects. -/
private theorem tensor_then_whisker [Category.{v} A] [MonoidalCategory A]
    {P Q R T V : A}
    (f : P ⟶ Q) (g : Q ⟶ R) (h : T ⟶ V) :
    (f ⊗ₘ h) ≫ (g ▷ V) = (f ≫ g) ⊗ₘ h := by
  rw [← MonoidalCategory.tensorHom_id g V,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]

end NormMaps

/-! ## The normalised colouring maps -/

namespace MixedLetters

variable {A : Type u}

/-- **The normalised inclusion of a colouring**: the colouring
inclusion, read off the `U`-power normal form of its word power. -/
noncomputable def nIn
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] {K : Type}
    [Fintype K] {par : K → Bool} {U : A} {M : A}
    (S : MixedLetters K par U M) (n : ℕ)
    (c : Fin n → K) :
    tensorPow A U (popCount (par ∘ c)) ⟶ tensorPow A M n :=
  (normIso U n (par ∘ c)).inv ≫ S.colourInto n c

/-- **The normalised projection onto a colouring.** -/
noncomputable def nOut
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] {K : Type}
    [Fintype K] {par : K → Bool} {U : A} {M : A}
    (S : MixedLetters K par U M) (n : ℕ)
    (c : Fin n → K) :
    tensorPow A M n ⟶ tensorPow A U (popCount (par ∘ c)) :=
  S.colourFrom n c ≫ (normIso U n (par ∘ c)).hom

/-- The colouring inclusion factors through its normalised form. -/
theorem colourInto_eq_nIn
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] {K : Type}
    [Fintype K] {par : K → Bool} {U : A} {M : A}
    (S : MixedLetters K par U M) (n : ℕ)
    (c : Fin n → K) :
    S.colourInto n c = (normIso U n (par ∘ c)).hom ≫ S.nIn n c := by
  rw [nIn, Iso.hom_inv_id_assoc]

/-- **Same-colouring round trip of the normalised maps.** -/
theorem nIn_nOut_same
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] {K : Type}
    [Fintype K] {par : K → Bool} {U : A} {M : A}
    (S : MixedLetters K par U M) (n : ℕ)
    (c : Fin n → K) :
    S.nIn n c ≫ S.nOut n c =
      𝟙 (tensorPow A U (popCount (par ∘ c))) := by
  rw [nIn, nOut]
  slice_lhs 2 3 => rw [S.colourInto_colourFrom_same n c]
  rw [Category.id_comp, Iso.inv_hom_id]

/-- **Distinct-colouring round trips of the normalised maps
vanish.** -/
theorem nIn_nOut_ne
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] {K : Type}
    [Fintype K] {par : K → Bool} {U : A} {M : A}
    [MonoidalPreadditive A]
    (S : MixedLetters K par U M) (n : ℕ) {c c' : Fin n → K}
    (h : c ≠ c') : S.nIn n c ≫ S.nOut n c' = 0 := by
  rw [nIn, nOut]
  slice_lhs 2 3 => rw [S.colourInto_colourFrom_ne n h]
  rw [Limits.zero_comp, Limits.comp_zero]

/-- The recursion of the normalised inclusion: strip the top
letter. -/
theorem nIn_succ
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] {K : Type}
    [Fintype K] {par : K → Bool} {U : A} {M : A}
    (S : MixedLetters K par U M) (n : ℕ)
    (c : Fin (n + 1) → K) :
    S.nIn (n + 1) c =
      eqToHom (congrArg (tensorPow A U) (popCount_succ (par ∘ c))) ≫
        (tailIso U (popCount (par ∘ (c ∘ Fin.castSucc)))
          (par (c (Fin.last n)))).inv ≫
        (S.nIn n (c ∘ Fin.castSucc) ⊗ₘ S.ins (c (Fin.last n))) := by
  rw [nIn, colourInto_succ, normIso_inv_succ]
  exact split_glue _ _ _ _ _

/-- Transport of the normalised inclusion along an equality of
colourings. -/
theorem nIn_congr
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] {K : Type}
    [Fintype K] {par : K → Bool} {U : A} {M : A}
    (S : MixedLetters K par U M) {n : ℕ}
    {c c' : Fin n → K} (h : c = c')
    (hp : popCount (par ∘ c) = popCount (par ∘ c')) :
    S.nIn n c = eqToHom (congrArg (tensorPow A U) hp) ≫ S.nIn n c'
    := by
  subst h
  rw [show congrArg (tensorPow A U) hp =
    (rfl : tensorPow A U (popCount (par ∘ c)) =
      tensorPow A U (popCount (par ∘ c))) from rfl]
  rw [eqToHom_refl, Category.id_comp]

end MixedLetters

/-! ## Reindexing along the generators -/

section PermFacts

open Equiv

/-- Extension to one more slot commutes with inversion. -/
theorem extPerm_inv {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    (extPerm τ)⁻¹ = extPerm τ⁻¹ := by
  rw [eq_comm, eq_inv_iff_mul_eq_one, ← extPerm_mul,
    inv_mul_cancel, extPerm_one]

/-- Reindexing along a top-fixing permutation restricts below the
top slot. -/
theorem permIndex_extPerm_castSucc {K : Type*} {n : ℕ}
    (τ : Equiv.Perm (Fin n)) (c : Fin (n + 1) → K) :
    permIndex (extPerm τ) c ∘ Fin.castSucc =
      permIndex τ (c ∘ Fin.castSucc) := by
  funext j
  change c ((extPerm τ)⁻¹ (Fin.castSucc j)) = c (Fin.castSucc (τ⁻¹ j))
  rw [extPerm_inv, extPerm_castSucc]

/-- Reindexing along a top-fixing permutation fixes the top
letter. -/
theorem permIndex_extPerm_last {K : Type*} {n : ℕ}
    (τ : Equiv.Perm (Fin n)) (c : Fin (n + 1) → K) :
    permIndex (extPerm τ) c (Fin.last n) = c (Fin.last n) := by
  change c ((extPerm τ)⁻¹ (Fin.last n)) = c (Fin.last n)
  rw [extPerm_inv, extPerm_last]

/-- The top transposition is its own inverse. -/
theorem topSwap_inv {n : ℕ} :
    (topSwap : Equiv.Perm (Fin (n + 2)))⁻¹ = topSwap :=
  Equiv.swap_inv _ _

/-- Reindexing along the top transposition, top letter. -/
theorem permIndex_topSwap_last {K : Type*} {n : ℕ}
    (c : Fin (n + 2) → K) :
    permIndex topSwap c (Fin.last (n + 1)) =
      c (Fin.castSucc (Fin.last n)) := by
  change c (topSwap⁻¹ (Fin.last (n + 1))) = _
  rw [topSwap_inv, topSwap_last]

/-- Reindexing along the top transposition, second letter. -/
theorem permIndex_topSwap_castSucc_last {K : Type*} {n : ℕ}
    (c : Fin (n + 2) → K) :
    permIndex topSwap c (Fin.castSucc (Fin.last n)) =
      c (Fin.last (n + 1)) := by
  change c (topSwap⁻¹ (Fin.castSucc (Fin.last n))) = _
  rw [topSwap_inv, topSwap_castSucc_last]

/-- Reindexing along the top transposition, lower letters. -/
theorem permIndex_topSwap_low {K : Type*} {n : ℕ}
    (c : Fin (n + 2) → K) :
    permIndex topSwap c ∘ Fin.castSucc ∘ Fin.castSucc =
      c ∘ Fin.castSucc ∘ Fin.castSucc := by
  funext j
  change c (topSwap⁻¹ (Fin.castSucc (Fin.castSucc j))) = _
  rw [topSwap_inv, topSwap_castSucc_castSucc]
  rfl

end PermFacts

/-! ## The braiding on a pair of letters -/

section LetterSwap

variable {A : Type u}

/-- Conjugation of a scalar of the identity by an isomorphism.
Stated at general objects. -/
private theorem conj_smul_id' [Category.{v} A]
    [Preadditive A] [Linear ℂ A]
    {W V : A} (e : W ≅ V) (c : ℂ) :
    e.hom ≫ (c • 𝟙 V) ≫ e.inv = c • 𝟙 W := by
  simp

/-- Exchanging a braiding of the ambient object for the braiding of
the two included letters.  Stated at general objects. -/
private theorem tensor_swap_exchange [Category.{v} A] [MonoidalCategory A]
    [BraidedCategory A]
    {P Q N La Lb : A} (F : P ⟶ Q) (g : La ⟶ N) (h : Lb ⟶ N) :
    ((F ⊗ₘ g) ⊗ₘ h) ≫ (α_ Q N N).hom ≫ (Q ◁ (β_ N N).hom) ≫
        (α_ Q N N).inv =
      (α_ P La Lb).hom ≫ (P ◁ (β_ La Lb).hom) ≫ (α_ P Lb La).inv ≫
        ((F ⊗ₘ h) ⊗ₘ g) := by
  calc ((F ⊗ₘ g) ⊗ₘ h) ≫ (α_ Q N N).hom ≫ (Q ◁ (β_ N N).hom) ≫
      (α_ Q N N).inv
      = (α_ P La Lb).hom ≫ (F ⊗ₘ (g ⊗ₘ h)) ≫ (Q ◁ (β_ N N).hom) ≫
        (α_ Q N N).inv := by
        rw [← Category.assoc, MonoidalCategory.associator_naturality,
          Category.assoc]
    _ = (α_ P La Lb).hom ≫ (F ⊗ₘ ((g ⊗ₘ h) ≫ (β_ N N).hom)) ≫
        (α_ Q N N).inv := by
        rw [← MonoidalCategory.id_tensorHom,
          ← Category.assoc (F ⊗ₘ (g ⊗ₘ h)),
          MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
    _ = (α_ P La Lb).hom ≫ (F ⊗ₘ ((β_ La Lb).hom ≫ (h ⊗ₘ g))) ≫
        (α_ Q N N).inv := by
        rw [BraidedCategory.braiding_naturality]
    _ = (α_ P La Lb).hom ≫ (P ◁ (β_ La Lb).hom) ≫
        (F ⊗ₘ (h ⊗ₘ g)) ≫ (α_ Q N N).inv := by
        rw [show F ⊗ₘ ((β_ La Lb).hom ≫ (h ⊗ₘ g)) =
          (P ◁ (β_ La Lb).hom) ≫ (F ⊗ₘ (h ⊗ₘ g)) from by
          rw [← MonoidalCategory.id_tensorHom,
            MonoidalCategory.tensorHom_comp_tensorHom,
            Category.id_comp]]
        rw [Category.assoc]
    _ = (α_ P La Lb).hom ≫ (P ◁ (β_ La Lb).hom) ≫ (α_ P Lb La).inv ≫
        ((F ⊗ₘ h) ⊗ₘ g) := by
        rw [MonoidalCategory.associator_inv_naturality]

/-- The conjugated braiding of two unit letters is the identity. -/
private theorem letter_swap_unit_unit [Category.{v} A] [MonoidalCategory A]
    [SymmetricCategory A] (P : A) :
    (α_ P (𝟙_ A) (𝟙_ A)).hom ≫ (P ◁ (β_ (𝟙_ A) (𝟙_ A)).hom) ≫
        (α_ P (𝟙_ A) (𝟙_ A)).inv = 𝟙 ((P ⊗ 𝟙_ A) ⊗ 𝟙_ A) := by
  rw [braiding_unit_self, MonoidalCategory.whiskerLeft_id,
    Category.id_comp, Iso.hom_inv_id]

/-- The conjugated braiding of two odd letters is minus the
identity. -/
private theorem letter_swap_odd_odd [Category.{v} A] [MonoidalCategory A]
    [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] (P : A) {U : A}
    (hβ : (β_ U U).hom = -(𝟙 (U ⊗ U))) :
    (α_ P U U).hom ≫ (P ◁ (β_ U U).hom) ≫ (α_ P U U).inv =
      -(𝟙 ((P ⊗ U) ⊗ U)) := by
  have h1 : (β_ U U).hom = (-1 : ℂ) • 𝟙 (U ⊗ U) := by
    rw [hβ]
    exact (neg_one_smul ℂ _).symm
  rw [h1, MonoidalLinear.whiskerLeft_smul,
    MonoidalCategory.whiskerLeft_id,
    conj_smul_id' (α_ P U U) (-1 : ℂ), neg_one_smul]

/-- The conjugated braiding of a unit letter under an odd letter is
absorbed by unitors. -/
private theorem letter_swap_unit_odd [Category.{v} A] [MonoidalCategory A]
    [SymmetricCategory A]
    (P U : A) :
    ((ρ_ P).inv ▷ U) ≫ (α_ P (𝟙_ A) U).hom ≫
        (P ◁ (β_ (𝟙_ A) U).hom) ≫ (α_ P U (𝟙_ A)).inv =
      (ρ_ (P ⊗ U)).inv := by
  have hb : (β_ (𝟙_ A) U).hom = (λ_ U).hom ≫ (ρ_ U).inv := by
    rw [← braiding_rightUnitor U, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [hb]
  monoidal

/-- The conjugated braiding of an odd letter under a unit letter is
absorbed by unitors. -/
private theorem letter_swap_odd_unit [Category.{v} A] [MonoidalCategory A]
    [SymmetricCategory A]
    (P U : A) :
    (ρ_ (P ⊗ U)).inv ≫ (α_ P U (𝟙_ A)).hom ≫
        (P ◁ (β_ U (𝟙_ A)).hom) ≫ (α_ P (𝟙_ A) U).inv =
      (ρ_ P).inv ▷ U := by
  have hb : (β_ U (𝟙_ A)).hom = (ρ_ U).hom ≫ (λ_ U).inv := by
    rw [← braiding_leftUnitor U, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [hb]
  monoidal

end LetterSwap

/-! ## The sign transport of the permutation action

The heart of the comparison: on the normal form, the action of a
permutation is the transport between the shuffled colourings,
scaled by the combinatorial Koszul sign — the same scalar in every
ambient category. -/

namespace MixedLetters

variable {A : Type u}

/-- Scalars pull out of the first factor of a tensor. -/
private theorem smul_tensorHom
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] [Linear ℂ A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A]
    {P Q R T : A} (a : ℂ) (f : P ⟶ Q)
    (g : R ⟶ T) : (a • f) ⊗ₘ g = a • (f ⊗ₘ g) := by
  rw [MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_def,
    MonoidalLinear.smul_whiskerRight, Linear.smul_comp]

/-- The identity-preserving statement of the sign transport for a
single permutation, quantified over the count proof. -/
private def SignStmt [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] {K : Type} [Fintype K] {par : K → Bool}
    {U : A} {M : A}
    (S : MixedLetters K par U M) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ (c : Fin n → K)
    (h : popCount (par ∘ c) = popCount (par ∘ permIndex σ c)),
    S.nIn n c ≫ permMor M n σ =
      parSign σ (par ∘ c) •
        (eqToHom (congrArg (tensorPow A U) h) ≫
          S.nIn n (permIndex σ c))

/-- The sign transport for the identity permutation. -/
private theorem signStmt_one
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] {K : Type} [Fintype K] {par : K → Bool}
    {U : A} {M : A}
    (S : MixedLetters K par U M) (n : ℕ) :
    S.SignStmt n 1 := by
  intro c h
  rw [permMor_one, Category.comp_id, parSign_one, one_smul]
  exact S.nIn_congr (permIndex_one c).symm h

/-- The sign transport is closed under composition. -/
private theorem signStmt_mul
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] {K : Type} [Fintype K] {par : K → Bool}
    {U : A} {M : A}
    (S : MixedLetters K par U M) {n : ℕ}
    {g τ : Equiv.Perm (Fin n)} (hg : S.SignStmt n g)
    (hτ : S.SignStmt n τ) : S.SignStmt n (g * τ) := by
  intro c h
  rw [permMor_mul, ← Category.assoc,
    hτ c (popCount_permIndex τ (par ∘ c)).symm, Linear.smul_comp,
    Category.assoc,
    hg (permIndex τ c)
      (popCount_permIndex g (permIndex τ (par ∘ c))).symm,
    Linear.comp_smul, smul_smul, parSign_mul, mul_comm,
    eqToHom_trans_assoc]
  rfl

/-- The unit-letter absorption, spelled. -/
@[simp]
theorem tailIso_false [Category.{v} A] [MonoidalCategory A]
    {U : A} (k : ℕ) :
    tailIso U k false = ρ_ (tensorPow A U k) := rfl

/-- The `U`-letter absorption, spelled. -/
@[simp]
theorem tailIso_true [Category.{v} A] [MonoidalCategory A]
    {U : A} (k : ℕ) :
    tailIso U k true = Iso.refl (tensorPow A U (k + 1)) := rfl

/-- A count transport passes the letter absorption. -/
private theorem tailIso_inv_cast [Category.{v} A] [MonoidalCategory A]
    (U : A) {k k' : ℕ} (hk : k = k')
    (b : Bool) :
    (tailIso U k b).inv ≫
        (eqToHom (congrArg (tensorPow A U) hk) ▷
          (bif b then U else 𝟙_ A)) =
      eqToHom (congrArg (tensorPow A U)
          (congrArg (· + (bif b then 1 else 0)) hk)) ≫
        (tailIso U k' b).inv := by
  subst hk
  have e1 : eqToHom (congrArg (tensorPow A U) (Eq.refl k)) =
      𝟙 (tensorPow A U k) := eqToHom_refl _ _
  have e2 : eqToHom (congrArg (tensorPow A U)
      (congrArg (· + (bif b then 1 else 0)) (Eq.refl k))) =
      𝟙 (tensorPow A U (k + (bif b then 1 else 0))) :=
    eqToHom_refl _ _
  rw [e1, e2, MonoidalCategory.id_whiskerRight, Category.comp_id,
    Category.id_comp]

/-- A count transport passes the letter absorption, with a tail. -/
private theorem tailIso_inv_cast_assoc [Category.{v} A] [MonoidalCategory A]
    (U : A) {k k' : ℕ}
    (hk : k = k') (b : Bool) {Z : A}
    (X : tensorPow A U k' ⊗ (bif b then U else 𝟙_ A) ⟶ Z) :
    (tailIso U k b).inv ≫
        ((eqToHom (congrArg (tensorPow A U) hk) ▷
          (bif b then U else 𝟙_ A)) ≫ X) =
      eqToHom (congrArg (tensorPow A U)
          (congrArg (· + (bif b then 1 else 0)) hk)) ≫
        (tailIso U k' b).inv ≫ X := by
  rw [← Category.assoc, tailIso_inv_cast U hk b, Category.assoc]

/-- The letter count of a colouring splits off the last letter, in
the composite spelling. -/
theorem popCount_split {K : Type} {par : K → Bool}
    {n : ℕ} (c : Fin (n + 1) → K) :
    popCount (par ∘ c) =
      popCount (par ∘ (c ∘ Fin.castSucc)) +
        (bif par (c (Fin.last n)) then 1 else 0) :=
  popCount_succ (par ∘ c)

/-- Reindexing preserves letter counts, in the composite
spelling. -/
theorem popCount_permIndex' {K : Type} {par : K → Bool}
    {n : ℕ} (σ : Equiv.Perm (Fin n))
    (c : Fin n → K) :
    popCount (par ∘ c) = popCount (par ∘ permIndex σ c) :=
  (popCount_permIndex σ (par ∘ c)).symm

/-- Splitting the normalised inclusion at the last letter, with the
tail and last letter replaced by given values. -/
theorem nIn_split
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] {K : Type}
    [Fintype K] {par : K → Bool} {U : A} {M : A}
    (S : MixedLetters K par U M) (n : ℕ)
    (c : Fin (n + 1) → K) (c' : Fin n → K) (k : K)
    (hc : c ∘ Fin.castSucc = c') (hk : c (Fin.last n) = k)
    (h : popCount (par ∘ c) =
      popCount (par ∘ c') + (bif par k then 1 else 0)) :
    S.nIn (n + 1) c =
      eqToHom (congrArg (tensorPow A U) h) ≫
        (tailIso U (popCount (par ∘ c')) (par k)).inv ≫
        (S.nIn n c' ⊗ₘ S.ins k) := by
  subst hc
  subst hk
  exact S.nIn_succ n c

/-- The complete gluing of the top-fixing case.  All specific
morphisms enter as parameters, so the tensor-power arities never
meet a rewrite. -/
private theorem ext_glue
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] [Linear ℂ A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A]
    {W W' Xa Xb Pd Pe Pn L N : A}
    (E₀ : W ⟶ Xa) (Ti : Xa ⟶ Pd ⊗ L) (I : Pd ⟶ Pn) (J : L ⟶ N)
    (G : Pn ⟶ Pn) (a : ℂ) (Ec : Pd ⟶ Pe) (I' : Pe ⟶ Pn)
    (Ed : Xa ⟶ Xb) (Ti' : Xb ⟶ Pe ⊗ L) (Eh : W ⟶ W') (E₂ : W' ⟶ Xb)
    (hI : I ≫ G = a • (Ec ≫ I'))
    (hT : Ti ≫ (Ec ▷ L) = Ed ≫ Ti')
    (hE : E₀ ≫ Ed = Eh ≫ E₂) :
    (E₀ ≫ Ti ≫ (I ⊗ₘ J)) ≫ (G ▷ N) =
      a • (Eh ≫ E₂ ≫ Ti' ≫ (I' ⊗ₘ J)) := by
  calc (E₀ ≫ Ti ≫ (I ⊗ₘ J)) ≫ (G ▷ N)
      = E₀ ≫ Ti ≫ ((I ≫ G) ⊗ₘ J) := by
        simp only [Category.assoc]
        rw [tensor_then_whisker]
    _ = a • (E₀ ≫ Ti ≫ ((Ec ≫ I') ⊗ₘ J)) := by
        rw [hI, smul_tensorHom]
        simp only [Linear.comp_smul]
    _ = a • (E₀ ≫ (Ti ≫ (Ec ▷ L)) ≫ (I' ⊗ₘ J)) := by
        rw [← whisker_then_tensor]
        simp only [Category.assoc]
    _ = a • ((E₀ ≫ Ed) ≫ Ti' ≫ (I' ⊗ₘ J)) := by
        rw [hT]
        simp only [Category.assoc]
    _ = a • (Eh ≫ E₂ ≫ Ti' ≫ (I' ⊗ₘ J)) := by
        rw [hE]
        simp only [Category.assoc]

/-- The sign transport lifts along a top-fixing extension. -/
private theorem signStmt_extPerm
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] {K : Type} [Fintype K] {par : K → Bool} {U : A}
    {M : A}
    (S : MixedLetters K par U M)
    {n : ℕ} {τ : Equiv.Perm (Fin n)} (hτ : S.SignStmt n τ)
    (hε : ∀ c : Fin (n + 1) → K,
      parSign (extPerm τ) (par ∘ c) =
        parSign τ (par ∘ (c ∘ Fin.castSucc))) :
    S.SignStmt (n + 1) (extPerm τ) := by
  intro c h
  have hcount : popCount (par ∘ permIndex (extPerm τ) c) =
      popCount (par ∘ permIndex τ (c ∘ Fin.castSucc)) +
        (bif par (c (Fin.last n)) then 1 else 0) := by
    have h1 := popCount_succ (par ∘ permIndex (extPerm τ) c)
    rw [h1,
      show (par ∘ permIndex (extPerm τ) c) ∘ Fin.castSucc =
        par ∘ permIndex τ (c ∘ Fin.castSucc) from
        congrArg (fun f => par ∘ f) (permIndex_extPerm_castSucc τ c),
      show (par ∘ permIndex (extPerm τ) c) (Fin.last n) =
        par (c (Fin.last n)) from
        congrArg par (permIndex_extPerm_last τ c)]
  rw [permMor_extPerm,
    S.nIn_split n c (c ∘ Fin.castSucc) (c (Fin.last n)) rfl rfl
      (popCount_split c),
    S.nIn_split n (permIndex (extPerm τ) c)
      (permIndex τ (c ∘ Fin.castSucc)) (c (Fin.last n))
      (permIndex_extPerm_castSucc τ c) (permIndex_extPerm_last τ c)
      hcount,
    hε c]
  exact ext_glue _ _ _ _ _ _ _ _ _ _ _ _
    (hτ (c ∘ Fin.castSucc)
      (popCount_permIndex' τ (c ∘ Fin.castSucc)))
    (tailIso_inv_cast U (popCount_permIndex' τ (c ∘ Fin.castSucc))
      (par (c (Fin.last n))))
    (by rw [eqToHom_trans, eqToHom_trans])

/-- Prefixing a scalar identity of chains.  Stated at general
objects. -/
private theorem smul_chain_glue [Category.{v} A] [Preadditive A] [Linear ℂ A]
    {W X Y : A} (E E' : W ⟶ X)
    (hE : E = E') (F G : X ⟶ Y) (a : ℂ) (hFG : F = a • G) :
    E ≫ F = a • (E' ≫ G) := by
  subst hE
  rw [hFG, Linear.comp_smul]

/-- The letter-swap chain at two even letters. -/
private theorem chain_ff
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] {U : A}
    (m : ℕ) (a : ℂ) (ha : a = 1)
    (E : tensorPow A U m ⟶ tensorPow A U m) (hE : E = 𝟙 _) :
    (ρ_ (tensorPow A U m)).inv ≫
        ((ρ_ (tensorPow A U m)).inv ▷ 𝟙_ A) ≫
        (α_ (tensorPow A U m) (𝟙_ A) (𝟙_ A)).hom ≫
        (tensorPow A U m ◁ (β_ (𝟙_ A) (𝟙_ A)).hom) ≫
        (α_ (tensorPow A U m) (𝟙_ A) (𝟙_ A)).inv =
      a • (E ≫ (ρ_ (tensorPow A U m)).inv ≫
        ((ρ_ (tensorPow A U m)).inv ▷ 𝟙_ A)) := by
  subst ha
  rw [hE, one_smul, Category.id_comp,
    letter_swap_unit_unit (tensorPow A U m), Category.comp_id]

/-- The letter-swap chain at an even letter under an odd one. -/
private theorem chain_ft
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] {U : A}
    (m : ℕ) (a : ℂ) (ha : a = 1)
    (E : tensorPow A U m ⊗ U ⟶ tensorPow A U m ⊗ U) (hE : E = 𝟙 _) :
    𝟙 (tensorPow A U m ⊗ U) ≫
        ((ρ_ (tensorPow A U m)).inv ▷ U) ≫
        (α_ (tensorPow A U m) (𝟙_ A) U).hom ≫
        (tensorPow A U m ◁ (β_ (𝟙_ A) U).hom) ≫
        (α_ (tensorPow A U m) U (𝟙_ A)).inv =
      a • (E ≫ (ρ_ (tensorPow A U m ⊗ U)).inv ≫
        (𝟙 (tensorPow A U m ⊗ U) ▷ 𝟙_ A)) := by
  subst ha
  rw [hE, one_smul, Category.id_comp, Category.id_comp,
    MonoidalCategory.id_whiskerRight, Category.comp_id]
  exact letter_swap_unit_odd (tensorPow A U m) U

/-- The letter-swap chain at an odd letter under an even one. -/
private theorem chain_tf
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] {U : A}
    (m : ℕ) (a : ℂ) (ha : a = 1)
    (E : tensorPow A U m ⊗ U ⟶ tensorPow A U m ⊗ U) (hE : E = 𝟙 _) :
    (ρ_ (tensorPow A U m ⊗ U)).inv ≫
        (𝟙 (tensorPow A U m ⊗ U) ▷ 𝟙_ A) ≫
        (α_ (tensorPow A U m) U (𝟙_ A)).hom ≫
        (tensorPow A U m ◁ (β_ U (𝟙_ A)).hom) ≫
        (α_ (tensorPow A U m) (𝟙_ A) U).inv =
      a • (E ≫ 𝟙 (tensorPow A U m ⊗ U) ≫
        ((ρ_ (tensorPow A U m)).inv ▷ U)) := by
  subst ha
  rw [hE, one_smul, MonoidalCategory.id_whiskerRight,
    Category.id_comp, Category.id_comp, Category.id_comp]
  exact letter_swap_odd_unit (tensorPow A U m) U

/-- The letter-swap chain at two odd letters: the sign appears. -/
private theorem chain_tt
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] {U : A}
    (hβ : (β_ U U).hom = -(𝟙 (U ⊗ U)))
    (m : ℕ) (a : ℂ) (ha : a = -1)
    (E : (tensorPow A U m ⊗ U) ⊗ U ⟶ (tensorPow A U m ⊗ U) ⊗ U)
    (hE : E = 𝟙 _) :
    𝟙 ((tensorPow A U m ⊗ U) ⊗ U) ≫
        (𝟙 (tensorPow A U m ⊗ U) ▷ U) ≫
        (α_ (tensorPow A U m) U U).hom ≫
        (tensorPow A U m ◁ (β_ U U).hom) ≫
        (α_ (tensorPow A U m) U U).inv =
      a • (E ≫ 𝟙 ((tensorPow A U m ⊗ U) ⊗ U) ≫
        (𝟙 (tensorPow A U m ⊗ U) ▷ U)) := by
  subst ha
  rw [hE, Category.id_comp, MonoidalCategory.id_whiskerRight,
    Category.id_comp, Category.id_comp, Category.id_comp,
    letter_swap_odd_odd (tensorPow A U m) hβ]
  exact (neg_one_smul ℂ _).symm

/-- **The letter-swap core**: on normal forms, braiding the top two
letters is the transport to the swapped word, with sign `−1`
exactly when both letters are odd.  The case analysis on the two
letters happens here, where they are free Booleans. -/
private theorem tail_swap_core
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] {U : A}
    (hβ : (β_ U U).hom = -(𝟙 (U ⊗ U)))
    (m : ℕ) (b₁ b₂ : Bool)
    (hQ : tensorPow A U
        (m + (bif b₁ then 1 else 0) + (bif b₂ then 1 else 0)) =
      tensorPow A U
        (m + (bif b₂ then 1 else 0) + (bif b₁ then 1 else 0))) :
    (tailIso U (m + (bif b₁ then 1 else 0)) b₂).inv ≫
      ((tailIso U m b₁).inv ▷ (bif b₂ then U else 𝟙_ A)) ≫
      (α_ (tensorPow A U m) (bif b₁ then U else 𝟙_ A)
        (bif b₂ then U else 𝟙_ A)).hom ≫
      (tensorPow A U m ◁
        (β_ (bif b₁ then U else 𝟙_ A) (bif b₂ then U else 𝟙_ A)).hom)
        ≫
      (α_ (tensorPow A U m) (bif b₂ then U else 𝟙_ A)
        (bif b₁ then U else 𝟙_ A)).inv =
    (if b₁ = true ∧ b₂ = true then (-1 : ℂ) else 1) •
      (eqToHom hQ ≫
        (tailIso U (m + (bif b₂ then 1 else 0)) b₁).inv ≫
        ((tailIso U m b₂).inv ▷ (bif b₁ then U else 𝟙_ A))) := by
  cases b₁ <;> cases b₂
  · exact chain_ff m _ (by simp) _ (eqToHom_refl _ _)
  · exact chain_ft m _ (by simp) _ (eqToHom_refl _ _)
  · exact chain_tf m _ (by simp) _ (eqToHom_refl _ _)
  · exact chain_tt hβ m _ (by simp) _ (eqToHom_refl _ _)

/-- The complete gluing of the top-transposition case: the two
letter maps exchange through the braiding of the ambient object,
and everything else is carried by the core hypothesis.  Stated at
general objects. -/
private theorem topSwap_glue
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A]
    {W W' Xa Xb Xc Xd Q₂ Q₁ P Pm L₁ L₂ N : A}
    (a : ℂ)
    (E₀ : W ⟶ Xa) (T₂i : Xa ⟶ Q₂ ⊗ L₂)
    (E₁ : Q₂ ⟶ Xc) (T₁i : Xc ⟶ P ⊗ L₁)
    (I : P ⟶ Pm) (J₁ : L₁ ⟶ N) (J₂ : L₂ ⟶ N)
    (Eh : W ⟶ W') (E₂ : W' ⟶ Xb) (T₂i' : Xb ⟶ Q₁ ⊗ L₁)
    (E₁' : Q₁ ⟶ Xd) (T₁i' : Xd ⟶ P ⊗ L₂)
    (hcore : E₀ ≫ T₂i ≫ ((E₁ ≫ T₁i) ▷ L₂) ≫ (α_ P L₁ L₂).hom ≫
        (P ◁ (β_ L₁ L₂).hom) ≫ (α_ P L₂ L₁).inv =
      a • (Eh ≫ E₂ ≫ T₂i' ≫ ((E₁' ≫ T₁i') ▷ L₁))) :
    (E₀ ≫ T₂i ≫ ((E₁ ≫ T₁i ≫ (I ⊗ₘ J₁)) ⊗ₘ J₂)) ≫
        (α_ Pm N N).hom ≫ (Pm ◁ (β_ N N).hom) ≫ (α_ Pm N N).inv =
      a • (Eh ≫ E₂ ≫ T₂i' ≫ ((E₁' ≫ T₁i' ≫ (I ⊗ₘ J₂)) ⊗ₘ J₁)) := by
  have hsplit : (E₁ ≫ T₁i ≫ (I ⊗ₘ J₁)) ⊗ₘ J₂ =
      ((E₁ ≫ T₁i) ▷ L₂) ≫ ((I ⊗ₘ J₁) ⊗ₘ J₂) := by
    rw [whisker_then_tensor]
    simp only [Category.assoc]
  have hsplit' : (E₁' ≫ T₁i' ≫ (I ⊗ₘ J₂)) ⊗ₘ J₁ =
      ((E₁' ≫ T₁i') ▷ L₁) ≫ ((I ⊗ₘ J₂) ⊗ₘ J₁) := by
    rw [whisker_then_tensor]
    simp only [Category.assoc]
  rw [hsplit, hsplit']
  simp only [Category.assoc]
  rw [tensor_swap_exchange I J₁ J₂]
  have h1 := congrArg (fun t => t ≫ ((I ⊗ₘ J₂) ⊗ₘ J₁)) hcore
  simp only [Category.assoc, Linear.smul_comp] at h1
  exact h1
/-- Composing a scalar identity of chains across a transport.
Stated at general objects. -/
private theorem smul_cast_glue [Category.{v} A] [Preadditive A] [Linear ℂ A]
    {W X X' Y : A} (E : W ⟶ X)
    (Ecast : X ⟶ X') (E' : W ⟶ X') (F : X ⟶ Y) (G : X' ⟶ Y) (a : ℂ)
    (hEE : E ≫ Ecast = E') (hFG : F = a • (Ecast ≫ G)) :
    E ≫ F = a • (E' ≫ G) := by
  rw [hFG, Linear.comp_smul, ← Category.assoc, hEE]

/-- The sign transport holds for the top transposition. -/
private theorem signStmt_topSwap
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] {K : Type} [Fintype K] {par : K → Bool} {U : A}
    {M : A}
    (S : MixedLetters K par U M)
    (hβ : (β_ U U).hom = -(𝟙 (U ⊗ U))) {n : ℕ} :
    S.SignStmt (n + 2) (topSwap : Equiv.Perm (Fin (n + 2))) := by
  intro c h
  have hd_last : permIndex topSwap c (Fin.last (n + 1)) =
      c (Fin.castSucc (Fin.last n)) := permIndex_topSwap_last c
  have hd_mid : (permIndex topSwap c ∘ Fin.castSucc) (Fin.last n) =
      c (Fin.last (n + 1)) := permIndex_topSwap_castSucc_last c
  have hd_low : (permIndex topSwap c ∘ Fin.castSucc) ∘ Fin.castSucc =
      c ∘ Fin.castSucc ∘ Fin.castSucc := permIndex_topSwap_low c
  have hm₁ : popCount (par ∘ (c ∘ Fin.castSucc)) =
      popCount (par ∘ (c ∘ Fin.castSucc ∘ Fin.castSucc)) +
        (bif par (c (Fin.castSucc (Fin.last n))) then 1 else 0) :=
    popCount_split (c ∘ Fin.castSucc)
  have hcount₁ : popCount (par ∘ permIndex topSwap c) =
      popCount (par ∘ (permIndex topSwap c ∘ Fin.castSucc)) +
        (bif par (c (Fin.castSucc (Fin.last n))) then 1 else 0) := by
    have h0 := popCount_split (par := par) (permIndex topSwap c)
    rwa [show par (permIndex topSwap c (Fin.last (n + 1))) =
      par (c (Fin.castSucc (Fin.last n))) from congrArg par hd_last]
      at h0
  have hcount₂ :
      popCount (par ∘ (permIndex topSwap c ∘ Fin.castSucc)) =
      popCount (par ∘ (c ∘ Fin.castSucc ∘ Fin.castSucc)) +
        (bif par (c (Fin.last (n + 1))) then 1 else 0) := by
    have h0 := popCount_split (par := par)
      (permIndex topSwap c ∘ Fin.castSucc)
    rwa [show par ((permIndex topSwap c ∘ Fin.castSucc) (Fin.last n))
        = par (c (Fin.last (n + 1))) from congrArg par hd_mid,
      show (permIndex topSwap c ∘ Fin.castSucc) ∘ Fin.castSucc =
        c ∘ Fin.castSucc ∘ Fin.castSucc from hd_low] at h0
  have hws : parSign topSwap (par ∘ c) =
      if par (c (Fin.castSucc (Fin.last n))) = true ∧
          par (c (Fin.last (n + 1))) = true then (-1 : ℂ) else 1 := by
    rw [show (topSwap : Equiv.Perm (Fin (n + 2))) =
      Equiv.swap (Fin.last n).castSucc (Fin.last n).succ from by
        rw [topSwap, Fin.succ_last],
      parSign_swap (Fin.last n) (par ∘ c),
      show (Fin.last n).succ = Fin.last (n + 1) from Fin.succ_last n]
    rfl
  rw [permMor_topSwap_eq,
    show swapTop M n = (α_ (tensorPow A M n) M M).hom ≫
      (tensorPow A M n ◁ (β_ M M).hom) ≫
      (α_ (tensorPow A M n) M M).inv from rfl,
    S.nIn_split (n + 1) c (c ∘ Fin.castSucc) (c (Fin.last (n + 1)))
      rfl rfl (popCount_split c),
    S.nIn_split n (c ∘ Fin.castSucc)
      (c ∘ Fin.castSucc ∘ Fin.castSucc)
      (c (Fin.castSucc (Fin.last n))) rfl rfl hm₁,
    S.nIn_split (n + 1) (permIndex topSwap c)
      (permIndex topSwap c ∘ Fin.castSucc)
      (c (Fin.castSucc (Fin.last n))) rfl hd_last hcount₁,
    S.nIn_split n (permIndex topSwap c ∘ Fin.castSucc)
      (c ∘ Fin.castSucc ∘ Fin.castSucc) (c (Fin.last (n + 1)))
      hd_low hd_mid hcount₂,
    hws]
  refine topSwap_glue _ _ _ _ _ _ _ _ _ _ _ _ _ ?_
  rw [MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.comp_whiskerRight]
  simp only [Category.assoc]
  rw [tailIso_inv_cast_assoc U hm₁ (par (c (Fin.last (n + 1)))),
    tailIso_inv_cast_assoc U hcount₂
      (par (c (Fin.castSucc (Fin.last n)))),
    eqToHom_trans_assoc, eqToHom_trans_assoc, eqToHom_trans_assoc]
  exact smul_cast_glue _
    (eqToHom (congrArg (tensorPow A U)
      (Nat.add_right_comm
        (popCount (par ∘ (c ∘ Fin.castSucc ∘ Fin.castSucc)))
        (bif par (c (Fin.castSucc (Fin.last n))) then 1 else 0)
        (bif par (c (Fin.last (n + 1))) then 1 else 0)))) _ _ _ _
    (by rw [eqToHom_trans])
    (tail_swap_core hβ
      (popCount (par ∘ (c ∘ Fin.castSucc ∘ Fin.castSucc)))
      (par (c (Fin.castSucc (Fin.last n))))
      (par (c (Fin.last (n + 1))))
      (congrArg (tensorPow A U)
        (Nat.add_right_comm
          (popCount (par ∘ (c ∘ Fin.castSucc ∘ Fin.castSucc)))
          (bif par (c (Fin.castSucc (Fin.last n))) then 1 else 0)
          (bif par (c (Fin.last (n + 1))) then 1 else 0))))

/-- The sign transport holds for every permutation: generators and
closure. -/
private theorem signStmt_all
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] {K : Type} [Fintype K] {par : K → Bool} {U : A}
    {M : A}
    (S : MixedLetters K par U M)
    (hβ : (β_ U U).hom = -(𝟙 (U ⊗ U))) :
    ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)), S.SignStmt n σ := by
  intro n
  induction n with
  | zero =>
    intro σ
    rw [show σ = 1 from Equiv.ext fun x => x.elim0]
    exact S.signStmt_one 0
  | succ n' ih =>
    match n' with
    | 0 =>
      intro σ
      rw [show σ = 1 from Equiv.ext fun x => Fin.ext (by omega)]
      exact S.signStmt_one 1
    | n'' + 1 =>
      intro σ
      have hgen : ∀ i : Fin (n'' + 1),
          S.SignStmt (n'' + 2) (Equiv.swap i.castSucc i.succ) := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [show Equiv.swap (Fin.castSucc (Fin.last n''))
            (Fin.last n'').succ =
              (topSwap : Equiv.Perm (Fin (n'' + 2))) from by
            rw [topSwap, Fin.succ_last]]
          exact S.signStmt_topSwap hβ
        · rw [swap_castSucc_succ_castSucc j]
          refine S.signStmt_extPerm
            (ih (Equiv.swap j.castSucc j.succ)) ?_
          intro c
          rw [← swap_castSucc_succ_castSucc j,
            parSign_swap (Fin.castSucc j) (par ∘ c),
            parSign_swap j (par ∘ (c ∘ Fin.castSucc)),
            Fin.succ_castSucc]
          rfl
      have key : ∀ τ : Equiv.Perm (Fin (n'' + 2)),
          τ ∈ Submonoid.closure
            (Set.range fun i : Fin (n'' + 1) =>
              Equiv.swap i.castSucc i.succ) →
          S.SignStmt (n'' + 2) τ := by
        intro τ hτ
        induction hτ using Submonoid.closure_induction_left with
        | one => exact S.signStmt_one _
        | mul_left g hg τ' hτ' ihτ' =>
          obtain ⟨i, rfl⟩ := hg
          exact S.signStmt_mul (hgen i) ihτ'
      exact key σ (by
        rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial)

/-- **The sign transport of the permutation action**: on normal
forms, a permutation acts on a colouring of a letter system by the
transport to the shuffled colouring, scaled by the combinatorial
Koszul sign of the shuffle. -/
theorem nIn_permMor [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] {K : Type} [Fintype K] {par : K → Bool} {U : A}
    {M : A}
    (S : MixedLetters K par U M)
    (hβ : (β_ U U).hom = -(𝟙 (U ⊗ U))) {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (c : Fin n → K)
    (h : popCount (par ∘ c) = popCount (par ∘ permIndex σ c)) :
    S.nIn n c ≫ permMor M n σ =
      parSign σ (par ∘ c) •
        (eqToHom (congrArg (tensorPow A U) h) ≫
          S.nIn n (permIndex σ c)) :=
  S.signStmt_all hβ n σ c h

end MixedLetters

/-! ## The colour sum

The matrix coefficient of a group-algebra element between two
colourings: the sum of its coefficients over the permutations
routing the one colouring to the other, weighted by the Koszul
sign.  It is purely combinatorial — the same scalar in every
ambient category carrying a letter system. -/

/-- **The colour sum**: the signed coefficient sum of a
group-algebra element over the permutations carrying `c` to `d`. -/
noncomputable def colourSum {K : Type} [DecidableEq K]
    (par : K → Bool) {n : ℕ} (x : SymGroupAlgebra n)
    (c d : Fin n → K) : ℂ :=
  ∑ σ ∈ Finset.univ.filter
      (fun σ : Equiv.Perm (Fin n) => permIndex σ c = d),
    x.coeff σ * parSign σ (par ∘ c)

/-- The colour sum vanishes between colourings of different
counts. -/
theorem colourSum_eq_zero_of_ne {K : Type} [DecidableEq K]
    (par : K → Bool) {n : ℕ} (x : SymGroupAlgebra n)
    {c d : Fin n → K}
    (h : popCount (par ∘ c) ≠ popCount (par ∘ d)) :
    colourSum par x c d = 0 := by
  rw [colourSum]
  refine Finset.sum_eq_zero fun σ hσ => ?_
  exfalso
  refine h ?_
  rw [← (Finset.mem_filter.mp hσ).2]
  exact (popCount_permIndex σ (par ∘ c)).symm

namespace MixedLetters

section Entries

variable {A : Type u}

/-- The group-algebra action expanded over the group. -/
private theorem permAlg_expand
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A]
    (X : A) {n : ℕ}
    (x : SymGroupAlgebra n) :
    permAlg X n x = ∑ σ : Equiv.Perm (Fin n), x.coeff σ • permMor X n σ
    := by
  classical
  have hlift : permAlg X n x =
      x.coeff.sum fun σ r => r • permMor X n σ := by
    rw [permAlg]
    exact MonoidAlgebra.lift_apply _ _
  rw [hlift, show (x.coeff.sum fun σ r => r • permMor X n σ) =
    ∑ σ ∈ x.coeff.support, x.coeff σ • permMor X n σ from rfl]
  refine Finset.sum_subset (Finset.subset_univ _) fun σ _ hσ => ?_
  rw [Finsupp.notMem_support_iff.mp hσ, zero_smul]

/-- The round trip through equal colourings is the transport. -/
private theorem nIn_nOut_of_eq
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] {K : Type}
    [Fintype K] {par : K → Bool} {U : A} {M : A}
    (S : MixedLetters K par U M) {n : ℕ}
    {c' d : Fin n → K} (hcd : c' = d) :
    S.nIn n c' ≫ S.nOut n d =
      eqToHom (congrArg (fun e => tensorPow A U (popCount (par ∘ e)))
        hcd) := by
  subst hcd
  rw [S.nIn_nOut_same]
  exact (eqToHom_refl _ _).symm

/-- **The entry formula**: between two colourings, the normalised
matrix entry of a group-algebra element is the colour sum times the
count transport. -/
theorem nIn_permAlg_nOut
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] {K : Type} [Fintype K] [DecidableEq K]
    {par : K → Bool} {U : A} {M : A}
    (S : MixedLetters K par U M)
    (hβ : (β_ U U).hom = -(𝟙 (U ⊗ U))) {n : ℕ}
    (x : SymGroupAlgebra n) (c d : Fin n → K) :
    S.nIn n c ≫ permAlg M n x ≫ S.nOut n d =
      if hpop : popCount (par ∘ c) = popCount (par ∘ d) then
        colourSum par x c d •
          eqToHom (congrArg (tensorPow A U) hpop)
      else 0 := by
  have hstep : S.nIn n c ≫ permAlg M n x ≫ S.nOut n d =
      ∑ σ : Equiv.Perm (Fin n),
        ((x.coeff σ * parSign σ (par ∘ c)) •
          (eqToHom (congrArg (tensorPow A U)
            (popCount_permIndex' σ c)) ≫
            S.nIn n (permIndex σ c))) ≫ S.nOut n d := by
    rw [permAlg_expand M x, Preadditive.sum_comp,
      Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Linear.smul_comp, Linear.comp_smul, ← Category.assoc,
      S.nIn_permMor hβ σ c (popCount_permIndex' σ c),
      Linear.smul_comp, smul_smul, Linear.smul_comp]
  rw [hstep]
  by_cases hpop : popCount (par ∘ c) = popCount (par ∘ d)
  · rw [dite_eq_left hpop, colourSum, Finset.sum_filter,
      Finset.sum_smul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    by_cases hσ : permIndex σ c = d
    · rw [ite_eq_left hσ, Linear.smul_comp, Category.assoc,
        S.nIn_nOut_of_eq hσ, eqToHom_trans]
    · rw [ite_eq_right hσ, Linear.smul_comp, Category.assoc,
        S.nIn_nOut_ne n hσ, Limits.comp_zero, smul_zero, zero_smul]
  · rw [dite_eq_right hpop]
    refine Finset.sum_eq_zero fun σ _ => ?_
    have hσ : permIndex σ c ≠ d := fun hcd => hpop (by
      rw [← hcd]
      exact popCount_permIndex' σ c)
    rw [Linear.smul_comp, Category.assoc, S.nIn_nOut_ne n hσ,
      Limits.comp_zero, smul_zero]

/-- The colouring projection factors through its normalised form. -/
theorem colourFrom_eq_nOut
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] {K : Type}
    [Fintype K] {par : K → Bool} {U : A} {M : A}
    (S : MixedLetters K par U M) (n : ℕ)
    (d : Fin n → K) :
    S.colourFrom n d = S.nOut n d ≫ (normIso U n (par ∘ d)).inv := by
  rw [nOut, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **Extraction**: if a group-algebra element acts as zero on the
tensor power of the mixed object, all its colour sums vanish —
provided no power of the odd line is a zero object. -/
theorem colourSum_eq_zero
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] {K : Type} [Fintype K] [DecidableEq K]
    {par : K → Bool} {U : A} {M : A}
    (S : MixedLetters K par U M)
    (hβ : (β_ U U).hom = -(𝟙 (U ⊗ U)))
    (hU : ∀ k : ℕ, 𝟙 (tensorPow A U k) ≠
      (0 : tensorPow A U k ⟶ tensorPow A U k))
    {n : ℕ} {x : SymGroupAlgebra n} (hx : permAlg M n x = 0)
    (c d : Fin n → K) : colourSum par x c d = 0 := by
  by_cases hpop : popCount (par ∘ c) = popCount (par ∘ d)
  · have hx' : permAlg M n x =
        (0 : tensorPow A M n ⟶ tensorPow A M n) := hx
    have h0 : S.nIn n c ≫ permAlg M n x ≫ S.nOut n d = 0 := by
      rw [hx', Limits.zero_comp, Limits.comp_zero]
    rw [S.nIn_permAlg_nOut hβ x c d, dite_eq_left hpop] at h0
    by_contra hne
    have h1 : eqToHom (congrArg (tensorPow A U) hpop) =
        (0 : tensorPow A U (popCount (par ∘ c)) ⟶
          tensorPow A U (popCount (par ∘ d))) := by
      have h2 := congrArg
        (fun t => (colourSum par x c d)⁻¹ • t) h0
      simp only [smul_smul, inv_mul_cancel₀ hne, one_smul,
        smul_zero] at h2
      exact h2
    have h3 : 𝟙 (tensorPow A U (popCount (par ∘ c))) =
        (0 : tensorPow A U (popCount (par ∘ c)) ⟶
          tensorPow A U (popCount (par ∘ c))) := by
      have h4 := congrArg (fun t => t ≫
        eqToHom (congrArg (tensorPow A U) hpop).symm) h1
      simpa only [eqToHom_trans, eqToHom_refl, Limits.zero_comp]
        using h4
    exact hU _ h3
  · exact colourSum_eq_zero_of_ne par x hpop

/-- **Reconstruction**: if all colour sums of a group-algebra
element vanish, it acts as zero on the tensor power of the mixed
object. -/
theorem permAlg_eq_zero
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A] {K : Type} [Fintype K] [DecidableEq K]
    {par : K → Bool} {U : A} {M : A}
    (S : MixedLetters K par U M)
    (hβ : (β_ U U).hom = -(𝟙 (U ⊗ U))) {n : ℕ}
    {x : SymGroupAlgebra n}
    (hx : ∀ c d : Fin n → K, colourSum par x c d = 0) :
    permAlg M n x = 0 := by
  have hmid : ∀ c d : Fin n → K,
      S.colourInto n c ≫ permAlg M n x ≫ S.colourFrom n d = 0 := by
    intro c d
    calc S.colourInto n c ≫ permAlg M n x ≫ S.colourFrom n d
        = (normIso U n (par ∘ c)).hom ≫
          (S.nIn n c ≫ permAlg M n x ≫ S.nOut n d) ≫
          (normIso U n (par ∘ d)).inv := by
          rw [S.colourInto_eq_nIn n c, S.colourFrom_eq_nOut n d]
          simp only [Category.assoc]
      _ = 0 := by
          rw [S.nIn_permAlg_nOut hβ x c d]
          by_cases hpop : popCount (par ∘ c) = popCount (par ∘ d)
          · rw [dite_eq_left hpop, hx c d, zero_smul, Limits.zero_comp,
              Limits.comp_zero]
          · rw [dite_eq_right hpop, Limits.zero_comp, Limits.comp_zero]
  have hmid2 : ∀ c : Fin n → K,
      S.colourInto n c ≫ permAlg M n x ≫
        (∑ d : Fin n → K, S.colourFrom n d ≫ S.colourInto n d) = 0
      := by
    intro c
    rw [Preadditive.comp_sum, Preadditive.comp_sum]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [show S.colourInto n c ≫ permAlg M n x ≫
        S.colourFrom n d ≫ S.colourInto n d =
      (S.colourInto n c ≫ permAlg M n x ≫ S.colourFrom n d) ≫
        S.colourInto n d from by simp only [Category.assoc]]
    rw [hmid c d, Limits.zero_comp]
  calc permAlg M n x
      = 𝟙 (tensorPow A M n) ≫ permAlg M n x ≫
        𝟙 (tensorPow A M n) := by
        rw [Category.id_comp, Category.comp_id]
    _ = (∑ c : Fin n → K, S.colourFrom n c ≫ S.colourInto n c) ≫
        permAlg M n x ≫
        (∑ d : Fin n → K, S.colourFrom n d ≫ S.colourInto n d) := by
        rw [S.sum_colourFrom_colourInto n]
    _ = ∑ c : Fin n → K, S.colourFrom n c ≫
        (S.colourInto n c ≫ permAlg M n x ≫
          (∑ d : Fin n → K, S.colourFrom n d ≫ S.colourInto n d))
        := by
        rw [Preadditive.sum_comp]
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [Category.assoc]
    _ = 0 := by
        refine Finset.sum_eq_zero fun c _ => ?_
        rw [hmid2 c, Limits.comp_zero]

end Entries

end MixedLetters

end RS
