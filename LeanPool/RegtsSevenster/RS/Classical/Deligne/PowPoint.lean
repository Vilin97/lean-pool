/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.CatTheory.UnitEnd
import LeanPool.RegtsSevenster.RS.Classical.Deligne.PermNat
import LeanPool.RegtsSevenster.RS.Classical.Deligne.UnitMod

/-!
# Point powers and the trivial permutation action on unit strands

The tensor powers of a point of an object, and their invariance
under the permutation action: permutations act trivially on powers
of the unit object, and naturality carries the invariance onto the
point powers.  In a rigid category the point powers of a
monomorphism are monomorphisms.  The substrate of the
nonvanishing of the local splitting algebra.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {D : Type u}

/-- The top transposition on a power of the unit is the
identity. -/
theorem swapTop_unit [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (n : ℕ) :
    swapTop (𝟙_ D) n = 𝟙 (tensorPow D (𝟙_ D) (n + 2)) := by
  unfold swapTop
  rw [braiding_unit_self, MonoidalCategory.whiskerLeft_id,
    Category.id_comp, Iso.hom_inv_id]

/-- Every adjacent transposition acts trivially on a power of the
unit. -/
theorem permMor_unit_adjSwap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] :
    ∀ (n : ℕ) (i : Fin (n + 1)),
      permMor (𝟙_ D) (n + 2) (Equiv.swap i.castSucc i.succ) =
        𝟙 (tensorPow D (𝟙_ D) (n + 2)) := by
  intro n
  induction n with
  | zero =>
    intro i
    refine Fin.lastCases ?_ (fun j => j.elim0) i
    rw [show Equiv.swap (Fin.castSucc (Fin.last 0))
          (Fin.last 0).succ
        = (topSwap : Equiv.Perm (Fin 2)) from by
          rw [topSwap, Fin.succ_last],
      permMor_topSwap_eq]
    exact swapTop_unit 0
  | succ n ih =>
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [show Equiv.swap (Fin.castSucc (Fin.last (n + 1)))
          (Fin.last (n + 1)).succ
          = (topSwap : Equiv.Perm (Fin (n + 3))) from by
            rw [topSwap, Fin.succ_last],
        permMor_topSwap_eq]
      exact swapTop_unit (n + 1)
    · rw [swap_castSucc_succ_castSucc j, permMor_extPerm, ih j]
      exact MonoidalCategory.id_whiskerRight _ _

/-- **Permutations act trivially on powers of the unit**: every
adjacent transposition does, and the action and the trivial
character are both multiplicative. -/
theorem permMor_unit [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    permMor (𝟙_ D) n σ = 𝟙 (tensorPow D (𝟙_ D) n) := by
  match n, σ with
  | 0, σ =>
    have hσ : σ = 1 := Equiv.ext fun x => x.elim0
    rw [hσ, permMor_one]
  | 1, σ =>
    have hσ : σ = 1 := Equiv.ext fun x => Fin.ext (by omega)
    rw [hσ, permMor_one]
  | n + 2, σ =>
    have key : ∀ τ : Equiv.Perm (Fin (n + 2)),
        τ ∈ Submonoid.closure (Set.range fun i : Fin (n + 1) =>
          Equiv.swap i.castSucc i.succ) →
        permMor (𝟙_ D) (n + 2) τ =
          𝟙 (tensorPow D (𝟙_ D) (n + 2)) := by
      intro τ hτ
      induction hτ using Submonoid.closure_induction_left with
      | one => rw [permMor_one]
      | mul_left g hg τ' hτ' ihτ' =>
        obtain ⟨i, rfl⟩ := hg
        rw [permMor_mul, ihτ', permMor_unit_adjSwap n i]
        simp
    exact key σ (by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial)

section Point

/-- The powers of the unit collapse onto the unit. -/
noncomputable def unitPow [Category.{v} D] [MonoidalCategory D] : (n : ℕ) →
    (tensorPow D (𝟙_ D) n ≅ 𝟙_ D)
  | 0 => Iso.refl _
  | (n + 1) => (ρ_ (tensorPow D (𝟙_ D) n)) ≪≫ unitPow n

variable {Y} in
/-- **The power of a point**: the collapsed unit power carried
into the power of the target. -/
noncomputable def tensorPowPoint
    [Category.{v} D] [MonoidalCategory D] {Y : D} (pt : 𝟙_ D ⟶ Y)
    (n : ℕ) :
    𝟙_ D ⟶ tensorPow D Y n :=
  (unitPow n).inv ≫ tensorPowMap pt n

variable {Y} in
/-- In a rigid category the power of a monic point is monic. -/
theorem tensorPowPoint_mono
    [Category.{v} D] [MonoidalCategory D] {Y : D} (pt : 𝟙_ D ⟶ Y)
    [RigidCategory D] [Mono pt] (n : ℕ) :
    Mono (tensorPowPoint pt n) := by
  haveI := tensorPowMap_mono pt n
  exact mono_comp _ _

variable {Y} in
/-- The power of a monic point is monic, from mono preservation
of the tensor factors alone. -/
theorem tensorPowPoint_mono'
    [Category.{v} D] [MonoidalCategory D] {Y : D} (pt : 𝟙_ D ⟶ Y)
    [∀ Z : D, (tensorLeft Z).PreservesMonomorphisms]
    [∀ Z : D, (tensorRight Z).PreservesMonomorphisms]
    [Mono pt] (n : ℕ) :
    Mono (tensorPowPoint pt n) := by
  haveI := tensorPowMap_mono' pt n
  exact mono_comp _ _

variable {Y} in
/-- The empty point power is the identity. -/
theorem tensorPowPoint_zero
    [Category.{v} D] [MonoidalCategory D] {Y : D} (pt : 𝟙_ D ⟶ Y) :
    tensorPowPoint pt 0 = 𝟙 (𝟙_ D) := by
  rw [tensorPowPoint, tensorPowMap_zero]
  exact Category.comp_id _

variable {Y} in
/-- The recursion of the point powers: one more letter joins on
the right. -/
theorem tensorPowPoint_succ
    [Category.{v} D] [MonoidalCategory D] {Y : D} (pt : 𝟙_ D ⟶ Y)
    (n : ℕ) :
    tensorPowPoint pt (n + 1) =
      (ρ_ (𝟙_ D)).inv ≫ (tensorPowPoint pt n ⊗ₘ pt) := by
  rw [tensorPowPoint, tensorPowPoint, tensorPowMap_succ]
  have hsplit : ((unitPow n).inv ≫ tensorPowMap pt n) ⊗ₘ pt =
      ((unitPow n).inv ▷ (𝟙_ D)) ≫
        (tensorPowMap pt n ⊗ₘ pt) := by
    rw [← MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_comp_tensorHom,
      Category.id_comp]
  rw [hsplit]
  exact (eq_whisker (rightUnitor_inv_naturality
    ((unitPow n).inv)) _).trans (Category.assoc _ _ _)

variable {Y} in
/-- **Point powers concatenate**: the tensor of two point powers
meets the concatenation as the joint point power. -/
theorem tensorPowPoint_concat
    [Category.{v} D] [MonoidalCategory D] {Y : D} (pt : 𝟙_ D ⟶ Y)
    (m : ℕ) :
    ∀ n : ℕ,
    (tensorPowPoint pt m ⊗ₘ tensorPowPoint pt n) ≫
        (tensorPowConcat Y m n).hom =
      (λ_ (𝟙_ D)).hom ≫ tensorPowPoint pt (m + n)
  | 0 => by
    have hnat : (tensorPowPoint pt m ▷ (𝟙_ D)) ≫
        (ρ_ (tensorPow D Y m)).hom =
      (ρ_ (𝟙_ D)).hom ≫ tensorPowPoint pt m :=
      rightUnitor_naturality _
    calc (tensorPowPoint pt m ⊗ₘ tensorPowPoint pt 0) ≫
        (tensorPowConcat Y m 0).hom
        = (tensorPowPoint pt m ⊗ₘ 𝟙 (𝟙_ D)) ≫
            (ρ_ (tensorPow D Y m)).hom := by
          rw [tensorPowPoint_zero]
          rfl
      _ = (ρ_ (𝟙_ D)).hom ≫ tensorPowPoint pt m := by
          rw [MonoidalCategory.tensorHom_id]
          exact hnat
      _ = (λ_ (𝟙_ D)).hom ≫ tensorPowPoint pt (m + 0) := by
          rw [unitors_equal]
          rfl
  | (n + 1) => by
    have hsucc := tensorPowPoint_succ (pt := pt) n
    have hdec : tensorPowPoint pt m ⊗ₘ
        ((ρ_ (𝟙_ D)).inv ≫
          (tensorPowPoint pt n ⊗ₘ pt)) =
      ((𝟙 (𝟙_ D)) ⊗ₘ (ρ_ (𝟙_ D)).inv) ≫
        (tensorPowPoint pt m ⊗ₘ
          (tensorPowPoint pt n ⊗ₘ pt)) := by
      rw [MonoidalCategory.tensorHom_comp_tensorHom,
        Category.id_comp]
    have hα : (tensorPowPoint pt m ⊗ₘ
        (tensorPowPoint pt n ⊗ₘ pt)) ≫
        (α_ (tensorPow D Y m) (tensorPow D Y n) Y).inv =
      (α_ (𝟙_ D) (𝟙_ D) (𝟙_ D)).inv ≫
        ((tensorPowPoint pt m ⊗ₘ tensorPowPoint pt n) ⊗ₘ
          pt) :=
      associator_inv_naturality _ _ _
    have hIH : ((tensorPowPoint pt m ⊗ₘ
        tensorPowPoint pt n) ⊗ₘ pt) ≫
        ((tensorPowConcat Y m n).hom ▷ Y) =
      (((λ_ (𝟙_ D)).hom ≫ tensorPowPoint pt (m + n)) ⊗ₘ
        pt) := by
      rw [← MonoidalCategory.tensorHom_id,
        MonoidalCategory.tensorHom_comp_tensorHom,
        Category.comp_id, tensorPowPoint_concat pt m n]
    have hcoh : ((𝟙 (𝟙_ D)) ⊗ₘ (ρ_ (𝟙_ D)).inv) ≫
        (α_ (𝟙_ D) (𝟙_ D) (𝟙_ D)).inv ≫
        ((λ_ (𝟙_ D)).hom ▷ (𝟙_ D)) =
      (λ_ (𝟙_ D)).hom ≫ (ρ_ (𝟙_ D)).inv := by
      monoidal
    refine Eq.trans ?_ (whisker_eq (λ_ (𝟙_ D)).hom
      (tensorPowPoint_succ (pt := pt) (m + n)).symm)
    calc (tensorPowPoint pt m ⊗ₘ tensorPowPoint pt (n + 1)) ≫
        (tensorPowConcat Y m (n + 1)).hom
        = (tensorPowPoint pt m ⊗ₘ
            ((ρ_ (𝟙_ D)).inv ≫
              (tensorPowPoint pt n ⊗ₘ pt))) ≫
            (α_ (tensorPow D Y m) (tensorPow D Y n) Y).inv ≫
            ((tensorPowConcat Y m n).hom ▷ Y) := by
          rw [hsucc]
          rfl
      _ = ((𝟙 (𝟙_ D)) ⊗ₘ (ρ_ (𝟙_ D)).inv) ≫
            ((tensorPowPoint pt m ⊗ₘ
              (tensorPowPoint pt n ⊗ₘ pt)) ≫
              (α_ (tensorPow D Y m) (tensorPow D Y n) Y).inv) ≫
            ((tensorPowConcat Y m n).hom ▷ Y) := by
          rw [hdec]
          simp only [Category.assoc]
      _ = ((𝟙 (𝟙_ D)) ⊗ₘ (ρ_ (𝟙_ D)).inv) ≫
            (α_ (𝟙_ D) (𝟙_ D) (𝟙_ D)).inv ≫
            (((tensorPowPoint pt m ⊗ₘ
              tensorPowPoint pt n) ⊗ₘ pt) ≫
              ((tensorPowConcat Y m n).hom ▷ Y)) := by
          rw [hα]
          simp only [Category.assoc]
      _ = ((𝟙 (𝟙_ D)) ⊗ₘ (ρ_ (𝟙_ D)).inv) ≫
            (α_ (𝟙_ D) (𝟙_ D) (𝟙_ D)).inv ≫
            (((λ_ (𝟙_ D)).hom ≫ tensorPowPoint pt (m + n)) ⊗ₘ
              pt) := by
          rw [hIH]
      _ = ((𝟙 (𝟙_ D)) ⊗ₘ (ρ_ (𝟙_ D)).inv) ≫
            (α_ (𝟙_ D) (𝟙_ D) (𝟙_ D)).inv ≫
            ((λ_ (𝟙_ D)).hom ▷ (𝟙_ D)) ≫
            (tensorPowPoint pt (m + n) ⊗ₘ pt) := by
          rw [← MonoidalCategory.tensorHom_id
            ((λ_ (𝟙_ D)).hom),
            MonoidalCategory.tensorHom_comp_tensorHom,
            Category.id_comp]
      _ = (λ_ (𝟙_ D)).hom ≫ (ρ_ (𝟙_ D)).inv ≫
            (tensorPowPoint pt (m + n) ⊗ₘ pt) := by
          rw [reassoc_of% hcoh]

variable {Y} in
/-- **The permutation action fixes point powers**: naturality
carries the action onto the unit strands, where it is trivial. -/
theorem tensorPowPoint_permMor
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] {Y : D}
    (pt : 𝟙_ D ⟶ Y)
    (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    tensorPowPoint pt n ≫ permMor Y n σ =
      tensorPowPoint pt n := by
  rw [tensorPowPoint, Category.assoc, ← permMor_natural,
    ← Category.assoc, permMor_unit, Category.comp_id]

end Point

section Symmetrise

/-- **The symmetriser fixes point powers** in the module power:
every permutation fixes them, so their average does. -/
theorem tensorPowPoint_symPowIdem
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] [Linear ℂ D]
    (A : D) [MonObj A] (X : D) [ModObj A X] (pt : 𝟙_ D ⟶ X)
    (n : ℕ) :
    tensorPowPoint pt n ≫ modPowπ A X n ≫ symPowIdem A X n =
      tensorPowPoint pt n ≫ modPowπ A X n := by
  rw [symPowIdem, symmetriser, map_smul, map_sum]
  simp only [modPowAlg_single]
  show tensorPowPoint pt n ≫ modPowπ A X n ≫
      (((n.factorial : ℂ))⁻¹ •
        ∑ σ : Equiv.Perm (Fin n),
          (modPowPerm (A := A) (X := X) n σ :
            modPow A X n ⟶ modPow A X n)) =
    tensorPowPoint pt n ≫ modPowπ A X n
  rw [Linear.comp_smul, Preadditive.comp_sum, Linear.comp_smul,
    Preadditive.comp_sum]
  have habs : ∀ σ : Equiv.Perm (Fin n),
      tensorPowPoint pt n ≫ modPowπ A X n ≫
          modPowPerm (A := A) (X := X) n σ =
        tensorPowPoint pt n ≫ modPowπ A X n := by
    intro σ
    rw [modPowπ_perm, ← Category.assoc, tensorPowPoint_permMor]
  calc ((n.factorial : ℂ))⁻¹ •
      ∑ σ : Equiv.Perm (Fin n), tensorPowPoint pt n ≫
        (modPowπ A X n ≫ modPowPerm (A := A) (X := X) n σ)
      = ((n.factorial : ℂ))⁻¹ •
          ∑ _σ : Equiv.Perm (Fin n),
            tensorPowPoint pt n ≫ modPowπ A X n := by
        refine congrArg _ (Finset.sum_congr rfl fun σ _ => ?_)
        exact habs σ
    _ = tensorPowPoint pt n ≫ modPowπ A X n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
          Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
          inv_mul_cancel₀ (by
            exact_mod_cast n.factorial_ne_zero), one_smul]

end Symmetrise

section Nonzero

/-- **Nonvanishing of point powers in symmetric powers over the
unit monoid**: for a monic point of an object in a rigid category
with nonzero unit, no symmetrised point power vanishes. -/
theorem point_symPow_ne_zero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] [Linear ℂ D]
    [RigidCategory D] (X : D)
    (pt : 𝟙_ D ⟶ X) [Mono pt] (h1 : ¬ IsZero (𝟙_ D)) (n : ℕ) :
    tensorPowPoint pt n ≫ modPowπ (𝟙_ D) X n ≫
      symPowπ (𝟙_ D) X n ≠ 0 := by
  intro h0
  have h2 : tensorPowPoint pt n ≫ modPowπ (𝟙_ D) X n ≫
      symPowIdem (𝟙_ D) X n = 0 := by
    have := congrArg (fun t => t ≫ symPowσ (𝟙_ D) X n) h0
    simpa [symPowπ_symPowσ] using this
  have h3 : tensorPowPoint pt n ≫ modPowπ (𝟙_ D) X n = 0 :=
    (tensorPowPoint_symPowIdem (𝟙_ D) X pt n).symm.trans h2
  have h4 : tensorPowPoint pt n = 0 := by
    have := congrArg
      (fun t => t ≫ inv (modPowπ (𝟙_ D) X n)) h3
    simpa using this
  haveI := tensorPowPoint_mono pt n
  exact h1 ((IsZero.iff_id_eq_zero _).mpr
    ((cancel_mono (tensorPowPoint pt n)).mp
      (by rw [h4, comp_zero, zero_comp])))

/-- The nonvanishing of symmetrised point powers, from mono
preservation of the tensor factors alone. -/
theorem point_symPow_ne_zero'
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] [Linear ℂ D]
    (X : D)
    [∀ Z : D, (tensorLeft Z).PreservesMonomorphisms]
    [∀ Z : D, (tensorRight Z).PreservesMonomorphisms]
    (pt : 𝟙_ D ⟶ X) [Mono pt] (h1 : ¬ IsZero (𝟙_ D)) (n : ℕ) :
    tensorPowPoint pt n ≫ modPowπ (𝟙_ D) X n ≫
      symPowπ (𝟙_ D) X n ≠ 0 := by
  intro h0
  have h2 : tensorPowPoint pt n ≫ modPowπ (𝟙_ D) X n ≫
      symPowIdem (𝟙_ D) X n = 0 := by
    have := congrArg (fun t => t ≫ symPowσ (𝟙_ D) X n) h0
    simpa [symPowπ_symPowσ] using this
  have h3 : tensorPowPoint pt n ≫ modPowπ (𝟙_ D) X n = 0 :=
    (tensorPowPoint_symPowIdem (𝟙_ D) X pt n).symm.trans h2
  have h4 : tensorPowPoint pt n = 0 := by
    have := congrArg
      (fun t => t ≫ inv (modPowπ (𝟙_ D) X n)) h3
    simpa using this
  haveI := tensorPowPoint_mono' pt n
  exact h1 ((IsZero.iff_id_eq_zero _).mpr
    ((cancel_mono (tensorPowPoint pt n)).mp
      (by rw [h4, comp_zero, zero_comp])))

end Nonzero

end RS
