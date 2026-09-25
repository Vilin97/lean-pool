/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.CoverFactor
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.AltPow
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.OddPermSign

/-!
# Conjugating the permutation action through the twisted power
identification

Over the plain covers the twisted power identification is the
shuffle followed by the projection, so the descended permutation
action on the powers of a twisted module conjugates to the
simultaneous action: the plain action on the twisting powers
alongside the descended action on the module powers.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **The conjugated permutation action**: through the twisted
power identification, the descended action on the powers of a
twisted module is the simultaneous action on the twisting powers
and the module powers. -/
theorem twistPow_perm_conj
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A]
    (V : D) (R : Mod D A) (k : ℕ)
    (σ : Equiv.Perm (Fin (k + 1))) :
    modPowPerm (A := A) (X := (tensorLeftMod A V R).X)
        (k + 1) σ ≫ ((twistPowModIso A V R k).hom).hom =
      ((twistPowModIso A V R k).hom).hom ≫
        (permMor V (k + 1) σ ⊗ₘ
          modPowPerm (A := A) (X := R.X) (k + 1) σ) := by
  refine (cancel_epi
    (modPowπ A ((tensorLeftMod A V R).X) (k + 1))).mp ?_
  have hcov := twistPow_cover_factor A V R k
  have h2 : permMor ((tensorLeftMod A V R).X) (k + 1) σ ≫
      (plainShuffle V R.X (k + 1)).hom =
    (plainShuffle V R.X (k + 1)).hom ≫
      (permMor V (k + 1) σ ⊗ₘ permMor R.X (k + 1) σ) :=
    plainShuffle_permMor V R.X (k + 1) σ
  have h3 : (permMor V (k + 1) σ ⊗ₘ
        permMor R.X (k + 1) σ) ≫
      (tensorPow D V (k + 1) ◁ modPowπ A R.X (k + 1)) =
    (tensorPow D V (k + 1) ◁ modPowπ A R.X (k + 1)) ≫
      (permMor V (k + 1) σ ⊗ₘ
        modPowPerm (A := A) (X := R.X) (k + 1) σ) := by
    erw [← MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp, modPowπ_perm]
  erw [modPowπ_perm_assoc, hcov]
  exact ((Category.assoc _ _ _).symm.trans
    ((eq_whisker h2 _).trans
      ((Category.assoc _ _ _).trans
        ((whisker_eq _ h3).trans
          ((Category.assoc _ _ _).symm.trans
            ((eq_whisker hcov.symm _).trans
              (Category.assoc _ _ _)))))))

/-- The carrier of the twisted power identification. -/
noncomputable def twistPowCarrierIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A]
    (V : D) (R : Mod D A)
    (k : ℕ) :
    modPow A ((tensorLeftMod A V R).X) (k + 1) ≅
      tensorPow D V (k + 1) ⊗ modPow A R.X (k + 1) where
  hom := ((twistPowModIso A V R k).hom).hom
  inv := ((twistPowModIso A V R k).inv).hom
  hom_inv_id := by
    exact congrArg Mod.Hom.hom
      (twistPowModIso A V R k).hom_inv_id
  inv_hom_id := by
    exact congrArg Mod.Hom.hom
      (twistPowModIso A V R k).inv_hom_id

section Collapse

/-- Each conjugated permutation over an odd line is the sign
times the whiskered module action. -/
theorem twistPow_perm_conj_oddLine
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (R : Mod D A)
    (k : ℕ) (σ : Equiv.Perm (Fin (k + 1))) :
    modPowPerm (A := A) (X := (tensorLeftMod A L.obj R).X)
        (k + 1) σ ≫ ((twistPowModIso A L.obj R k).hom).hom =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        (((twistPowModIso A L.obj R k).hom).hom ≫
          (tensorPow D L.obj (k + 1) ◁
            modPowPerm (A := A) (X := R.X) (k + 1) σ)) := by
  erw [twistPow_perm_conj, oddLine_permMor,
    MonoidalCategory.tensorHom_def,
    MonoidalLinear.smul_whiskerRight, Linear.smul_comp,
    MonoidalCategory.id_whiskerRight, Category.id_comp]
  exact Linear.comp_smul _ _ _ _ _ _

/-- **The symmetriser collapses over an odd line**: through the
twisted power identification, the symmetriser of the twisted
module powers is the whiskered antisymmetriser of the module
powers. -/
theorem twistPow_symIdem_conj
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (R : Mod D A)
    (k : ℕ) :
    symPowIdem A ((tensorLeftMod A L.obj R).X) (k + 1) ≫
        ((twistPowModIso A L.obj R k).hom).hom =
      ((twistPowModIso A L.obj R k).hom).hom ≫
        (tensorPow D L.obj (k + 1) ◁
          altPowIdem A R.X (k + 1)) := by
  have halt : ∀ σ : Equiv.Perm (Fin (k + 1)),
      modPowAlg A R.X (k + 1) (MonoidAlgebra.single σ
        ((Equiv.Perm.sign σ : ℤ) : ℂ)) =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        modPowPerm (A := A) (X := R.X) (k + 1) σ := by
    intro σ
    rw [show MonoidAlgebra.single σ
          ((Equiv.Perm.sign σ : ℤ) : ℂ) =
        ((Equiv.Perm.sign σ : ℤ) : ℂ) •
          MonoidAlgebra.single σ (1 : ℂ) from by
        rw [MonoidAlgebra.smul_single', mul_one],
      map_smul, modPowAlg_single]
  -- The antisymmetriser's whiskered normal form, free of the
  -- identification.
  have hb : tensorPow D L.obj (k + 1) ◁
      altPowIdem A R.X (k + 1) =
    ((Nat.factorial (k + 1) : ℂ))⁻¹ •
      ∑ σ : Equiv.Perm (Fin (k + 1)),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) •
          (tensorPow D L.obj (k + 1) ◁
            modPowPerm (A := A) (X := R.X) (k + 1) σ) := by
    rw [altPowIdem, antisymmetriser, map_smul, map_sum]
    simp only [halt]
    change tensorPow D L.obj (k + 1) ◁
        (((Nat.factorial (k + 1) : ℂ))⁻¹ •
          ∑ σ : Equiv.Perm (Fin (k + 1)),
            ((Equiv.Perm.sign σ : ℤ) : ℂ) •
              (modPowPerm (A := A) (X := R.X) (k + 1) σ :
                modPow A R.X (k + 1) ⟶
                  modPow A R.X (k + 1))) = _
    rw [MonoidalLinear.whiskerLeft_smul,
      whiskerLeft_sum]
    exact congrArg _ (Finset.sum_congr rfl fun σ _ =>
      MonoidalLinear.whiskerLeft_smul _ _ _)
  have hc : ((twistPowModIso A L.obj R k).hom).hom ≫
      (tensorPow D L.obj (k + 1) ◁ altPowIdem A R.X (k + 1)) =
    ((Nat.factorial (k + 1) : ℂ))⁻¹ •
      ∑ σ : Equiv.Perm (Fin (k + 1)),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) •
          (((twistPowModIso A L.obj R k).hom).hom ≫
            (tensorPow D L.obj (k + 1) ◁
              modPowPerm (A := A) (X := R.X) (k + 1) σ)) := by
    refine Eq.trans (congrArg (fun t :
        tensorPow D L.obj (k + 1) ⊗ modPow A R.X (k + 1) ⟶
          tensorPow D L.obj (k + 1) ⊗ modPow A R.X (k + 1) =>
        ((twistPowModIso A L.obj R k).hom).hom ≫ t) hb) ?_
    refine Eq.trans (Linear.comp_smul _ _ _ _ _ _)
      (congrArg _ ?_)
    refine Eq.trans (Preadditive.comp_sum _ _ _) ?_
    exact Finset.sum_congr rfl fun σ _ =>
      Linear.comp_smul _ _ _ _ _ _
  refine Eq.trans ?_ hc.symm
  rw [symPowIdem, symmetriser, map_smul, map_sum]
  simp only [modPowAlg_single]
  change (((Nat.factorial (k + 1) : ℂ))⁻¹ •
      ∑ σ : Equiv.Perm (Fin (k + 1)),
        (modPowPerm (A := A)
            (X := (tensorLeftMod A L.obj R).X) (k + 1) σ :
          modPow A ((tensorLeftMod A L.obj R).X) (k + 1) ⟶
            modPow A ((tensorLeftMod A L.obj R).X) (k + 1))) ≫
      ((twistPowModIso A L.obj R k).hom).hom = _
  erw [Linear.smul_comp, Preadditive.sum_comp]
  exact congrArg _ (Finset.sum_congr rfl fun σ _ =>
    twistPow_perm_conj_oddLine A L R k σ)

/-- **The symmetric powers of an odd twist are the twisted
alternating powers**: the coequalizer transports along the
identification through the symmetriser collapse, and the twist
passes out of the colimit. -/
noncomputable def symPowOddTwistIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D)
    (R : Mod D A) (k : ℕ) :
    symPow A ((tensorLeftMod A L.obj R).X) (k + 1) ≅
      tensorPow D L.obj (k + 1) ⊗ altPow A R.X (k + 1) :=
  HasColimit.isoOfNatIso (parallelPair.ext
    (F := parallelPair
      (symPowIdem A ((tensorLeftMod A L.obj R).X) (k + 1))
      (𝟙 (modPow A ((tensorLeftMod A L.obj R).X) (k + 1))))
    (G := parallelPair (altPowIdem A R.X (k + 1))
        (𝟙 (modPow A R.X (k + 1))) ⋙
      tensorLeft (tensorPow D L.obj (k + 1)))
    (twistPowCarrierIso A L.obj R k)
    (twistPowCarrierIso A L.obj R k)
    (twistPow_symIdem_conj A L R k)
    ((Category.id_comp _).trans
      ((Category.comp_id _).symm.trans
        (whisker_eq _
          (CategoryTheory.Functor.map_id _ _).symm)))) ≪≫
  (preservesColimitIso
    (tensorLeft (tensorPow D L.obj (k + 1)))
    (parallelPair (altPowIdem A R.X (k + 1))
      (𝟙 (modPow A R.X (k + 1))))).symm

/-- Tensor powers of the odd line reflect vanishing. -/
theorem OddLine.isZero_tensorPow_tensor_iff
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D]
    (L : OddLine D)
    (n : ℕ) (Z : D) :
    IsZero (tensorPow D L.obj n ⊗ Z) ↔ IsZero Z := by
  induction n generalizing Z with
  | zero =>
    exact ⟨fun h => h.of_iso (λ_ Z).symm,
      fun h => isZero_whiskerLeft _ h⟩
  | succ n ih =>
    refine Iff.trans
      ⟨fun h => h.of_iso (α_ _ _ _).symm,
        fun h => h.of_iso (α_ _ _ _)⟩ ?_
    exact (ih (L.obj ⊗ Z)).trans (L.isZero_tensor_iff Z)

/-- **The vanishing criterion for symmetric powers of an odd
twist**: they vanish exactly when the alternating powers of the
module do. -/
theorem symPowOddTwist_isZero_iff
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (R : Mod D A)
    (k : ℕ) :
    IsZero (symPow A ((tensorLeftMod A L.obj R).X) (k + 1)) ↔
      IsZero (altPow A R.X (k + 1)) :=
  Iff.trans
    ⟨fun h => h.of_iso (symPowOddTwistIso A L R k).symm,
      fun h => h.of_iso (symPowOddTwistIso A L R k)⟩
    (OddLine.isZero_tensorPow_tensor_iff L (k + 1)
      (altPow A R.X (k + 1)))

end Collapse

end RS
