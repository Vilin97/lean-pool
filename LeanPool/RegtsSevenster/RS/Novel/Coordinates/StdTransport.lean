/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OmegaStarVec
public import LeanPool.RegtsSevenster.RS.Classical.Super.ColourPower

/-!
# The model transport

Given the strand identification of the standard model, the
iterated identification of the monoidal powers: `stdToOmega`
assembles copies of the strand map left-nested through the
structure maps of the fibre functor, `stdFromOmega` disassembles,
and the two are mutually inverse whenever the strand maps are.
-/

@[expose] public section

namespace RS

open CategoryTheory Functor.LaxMonoidal Functor.OplaxMonoidal
open MonoidalCategory

variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}

section Transport

variable (e : stdSuperPair k ℓ ⟶ P.ω.obj (SkeinObj.mk 1))
variable (e' : P.ω.obj (SkeinObj.mk 1) ⟶ stdSuperPair k ℓ)

/-- The model transport: iterated strand identifications
assembled left-nested through the structure maps. -/
noncomputable def stdToOmega :
    (m : ℕ) → (superPow (stdSuperPair k ℓ) m ⟶
      P.ω.obj (SkeinObj.mk m))
  | 0 =>
      letI := P.braided
      (ε P.ω : SuperVect.tensorUnit ⟶ P.ω.obj (SkeinObj.mk 0))
  | m + 1 =>
      letI := P.braided
      ((stdToOmega m ⊗ₘ e) ≫
        (μ P.ω (SkeinObj.mk m) (SkeinObj.mk 1) :
          P.ω.obj (SkeinObj.mk m) ⊗ P.ω.obj (SkeinObj.mk 1) ⟶
            P.ω.obj (SkeinObj.mk (m + 1))))

/-- The reverse model transport. -/
noncomputable def stdFromOmega :
    (m : ℕ) → (P.ω.obj (SkeinObj.mk m) ⟶
      superPow (stdSuperPair k ℓ) m)
  | 0 =>
      letI := P.braided
      (η P.ω : P.ω.obj (SkeinObj.mk 0) ⟶ SuperVect.tensorUnit)
  | m + 1 =>
      letI := P.braided
      ((δ P.ω (SkeinObj.mk m) (SkeinObj.mk 1) :
          P.ω.obj (SkeinObj.mk (m + 1)) ⟶
            P.ω.obj (SkeinObj.mk m) ⊗ P.ω.obj (SkeinObj.mk 1)) ≫
        (stdFromOmega m ⊗ₘ e'))

/-- The transports are inverse on the fibre side. -/
theorem stdFromOmega_stdToOmega
    (hee' : (e' ≫ e : P.ω.obj (SkeinObj.mk 1) ⟶
      P.ω.obj (SkeinObj.mk 1)) = 𝟙 _) :
    ∀ m : ℕ,
      (stdFromOmega f P e' m ≫ stdToOmega f P e m :
        P.ω.obj (SkeinObj.mk m) ⟶ P.ω.obj (SkeinObj.mk m)) =
        𝟙 (P.ω.obj (SkeinObj.mk m))
  | 0 => by
    let := P.braided
    change (η P.ω ≫ ε P.ω : P.ω.obj (SkeinObj.mk 0) ⟶
      P.ω.obj (SkeinObj.mk 0)) = 𝟙 _
    exact Functor.Monoidal.η_ε P.ω
  | m + 1 => by
    let := P.braided
    change (δ P.ω (SkeinObj.mk m) (SkeinObj.mk 1) ≫
        (stdFromOmega f P e' m ⊗ₘ e')) ≫
      ((stdToOmega f P e m ⊗ₘ e) ≫
        (μ P.ω (SkeinObj.mk m) (SkeinObj.mk 1) :
          P.ω.obj (SkeinObj.mk m) ⊗ P.ω.obj (SkeinObj.mk 1) ⟶
            P.ω.obj (SkeinObj.mk (m + 1)))) = 𝟙 _
    simp only [Category.assoc]
    rw [← Category.assoc (stdFromOmega f P e' m ⊗ₘ e')]
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    rw [stdFromOmega_stdToOmega hee' m, hee']
    rw [MonoidalCategory.id_tensorHom_id]
    rw [Category.id_comp]
    exact Functor.Monoidal.δ_μ P.ω (SkeinObj.mk m)
      (SkeinObj.mk 1)

/-- The transports are inverse on the model side. -/
theorem stdToOmega_stdFromOmega
    (he'e : (e ≫ e' : stdSuperPair k ℓ ⟶ stdSuperPair k ℓ) = 𝟙 _) :
    ∀ m : ℕ,
      (stdToOmega f P e m ≫ stdFromOmega f P e' m :
        superPow (stdSuperPair k ℓ) m ⟶
          superPow (stdSuperPair k ℓ) m) =
        𝟙 (superPow (stdSuperPair k ℓ) m)
  | 0 => by
    let := P.braided
    change (ε P.ω ≫ η P.ω : SuperVect.tensorUnit ⟶
      SuperVect.tensorUnit) = 𝟙 _
    exact Functor.Monoidal.ε_η P.ω
  | m + 1 => by
    let := P.braided
    change ((stdToOmega f P e m ⊗ₘ e) ≫
        (μ P.ω (SkeinObj.mk m) (SkeinObj.mk 1) :
          P.ω.obj (SkeinObj.mk m) ⊗ P.ω.obj (SkeinObj.mk 1) ⟶
            P.ω.obj (SkeinObj.mk (m + 1)))) ≫
      (δ P.ω (SkeinObj.mk m) (SkeinObj.mk 1) ≫
        (stdFromOmega f P e' m ⊗ₘ e')) = 𝟙 _
    simp only [Category.assoc]
    rw [show (μ P.ω (SkeinObj.mk m) (SkeinObj.mk 1) :
          P.ω.obj (SkeinObj.mk m) ⊗ P.ω.obj (SkeinObj.mk 1) ⟶
            P.ω.obj (SkeinObj.mk (m + 1))) ≫
        (δ P.ω (SkeinObj.mk m) (SkeinObj.mk 1) ≫
          (stdFromOmega f P e' m ⊗ₘ e')) =
      𝟙 (P.ω.obj (SkeinObj.mk m) ⊗ P.ω.obj (SkeinObj.mk 1)) ≫
        (stdFromOmega f P e' m ⊗ₘ e') from by
      rw [← Category.assoc]
      rw [show (μ P.ω (SkeinObj.mk m) (SkeinObj.mk 1) :
            P.ω.obj (SkeinObj.mk m) ⊗ P.ω.obj (SkeinObj.mk 1) ⟶
              P.ω.obj (SkeinObj.mk (m + 1))) ≫
          δ P.ω (SkeinObj.mk m) (SkeinObj.mk 1) = 𝟙 _ from
        Functor.Monoidal.μ_δ P.ω (SkeinObj.mk m)
          (SkeinObj.mk 1)]]
    rw [Category.id_comp]
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    rw [stdToOmega_stdFromOmega he'e m, he'e]
    exact MonoidalCategory.id_tensorHom_id _ _

end Transport

end RS
