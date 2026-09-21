/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Linear structure on a Karoubi completion

The underlying-morphism map transports the linear structure of the
base category to its Karoubi completion.
-/

namespace RS

open CategoryTheory CategoryTheory.Idempotents

/-- The underlying-morphism map is additive. -/
def karoubiHomAddHom {C : Type*} [Category C] [Preadditive C]
    (P Q : Karoubi C) : (P ⟶ Q) →+ (P.X ⟶ Q.X) where
  toFun g := g.f
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Scaling a Karoubi morphism through its underlying morphism. -/
noncomputable instance karoubiHomSMul {C : Type*} [Category C]
    [Preadditive C] [Linear ℂ C] (P Q : Karoubi C) :
    SMul ℂ (P ⟶ Q) where
  smul c g := ⟨c • g.f, by
    rw [Linear.smul_comp, Linear.comp_smul, g.comm]⟩

/-- Karoubi hom-sets inherit the complex module structure. -/
noncomputable instance karoubiHomModule {C : Type*} [Category C]
    [Preadditive C] [Linear ℂ C] (P Q : Karoubi C) :
    Module ℂ (P ⟶ Q) :=
  Function.Injective.module ℂ (karoubiHomAddHom P Q)
    (fun _ _ h => Karoubi.Hom.ext h) (fun _ _ => rfl)

/-- The Karoubi completion of a complex linear category is linear. -/
noncomputable instance karoubiLinear {C : Type*} [Category C]
    [Preadditive C] [Linear ℂ C] : Linear ℂ (Karoubi C) where
  smul_comp P Q R c g h := by
    apply Karoubi.hom_ext
    show (c • g.f) ≫ h.f = c • (g.f ≫ h.f)
    rw [Linear.smul_comp]
  comp_smul P Q R g c h := by
    apply Karoubi.hom_ext
    show g.f ≫ (c • h.f) = c • (g.f ≫ h.f)
    rw [Linear.comp_smul]

/-- The underlying-morphism map is complex linear. -/
noncomputable def karoubiHomLinearMap {C : Type*} [Category C]
    [Preadditive C] [Linear ℂ C] (P Q : Karoubi C) :
    (P ⟶ Q) →ₗ[ℂ] (P.X ⟶ Q.X) where
  toFun g := g.f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end RS
