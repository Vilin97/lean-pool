/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import LeanPool.QuasiBorelSpaces.Basic

/-!
# LeanPool.QuasiBorelSpaces.Lift

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.Lift`.
-/

variable {A B : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B]

namespace QuasiBorelSpace.ULift

instance : QuasiBorelSpace (ULift A) := lift ULift.down

@[simp]
lemma isHom_def {φ : A → ULift B} : IsHom φ ↔ IsHom (fun x ↦ (φ x).down) := by
  simp only [isHom_to_lift]

@[fun_prop]
lemma isHom_up {f : A → B} (hf : IsHom f) : IsHom (fun x ↦ ULift.up (f x)) := by
  simp only [isHom_def, hf]

@[fun_prop]
lemma isHom_down {f : A → ULift B} (hf : IsHom f) : IsHom (fun x ↦ ULift.down (f x)) := by
  simp only [isHom_def] at hf
  exact hf

end QuasiBorelSpace.ULift

namespace QuasiBorelSpace.PLift

instance : QuasiBorelSpace (PLift A) := lift PLift.down

@[simp]
lemma isHom_def {φ : A → PLift B} : IsHom φ ↔ IsHom (fun x ↦ (φ x).down) := by
  simp only [isHom_to_lift]

@[fun_prop]
lemma isHom_up {f : A → B} (hf : IsHom f) : IsHom (fun x ↦ PLift.up (f x)) := by
  simp only [isHom_def, hf]

@[fun_prop]
lemma isHom_down {f : A → PLift B} (hf : IsHom f) : IsHom (fun x ↦ PLift.down (f x)) := by
  simp only [isHom_def] at hf
  exact hf

end QuasiBorelSpace.PLift
