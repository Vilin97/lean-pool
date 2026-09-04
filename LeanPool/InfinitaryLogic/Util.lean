/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.VecNotation

/-!
# Utility Lemmas

Small lemmas about `Empty.elim`, `Fin.elim0`, `Fin.snoc`, and `Fin.append` that are used
across the infinitary logic library but not (yet) in Mathlib.
-/

universe u v

/-- Any function from `Empty` equals `Empty.elim`. -/
theorem Empty.eq_elim {α : Sort u} (f : Empty → α) : f = Empty.elim :=
  funext (fun x => x.elim)

/-- Any function composed with `Empty.elim` is `Empty.elim`. -/
theorem comp_empty_elim {α : Sort u} {β : Sort v} (f : α → β) :
    f ∘ (Empty.elim : Empty → α) = Empty.elim :=
  funext (fun x => x.elim)

/-- Any function composed with `Fin.elim0` is `Fin.elim0`. -/
theorem comp_fin_elim0 {α : Type u} {β : Type v} (f : α → β) :
    f ∘ (Fin.elim0 : Fin 0 → α) = (Fin.elim0 : Fin 0 → β) :=
  funext (fun x => x.elim0)

/-- Any function from `Fin 0` equals `Fin.elim0`. -/
theorem Fin.eq_elim0 {α : Type u} (f : Fin 0 → α) : f = Fin.elim0 :=
  funext (fun x => x.elim0)

/-- `Fin.snoc Fin.elim0 x` is the constant function `fun _ => x` on `Fin 1`. -/
theorem Fin.snoc_elim0_eq {α : Type u} (x : α) :
    (Fin.snoc (α := fun _ => α) Fin.elim0 x : Fin 1 → α) = fun _ => x :=
  funext fun v => Fin.lastCases rfl (fun i => i.elim0) v
