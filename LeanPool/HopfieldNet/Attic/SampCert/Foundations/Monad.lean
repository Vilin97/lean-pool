/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.Attic.SampCert.SLang

/-!
# Monad Properties

This file contains the standard monadic equations for ``SLang``.
-/

noncomputable section

open Classical NNReal ENNReal PMF

namespace SLang

variable {α β γ : Type}

/--
Convert a normalized SLang term back into a PMF.
-/
def toPMF (p : SLang α) (h : HasSum p 1) : PMF α := ⟨ p , h ⟩

@[ext]
protected theorem ext {p q : SLang α} (h : ∀ x, p x = q x) : p = q := by
  ext x
  simp [h]

@[simp]
theorem zero_apply (x : α) : probZero x = 0 := by
  unfold probZero
  simp

variable (a a' : α)

@[simp]
theorem pure_apply : probPure a a' = if a' = a then 1 else 0 := rfl

theorem pure_apply_self : probPure a a = 1 :=
  if_pos rfl

theorem pure_apply_of_ne (h : a' ≠ a) : probPure a a' = 0 :=
  if_neg h

variable (p : SLang α) (f : α → SLang β) (g : β → SLang γ)

@[simp]
theorem bind_apply (b : β) : p.probBind f b = ∑' a, p a * f a b := rfl

@[simp]
theorem pure_bind (a : α) (f : α → SLang β) : (probPure a).probBind f = f a := by
  have : ∀ b a', ite (a' = a) (f a' b) 0 = ite (a' = a) (f a b) 0 := fun b a' => by
    split_ifs with h <;> simp [h]
  ext b
  simp [this]

@[simp]
theorem bind_pure : p.probBind probPure = p :=
  SLang.ext fun x => (bind_apply _ _ _).trans (_root_.trans
    (tsum_eq_single x fun y hy => by rw [pure_apply_of_ne _ _ hy.symm, mul_zero]) <|
    by rw [pure_apply_self, mul_one])

@[simp]
theorem bind_bind : (p.probBind f).probBind g = p.probBind fun a => (f a).probBind g :=
  SLang.ext fun b => by
      simpa only [ENNReal.coe_inj.symm, bind_apply, ENNReal.tsum_mul_left.symm,
        ENNReal.tsum_mul_right.symm, mul_assoc, mul_left_comm, mul_comm] using ENNReal.tsum_comm

end SLang
