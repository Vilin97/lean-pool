/-
Copyright (c) 2026 Joseph Eremondi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Eremondi
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Logic.Function.Basic

namespace LeanPool.LeanCwf

theorem heq_type_eq {a a_1 : Sort u_1} {x : a} {y : a_1}
  (eq : HEq x y) : a = a_1 := by
  cases eq
  rfl

theorem eq_cast_of_heq {a a_1 : Sort u_1} {a_2 : a} {a' : a_1}
  (heq : HEq a_2 a') : cast (heq_type_eq heq) a_2 = a' := by
  cases heq
  rfl


theorem cast_moveR {A B : Sort u_1} {a : A} {b : B}
  {eq : A = B} (abeq : cast eq a = b) : a = cast (by rw [eq]) b := by aesop


theorem cast_moveL {A B : Sort u_1} {a : A} {b : B}
  {eq : B = A} (abeq : a = cast eq b) : cast (by rw [eq]) a = b := by aesop

theorem hCong {A : Type u} {B : A → Type v} {f g : (a : A) → B a} {x y : A}
    (funEq : f = g) (argEq : x = y) :
      HEq (f x) (g y) := by aesop

theorem castSymmL {A B : Type u} {eq : A = B} {x : A} {y : B}
  (pf : cast eq x = y) :
  x = cast (symm eq) y := by aesop


theorem castSymmR {A B : Type u} {eq : B = A} {x : A} {y : B}
  (pf : x = cast eq y) :
  cast (symm eq) x = y := by aesop

theorem hCongFun {A : Type u} {B C : A → Type v} {f : (a : A) → B a} {g : (a : A) → C a}
    (x : A)
    (eq : B = C)
    (funEq : HEq f g) :
    HEq (f x) (g x) := by aesop


theorem hCongArg {A : Type u} {B : A → Type v} {f : (a : A) → B a}
    {x y : A}
    (eq : x = y) :
    HEq (f x) (f y) := by aesop


-- theorem hCongArg2 {A A' : Type u}
--     {B : A → Type v}
--     {B' : A' → Type v}
--     {C : (a : A) → B a → Type v}
--     {C' : (a : A') -> B' a -> Type v}
--     {f : (a : A) → (b : B a) → C a b}
--     {g : (a : A') → (b : B' a) → C' a b}
--     {x : A} {y : A'}
--     {bx : B x} {byy : B' y}
--     (feq : HEq f g)
--     (eq : HEq x y)
--     (heq : HEq bx byy):
--       HEq (f x bx) (g y byy) := by
--     cases eq
--     let teq := heq_type_eq heq
--     apply heq_of_cast_eq <;> aesop_cat
--     cases teq
--     cases heq

theorem hCongFunImplicit {A : Type u} {B C : A → Type v} {f : {a : A} → B a} {g : {a : A} → C a}
    (x : A)
    (eq : B = C)
    (funEq : HEq @f @g) :
    HEq (f (a := x)) (g (a := x)) := by aesop


theorem hCongFunSimp {A : Type u} {B C : Type v} {f : (a : A) → B} {g : (a : A) → C}
    (x : A)
    (eq : B = C)
    (funEq : HEq f g) :
    HEq (f x) (g x) := by aesop


theorem hFunExt {A B C : Type u}
  {f : A -> B} {g : A -> C}
  (eq : B = C)
  (extEq : (a : A) -> HEq (f a) (g a))
  : HEq f g := by
    let funEq : (A -> B) = (A -> C) := by aesop
    fapply heq_of_cast_eq funEq
    funext x
    let fxEq : HEq (cast funEq f x) (f x) := by aesop
    fapply eq_of_heq
    fapply HEq.trans fxEq
    fapply extEq


theorem insertBothCasts {A B C : Type u}
  {x : A} {y : B} {eq1 : A = C} {eq2 : B = C}
  (eq : cast eq1 x = cast eq2 y)
  : HEq x y := by aesop


theorem deleteBothCasts {A B C : Type u}
  {x : A} {y : B} {eq1 : A = C} {eq2 : B = C}
  (eq : HEq x y)
  : cast eq1 x = cast eq2 y := by aesop

-- Helper module for a Sigma lemma we need over and over again
-- Helps dealing with HEq for sigma types
theorem Sigma_HExt
  {α : Type u_1} {β : α → Type u_2} {x y : Sigma β}
  (eq : x.fst = y.fst) (heq : x.fst = y.fst -> HEq x.snd y.snd)
  : x = y := Sigma.ext eq (heq eq)

theorem Subtype_Sigma_ext
  {A : Type u}
  {B : A -> Type u}
  {P : {a : A} -> B a -> Prop}
  {x y : (a : A) × @Subtype (B a) P}
  (eq1 : x.fst = y.fst)
  (eq2 : HEq x.snd.val y.snd.val)
  : x = y := by cases x with
  | mk x1 x2 => cases y with
  | mk y1 y2 =>
    fapply Sigma.ext
    · exact eq1
    · cases eq1
      exact heq_of_eq (Subtype.ext (eq_of_heq eq2))

theorem Subtype_HExtEq {A : Type u} {P Q : A -> Prop}
 {x : Subtype P} {y : Subtype Q}
 (eq : x.val = y.val)
 (equiv : P = Q)
 : HEq x y := by aesop

theorem Subtype_HExt {A : Type u} {P Q : A -> Prop}
 {x : Subtype P} {y : Subtype Q}
 (eq : x.val = y.val)
 (equiv : (x : A) -> P x ↔ Q x)
 : HEq x y :=  by
   let PeqQ : P = Q := by
     funext x
     apply propext
     apply equiv x
   apply Subtype_HExtEq <;> assumption

theorem HEq_iff {P : Prop}
  (p : P)
  (t : True)
  : HEq p t := by aesop

end LeanPool.LeanCwf
