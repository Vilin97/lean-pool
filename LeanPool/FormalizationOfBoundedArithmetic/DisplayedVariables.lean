/-
Copyright (c) 2026 Mary Jane. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mary Jane
-/

import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.Tactic.FinCases
import LeanPool.FormalizationOfBoundedArithmetic.IsEnum
import LeanPool.FormalizationOfBoundedArithmetic.Register

inductive FvName | x | y | z | X

class HasVar.{u} (n : FvName) (α : Type u)  where fv : α


inductive Vars0 : Type
inductive Vars1 : FvName -> Type
| fv1 {n1} : Vars1 n1
inductive Vars2 : FvName -> FvName -> Type
| fv1 {n1 n2} : Vars2 n1 n2
| fv2 {n1 n2} : Vars2 n1 n2
inductive Vars3 : FvName -> FvName -> FvName -> Type
| fv1 {n1 n2 n3} : Vars3 n1 n2 n3
| fv2 {n1 n2 n3} : Vars3 n1 n2 n3
| fv3 {n1 n2 n3} : Vars3 n1 n2 n3
inductive Vars4 : FvName -> FvName -> FvName -> FvName -> Type
| fv1 {n1 n2 n3 n4} : Vars4 n1 n2 n3 n4
| fv2 {n1 n2 n3 n4} : Vars4 n1 n2 n3 n4
| fv3 {n1 n2 n3 n4} : Vars4 n1 n2 n3 n4
| fv4 {n1 n2 n3 n4} : Vars4 n1 n2 n3 n4

@[delta0_simps] instance (n1 : FvName): HasVar n1 (Vars1 n1) where fv := .fv1
@[delta0_simps] instance (n1 n2 : FvName): HasVar n1 (Vars2 n1 n2) where fv := .fv1
@[delta0_simps] instance (n1 n2 : FvName): HasVar n2 (Vars2 n1 n2) where fv := .fv2
@[delta0_simps] instance (n1 n2 n3 : FvName): HasVar n1 (Vars3 n1 n2 n3) where fv := .fv1
@[delta0_simps] instance (n1 n2 n3 : FvName): HasVar n2 (Vars3 n1 n2 n3) where fv := .fv2
@[delta0_simps] instance (n1 n2 n3 : FvName): HasVar n3 (Vars3 n1 n2 n3) where fv := .fv3
@[delta0_simps] instance (n1 n2 n3 n4 : FvName): HasVar n1 (Vars4 n1 n2 n3 n4) where fv := .fv1
@[delta0_simps] instance (n1 n2 n3 n4 : FvName): HasVar n2 (Vars4 n1 n2 n3 n4) where fv := .fv2
@[delta0_simps] instance (n1 n2 n3 n4 : FvName): HasVar n3 (Vars4 n1 n2 n3 n4) where fv := .fv3
@[delta0_simps] instance (n1 n2 n3 n4 : FvName): HasVar n4 (Vars4 n1 n2 n3 n4) where fv := .fv4


@[delta0_simps] instance : IsEnum Empty where
  size := 0
  toIdx := Empty.elim
  fromIdx := Fin.elim0
  to_from_id id := Fin.elim0 id
  from_to_id x := Empty.elim x
@[delta0_simps] lemma IsEnum.size.Empty : IsEnum.size Empty = 0 := rfl

@[delta0_simps] instance {n1} : IsEnum (Vars1 n1) where
  size := 1
  toIdx _ := 0
  fromIdx _ := .fv1
  to_from_id id := (Fin.fin_one_eq_zero id).symm
  from_to_id _ := rfl
@[delta0_simps] lemma IsEnum.size.Vars1 {n1} : IsEnum.size (Vars1 n1) = 1 := rfl
@[delta0_simps] lemma IsEnum.toIdx.Vars1 {n1} {x : Vars1 n1}
  : IsEnum.toIdx x = 0
  := rfl

@[delta0_simps] instance {n1 n2} : IsEnum (Vars2 n1 n2) where
  size := 2
  toIdx | .fv1 => 0 | .fv2 => 1
  fromIdx | 0 => .fv1 | 1 => .fv2
  to_from_id id := by
    fin_cases id <;> rfl
  from_to_id x := by
    cases x <;> rfl
@[delta0_simps] lemma IsEnum.size.Vars2 {n1 n2} : IsEnum.size (Vars2 n1 n2) = 2 := rfl
@[delta0_simps] lemma IsEnum.toIdx.Vars2 {n1 n2} {x : Vars2 n1 n2}
  : IsEnum.toIdx x = match x with | .fv1 => 0 | .fv2 => 1
  := rfl

@[delta0_simps] instance {n1 n2 n3} : IsEnum (Vars3 n1 n2 n3) where
  size := 3
  toIdx | .fv1 => 0 | .fv2 => 1 | .fv3 => 2
  fromIdx | 0 => .fv1 | 1 => .fv2 | 2 => .fv3
  to_from_id id := by
    fin_cases id <;> rfl
  from_to_id x := by
    cases x <;> rfl
@[delta0_simps] lemma IsEnum.size.Vars3 {n1 n2 n3} : IsEnum.size (Vars3 n1 n2 n3) = 3 := rfl
@[delta0_simps] lemma IsEnum.toIdx.Vars3 {n1 n2 n3} {x : Vars3 n1 n2 n3}
  : IsEnum.toIdx x = match x with | .fv1 => 0 | .fv2 => 1 | .fv3 => 2
  := rfl

@[delta0_simps] instance {n1 n2 n3 n4} : IsEnum (Vars4 n1 n2 n3 n4) where
  size := 4
  toIdx | .fv1 => 0 | .fv2 => 1 | .fv3 => 2 | .fv4 => 3
  fromIdx | 0 => .fv1 | 1 => .fv2 | 2 => .fv3 | 3 => .fv4
  to_from_id id := by
    fin_cases id <;> rfl
  from_to_id x := by
    cases x <;> rfl
@[delta0_simps] lemma IsEnum.size.Vars4 {n1 n2 n3 n4} : IsEnum.size (Vars4 n1 n2 n3 n4) = 4 := rfl
@[delta0_simps] lemma IsEnum.toIdx.Vars4 {n1 n2 n3 n4} {x : Vars4 n1 n2 n3 n4}
  : IsEnum.toIdx x = match x with | .fv1 => 0 | .fv2 => 1 | .fv3 => 2 | .fv4 => 3
  := rfl

universe u
variable {α : Type u} {L : FirstOrder.Language}


@[delta0_simps] def x.name [h : HasVar .x α] := h.fv
@[delta0_simps] def y.name [h : HasVar .y α] := h.fv
@[delta0_simps] def z.name [h : HasVar .z α] := h.fv
@[delta0_simps] def X.name [h : HasVar .X α] := h.fv
@[delta0_simps] def x {k} [h : HasVar .x α] : L.Term (α ⊕ Fin k) := (L.var $ Sum.inl h.fv)
@[delta0_simps] def y {k} [h : HasVar .y α] : L.Term (α ⊕ Fin k) := (L.var $ Sum.inl h.fv)
@[delta0_simps] def z {k} [h : HasVar .z α] : L.Term (α ⊕ Fin k) := (L.var $ Sum.inl h.fv)
@[delta0_simps] def X {k} [h : HasVar .X α] : L.Term (α ⊕ Fin k) := (L.var $ Sum.inl h.fv)

def FirstOrder.Language.Formula.display1
  {n1 : FvName}
  (phi : L.Formula (Vars1 n1))
  : L.Formula ((Vars1 n1) ⊕ Empty)
:=
  phi.relabelEquiv {
    toFun := (fun fv => match fv with
    | .fv1 => Sum.inl .fv1
    )
    invFun := (fun fv => match fv with | .inl _ => .fv1)
    right_inv := by
      intro v; cases v; simp only;
      apply Empty.elim; assumption
  }


def FirstOrder.Language.Formula.display2
  (name : FvName)
  {other : FvName}
  (phi : L.Formula (Vars2 name other))
  : L.Formula (Vars1 name ⊕ Vars1 other)
:=
  phi.relabelEquiv {
    toFun := (fun fv => match fv with
    | .fv1 => Sum.inl .fv1
    | .fv2 => Sum.inr .fv1
    ),
    invFun := (fun fv => match fv with | .inl _ => .fv1 | .inr _ => .fv2)
    left_inv := by intro v; cases v <;> simp only
    right_inv := by simp only [Function.RightInverse, Function.LeftInverse, Sum.forall, implies_true, and_self]
  }

def FirstOrder.Language.Formula.display3
  (name : FvName)
  {other1 other2 : FvName}
  (phi : L.Formula (Vars3 name other1 other2))
  : L.Formula (Vars1 name ⊕ Vars2 other1 other2)
:=
  phi.relabelEquiv {
    toFun := (fun fv => match fv with
      | .fv1 => Sum.inl .fv1
      | .fv2 => Sum.inr .fv1
      | .fv3 => Sum.inr .fv2)
    invFun := (fun fv => match fv with
      | .inl _    => .fv1
      | .inr .fv1   => .fv2
      | .inr .fv2   => .fv3)
    left_inv := by intro v; cases v <;> simp only
    right_inv := by
      simp only [Function.RightInverse, Function.LeftInverse, Sum.forall, implies_true, true_and]
      intro v; cases v <;> simp only
  }

def FirstOrder.Language.Formula.display4
  (name : FvName)
  {o1 o2 o3 : FvName}
  (phi : L.Formula (Vars4 name o1 o2 o3))
  : L.Formula (Vars1 name ⊕ Vars3 o1 o2 o3)
:=
  phi.relabelEquiv {
    toFun := (fun fv => match fv with
      | .fv1 => Sum.inl .fv1
      | .fv2 => Sum.inr .fv1
      | .fv3 => Sum.inr .fv2
      | .fv4 => Sum.inr .fv3)
    invFun := (fun fv => match fv with
      | .inl _    => .fv1
      | .inr .fv1 => .fv2
      | .inr .fv2 => .fv3
      | .inr .fv3 => .fv4)
    left_inv := by intro v; cases v <;> simp only
    right_inv := by
      simp only [Function.RightInverse, Function.LeftInverse, Sum.forall, implies_true, true_and]
      intro v; cases v <;> simp only
  }

def FirstOrder.Language.Formula.display_swapleft
  {n1 n2 n3 : FvName}
  (phi : L.Formula (Vars1 n1 ⊕ Vars2 n2 n3))
  : L.Formula (Vars2 n1 n2 ⊕ Vars1 n3)
:=
  phi.relabelEquiv {
    toFun := (fun fv => match fv with
      | .inl .fv1 => .inl .fv1
      | .inr .fv1 => .inl .fv2
      | .inr .fv2 => .inr .fv1)
    invFun := (fun fv => match fv with
      | .inl .fv1 => .inl .fv1
      | .inl .fv2 => .inr .fv1
      | .inr .fv1 => .inr .fv2)
    left_inv := by
      intro v;
      cases v with
      | inl vl => simp only
      | inr vr =>
        cases vr <;> simp only
    right_inv := by
      intro v
      cases v with
      | inl vl =>
        cases vl <;> simp only
      | inr vr => simp only
  }

def FirstOrder.Language.Formula.display_swapleft'
  {n1 n2 n3 : FvName}
  (phi : L.Formula (Vars1 n1 ⊕ Vars2 n2 n3))
  : L.Formula ((Vars1 n1 ⊕ Vars1 n2) ⊕ Vars1 n3)
:=
  phi.relabelEquiv {
    toFun := (fun fv => match fv with
      | .inl .fv1 => .inl $ .inl .fv1
      | .inr .fv1 => .inl $ .inr .fv1
      | .inr .fv2 => .inr .fv1)
    invFun := (fun fv => match fv with
      | .inl $ .inl .fv1 => .inl .fv1
      | .inl $ .inr .fv1 => .inr .fv1
      | .inr .fv1 => .inr .fv2)
    left_inv := by
      intro v;
      cases v with
      | inl vl => simp only
      | inr vr =>
        cases vr <;> simp only
    right_inv := by
      intro v
      cases v with
      | inl vl =>
        cases vl <;> simp only
      | inr vr => simp only
  }

-- Vars2 .x .y -> Vars2 .y .x
def FirstOrder.Language.Formula.rotate_21
  {n1 n2 : FvName}
  (phi : L.Formula (Vars2 n1 n2))
  : L.Formula (Vars2 n2 n1)
:=
  phi.relabelEquiv {
    toFun := (fun fv => match fv with
      | .fv1 => .fv2
      | .fv2 => .fv1)
    invFun := (fun fv => match fv with
      | .fv1 => .fv2
      | .fv2 => .fv1)
    left_inv := by intro v; cases v <;> simp only
    right_inv := by
      simp only [Function.RightInverse, Function.LeftInverse]
      intro v; cases v <;> simp only
  }

-- Vars3 .x .y .z -> Vars3 .y .x. .z
def FirstOrder.Language.Formula.rotate_213
  (n1 n2 n3 : FvName)
  (phi : L.Formula (Vars3 n1 n2 n3))
  : L.Formula (Vars3 n2 n1 n3)
:=
  phi.relabelEquiv {
    toFun := (fun fv => match fv with
      | .fv1 => .fv2
      | .fv2 => .fv1
      | .fv3 => .fv3)
    invFun := (fun fv => match fv with
      | .fv1 => .fv2
      | .fv2 => .fv1
      | .fv3 => .fv3)
    left_inv := by intro v; cases v <;> simp only
    right_inv := by
      simp only [Function.RightInverse, Function.LeftInverse]
      intro v; cases v <;> simp only
  }

-- Vars3 .x .y .z -> Vars3 .y .x. .z
def FirstOrder.Language.Formula.rotate_231
  (n1 n2 n3 : FvName)
  (phi : L.Formula (Vars3 n1 n2 n3))
  : L.Formula (Vars3 n3 n1 n2)
:=
  phi.relabelEquiv {
    toFun := (fun fv => match fv with
      | .fv1 => .fv2
      | .fv2 => .fv3
      | .fv3 => .fv1)
    invFun := (fun fv => match fv with
      | .fv1 => .fv3
      | .fv2 => .fv1
      | .fv3 => .fv2)
    left_inv := by intro v; cases v <;> simp only
    right_inv := by
      simp only [Function.RightInverse, Function.LeftInverse]
      intro v; cases v <;> simp only
  }

variable {β}

def FirstOrder.Language.BoundedFormula.flip {n} (phi : L.BoundedFormula (α ⊕ β) n) : L.BoundedFormula (β ⊕ α) n:=
  phi.relabelEquiv {
    toFun := Sum.swap (α := α) (β := β)
    invFun := Sum.swap
    left_inv := Sum.swap_leftInverse
    right_inv := Sum.swap_rightInverse
  }

def FirstOrder.Language.Formula.flip (phi : L.Formula (α ⊕ β)) : L.Formula (β ⊕ α) :=
  phi.relabelEquiv {
    toFun := Sum.swap (α := α) (β := β)
    invFun := Sum.swap
    left_inv := Sum.swap_leftInverse
    right_inv := Sum.swap_rightInverse
  }

-- theorem FirstOrder.Language.Formula.realize_flip (phi : L.Formula (α ⊕ β)) {v}
--   : phi.flip.Realize v <-> phi.Realize (v ∘ )

def FirstOrder.Language.Formula.mkInl (phi : L.Formula α) : L.Formula (α ⊕ Empty) :=
  phi.relabelEquiv {
    toFun := Sum.inl
    invFun := Sum.elim id Empty.elim
    left_inv := by
      intro x
      simp only [Sum.elim_inl, id_eq]
    right_inv := by
      intro x
      cases x with
      | inl x => simp only [Sum.elim_inl, id_eq]
      | inr x => apply Empty.elim x
  }
