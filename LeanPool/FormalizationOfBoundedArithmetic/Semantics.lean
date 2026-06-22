/-
Copyright (c) 2026 ruplet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ruplet
-/

import Lean.Elab.Command

import Mathlib.ModelTheory.Semantics

import LeanPool.FormalizationOfBoundedArithmetic.Syntax
import LeanPool.FormalizationOfBoundedArithmetic.DisplayedVariables
import LeanPool.FormalizationOfBoundedArithmetic.SimpRules
import LeanPool.FormalizationOfBoundedArithmetic.Order
import LeanPool.FormalizationOfBoundedArithmetic.LanguagePeano
import LeanPool.FormalizationOfBoundedArithmetic.LanguageZambella

/-!
# LeanPool.FormalizationOfBoundedArithmetic.Semantics
-/

namespace FirstOrder.Language
open BoundedFormula

open Lean Elab Tactic Command


namespace Term


@[delta0_simps] lemma realize_zero {M} [peano.Structure M] {a} {env : a → M} :
  Language.Term.realize env (0 : peano.Term a) = (0 : M) := by
  simp only [OfNat.ofNat, Zero.zero]
  simp only [peano, Term.realize_constants]
  rfl

-- it is important to define OfNat 1 as 1, not (0+1), as the later needs an axiom to
-- be asserted equal to 1.
@[delta0_simps] lemma realize_one {M} [peano.Structure M] {a} {env : a → M} :
  Term.realize env (1 : peano.Term a) = (1 : M) := by
  simp only [OfNat.ofNat, One.one]
  simp only [peano, Term.realize_constants]
  rfl

@[delta0_simps] lemma realize_add {M} [h : peano.Structure M] {a} {env : a → M}
    (t u : peano.Term a) :
  Term.realize env (t + u) = Term.realize env t + Term.realize env u := by
  simp only [peano, HAdd.hAdd, Add.add]
  -- TODO: why the below doesn't work without @?
  rw [@Term.realize_functions_apply₂]

@[delta0_simps] lemma realize_mul {M} [peano.Structure M] {a} {env : a → M}
    (t u : peano.Term a) :
  Term.realize env (t * u) = Term.realize env t * Term.realize env u := by
  simp only [HMul.hMul, Mul.mul]
  rw [@Term.realize_functions_apply₂]

end Term


namespace BoundedFormula
variable {L : Language} {M : Type*} [L.Structure M] {a b} {n1 n2 n3} {n}

-- important: DON'T make this a simp lemma!
-- breaks everything
-- @[delta0_simps]
-- lemma realize_Formula (phi : L.Formula a) {v : a -> M} {xs}
--   : BoundedFormula.Realize phi v xs
--     <->
--     phi.Realize v
--   :=
-- by
--   exact Formula.boundedFormula_realize_eq_realize phi v xs

-- @[delta0_simps]
-- lemma realize_flip (phi : L.BoundedFormula (a ⊕ b) n) {v : (b ⊕ a) -> M} {xs}
--   : phi.flip.Realize v xs
--     <->
--     phi.Realize (v ∘ Sum.swap) xs
--   :=
-- by
--   unfold BoundedFormula.flip
--   rw [realize_relabelEquiv]
--   dsimp only [Equiv.coe_fn_mk]
--   exact Eq.to_iff rfl

end BoundedFormula


namespace Formula

variable {L : Language} {M : Type*} [L.Structure M] {a b} {n1 n2 n3 n4}

@[delta0_simps]
lemma realize_flip (phi : L.Formula (a ⊕ b)) {v : (b ⊕ a) -> M}
  : phi.flip.Realize v
    <->
    phi.Realize (v ∘ Sum.swap)
  :=
by
  unfold Formula.Realize
  unfold Formula.flip
  rw [realize_relabelEquiv]
  dsimp only [Equiv.coe_fn_mk]
  exact Eq.to_iff rfl

@[delta0_simps]
lemma realize_rotate_21 (phi : L.Formula (Vars2 n1 n2)) {v : _ -> M}
  : phi.rotate21.Realize v
    <->
    phi.Realize (v ∘ (fun fv => match fv with
      | .fv1 => .fv2
      | .fv2 => .fv1))
  :=
by
  unfold Formula.Realize
  unfold Formula.rotate21
  rw [realize_relabelEquiv]
  dsimp only [Equiv.coe_fn_mk]
  exact Eq.to_iff rfl

@[delta0_simps]
lemma realize_rotate_213 (phi : L.Formula (Vars3 n1 n2 n3)) {v : _ -> M}
  : phi.rotate213.Realize v
    <->
    phi.Realize (v ∘ (fun fv => match fv with
      | .fv1 => .fv2
      | .fv2 => .fv1
      | .fv3 => .fv3))
  :=
by
  unfold Formula.Realize
  unfold Formula.rotate213
  rw [realize_relabelEquiv]
  dsimp only [Equiv.coe_fn_mk]
  exact Eq.to_iff rfl

@[delta0_simps]
lemma realize_mkInl (phi : L.Formula a) {v : (a ⊕ Empty) -> M}
  : phi.mkInl.Realize v
    <->
    phi.Realize (v ∘ Sum.inl)
  :=
by
  unfold Formula.Realize
  unfold Formula.mkInl
  rw [realize_relabelEquiv]
  dsimp only [Equiv.coe_fn_mk]
  exact Eq.to_iff rfl

@[delta0_simps]
lemma realize_display1 (phi : L.Formula (Vars1 n1)) {v : ((Vars1 n1) ⊕ Empty) -> M}
  : phi.display1.Realize v
    <->
    phi.Realize (v ∘ .inl)
  :=
by
  unfold Formula.Realize
  unfold Formula.display1
  rw [realize_relabelEquiv]
  dsimp only [Equiv.coe_fn_mk]
  exact Eq.to_iff rfl

@[delta0_simps]
lemma realize_display2 (phi : L.Formula (Vars2 n1 n2))
    {v : ((Vars1 n1) ⊕ (Vars1 n2)) -> M}
  : phi.display2.Realize v
    <->
    phi.Realize (v ∘ (fun fv => match fv with
      | .fv1 => .inl .fv1
      | .fv2 => .inr .fv1))
  :=
by
  unfold Formula.Realize
  unfold Formula.display2
  rw [realize_relabelEquiv]
  dsimp only [Equiv.coe_fn_mk]
  exact Eq.to_iff rfl

@[delta0_simps]
lemma realize_display3 (phi : L.Formula (Vars3 n1 n2 n3))
    {v : ((Vars1 n1) ⊕ (Vars2 n2 n3)) -> M}
  : phi.display3.Realize v
    <->
    phi.Realize (v ∘ (fun fv => match fv with
      | .fv1 => .inl .fv1
      | .fv2 => .inr .fv1
      | .fv3 => .inr .fv2))
  :=
by
  unfold Formula.Realize
  unfold Formula.display3
  rw [realize_relabelEquiv]
  dsimp only [Equiv.coe_fn_mk]
  exact Eq.to_iff rfl

@[delta0_simps]
lemma realize_display4 (phi : L.Formula (Vars4 n1 n2 n3 n4))
    {v : ((Vars1 n1) ⊕ (Vars3 n2 n3 n4)) -> M}
  : phi.display4.Realize v
    <->
    phi.Realize (v ∘ (fun fv => match fv with
      | .fv1 => .inl .fv1
      | .fv2 => .inr .fv1
      | .fv3 => .inr .fv2
      | .fv4 => .inr .fv3))
  :=
by
  unfold Formula.Realize
  unfold Formula.display4
  rw [realize_relabelEquiv]
  dsimp only [Equiv.coe_fn_mk]
  exact Eq.to_iff rfl


@[delta0_simps]
lemma realize_display_swapleft (phi : L.Formula (Vars1 n1 ⊕ Vars2 n2 n3))
    {v : ((Vars2 n1 n2) ⊕ (Vars1 n3)) -> M}
  : phi.displaySwapleft.Realize v
    <->
    phi.Realize (v ∘ (fun fv => match fv with
      | .inl .fv1 => .inl .fv1
      | .inr .fv1 => .inl .fv2
      | .inr .fv2 => .inr .fv1))
  :=
by
  unfold Formula.Realize
  unfold Formula.displaySwapleft
  rw [realize_relabelEquiv]
  dsimp only [Equiv.coe_fn_mk]
  exact Eq.to_iff rfl

@[delta0_simps]
lemma realize_display_swapleft' (phi : L.Formula (Vars1 n1 ⊕ Vars2 n2 n3))
    {v : ((Vars1 n1 ⊕ Vars1 n2) ⊕ (Vars1 n3)) -> M}
  : phi.displaySwapleft'.Realize v
    <->
    phi.Realize (v ∘ (fun fv => match fv with
      | .inl .fv1 => .inl (.inl .fv1)
      | .inr .fv1 => .inl (.inr .fv1)
      | .inr .fv2 => .inr .fv1))
  :=
by
  unfold Formula.Realize
  unfold Formula.displaySwapleft'
  rw [realize_relabelEquiv]
  dsimp only [Equiv.coe_fn_mk]
  exact Eq.to_iff rfl


/-- `peel_iAlls' k` rewrites `(iAlls' φ).Realize` by peeling exactly
    `k` quantifiers (`realize_all; intro`). -/
syntax (name := peelIAlls) "peel_iAlls' " num : conv

-- TODO: substitute `n` with actual size of `IsEnum`'ed type
elab_rules : conv
| `(conv| peel_iAlls' $k:num) => do
  let some n := k.raw.isNatLit?
    | throwErrorAt k "peel_iAlls': expected a nonnegative integer literal"
  Conv.evalUnfold (← `(conv| unfold iAlls'))
  Conv.evalSimp (← `(conv| simp only [IsEnum.size.Empty, IsEnum.size.Vars1,
    IsEnum.size.Vars2, IsEnum.size.Vars3, Nat.add_zero, Nat.reduceAdd]))
  for _ in [:n + 1] do
    Conv.evalUnfold (← `(conv| unfold BoundedFormula.alls))
    Conv.evalSimp (← `(conv| simp only [IsEnum.size.Empty, IsEnum.size.Vars1,
      IsEnum.size.Vars2, IsEnum.size.Vars3, Nat.add_zero, Nat.reduceAdd]))
  for _ in [:n] do
    Conv.evalRewrite (← `(conv| rw [BoundedFormula.realize_all]))
    Conv.evalExt (← `(conv| ext))
  Conv.evalRewrite (← `(conv| rw [BoundedFormula.realize_relabel]))

/-- `peel_iExs' k` rewrites `(iExs' φ).Realize` by peeling exactly
    `k` quantifiers (`realize_ex; intro`). -/
syntax (name := peelIExs) "peel_iExs' " num : conv

-- TODO: substitute `n` with actual size of `IsEnum`'ed type
elab_rules : conv
| `(conv| peel_iExs' $k:num) => do
  let some n := k.raw.isNatLit?
    | throwErrorAt k "peel_iExs': expected a nonnegative integer literal"
  Conv.evalUnfold (← `(conv| unfold iExs'))
  Conv.evalSimp (← `(conv| simp only [IsEnum.size.Empty, IsEnum.size.Vars1,
    IsEnum.size.Vars2, IsEnum.size.Vars3, Nat.add_zero, Nat.reduceAdd]))
  for _ in [:n + 1] do
    Conv.evalUnfold (← `(conv| unfold BoundedFormula.exs))
    Conv.evalSimp (← `(conv| simp only [IsEnum.size.Empty, IsEnum.size.Vars1,
      IsEnum.size.Vars2, IsEnum.size.Vars3, Nat.add_zero, Nat.reduceAdd]))
  Conv.evalUnfold (← `(conv| unfold Formula.Realize))
  for _ in [:n] do
    Conv.evalRewrite (← `(conv| rw [BoundedFormula.realize_ex]))
    Conv.evalEnter (← `(conv| enter [1]))
    Conv.evalExt (← `(conv| ext))
  Conv.evalRewrite (← `(conv| rw [BoundedFormula.realize_relabel]))



namespace realize_iAlls'

@[delta0_simps]
lemma Empty (phi : L.Formula (a ⊕ Empty)) {v : a -> M}
  : phi.iAlls'.Realize v
    <->
      phi.Realize
        (Sum.elim v Empty.elim)
  :=
by
  unfold Formula.Realize
  conv =>
    lhs
    peel_iAlls' 0
  constructor <;>
    (
      intro h;
      convert h;
      funext;
      rename_i x;
      cases x;
      simp only [Sum.elim_inl, Nat.add_zero, Fin.castAdd_zero, Fin.cast_refl, Function.comp_id,
        Function.comp_apply, Sum.map_inl, id_eq]
      apply Empty.elim; assumption
    )

-- TODO: IT SHOULD HOLD DEFINITIONALLY?... but I couldn't prove without funext
@[delta0_simps]
lemma Vars1 (phi : L.Formula (a ⊕ Vars1 n1)) {v : a -> M}
  : phi.iAlls'.Realize v
    <->
      ∀ x : M, phi.Realize
        (Sum.elim v (fun fv => match fv with | .fv1 => x))
  :=
by
  unfold Formula.Realize
  conv =>
    lhs
    peel_iAlls' 1
    -- unfold IsEnum.toIdx instIsEnumVars1; dsimp only
  -- conv =>
  --   rhs; rhs; arg 2; arg 2; intro; dsimp only
  constructor <;>
    (
      intro h a;
      specialize h a;
      convert h;
      funext;
      rename_i x;
      cases x;
    ) <;>
    simp [Fin.snoc]


@[delta0_simps]
lemma Vars2 (phi : L.Formula (a ⊕ Vars2 n1 n2)) {v : a -> M}
  : phi.iAlls'.Realize v
    <->
      ∀ x y : M, phi.Realize
        (Sum.elim v (fun fv => match fv with | .fv1 => x | .fv2 => y))
  :=
by
  unfold Formula.Realize
  conv =>
    lhs
    peel_iAlls' 2
  constructor <;> intro h x y <;> specialize h x y <;> convert h
  all_goals
    funext z
    cases z with
    | inl z => simp
    | inr z => cases z <;> simp [Fin.snoc, IsEnum.toIdx.Vars2]

@[delta0_simps]
lemma Vars3 (phi : L.Formula (a ⊕ Vars3 n1 n2 n3)) {v : a -> M}
  : phi.iAlls'.Realize v
    <->
      ∀ x y z : M, phi.Realize
        (Sum.elim v (fun fv => match fv with | .fv1 => x | .fv2 => y | .fv3 => z))
  :=
by
  unfold Formula.Realize
  conv =>
    lhs
    peel_iAlls' 3
  constructor <;> intro h x y z <;> specialize h x y z <;> convert h
  all_goals
    funext w
    cases w with
    | inl w => simp
    | inr w => cases w <;> simp [Fin.snoc, IsEnum.toIdx.Vars3]

end realize_iAlls'

namespace realize_iExs'

@[delta0_simps]
lemma Vars1 (phi : L.Formula (a ⊕ Vars1 n1)) {v : a -> M}
  : phi.iExs'.Realize v
    <->
      ∃ x : M, phi.Realize
        (Sum.elim v (fun fv => match fv with | .fv1 => x))
  :=
by
  unfold Formula.Realize
  conv =>
    lhs
    peel_iExs' 1
  constructor <;>
    (
      intro h;
      obtain ⟨x, hx⟩ := h;
      exists x
      convert hx
      funext
      rename_i x
    )
  · cases x
    · simp only [Sum.elim_inl, Nat.add_zero, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.castAdd_zero,
      Fin.cast_refl, Function.comp_id, Function.comp_apply, Sum.map_inl, id_eq]
    · simp only [Sum.elim_inr, Nat.add_zero, Nat.succ_eq_add_one, Nat.reduceAdd,
      Fin.castAdd_zero, Fin.cast_refl, Function.comp_id, Function.comp_apply, Sum.map_inr]
      simp only [Fin.snoc, Nat.reduceAdd, Fin.val_eq_zero, lt_self_iff_false,
        ↓reduceDIte, Fin.reduceLast, cast_eq]
  · cases x;
    · simp only [Sum.elim_inl, Nat.add_zero, Nat.succ_eq_add_one, Nat.reduceAdd,
        Fin.castAdd_zero, Fin.cast_refl, Function.comp_id, Function.comp_apply, Sum.map_inl, id_eq]
    · simp only [Sum.elim_inr, Nat.add_zero, Nat.succ_eq_add_one, Nat.reduceAdd,
      Fin.castAdd_zero, Fin.cast_refl, Function.comp_id, Function.comp_apply, Sum.map_inr, Fin.snoc,
      Fin.val_eq_zero, lt_self_iff_false, ↓reduceDIte, Fin.reduceLast, cast_eq]

end realize_iExs'


open ZambellaModel
universe u

@[delta0_simps]
theorem _root_.FirstOrder.Term.realize_isnum {num str : Type u} [ZambellaModel num str] {a : Type}
    {t : zambella.Term (a ⊕ Fin 0)} {v : a -> (num ⊕ str)} :
    t.IsNum.Realize v
    <-> (t.realize (Sum.elim v Fin.elim0)).isLeft := ax_realize_isnum

@[delta0_simps]
theorem _root_.FirstOrder.Term.realize_isstr {num str : Type u} [ZambellaModel num str] {a : Type}
    {t : zambella.Term (a ⊕ Fin 0)} {v : a -> (num ⊕ str)} :
    t.IsStr.Realize v
    <-> (t.realize (Sum.elim v Fin.elim0)).isRight := ax_realize_isstr


-- @[delta0_simps]
-- lemma realize_IsNum (phi : zambella.Formula a) {v : a -> (num ⊕ str)}
--   : (Formula.IsNum phi).Realize v
--     <->
--     phi.Realize (v ∘ Sum.inl)
--   :=
-- by
--   unfold Formula.Realize
--   unfold Formula.mkInl
--   rw [realize_relabelEquiv]
--   dsimp only [Equiv.coe_fn_mk]
--   exact Eq.to_iff rfl


-- @[delta0_simps]
-- theorem realize_isstr {a : Type} {v : a -> (num ⊕ str)} {t : zambella.Term (a ⊕ Fin 0)} :
--     (IsStr t).Realize v
--     <-> (t.realize (Sum.elim v Fin.elim0)).isRight := ax_realize_isstr

@[delta0_simps]
theorem _root_.FirstOrder.Term.realize_in {num str : Type u} [ZambellaModel num str] {a : Type} {n}
    {t1 t2 : zambella.Term (a ⊕ Fin n)}
    {v : a -> (num ⊕ str)}
    {xs : Fin n -> (num ⊕ str)} :
    (Term.in t1 t2).Realize v xs
    <-> (t1.realize (Sum.elim v xs)) ∈ (t2.realize (Sum.elim v xs)) := ax_realize_in

@[delta0_simps]
theorem realize_in {num str : Type u} [ZambellaModel num str] {a : Type}
  {t1 t2 : zambella.Term (a ⊕ Fin 0)}
  {v : a -> (num ⊕ str)} :
  Formula.Realize (Term.in t1 t2) v
  <-> (t1.realize (Sum.elim v default)) ∈ (t2.realize (Sum.elim v default))
  :=
by
  unfold Formula.Realize
  rw [Term.realize_in]

@[delta0_simps]
theorem realize_notin {num str : Type u} [ZambellaModel num str] {a : Type}
    {t1 t2 : zambella.Term (a ⊕ Fin 0)}
    {v : a -> (num ⊕ str)}
    {xs : Fin 0 -> (num ⊕ str)} :
    (Term.notin t1 t2).Realize v xs
    <-> (t1.realize (Sum.elim v default)) ∉ (t2.realize (Sum.elim v default))
    := by
    unfold Term.notin
    conv =>
      lhs;
      unfold Formula.Realize
      rw [Formula.boundedFormula_realize_eq_realize]
      rw [realize_not]
    conv =>
      rhs
      unfold Not
    unfold Formula.Realize
    rw [Term.realize_in]

-- @[irreducible] def iBdEx' {α n} (bdTerm : L.Term (α ⊕ Fin 0))
--     (φ : L.Formula (α ⊕ (Vars1 n))) : L.Formula α :=
--   let bd := (var (.inl (Sum.inr (.fv1)))).le $ bdTerm.relabel (Sum.map .inl id)
--   iExs' $ bd ⊓ φ
@[delta0_simps]
theorem realize_iBdEx' {M : Type*} [peano.Structure M] {t : peano.Term (a ⊕ Fin 0)}
    (phi : peano.Formula (a ⊕ Vars1 n1)) {v : a -> M}
  : (iBdEx' t phi).Realize v
    <->
    ∃ x : M,
      (x <= (t.realize (Sum.elim v Fin.elim0)) ∧
        phi.Realize (Sum.elim v (fun _ => x))) :=
by
  unfold iBdEx'
  rw [realize_iExs'.Vars1]
  conv =>
    lhs; rhs; intro;
    rw [realize_inf]
    conv =>
      lhs;
      change BoundedFormula.Realize _ _ _
      rw [Term.realize_le]
      simp only [peano.instLEOfStructure, Term.realize_var, Sum.elim_inl, Sum.elim_inr,
        Term.realize_relabel]
    conv =>
      rhs;
      simp only
  conv =>
    rhs
    rhs; intro;
    lhs;
  unfold Formula.Realize
  constructor
  · intro h
    rcases h with ⟨x, hx⟩
    rcases hx with ⟨hxle, hphi⟩
    have henv :
        ((Sum.elim (Sum.elim v (fun _ : Vars1 n1 => x)) (default : Fin 0 → M)) ∘
          (Sum.map (Sum.inl : a → a ⊕ Vars1 n1) (id : Fin 0 → Fin 0))) =
          Sum.elim v Fin.elim0 := by
      funext y
      cases y with
      | inl y => simp
      | inr y => exact Fin.elim0 y
    refine ⟨x, ?_, hphi⟩
    simpa only [peano.instLEOfStructure, Sum.elim_inl, Sum.elim_inr, Term.realize_relabel,
      Sum.elim_map, henv] using hxle
  · intro h
    rcases h with ⟨x, hxle, hphi⟩
    have henv :
        ((Sum.elim (Sum.elim v (fun _ : Vars1 n1 => x)) (default : Fin 0 → M)) ∘
          (Sum.map (Sum.inl : a → a ⊕ Vars1 n1) (id : Fin 0 → Fin 0))) =
          Sum.elim v Fin.elim0 := by
      funext y
      cases y with
      | inl y => simp
      | inr y => exact Fin.elim0 y
    refine ⟨x, ⟨?_, hphi⟩⟩
    simpa only [peano.instLEOfStructure, Sum.elim_inl, Sum.elim_inr, Term.realize_relabel,
      Sum.elim_map, henv] using hxle

namespace realize_iBdAll'

@[delta0_simps]
lemma Vars1
  {num str}
  [inst1 : ZambellaModel num str]
  (phi : zambella.Formula (a ⊕ Vars1 n1))
  {t : zambella.Term (a ⊕ Fin 0)}
  {v : a -> (num ⊕ str)}
  : (phi.iBdAll' t).Realize v
    <->
      ∀ x : (num ⊕ str),
      x <= (t.realize (Sum.elim v default))
      -> phi.Realize
        (Sum.elim v (fun fv => match fv with | .fv1 => x))
  :=
by
  unfold iBdAll'
  rw [realize_iAlls'.Vars1]
  conv =>
    lhs; ext;
    rw [realize_imp]
    unfold Formula.Realize
    rw [Term.realize_le]
    simp only [Term.realize_var, Sum.elim_inl, Sum.elim_inr, Term.realize_relabel]
    conv =>
      left; right; arg 1
      unfold Function.comp; intro
      rw [Sum.elim_map]
      simp only [Sum.elim_comp_inl, Function.comp_id]
  conv =>
    rhs; ext
    simp only
  unfold Formula.Realize
  exact Lex.forall

end realize_iBdAll'

namespace realize_iBdAllLt'

@[delta0_simps]
lemma Vars1 {M : Type*} [IsOrdered L] [L.Structure M] [Preorder M]
  [h : L.OrderedStructure M] (phi : L.Formula (a ⊕ Vars1 n1))
  {t : L.Term (a ⊕ Fin 0)}
  {v : a -> M}
  : (phi.iBdAllLt' t).Realize v
    <->
      ∀ x : M, x < (t.realize (Sum.elim v default)) -> phi.Realize
        (Sum.elim v (fun fv => match fv with | .fv1 => x))
  :=
by
  unfold iBdAllLt'
  rw [realize_iAlls'.Vars1]
  conv =>
    lhs; ext;
    rw [realize_imp]
    unfold Formula.Realize
    rw [Term.realize_lt]
    simp only [Term.realize_var, Sum.elim_inl, Sum.elim_inr, Term.realize_relabel]
    conv =>
      left; right; arg 1
      unfold Function.comp; intro
      rw [Sum.elim_map]
      simp only [Sum.elim_comp_inl, Function.comp_id]
  conv =>
    rhs; ext
    simp only
  unfold Formula.Realize
  exact Lex.forall

end realize_iBdAllLt'

namespace realize_iBdAllNum'

@[delta0_simps]
lemma Vars1
  {num str}
  [inst1 : ZambellaModel num str]
  (phi : zambella.Formula (a ⊕ Vars1 n1))
  {t : zambella.Term (a ⊕ Fin 0)}
  {v : a -> (num ⊕ str)}
  : (phi.iBdAllNum' t).Realize v
    <->
      ∀ x : (num ⊕ str),
      x <= (t.realize (Sum.elim v default))
      -> x.isLeft
      -> phi.Realize
        (Sum.elim v (fun fv => match fv with | .fv1 => x))
  :=
by
  unfold iBdAllNum'
  rw [realize_iBdAll'.Vars1]
  conv =>
    lhs; ext; rhs;
    rw [realize_imp]
    conv =>
      lhs
      rw [Term.realize_isnum]
      simp only [Term.realize_var, Sum.elim_inl, Sum.elim_inr]

end realize_iBdAllNum'

-- @[delta0_simps]
-- lemma realize_iBdAllNumLt'.Vars1
--   {num str}
--   [inst1 : ZambellaModel num str]
--   (phi : zambella.Formula (a ⊕ Vars1 n1) )
--   {t : zambella.Term (a ⊕ Fin 0)}
--   {v : a -> (num ⊕ str)}
--   : (phi.iBdAllNumLt' t).Realize v
--     <->
--       ∀ x : (num ⊕ str),
--       x < (t.realize (Sum.elim v default))
--       -> x.isLeft
--       -> phi.Realize
--         (Sum.elim v (fun fv => match fv with | .fv1 => x))
--   :=
-- by
--   unfold iBdAllNumLt'
--   rw [realize_iBdAllLt'.Vars1]

--   conv =>
--     lhs; ext; rhs;
--     rw [realize_imp]
--     conv =>
--       lhs
--       rw [Term.realize_isnum]
--       simp only [Term.realize_var, Sum.elim_inl, Sum.elim_inr]
end Formula
end FirstOrder.Language
