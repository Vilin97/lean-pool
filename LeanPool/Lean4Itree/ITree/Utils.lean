/-
Copyright (c) 2026 Paul Mure, Joonhyup Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Mure, Joonhyup Lee
-/
import Mathlib.Data.QPF.Univariate.Basic
import Mathlib.Data.Vector3

/-! # ----------------------------------------------------------------------- -/
/-! # --------------------Start Vector3 Utilities---------------------------- -/
/-! # ----------------------------------------------------------------------- -/

namespace Lean4Itree

instance instOfNatULiftFin2Zero {n : Nat} [Fin2.IsLT 0 n] : OfNat (ULift (Fin2 n)) 0 :=
  ⟨.up <| .ofNat' 0⟩

instance instOfNatULiftFin2One {n : Nat} [Fin2.IsLT 1 n] : OfNat (ULift (Fin2 n)) 1 :=
  ⟨.up <| .ofNat' 1⟩

/-- The empty eliminator out of `ULift (Fin2 0)`: a lifted `Fin2 0` has no inhabitant. -/
def elim0 {α : Sort u} (i : ULift (Fin2 0)) : α :=
  i.down.elim0 (C := fun _ => α)

/-- The constant function `ULift (Fin2 1) → α` returning `v` at the unique index. -/
def fin1Const {α} (v : α) :=
  fun (i : ULift (Fin2 1)) =>
    match i.down with | .ofNat' 0 => v

open Vector3 in
/-- The function `ULift (Fin2 2) → α` returning `x` at index `0` and `y` at index `1`. -/
def fin2Const {α} (x y : α) :=
  fun (i : ULift (Fin2 2)) => [x, y] i.down

theorem elim0_eq_all {α} : ∀ x : ULift (Fin2 0) → α, x = elim0 :=
  fun x => funext fun z => @z.down.elim0 fun _ => x z = elim0 z

theorem fin1Const_inj {α} {x y : α}
  (h : fin1Const x = fin1Const y) : x = y := by
  have := congr (a₁ := 0) h rfl
  simp only [fin1Const] at this
  exact this

theorem fin1Const_fin0 : fin1Const (c 0) = c := by
  funext i
  match i with
  | .up (.ofNat' 0) =>
    have fwd : Fin2 1 := i.down
    rfl

/-! # ----------------------------------------------------------------------- -/
/-! # --------------------End Vector3 Utilities------------------------------ -/
/-! # ----------------------------------------------------------------------- -/

/-! # ----------------------------------------------------------------------- -/
/-! # --------------------Start PFunctor Utilities--------------------------- -/
/-! # ----------------------------------------------------------------------- -/

universe uA uB u

theorem PFunctor.M.unfold_corec'_left {P : PFunctor.{uA, uB}} {α : Type u}
  (F : P.M ⊕ α → P (P.M ⊕ α))
  (h_eq : ∀ l, F (.inl l) = ⟨l.dest.1, Sum.inl ∘ l.dest.2⟩) :
  ∀ l, PFunctor.M.corec F (.inl l) = l := by
  intros
  apply PFunctor.M.bisim (fun t1 t2 => t1 = PFunctor.M.corec _ (Sum.inl t2)) _ _ _ rfl
  intros t1 t2 h; subst h
  simp only [PFunctor.M.dest_corec, PFunctor.map, h_eq]
  have ⟨a, g⟩ := t2.dest
  exact ⟨_, _, _, rfl, rfl, fun _ => rfl⟩

theorem PFunctor.M.unfold_corec' {P : PFunctor.{uA, uB}} {α : Type u}
  (F : ∀ {X : Type (max u uA uB)}, (α → X) → α → P.M ⊕ P X) (x : α) :
  .corec' F x =
  match F (@Sum.inr P.M α) x with
  | .inl l => l
  | .inr ⟨a, g⟩ => .mk ⟨a, fun i ↦
    match g i with
    | .inl l => l
    | .inr r => .corec' F r⟩ := by
  conv =>
    lhs
    simp only [PFunctor.M.corec', PFunctor.M.corec₁, PFunctor.M.corec_def, PFunctor.map,
      Sum.bind, Function.id_comp]
  match F (@Sum.inr P.M α) x with
  | .inl v =>
    simp only
    conv => rhs; rw [← (PFunctor.M.mk_dest v)]
    congr
    have ⟨a, g⟩ := v.dest
    simp only; congr; funext i
    apply unfold_corec'_left _ (fun _ => rfl)
  | .inr ⟨a, g⟩ =>
    simp only; congr; funext i
    simp only [Function.comp]
    match g i with
    | .inl l =>
      simp only
      apply unfold_corec'_left _ (fun _ => rfl)
    | .inr r =>
      simp only [PFunctor.M.corec', PFunctor.M.corec₁, PFunctor.map, Sum.bind, Function.id_comp]

end Lean4Itree

/-! # ----------------------------------------------------------------------- -/
/-! # --------------------End PFunctor Utilities--------------------------- -/
/-! # ----------------------------------------------------------------------- -/
