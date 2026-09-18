/-
Copyright (c) 2026 Paul Mure, Joonhyup Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Mure, Joonhyup Lee
-/
module

public import Mathlib.Data.Vector3
public import Mathlib.Data.PFunctor.Univariate.M

/-! # ----------------------------------------------------------------------- -/

@[expose] public section
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
  | .up (.ofNat' 0) => rfl

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
  apply PFunctor.M.bisim (fun t1 t2 => t1 = PFunctor.M.corec F (Sum.inl t2)) ?_ _ _ rfl
  intros t1 t2 h; subst h
  refine ⟨t2.dest.fst, _, t2.dest.snd, ?_, rfl, fun _ => rfl⟩
  rw [PFunctor.M.dest_corec, h_eq]
  rfl

theorem PFunctor.M.unfold_corec' {P : PFunctor.{uA, uB}} {α : Type u}
  (F : ∀ {X : Type (max u uA uB)}, (α → X) → α → P.M ⊕ P X) (x : α) :
  .corec' F x =
  match F (@Sum.inr P.M α) x with
  | .inl l => l
  | .inr ⟨a, g⟩ => .mk ⟨a, fun i ↦
    match g i with
    | .inl l => l
    | .inr r => .corec' F r⟩ := by
  have main : ∀ G : P.M ⊕ α → P (P.M ⊕ α),
      (∀ l : P.M, G (.inl l) = P.map Sum.inl l.dest) →
      (∀ (a : α) (l : P.M), F (@Sum.inr P.M α) a = .inl l → G (.inr a) = P.map Sum.inl l.dest) →
      (∀ (a : α) (w : P (P.M ⊕ α)), F (@Sum.inr P.M α) a = .inr w → G (.inr a) = w) →
      ∀ a : α, PFunctor.M.corec G (.inr a) =
        match F (@Sum.inr P.M α) a with
        | .inl l => l
        | .inr ⟨b, g⟩ => .mk ⟨b, fun i ↦
          match g i with
          | .inl l => l
          | .inr r => PFunctor.M.corec G (.inr r)⟩ := by
    intro G hl hinl hinr a
    have key : ∀ l : P.M, PFunctor.M.corec G (Sum.inl l) = l :=
      unfold_corec'_left G hl
    rw [PFunctor.M.corec_def]
    rcases hF : F (@Sum.inr P.M α) a with v | ⟨b, g⟩
    · simp only
      rw [hinl a v hF, PFunctor.map_map,
        show (PFunctor.M.corec G ∘ Sum.inl) = id from funext key,
        PFunctor.id_map, PFunctor.M.mk_dest]
    · simp only
      rw [hinr a _ hF]
      refine congrArg PFunctor.M.mk (congrArg (PFunctor.Obj.mk b) (funext fun i ↦ ?_))
      change PFunctor.M.corec G (g i) = _
      match g i with
      | .inl l => exact key l
      | .inr r => rfl
  simp only [PFunctor.M.corec', PFunctor.M.corec₁]
  refine main _ (fun _ ↦ rfl) ?_ ?_ x
  · intro a l h
    simp only [Sum.bind, Function.id_comp, h]
  · intro a w h
    simp only [Sum.bind, Function.id_comp, h]

end Lean4Itree

/-! # ----------------------------------------------------------------------- -/
/-! # --------------------End PFunctor Utilities--------------------------- -/
/-! # ----------------------------------------------------------------------- -/
