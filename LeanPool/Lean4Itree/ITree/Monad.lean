/-
Copyright (c) 2026 Paul Mure, Joonhyup Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Mure, Joonhyup Lee
-/
import LeanPool.Lean4Itree.ITree.Basic
import LeanPool.Lean4Itree.Paco.PacoDefs
import LeanPool.Lean4Itree.Paco.PacoTactics

/-!
# Monad structure on interaction trees

This module equips `ITree` with its functor and monad operations (`map`, `bind`,
`iter`) and proves the lawful functor and monad instances, including
`bind_assoc`, using the parameterized-coinduction (Paco) tactics.
-/

namespace Lean4Itree

namespace ITree

/- Functor Instance -/
/-- Map the function `f` over the returned values of the interaction tree `t`. -/
def map (f : α → β) (t : ITree ε α) : ITree ε β :=
  .corec' (fun rec t =>
    match t.dest with
    | ⟨.ret v, _⟩ =>
      .inl <| ret <| f v
    | ⟨.tau, c⟩ =>
      .inr <| tau' <| rec <| c 0
    | ⟨.vis _ e, k⟩ =>
      .inr <| vis' e (rec ∘ k)
  ) t

instance : Functor (ITree ε) where
  map := map

/- Basic map lemmas -/
theorem map_ret {ε : Type u1 → Type v1} : map (ε := ε) f (ret v) = ret (f v) := by
  conv => lhs; simp only [map]; rw [PFunctor.M.unfold_corec']
  proveUnfoldLemma

theorem map_tau {ε : Type u1 → Type v1} {c : ITree ε ρ} : map f (tau c) = tau (map f c) := by
  conv => lhs; simp only [map]; rw [PFunctor.M.unfold_corec']
  proveUnfoldLemma

theorem map_vis {ε : Type u1 → Type v1} {α : Type u1} {e : ε α} {k : α → ITree ε ρ} {f : ρ → σ}
  : map f (vis e k) = vis e (fun x => map f <| k x) := by
  conv => lhs; simp only [map]; rw [PFunctor.M.unfold_corec']
  proveUnfoldLemma

/- Monad Instance -/
/-- Monadic bind: run `t` and feed each returned value into the continuation `f`. -/
def bind {σ} (t : ITree ε ρ) (f : ρ → ITree ε σ) : ITree ε σ :=
  .corec' (fun rec t =>
    match t.dest with
    | ⟨.ret v, _⟩ =>
      .inl <| f v
    | ⟨.tau, c⟩ =>
      .inr <| tau' <| rec <| c 0
    | ⟨.vis _ e, k⟩ =>
      .inr <| vis' e (rec ∘ k)
  ) t

instance : Monad (ITree ε) where
  pure := ret
  bind := bind

theorem bind_map (f : ITree ε (α → β)) (x : ITree ε α) : (f >>= fun f => map f x) = f <*> x := by
  simp only [Bind.bind, Seq.seq, Functor.map]

/- Bind monad lemmas -/
theorem bind_ret : bind (ret v) f = f v := by
  conv => lhs; simp only [bind]; rw [PFunctor.M.unfold_corec']
  proveUnfoldLemma

theorem bind_tau : bind (tau c) f = tau (bind c f) := by
  conv => lhs; simp only [bind]; rw [PFunctor.M.unfold_corec']
  proveUnfoldLemma

theorem bind_vis : bind (vis e k) f = vis e fun x => bind (k x) f := by
  conv => lhs; simp only [bind]; rw [PFunctor.M.unfold_corec']
  proveUnfoldLemma

/- Functor Laws -/

/--
  `itree_eq t` tries to prove the equivalence of two `ITree`s transformed by `map` and `bind`.

  `t` is the tree to be reverted
-/
macro "itree_eq" t:ident : tactic => `(tactic|(
  rw [← ieq_iff_eq]
  revert $t
  pcofix cih
  intro t
  pfold
  apply dMatchOn t <;> (intros; rename_i h; subst h)
  · repeat rw [map_ret]
    repeat rw [bind_ret]
    constructor
  · repeat rw [map_tau]
    repeat rw [bind_tau]
    constructor; pleft; apply cih
  · repeat rw [map_vis]
    repeat rw [bind_vis]
    constructor; intros; pleft; apply cih
))

theorem id_map (t : ITree ε ρ) : map id t = t := by itree_eq t

theorem comp_map (g : α → β) (h : β → γ) (t : ITree ε α) : map (h ∘ g) t = map h (map g t) := by
  itree_eq t

instance : LawfulFunctor (ITree ε) where
  map_const := by simp only [Functor.mapConst, Functor.map, implies_true]
  id_map := id_map
  comp_map := comp_map

/- Monad Laws -/

theorem map_const_left : map (Function.const α v) t = bind t fun _ => ret v := by
  itree_eq t

theorem map_const_right : map (Function.const α id v) t = t := by
  rw [Function.const]
  apply id_map

/--
  `itree_eq_map_const x y` tries to prove the equivalence of two `ITree`s
  transformed by `seq` and `map` with `Function.const`.

  `x` and `y` are the trees to be reverted
-/
macro "itree_eq_map_const" x:ident y:ident : tactic => `(tactic|(
  simp only [SeqRight.seqRight, SeqLeft.seqLeft, Seq.seq, Functor.map]
  rw [← ieq_iff_eq]
  revert $x $y
  pcofix cih
  intro x y
  pfold
  apply dMatchOn x <;> (intros; rename_i h; subst h)
  · repeat rw [map_ret]
    repeat rw [bind_ret]
    repeat rw [map_const_left]
    repeat rw [map_const_right]
    apply ieq_rfl
    intros _ _ h
    pright
    pinit at h
    pmon <;> try assumption
    ptop
  · repeat rw [map_tau]
    repeat rw [bind_tau]
    constructor; pleft; apply cih
  · repeat rw [map_vis]
    repeat rw [bind_vis]
    constructor; intros; pleft; apply cih
))

theorem seqLeft_eq (x : ITree ε α) (y : ITree ε β) : x <* y = Function.const β <$> x <*> y := by
  itree_eq_map_const x y

theorem seqRight_eq (x : ITree ε α) (y : ITree ε β) : x *> y = Function.const α id <$> x <*> y := by
  itree_eq_map_const x y

theorem pure_seq (g : α → β) (x : ITree ε α) : pure g <*> x = g <$> x := by
  simp only [Seq.seq, pure, bind_ret]

theorem bind_pure_comp (f : α → β) (x : ITree ε α) : bind x (pure ∘ f) = map f x := by
  itree_eq x

theorem pure_bind (x : α) (f : α → ITree ε β) : bind (pure x) f = f x := by
  simp only [pure, bind_ret]

theorem bind_assoc (x : ITree ε α) (f : α → ITree ε β) (g : β → ITree ε γ)
  : bind (bind x f) g = bind x fun x => bind (f x) g := by
  rw [← ieq_iff_eq]
  revert x f g
  pcofix cih
  intro x f g
  pfold
  apply dMatchOn x <;> (intros; rename_i h; subst h)
  · repeat rw [bind_ret]
    apply ieq_rfl
    intros _ _ h
    pinit at h
    pright
    pmon <;> try assumption
    ptop
  · repeat rw [bind_tau]
    constructor; pleft; apply cih
  · repeat rw [bind_vis]
    constructor; intros; pleft; apply cih

instance : LawfulMonad (ITree ε) where
  seqLeft_eq := seqLeft_eq
  seqRight_eq := seqRight_eq
  pure_seq := pure_seq
  bind_pure_comp := bind_pure_comp
  bind_map := bind_map
  pure_bind := pure_bind
  bind_assoc := bind_assoc

end ITree

end Lean4Itree
