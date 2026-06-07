/-
Copyright (c) 2026 Paul Mure, Joonhyup Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Mure, Joonhyup Lee
-/
import Mathlib.Data.QPF.Univariate.Basic
import Mathlib.Data.Vector3
import LeanPool.Lean4Itree.ITree.Utils

inductive ITree.shape.{u1, v, u2} (ε : Type u1 → Type v) (ρ : Type u2)
  : Type (max (max (u1 + 1) u2) v)
  | ret (v : ρ)
  | tau
  | vis (α : Type u1) (e : ε α)

def ITree.children.{u1, v, u2} {ε : Type u1 → Type v} {ρ : Type u2}
  : ITree.shape ε ρ → Type u1
  | .ret _   => ULift (Fin2 0)
  | .tau     => ULift (Fin2 1)
  | .vis α _ => α

def ITree.P.{u1, v, u2} (ε : Type u1 → Type v) (ρ : Type u2) : PFunctor :=
  ⟨ITree.shape.{u1, v, u2} ε ρ, ITree.children.{u1, v, u2}⟩

/--
Coinductive Interaction Tree defined with `PFunctor.M`.
Equivalent to the following definition:
```
coinductive ITree (ε : Type → Type) (ρ : Type)
| ret (v : ρ)
| tau (t : ITree ε ρ)
| vis {α : Type} (e : ε α) (k : α → ITree ε ρ)
```
-/
def ITree.{u1, v, u2} (ε : Type u1 → Type v) (ρ : Type u2) :=
  (ITree.P ε ρ).M

abbrev KTree.{u1, v, u2} (ε : Type u1 → Type v) (α : Type u1) (β : Type u2) :=
  α → ITree ε β

namespace ITree

instance {ε ρ} : OfNat ((P ε ρ).B shape.tau) 0 := ⟨.up <| .ofNat' 0⟩

section
variable {ε : Type u1 → Type v} {ρ : Type u2}

/- Functor Constructors -/
section
variable {X : Type u}

@[simp]
def ret' (v : ρ) : P ε ρ X :=
  .mk (.ret v) elim0

@[simp]
def tau' (t : X) : P ε ρ X :=
  .mk .tau (fin1Const t)

@[simp]
def vis' {α : Type u1} (e : ε α) (k : α → X) : P ε ρ X :=
  .mk (.vis α e) (k ·)

end

/- Type Constructors -/

@[match_pattern, simp]
def ret (v : ρ) : ITree ε ρ :=
  .mk <| ret' v

@[match_pattern, simp]
def tau (t : ITree ε ρ) : ITree ε ρ :=
  .mk <| tau' t

def tauN (n : Nat) (t : ITree ε ρ) : ITree ε ρ :=
  match n with
  | 0     => t
  | n + 1 => tau (tauN n t)

@[match_pattern, simp]
def vis {α : Type u1} (e : ε α) (k : α → ITree ε ρ) : ITree ε ρ :=
  .mk <| vis' e k

def trigger {α : Type u1} (e : ε α) : ITree ε α :=
  vis e (λ x => ret x)

/- Injectivity of the constructors -/
theorem ret_inj {x y} (h : @ret ε ρ x = ret y) : x = y := by
  simp only [ret, ret'] at h
  have := (Sigma.mk.inj (PFunctor.M.mk_inj h)).left
  exact shape.ret.inj this

theorem vis_inj_α {ε α1 α2 ρ}
  {k1 : KTree ε α1 ρ} {k2 : KTree ε α2 ρ}
  {e1 : ε α1} {e2 : ε α2}
  (h : vis e1 k1 = vis e2 k2) : α1 = α2 := by
  simp only [vis, vis'] at h
  have := (Sigma.mk.inj (PFunctor.M.mk_inj h)).left
  exact (shape.vis.inj this).left

theorem vis_inj {ε α ρ}
  {e1 e2 : ε α} {k1 k2 : KTree ε α ρ}
  (h : vis e1 k1 = vis e2 k2) : e1 = e2 ∧ k1 = k2 := by
  simp only [vis, vis'] at h
  have := Sigma.mk.inj (PFunctor.M.mk_inj h)
  apply And.intro
  · exact eq_of_heq (shape.vis.inj this.left).right
  · have := eq_of_heq this.right
    funext x
    have := congr (a₁ := x) this rfl
    simp only at this
    exact this

theorem tau_inj {ε ρ} {t1 t2 : ITree ε ρ} (h : tau t1 = tau t2) : t1 = t2 := by
  simp only [tau, tau'] at h
  have := eq_of_heq (Sigma.mk.inj (PFunctor.M.mk_inj h)).right
  exact fin1Const_inj this

/-- Custom dependent match function for ITrees -/
def dMatchOn {motive : ITree ε ρ → Sort u} (x : ITree ε ρ)
  (ret : (v : ρ) → x = ret v → motive x)
  (tau : (c : ITree ε ρ) → x = tau c → motive x)
  (vis : (α : Type u1) → (e : ε α) → (k : α → ITree ε ρ) → x = vis e k → motive x)
  : motive x :=
  match hm : x.dest with
  | ⟨.ret v, snd⟩ =>
    ret v (by
      rw [elim0_eq_all snd] at hm
      simp only [ITree.ret, ret']
      rw [←hm]
      simp only [PFunctor.M.mk_dest]
    )
  | ⟨.tau, c⟩ =>
    tau (c 0) (by
      simp only [ITree.tau, tau']
      trans
      symm; apply PFunctor.M.mk_dest
      congr
      rw [hm]
      congr
      symm; apply fin1Const_fin0
    )
  | ⟨.vis α e, k⟩ =>
    vis α e k (by
      simp only [ITree.vis, vis']
      rw [←hm]
      simp only [PFunctor.M.mk_dest]
    )

/- Destructor utilities -/
theorem dest_ret {v} : PFunctor.M.dest (F := P ε ρ) (ret v) = ⟨.ret v, elim0⟩ :=
  rfl

theorem dest_tau {t} : PFunctor.M.dest (F := P ε ρ) (tau t) = ⟨.tau, fin1Const t⟩ :=
  rfl

theorem dest_vis {ε α ρ} {e : ε α} {k : KTree ε α ρ}
  : PFunctor.M.dest (F := P ε ρ) (vis e k) = ⟨.vis _ e, k⟩ :=
  rfl

/-- Infinite Taus -/
def infTau : ITree ε ρ :=
  PFunctor.M.corec' (fun rec x =>
    .inr <| ITree.tau' (rec x)
  ) ()

theorem infTau_eq : @infTau ε ρ = tau infTau := by
  conv =>
    lhs
    simp [infTau]
  rw [PFunctor.M.unfold_corec']
  simp only [tau, tau']
  congr; funext i
  match i with
  | 0 => rfl

inductive State (ε : Type u1 → Type v1) (ρ : Type u2)
| ct     : ITree ε ρ   → State ε ρ
| kt {α} : KTree ε α ρ → State ε ρ

notation:150 "C[ " t " ]" => State.ct t
notation:150 "K[ " t " ]" => State.kt t
notation:151 "K[ " α' " | " t " ]" => State.kt (α := α') t

macro "simp_itree_basic" : tactic => `(tactic|(
  simp only [
    ret', vis', tau',
    ret , vis , tau ,
    PFunctor.M.dest_mk
  ]
))

macro "subst_itree_inj " h:term : tactic => `(tactic|(
  first
  | have hv := ret_inj $h
    subst hv
  | have ht := tau_inj $h
    subst ht
  | have hα := vis_inj_α $h
    subst hα
    have ⟨he, hk⟩ := vis_inj $h
    subst he hk
))

/--
`itree_elim heq` where `heq` is an equality between `ITree`s tries to to prove `False` using `heq`.
-/
macro "itree_elim " h:term : tactic => `(tactic|(
  try (have := (Sigma.mk.inj (PFunctor.M.mk_inj $h)).left; contradiction)
))

/--
`prove_unfold_lemma` tries to finish a proof of an unfolding lemma defined by `corec'`
Note you have to first unfold `corec'` in the appropriate places,
possibly by some combination of `conv` and `rw [PFunctor.M.unfold_corec']`.
-/
macro "prove_unfold_lemma" : tactic => `(tactic|(
  (try simp only [dest_ret, dest_vis, dest_tau]) <;>
  (try simp only [vis, vis', tau, tau']) <;>
  (congr; try funext i) <;>
  solve
  | match i with
    | .up (.ofNat' 0) => rfl
    | .up (.ofNat' 1) => rfl
  | match i with
    | .up (.ofNat' 0) => rfl
))

@[grind]
inductive IEqF (sim : ITree ε ρ → ITree ε ρ → Prop) : ITree ε ρ → ITree ε ρ → Prop
| ret v : IEqF sim (ret v) (ret v)
| vis {α} e k1 k2 (h : ∀ a : α, sim (k1 a) (k2 a)) : IEqF sim (vis e k1) (vis e k2)
| tau t1 t2 (h : sim t1 t2) : IEqF sim (tau t1) (tau t2)

lemma IEqF_inv (sim : ITree ε ρ → ITree ε ρ → Prop) t1 t2 (h : IEqF sim t1 t2) :
  (∃ v, t1 = ret v ∧ t2 = ret v) ∨
  (∃ α, ∃ e : ε α, ∃ k1, ∃ k2, (∀ a : α, sim (k1 a) (k2 a)) ∧ t1 = vis e k1 ∧ t2 = vis e k2) ∨
  (∃ t1', ∃ t2', sim t1' t2' ∧ t1 = tau t1' ∧ t2 = tau t2') := by
  cases h
  · left
    repeat (on_goal 1 => apply Exists.intro)
    exact ⟨rfl, rfl⟩
  · right; left
    repeat (on_goal 1 => apply Exists.intro)
    rename_i h; exact ⟨h, ⟨rfl, rfl⟩⟩
  · right; right
    repeat (on_goal 1 => apply Exists.intro)
    rename_i h; exact ⟨h, ⟨rfl, rfl⟩⟩

theorem IEqF_monotone sim sim' (hsim : ∀ (t1 t2 : ITree ε ρ), sim t1 t2 → sim' t1 t2) :
  ∀ t1 t2, IEqF sim t1 t2 → IEqF sim' t1 t2 := by
  intros t1 t2 h
  cases h <;> constructor <;> intros <;> apply hsim <;> try assumption
  rename_i h _; apply h

/-- Custom equality predicate between ITrees -/
def IEq (t1 t2 : ITree ε ρ) : Prop :=
  IEqF IEq t1 t2
  coinductive_fixpoint monotonicity fun sim' sim hsim =>
    IEqF_monotone sim sim' hsim

theorem ieq_iff_eq (t1 t2 : ITree ε ρ) : IEq t1 t2 ↔ t1 = t2 := by
  constructor
  · intro h
    apply PFunctor.M.bisim (λ t1 t2 => IEq t1 t2) <;> try assumption
    intro t1; apply ITree.dMatchOn (x := t1)
    <;> (
      intros; rename_i h1 t2 heq
      simp only [IEq] at heq
      cases heq <;> itree_elim h1
      subst_itree_inj h1
      simp_itree_basic
      try grind [fin1Const]
    )
    rename_i v
    exists .ret v, elim0, elim0
    simp only [true_and]; intro i; exact elim0 i
  · intro h; subst h
    apply IEq.coinduct Eq _
    · rfl
    · intro t1
      apply t1.dMatchOn <;> grind

@[refl]
theorem ieq_rfl {sim} {hsim : ∀ t1 t2, IEq t1 t2 → sim t1 t2} (t : ITree ε ρ) : IEqF sim t t := by
  apply IEqF_monotone <;> try assumption
  rw [← IEq, ieq_iff_eq]
end

end ITree
