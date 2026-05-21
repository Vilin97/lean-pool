/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Mathlib.Analysis.Normed.Field.Lemmas

-- (*
-- Copyright © 2006-2008 Russell O’Connor
-- Copyright © 2020 Vincent Semeria

-- Permission is hereby granted, free of charge, to any person obtaining a copy of
-- this proof and associated documentation files (the "Proof"), to deal in
-- the Proof without restriction, including without limitation the rights to
-- use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
-- the Proof, and to permit persons to whom the Proof is furnished to do so,
-- subject to the following conditions:

-- The above copyright notice and this permission notice shall be included in all
-- copies or substantial portions of the Proof.

-- THE PROOF IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
-- IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
-- FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
-- COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
-- IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
-- CONNECTION WITH THE PROOF OR THE USE OR OTHER DEALINGS IN THE PROOF.
-- *)

-- From Coq Require Export QArith.
-- Require Import CoRN.algebra.RSetoid.
-- Require Import MathClasses.interfaces.canonical_names.
-- Require Import MathClasses.interfaces.abstract_algebra.


-- Local Open Scope Q_scope.

-- Set Implicit Arguments.

-- (**
-- * Metric Space

-- We define a metric space over a setoid X by a ball relation B
-- where B e x y means that the distance between the two points
-- x and y is less than or equal to the rational number e ( d(x,y) <= e ).

-- We do not take the usual definition of a distance function d : X^2 -> R_+,
-- because constructively this function would have to be computable.
-- For example this would prevent us to define metrics on functions
-- d(f,g) := inf_x d(f(x), g(x))
-- where the infinimum does not always exist constructively.
-- By using ball propositions instead, we make the distance function partial,
-- it is not always defined. For topological applications, it is often enough
-- to bound the distance instead of computing it exactly, this is
-- precisely what the balls do.

-- Interestingly, this definition by balls also handles infinite distances,
-- by proving that forall e, not (B e x y). It generalizes the usual distance functions.

-- This definition uses rational numbers instead of real numbers,
-- which is simpler. It allows to define the real numbers as a certain metric
-- space, namely the Cauchy completion of the rational numbers.

-- Lastly, this definition could include one other property of the distance functions
-- e < d -> {B d x y}+{~B e x y}.
-- But those properties are only used late in the proofs, so we move them
-- as additional definitions in module Classification.v (stability and locatedness).
-- *)

-- Record is_MetricSpace {X : Type} (B: Q -> relation X) : Prop :=
-- { msp_refl: forall e, 0 <= e -> Reflexive (B e)
-- ; msp_sym: forall e, Symmetric (B e)
-- ; msp_triangle: forall e1 e2 a b c, B e1 a b -> B e2 b c -> B (e1 + e2) a c
-- ; msp_closed: forall e a b, (forall d, 0 < d -> B (e + d) a b) -> B e a b
-- ; msp_nonneg : forall e a b, B e a b -> 0 <= e
-- ; msp_stable : forall e a b, (~~B e a b) -> B e a b
-- }.

structure IsMetricSpace {X : Type} (B : ℚ → X → X → Prop) : Prop where
  refl : ∀ e, 0 ≤ e → Reflexive (B e)
  symm : ∀ e, Symmetric (B e)
  triangle : ∀ e₁ e₂ a b c, B e₁ a b → B e₂ b c → B (e₁ + e₂) a c
  closed : ∀ e a b, (∀ d, 0 < d → B (e + d) a b) → B e a b
  nonneg : ∀ e a b, B e a b → 0 ≤ e
  stable : ∀ e a b, ¬¬ B e a b → B e a b

structure MetricSpace' where
  carrier : Type
  ball : ℚ → carrier → carrier → Prop
  ball_e_wd : ∀ (e d : ℚ) (x y : carrier), e = d → (ball e x y ↔ ball d x y)
  is_metric : IsMetricSpace ball

-- Record MetricSpace : Type :=
-- { msp_car :> Type
-- ; ball : Q -> msp_car -> msp_car -> Prop
-- ; ball_e_wd : forall (e d : Q) (x y : msp_car),
--     e == d -> (ball e x y <-> ball d x y)
-- ; msp : is_MetricSpace ball
-- }.

-- (* begin hide *)
-- Arguments ball [m].

-- Definition msp_eq {m:MetricSpace} (x y : msp_car m) : Prop
--   := ball 0 x y.

def msp_eq {m : MetricSpace'} (x y : m.carrier) : Prop :=
  m.ball 0 x y

def msp_rel (m : MetricSpace') : m.carrier → m.carrier → Prop :=
  λ x y => msp_eq x y

-- #[global]
-- Instance msp_Equiv (m : MetricSpace) : Equiv m := @msp_eq m.

instance msp_Setoid (m : MetricSpace') : Setoid m.carrier where
  r := msp_eq
  iseqv := ⟨
    by
      intro x
      have := m.is_metric.refl 0 (by linarith)
      exact this x,
    by
      intro x y hxy
      exact (m.is_metric.symm 0) hxy,
    by
      intro x y z hxy hyz
      have tri := m.is_metric.triangle 0 0 x y z hxy hyz
      simp only [zero_add] at tri
      exact tri⟩

-- Add Parametric Morphism {m:MetricSpace} : (@ball m)
--     with signature Qeq ==> (@msp_eq m) ==> (@msp_eq m) ==> iff as ball_wd.
-- Proof.
--   unfold msp_eq. split.
--   - intros.
--     assert (0+(x+0) == y).
--     { rewrite Qplus_0_r, Qplus_0_l. exact H. }
--     apply (ball_e_wd m y0 y1 H3).
--     clear H H3 y.
--     apply (msp_triangle (msp m)) with (b:=x0).
--     apply (msp_sym (msp m)), H0.
--     apply (msp_triangle (msp m)) with (b:=x1).
--     exact H2. exact H1.
--   - intros.
--     assert (0+(y+0) == x).
--     { rewrite Qplus_0_r, Qplus_0_l, H. reflexivity. }
--     apply (ball_e_wd m x0 x1 H3).
--     clear H H3 x.
--     apply (msp_triangle (msp m)) with (b:=y0).
--     exact H0. clear H0 x0.
--     apply (msp_triangle (msp m)) with (b:=y1).
--     exact H2.
--     apply (msp_sym (msp m)), H1.
-- Qed.

theorem ball_wd {m : MetricSpace'} {e d : ℚ} {x y x' y' : m.carrier}
  (heq : e = d) (hx : msp_eq x x') (hy : msp_eq y y') :
  (m.ball e x y ↔ m.ball d x' y') := by
  rw [←heq]
  constructor
  · intro h
    have h₁ := m.is_metric.symm 0 hx
    have h₂ := hy
    have step₁ := m.is_metric.triangle 0 e x' x y h₁ h
    simp only [zero_add] at step₁
    have step₂ := m.is_metric.triangle e 0 x' y y' step₁ h₂
    simp only [add_zero] at step₂
    exact step₂
  · intro h
    have h₁ := hx
    have h₂ := m.is_metric.symm 0 hy
    have step₁ := m.is_metric.triangle 0 e x x' y' h₁ h
    simp only [zero_add] at step₁
    have step₂ := m.is_metric.triangle e 0 x y' y step₁ h₂
    simp only [add_zero] at step₂
    exact step₂

-- Lemma msp_eq_refl : forall {m:MetricSpace} (x : m),
--     msp_eq x x.
-- Proof.
--   intros. apply (msp_refl (msp m) (Qle_refl 0)).
-- Qed.


theorem msp_eq_refl {m : MetricSpace'} (x : m.carrier) : msp_eq x x :=
  m.is_metric.refl 0 (by linarith) x

-- Lemma msp_eq_sym : forall {m:MetricSpace} (x y : m),
--     msp_eq x y -> msp_eq y x.
-- Proof.
--   intros. apply (msp_sym (msp m)), H.
-- Qed.


theorem msp_eq_sym {m : MetricSpace'} {x y : m.carrier} (h : msp_eq x y) : msp_eq y x :=
  m.is_metric.symm 0 h

-- Lemma msp_eq_trans : forall {m:MetricSpace} (x y z : m),
--     msp_eq x y -> msp_eq y z -> msp_eq x z.
-- Proof.
--   unfold msp_eq. intros.
--   rewrite <- (ball_wd m (Qplus_0_r 0)
--                      x x (msp_eq_refl x)
--                      z z (msp_eq_refl z)).
--   exact (msp_triangle (msp m) _ _ _ y _ H H0).
-- Qed.

theorem msp_eq_trans {m : MetricSpace'} {x y z : m.carrier}
  (hxy : msp_eq x y) (hyz : msp_eq y z) : msp_eq x z :=
  by
    -- msp_eq x z = m.ball 0 x z
    -- Use triangle property: m.ball 0 x y → m.ball 0 y z → m.ball (0 + 0) x z
    have tri := m.is_metric.triangle 0 0 x y z hxy hyz
    simp only [zero_add] at tri
    exact tri


-- Add Parametric Relation {m:MetricSpace} : (msp_car m) msp_eq
--     reflexivity proved by (msp_eq_refl)
--     symmetry proved by (msp_eq_sym)
--     transitivity proved by (msp_eq_trans)
--       as msp_eq_rel.
-- (* end hide *)


-- The following instance establishes that `msp_eq` is an equivalence relation on `m.carrier`.
instance msp_eq_setoid (m : MetricSpace') : Setoid m.carrier where
  r := msp_eq
  iseqv := ⟨
    msp_eq_refl,
    msp_eq_sym,
    msp_eq_trans
  ⟩


-- #[global]
-- Instance msp_Setoid (m : MetricSpace) : Setoid m := {}.

-- This instance is already provided above as `msp_eq_setoid`, but for completeness:
instance msp_Setoid' (m : MetricSpace') : Setoid m.carrier := msp_eq_setoid m

-- Definition msp_as_RSetoid : MetricSpace -> RSetoid
--   := fun m => Build_RSetoid (msp_Setoid m).

-- In Lean4, you can define an alias for the setoid structure as follows:
def msp_as_RSetoid (m : MetricSpace') : Setoid m.carrier :=
  msp_Setoid m

section Metric_Space

-- (*
-- ** Ball lemmas
-- *)

variable (X : MetricSpace')

-- (** These lemmas give direct access to the ball axioms of a metric space
-- *)

-- Lemma ball_refl : forall e (a:X), 0 <= e -> ball e a a.
-- Proof.
--  intros. apply (msp_refl (msp X) H).
-- Qed.

theorem ball_refl {e : ℚ} {a : X.carrier} (h : 0 ≤ e) : X.ball e a a :=
  X.is_metric.refl e h a

-- Lemma ball_sym : forall e (a b:X), ball e a b -> ball e b a.
-- Proof.
--  apply (msp_sym (msp X)).
-- Qed.

theorem ball_sym {e : ℚ} {a b : X.carrier} (h : X.ball e a b) : X.ball e b a :=
  X.is_metric.symm e h


-- Lemma ball_triangle : forall e1 e2 (a b c:X),
--     ball e1 a b -> ball e2 b c -> ball (e1 + e2) a c.
-- Proof.
--  apply (msp_triangle (msp X)).
-- Qed.

theorem ball_triangle {e₁ e₂ : ℚ} {a b c : X.carrier}
  (h₁ : X.ball e₁ a b) (h₂ : X.ball e₂ b c) : X.ball (e₁ + e₂) a c :=
  X.is_metric.triangle e₁ e₂ a b c h₁ h₂

-- Lemma ball_closed :  forall e (a b:X),
--     (forall d, 0 < d -> ball (e + d) a b) -> ball e a b.
-- Proof.
--  apply (msp_closed (msp X)).
-- Qed.

theorem ball_closed {e : ℚ} {a b : X.carrier}
  (h : ∀ d, 0 < d → X.ball (e + d) a b) : X.ball e a b :=
  X.is_metric.closed e a b h

-- Lemma ball_eq : forall (a b:X), (forall e, 0 < e -> ball e a b) -> msp_eq a b.
-- Proof.
--   intros. apply ball_closed.
--   intros. rewrite Qplus_0_l.
--   apply H, H0.
-- Qed.

theorem ball_eq'' {a b : X.carrier} (h : ∀ e, 0 < e → X.ball e a b) : msp_eq a b :=
  X.is_metric.closed 0 a b (λ d hd => by
    rw [zero_add]
    exact h d hd)

-- Lemma ball_eq_iff : forall (a b:X),
--     (forall e, 0 < e -> ball e a b) <-> msp_eq a b.
-- Proof.
--  split.
--   apply ball_eq.
--  intros H e epos.
--  rewrite H. apply ball_refl.
--  apply Qlt_le_weak, epos.
-- Qed.

theorem ball_eq_iff {a b : X.carrier} :
  (∀ e, 0 < e → X.ball e a b) ↔ msp_eq a b :=
⟨
  (λ h => X.is_metric.closed 0 a b (λ d hd => by
    rw [zero_add]
    exact h d hd)),
  fun h e epos =>
    by
      have : 0 ≤ e := by linarith
      rw [←zero_add e]
      exact ball_triangle X h (ball_refl X this)
⟩

-- (** The ball constraint on a and b can always be weakened.  Here are
-- two forms of the weakening lemma.
-- *)

-- Lemma ball_weak : forall e d (a b:X),
--     0 <= d -> ball e a b -> ball (e + d) a b.
-- Proof.
--  intros e d a b dpos B1.
--  eapply ball_triangle.
--   apply B1.
--  apply ball_refl. exact dpos.
-- Qed.
theorem ball_weak {e d : ℚ} {a b : X.carrier}
  (dpos : 0 ≤ d) (B1 : X.ball e a b) : X.ball (e + d) a b :=
  ball_triangle X B1 (ball_refl X dpos)

-- Hint Resolve ball_refl ball_triangle ball_weak : metric.

attribute [simp] ball_refl ball_triangle ball_weak

-- Lemma ball_weak_le : forall (e d:Q) (a b:X),
--     e <= d ->  ball e a b -> ball d a b.
-- Proof.
--  intros e d a b Hed B1.
--  setoid_replace d with (e + (d-e)) by ring.
--  apply (ball_triangle _ _ _ b). exact B1.
--  apply ball_refl.
--  unfold Qminus. rewrite <- Qle_minus_iff. exact Hed.
-- Qed.

theorem ball_weak_le {e d : ℚ} {a b : X.carrier}
  (Hed : e ≤ d) (B1 : X.ball e a b) : X.ball d a b :=
by
  have : d = e + (d - e) := by ring
  rw [this]
  apply ball_triangle X B1
  apply ball_refl X
  linarith

-- (* If d(x,y) is infinite and d(x,z) is finite, then d(z,y) is infinite. *)
-- Lemma ball_infinite
--   : forall (x y z : X) (e : Q),
--     (forall d : Q, ~ball d x y)
--     -> ball e x z
--     -> (forall d : Q, ~ball d z y).
-- Proof.
--   intros. intro abs.
--   apply (H (e+d)).
--   exact (ball_triangle e d x z y H0 abs).
-- Qed.

/-- If `d(x, y)` is infinite and `d(x, z)` is finite, then `d(z, y)` is infinite. -/
theorem ball_infinite {x y z : X.carrier} {e : ℚ}
  (H : ∀ d : ℚ, ¬ X.ball d x y)
  (h : X.ball e x z) :
  ∀ d : ℚ, ¬ X.ball d z y :=
fun d abs => H (e + d) (ball_triangle X h abs)

-- Lemma ball_stable : forall e (x y : X),
--     ~~(ball e x y) -> ball e x y.
-- Proof.
--   intros. apply (msp_stable (msp X)), H.
-- Qed.

theorem ball_stable {e : ℚ} {x y : X.carrier} (h : ¬¬ X.ball e x y) : X.ball e x y :=
  X.is_metric.stable e x y h


end Metric_Space

-- (* begin hide *)
attribute [simp] ball_refl ball_sym ball_triangle ball_weak

-- #[global]
-- Hint Resolve ball_refl ball_sym ball_triangle ball_weak : metric.
-- (* end hide *)

attribute [simp] ball_refl ball_sym ball_triangle ball_weak

-- Definition ball_ex (X: MetricSpace) (e: QposInf): X -> X -> Prop :=
--  match e with
--   | Qpos2QposInf e' => ball (proj1_sig e')
--   | QposInfinity => fun a b => True
--  end.

-- inductive QposInf
-- | qpos (e : {q : ℚ // 0 < q}) -- positive rational
-- | infinity

-- open QposInf

-- def ball_ex (X : MetricSpace') (e : QposInf) : X.carrier → X.carrier → Prop :=
--   match e with
--   | qpos e'    => X.ball e'.val
--   | infinity   => fun _ _ => True
