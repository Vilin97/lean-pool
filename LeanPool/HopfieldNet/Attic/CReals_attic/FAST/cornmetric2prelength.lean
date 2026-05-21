/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.Core.CoRNmodeltotalorderQMinMax
import LeanPool.HopfieldNet.CReals.Core.CornQposMinMax
import LeanPool.HopfieldNet.CReals.cornmetric2Complete
import LeanPool.HopfieldNet.CReals.Core.metric2UniformContinuity
-- (*
-- Copyright © 2006-2008 Russell O’Connor

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

-- Require Export CoRN.metric2.Metric.

-- Require Import CoRN.metric2.UniformContinuity.
-- Require Import CoRN.metric2.Complete.
-- Require Import CoRN.model.totalorder.QMinMax.
-- Require Import CoRN.model.totalorder.QposMinMax.

-- Require Import CoRN.stdlib_omissions.List.
-- Require Import CoRN.stdlib_omissions.Q.


-- Set Implicit Arguments.

-- Local Open Scope Q_scope.

-- Section Prelength_Space.
-- (**
-- ** Prelength space

-- In a length metric space, the distances between points can be realized by
-- continuous paths between the points. Loosely speaking they are metric
-- spaces without holes.

-- Because the notion of continuous paths makes most sense in complete metric
-- spaces, here we use a weaker notion of a prelength space. In this case
-- two points are within e of each other if you can get between the two points
-- making arbitarily short hops while covering a distance arbitrarily close to e.
-- *)
-- Variable X:MetricSpace.

-- (** The notion of a prelength space is neatly characterized by the
-- following simple definition. *)
-- Definition PrelengthSpace :=
--   forall (a b:X) (e d1 d2:Qpos),
--     proj1_sig e < proj1_sig (d1+d2)%Qpos
--     -> ball (proj1_sig e) a b ->
--     exists2 c:X, ball (proj1_sig d1) a c & ball (proj1_sig d2) c b.

-- (** There is some evidence that we should be using the classical
-- existential in the above definition.  For now we take the middle road
-- and use the [Prop] based existential.  This show that the exists
-- statement is not used in computations, but still every occurance is
-- constructive. *)

-- Hypothesis prelength : PrelengthSpace.

-- (** This proves that you can construct a trail of points between a and b
-- that is arbitarily close to e and with arbitrarily short hops. *)
-- Lemma trail : forall dl (e : Qpos) (a b:X),
--  ball (proj1_sig e) a b ->
--  proj1_sig e < Qpos_sum dl ->
--  let n := length dl in
--  (exists2 f : nat -> X, f 0 = a /\ f n = b
--                & forall i z, i < n -> ball (proj1_sig (nth i dl z)) (f i) (f (S i)))%nat.
-- Proof.
--  induction dl.
--   intros e a b H H1.
--   simpl in *.
--  - exfalso. destruct e. simpl in H1. apply (Qlt_not_le _ _ H1).
--    apply Qlt_le_weak, q.
--  - rename a into x.
--  intros e a b B pe.
--  simpl in pe.
--  destruct dl.
--   simpl in *.
--   pose (f:= (fun n => match n with O => a | S _ => b end)).
--   exists f; auto.
--   intros [|i] z H;[|exfalso; auto with *].
--   clear z H.
--   ring_simplify in pe.
--   apply ball_weak_le with (proj1_sig e).
--    apply Qlt_le_weak; assumption.
--   assumption.
--  set (Sigma := Qpos_sum (q::dl)).
--  pose (g := ((Qmax 0 (proj1_sig e- proj1_sig x))+Sigma) * (1#2)).
--  assert ((Qmax 0 (proj1_sig e- proj1_sig x))<Sigma).
--  { apply Qmax_case.
--    intros.
--    apply (Qlt_le_trans _ (proj1_sig q)).
--     destruct q; apply q.
--    unfold Sigma.
--    simpl.
--    apply (Qle_trans _ (proj1_sig q+0)).
--    rewrite Qplus_0_r. apply Qle_refl.
--    apply Qplus_le_r.
--    apply Qpos_sum_nonneg.
--   intros.
--   apply (Qplus_lt_l _ _ (proj1_sig x)). ring_simplify.
--   exact pe. }
--  assert (Hg1:=Qsmallest_less_average _ _ H).
--  assert (0<g).
--  refine (Qle_lt_trans _ _ _ _ Hg1).
--    apply Qmax_ub_l.
--  assert (proj1_sig e < proj1_sig x+ g) as H1.
--  { apply (Qplus_lt_l _ _ (-proj1_sig x)).
--    ring_simplify.
--    refine (Qle_lt_trans _ _ _ _ Hg1).
--    apply Qmax_ub_r. }
--  assert (g< Sigma).
--  { apply Qaverage_less_greatest.
--    exact H. }
--   destruct (@prelength a b e x (exist _ _ H0) H1 B) as [c Hc1 Hc2].
--  destruct (IHdl _ _ _ Hc2 H2) as [f' [Hf'1 Hf'2] Hf'3].
--  exists (fun n => match n with O => a | S n' => f' n' end).
--   auto.
--  intros [|i] z Hi.
--   simpl.
--   congruence.
--  apply Hf'3.
--  auto with *.
-- Qed.

-- Variable Y:MetricSpace.

-- (** The major application of prelength spaces is that it allows one to
-- reduce the problem of [ball (e1 + e2) (f a) (f b)] to
-- [ball (mu f e1 + mu f e2) a b] instead of reducing it to
-- [ball (mu f (e1 + e2)) a b].  This new reduction allows one to continue
-- reasoning by making use of the triangle law.

-- Below we show a more general lemma allowing for arbitarily many terms
-- in the sum. *)
-- Lemma mu_sum : forall e0 (es : list Qpos) (f:UniformlyContinuousFunction X Y) a b,
-- ball_ex (fold_right QposInf_plus (mu f e0) (map (mu f) es)) a b ->
-- ball (proj1_sig (fold_right Qpos_plus e0 es)) (f a) (f b).
-- Proof.
--  intros e0 es f a b Hab.
--  apply ball_closed.
--  intros e' epos.
--  setoid_replace (proj1_sig (fold_right Qpos_plus e0 es + exist _ _ epos)%Qpos)
--    with (proj1_sig (fold_right Qpos_plus e0 (exist _ _ epos::es)))
--    by (simpl; ring).
--  set (ds := map (mu f) es) in *.
--  set (d0 := (mu f e0)) in *.
--  set (d' := (mu f (exist _ _ epos))) in *.
--  assert (H:{ds' | (map Qpos2QposInf ds')=d0::d'::ds}+{In QposInfinity (d0::d'::ds)}).
--   generalize (d0::d'::ds); clear.
--   induction l as [|[d|] ds].
--     left.
--     exists (@nil Qpos).
--     reflexivity.
--    destruct IHds as [[ds' Hds']|Hds].
--     left.
--     exists (d::ds').
--     rewrite <- Hds'.
--     reflexivity.
--    firstorder.
--   firstorder.
--  destruct H as [[ds' Hds']|Hds].
--   destruct ds' as [|g0 [|g' gs]]; try discriminate Hds'.
--   inversion Hds'.
--   clear Hds'.
--   unfold d0 in *; clear d0.
--   unfold d' in *; clear d'.
--   unfold ds in *; clear ds.
--   replace (fold_right QposInf_plus (mu f e0) (map (mu f) es))
--     with (Qpos2QposInf (fold_right Qpos_plus g0 gs)) in Hab.
--    simpl in Hab.
--    assert (proj1_sig (fold_right Qpos_plus g0 gs) < Qpos_sum ((g' :: gs)++(g0::nil)))
--      as H.
--    { simpl. apply (Qle_lt_trans _ (Qpos_sum (gs ++ g0::nil))).
--      clear - g0.
--     induction gs.
--      simpl. rewrite Qplus_0_r. apply Qle_refl.
--     simpl. apply Qplus_le_r, IHgs.
--      rewrite -> Qlt_minus_iff.
--      ring_simplify.
--      destruct g'; exact q. }
--    case (trail _ _ _ _ Hab H).
--    clear Hab H.
--    cut (map Qpos2QposInf (g' :: gs) = map (mu f) (exist _ _ epos :: es)).
--     clear H2 H1.
--     generalize (exist _ _ epos::es) (g'::gs) a.
--     clear gs g' es epos e' a.
--     induction l as [|e es]; intros gs a Hes x [Ha Hb] H; destruct gs; try discriminate Hes.
--      simpl in *.
--      apply uc_prf.
--      rewrite <- H0.
--      rewrite <- Hb.
--      rewrite <- Ha.
--      simpl.
--      apply (H 0%nat g0).
--      auto with *.
--     simpl.
--     inversion Hes; clear Hes.
--     eapply ball_triangle.
--      apply uc_prf.
--      rewrite <- H2.
--      rewrite <- Ha.
--      simpl; apply (H 0%nat g0).
--      simpl; auto with *.
--     apply (IHes _ (x 1%nat) H3 (fun i => x (S i))). auto with *.
--     intros.
--     apply (H (S i) z).
--     simpl; auto with *.
--    simpl; congruence.
--   rewrite <- H2.
--   rewrite <- H0.
--   clear - gs.
--   induction gs.
--    reflexivity.
--   simpl.
--   rewrite <- IHgs.
--   reflexivity.
--   assert (H:forall (e:Qpos) es, proj1_sig e < proj1_sig (fold_right Qpos_plus e0 es)%Qpos
--                            -> (mu f e)=QposInfinity
--                            -> ball (m:=Y) (proj1_sig (fold_right Qpos_plus e0 es)) (f a) (f b)).
--   { intros e esx He Hmu.
--   apply ball_weak_le with (proj1_sig e);[apply Qlt_le_weak; assumption|].
--   apply uc_prf.
--   rewrite Hmu.
--   constructor. }
--  case (in_inv Hds).
--   intros Hd0.
--   apply H with e0.
--    clear - es.
--    induction es.
--     simpl.
--     rewrite -> Qlt_minus_iff.
--     ring_simplify.
--     exact epos.
--    simpl.
--    apply (Qlt_le_trans _ _ _ IHes).
--    simpl. apply Qplus_le_r.
--    rewrite <- Qplus_0_l, Qplus_assoc. apply Qplus_le_l.
--    rewrite Qplus_0_r. apply Qpos_nonneg.
--   assumption.
--  clear Hds.
--  change (d'::ds) with (map (mu f) (exist _ _ epos::es)).
--  induction (exist _ _ epos::es); intros Hds.
--   elim Hds.
--  simpl in Hds.
--  destruct Hds as [Ha0|Hds].
--   apply H with a0.
--    simpl.
--    rewrite -> Qlt_minus_iff.
--    ring_simplify.
--    destruct (fold_right Qpos_plus e0 l); exact q.
--   assumption.
--  simpl.
--  eapply ball_weak_le with (proj1_sig (fold_right Qpos_plus e0 l)).
--  simpl.
--   rewrite -> Qle_minus_iff; ring_simplify.
--   auto with *.
--  auto.
-- Qed.

-- End Prelength_Space.

-- Section Map.

-- Local Open Scope uc_scope.
-- Variable X Y : MetricSpace.
-- Hypothesis plX : PrelengthSpace X.
-- Variable f : X --> Y.

-- (**
-- *** A more effictient [Cmap] and [Cbind]
-- The main application of prelength spaces is to allow one to use a
-- more natural and more efficent map function for complete metric spaces.
-- Since this map function is more widely used in practice, it gets the
-- name [Cmap] while the original map function is stuck with the name
-- [Cmap_slow] as a reminder to try to use the function defined here if
-- possible. *)

-- Definition Cmap_raw (x:Complete X) (e:QposInf) :=
-- f (approximate x (QposInf_bind (mu f) e)).

-- Lemma Cmap_fun_prf (x:Complete X)
--   : is_RegularFunction (@ball Y) (fun e => f (approximate x (QposInf_bind (mu f) e))).
-- Proof.
--  intros e1 e2.
--  simpl.
--  apply (@mu_sum X plX Y e2 (e1::nil)).
--  simpl.
--  destruct (mu f e1) as [d1|].
--   destruct (mu f e2) as [d2|].
--    apply (@regFun_prf _ (@ball X)).
--   constructor.
--  constructor.
-- Qed.

-- Definition Cmap_fun (x:Complete X) : Complete Y :=
-- Build_RegularFunction (Cmap_fun_prf x).

-- Lemma Cmap_prf : is_UniformlyContinuousFunction Cmap_fun (mu f).
-- Proof.
--  intros e0 x y Hxy e1 e2.
--  simpl.
--  rewrite <- Qplus_assoc.
--  apply (@mu_sum X plX Y e2 (e1::e0::nil)).
--  simpl.
--  destruct (mu f e1) as [d1|];[|constructor].
--  destruct (mu f e0) as [d0|];[|constructor].
--  destruct (mu f e2) as [d2|];[|constructor].
--  simpl in *.
--  rewrite Qplus_assoc.
--  apply Hxy.
-- Qed.

-- Definition Cmap : (Complete X) --> (Complete Y) :=
-- Build_UniformlyContinuousFunction Cmap_prf.

-- (** [Cmap] is equivalent to the original [Cmap_slow] *)
-- Lemma Cmap_correct : msp_eq Cmap (Cmap_slow f).
-- Proof.
--   apply ucEq_equiv.
--  intros x e1 e2.
--  simpl.
--  unfold Cmap_slow_raw.
--  rewrite Qplus_0_r.
--  apply (@mu_sum X plX Y e2 (e1::nil)).
--  simpl.
--  destruct (mu f e1) as [d1|]; try constructor.
--  destruct (mu f e2) as [d2|]; try constructor.
--  simpl.
--  eapply ball_weak_le;[|apply regFun_prf].
--  simpl. apply Qplus_le_r.
--  rewrite <- (Qmult_1_l (proj1_sig d2)), Qmult_assoc.
--  apply Qmult_le_r. apply Qpos_ispos. discriminate.
-- Qed.

-- Lemma Cmap_fun_correct : forall x, msp_eq (Cmap_fun x) (Cmap_slow_fun f x).
-- Proof.
--  apply Cmap_correct.
-- Qed.

-- End Map.

-- Section fast_Monad_Laws.
-- Local Open Scope uc_scope.

-- Variable X Y Z : MetricSpace.
-- Hypothesis plX : PrelengthSpace X.
-- Hypothesis plY : PrelengthSpace Y.

-- Notation "a =m b" := (msp_eq a b)  (at level 70, no associativity).

-- Lemma fast_MonadLaw1 a : Cmap plX (uc_id X) a =m a.
-- Proof.
--   destruct (Cmap_correct plX (uc_id X)).
--   rewrite H0. apply MonadLaw1.
-- Qed.

-- Lemma fast_MonadLaw2 (f:Y --> Z) (g:X --> Y) a
--   : Cmap plX (uc_compose f g) a =m (Cmap plY f (Cmap plX g a)).
-- Proof.
--   destruct (Cmap_correct plX (f ∘ g)).
--   rewrite H0. clear H0 H.
--   destruct (Cmap_correct plY f).
--   rewrite H0. clear H0 H.
--   destruct (Cmap_correct plX g).
--   rewrite H0. clear H0 H.
--   apply MonadLaw2.
-- Qed.

-- Lemma fast_MonadLaw3 (f:X --> Y) a : Cmap plX f (Cunit a) =m Cunit (f a).
-- Proof.
--   destruct (Cmap_correct plX f).
--   rewrite H0. clear H0 H.
--   apply MonadLaw3.
-- Qed.

-- (* State them all in such a shape some day... *)

-- End fast_Monad_Laws.

-- Local Open Scope uc_scope.

-- (** [Cmap] preserves extensional equality *)

-- Lemma map_eq_complete {X Y : MetricSpace} {plX : PrelengthSpace X} (f g : X --> Y) :
--   (forall x : X, msp_eq (f x) (g x))
--   -> (forall x : Complete X, msp_eq (Cmap plX f x) (Cmap plX g x)).
-- Proof.
--   intros A x. apply lift_eq_complete. intro y.
--   rewrite fast_MonadLaw3, fast_MonadLaw3, A. reflexivity.
-- Qed.

-- (** Similarly we define a new Cbind *)
-- Definition Cbind X Y plX (f:X-->Complete Y) := uc_compose Cjoin (Cmap plX f).

-- Lemma Cbind_correct : forall X Y plX (f:X-->Complete Y), msp_eq (Cbind plX f) (Cbind_slow f).
-- Proof.
--  unfold Cbind, Cbind_slow.
--  intros X Y plX f.
--  rewrite -> (Cmap_correct).
--  reflexivity.
-- Qed.

-- Lemma Cbind_fun_correct : forall X Y plX (f:X-->Complete Y) x,
--     msp_eq (Cbind plX f x) (Cbind_slow f x).
-- Proof.
--  apply Cbind_correct.
-- Qed.

-- (** Similarly we define a new Cmap_strong *)
-- Lemma Cmap_strong_prf : forall (X Y:MetricSpace) (plX:PrelengthSpace X),
--  is_UniformlyContinuousFunction (@Cmap X Y plX) Qpos2QposInf.
-- Proof.
--  intros X Y plX e a b Hab.
--  apply (ball_wd _ eq_refl _ _ (Cmap_correct _ _) _ _ (Cmap_correct _ _)).
--  apply Cmap_strong_slow_prf.
--  auto.
-- Qed.

-- Definition Cmap_strong X Y plX : (X --> Y) --> (Complete X --> Complete Y) :=
-- Build_UniformlyContinuousFunction (@Cmap_strong_prf X Y plX).

-- Lemma Cmap_strong_correct : forall X Y plX,
--     msp_eq (@Cmap_strong X Y plX) (@Cmap_strong_slow X Y).
-- Proof.
--   intros X Y plX.
--   split. apply Qle_refl.
--   intro f.
--   destruct (Cmap_correct plX f) as [_ H0].
--   split. apply Qle_refl.
--   intro x. apply H0.
-- Qed.

-- (** Similarly we define a new Cap *)
-- Definition Cap_raw X Y plX (f:Complete (X --> Y)) (x:Complete X) (e:QposInf) :=
--   approximate (Cmap plX (approximate f (Qpos2QposInf (exist (Qlt 0) (1#2) eq_refl)*e)%QposInf) x)
--               (Qpos2QposInf (exist (Qlt 0) (1#2) eq_refl)*e)%QposInf.

-- Lemma Cap_fun_prf X Y plX (f:Complete (X --> Y)) (x:Complete X)
--   : is_RegularFunction (@ball Y) (Cap_raw plX f x).
-- Proof.
--  intros e1 e2.
--  pose (exist (Qlt 0) (1#2) eq_refl) as half.
--  unfold Cap_raw.
--  unfold Cap_raw.
--  unfold QposInf_mult, QposInf_bind.
--  set (he1 := (half * e1)%Qpos).
--  set (he2 := (half * e2)%Qpos).
--  set (f1 := (approximate f he1)).
--  set (f2 := (approximate f he2)).
--  change (Cmap (Y:=Y) plX f1) with (Cmap_strong Y plX f1).
--  change (Cmap (Y:=Y) plX f2) with (Cmap_strong Y plX f2).
--  set (y1 :=(Cmap_strong Y plX f1 x)).
--  set (y2 :=(Cmap_strong Y plX f2 x)).
--  setoid_replace (proj1_sig e1 + proj1_sig e2)
--    with (proj1_sig (he1 + (he1 + he2) + he2))%Qpos
--    by (simpl; ring).
--  rewrite <- ball_Cunit.
--  apply ball_triangle with y2;[|apply ball_approx_r].
--  apply ball_triangle with y1;[apply ball_approx_l|].
--  apply (uc_prf (Cmap_strong Y plX)).
--  apply (@regFun_prf _ (@ball (X-->Y))).
-- Qed.

-- Definition Cap_fun X Y plX (f:Complete (X --> Y)) (x:Complete X) : Complete Y :=
-- Build_RegularFunction (Cap_fun_prf plX f x).

-- Lemma Cap_fun_correct : forall X Y plX (f:Complete (X --> Y)) x,
--     msp_eq (Cap_fun plX f x) (Cap_slow_fun f x).
-- Proof.
--  intros X Y plX f x e1 e2.
--  pose (exist (Qlt 0) (1#2) eq_refl) as half.
--  simpl.
--  unfold Cap_raw, Cap_slow_raw.
--  set (e1':=(half * e1)%Qpos).
--  set (e2':=(half * e2)%Qpos).
--  rewrite Qplus_0_r.
--  change (ball (proj1_sig e1 + proj1_sig e2) (approximate (Cmap plX (approximate f (half * e1)%Qpos) x) e1')
--    (approximate (Cmap_slow (approximate f (half * e2)%Qpos) x) e2')).
--  setoid_replace (proj1_sig e1 + proj1_sig e2)
--    with (proj1_sig (e1' + ((half * e1)%Qpos + (half * e2)%Qpos) + e2'))%Qpos
--    by (unfold e1', e2'; simpl; ring).
--  generalize x e1' e2'.
--  assert (ball (proj1_sig (half * e1 + half * e2)%Qpos)
--               (Cmap plX (approximate f (half * e1)%Qpos))
--               (Cmap_slow (approximate f (half * e2)%Qpos))).
--  { assert (QposEq (half * e1 + half * e2) (half * e1 + half * e2)) by reflexivity.
--    apply (ball_wd _ H _ _ (Cmap_correct _ _) _ _ (reflexivity _)).
--    set (f1:=(approximate f (half * e1)%Qpos)).
--    set (f2:=(approximate f (half * e2)%Qpos)).
--    apply Cmap_strong_slow_prf.
--    apply (@regFun_prf _ (@ball (X-->Y))). }
--  apply H.
-- Qed.

-- Definition Cap_modulus X Y (f:Complete (X --> Y)) (e:Qpos) : QposInf
--   := mu (approximate f ((1#3)*e)%Qpos) ((1#3)*e).

-- Lemma Cap_weak_prf X Y plX (f:Complete (X --> Y)) : is_UniformlyContinuousFunction (Cap_fun plX f) (Cap_modulus f).
-- Proof.
--  intros e x y H.
--  set (e' := ((1#3)*e)%Qpos).
--  setoid_replace (proj1_sig e)
--    with (proj1_sig (e'+e'+e')%Qpos) by (simpl; ring).
--  apply ball_triangle with (Cmap plX (approximate f e') y).
--   apply ball_triangle with (Cmap plX (approximate f e') x).
--  - apply (ball_wd _ eq_refl _ _ (Cap_fun_correct plX f x) _ _ (reflexivity _)).
--    simpl (Cmap plX (approximate f e') x).
--    apply (ball_wd _ eq_refl _ _ (reflexivity _) _ _ (Cmap_fun_correct _ _ _)).
--    apply Cap_slow_help.
--  - apply (uc_prf). apply H.
--  - apply ball_sym.
--    apply (ball_wd _ eq_refl _ _ (Cap_fun_correct plX f y) _ _ (reflexivity _)).
--    simpl (Cmap plX (approximate f e') y).
--    apply (ball_wd _ eq_refl _ _ (reflexivity _) _ _ (Cmap_fun_correct _ _ _)).
--    apply Cap_slow_help.
-- Qed.

-- Definition Cap_weak X Y plX (f:Complete (X --> Y)) : Complete X --> Complete Y :=
-- Build_UniformlyContinuousFunction (Cap_weak_prf plX f).

-- Lemma Cap_weak_correct : forall X Y plX (f:Complete (X --> Y)),
--     msp_eq (Cap_weak plX f) (Cap_weak_slow f).
-- Proof.
--   intros. split. apply Qle_refl.
--   apply (Cap_fun_correct plX f).
-- Qed.

-- Lemma Cap_prf X Y plX : is_UniformlyContinuousFunction (@Cap_weak X Y plX) Qpos2QposInf.
-- Proof.
--  intros e a b Hab.
--  apply (ball_wd _ eq_refl _ _ (Cap_weak_correct plX a) _ _ (Cap_weak_correct plX b)).
--  apply Cap_slow_prf.
--  assumption.
-- Qed.

-- Definition Cap X Y plX : Complete (X --> Y) --> Complete X --> Complete Y :=
-- Build_UniformlyContinuousFunction (Cap_prf plX).

-- Lemma Cap_correct : forall X Y plX, msp_eq (Cap Y plX) (Cap_slow X Y).
-- Proof.
--   intros. split. apply Qle_refl.
--   intro f. split. apply Qle_refl.
--   apply (Cap_fun_correct plX f).
-- Qed.

-- (* begin hide *)
-- Add Parametric Morphism X Y plX : (@Cmap_fun X Y plX)
--     with signature (@msp_eq _) ==> (@msp_eq (Complete X)) ==> (@msp_eq (Complete Y))
--       as Cmap_wd.
-- Proof.
--  intros x1 x2 Hx y1 y2 Hy.
--  rewrite -> Cmap_fun_correct.
--  set (a:=(Cmap_slow_fun x1 y1)).
--  rewrite -> Cmap_fun_correct.
--  apply Cmap_slow_wd; auto.
-- Qed.

-- Lemma Cmap_wd_loc
--   : forall (X Y : MetricSpace) (plX : PrelengthSpace X)
--       (f g : X --> Y) (x : Complete X) (e : Qpos),
--     (forall a : X, ball (proj1_sig e) (Cunit a) x -> msp_eq (f a) (g a)) ->
--     msp_eq (Cmap_fun plX f x) (Cmap_fun plX g x).
-- Proof.
--   intros. rewrite Cmap_fun_correct.
--   rewrite Cmap_fun_correct.
--   apply Cmap_slow_wd_loc with (e:=e). exact H.
-- Qed.

-- Add Parametric Morphism X Y H : (@Cap_weak X Y H)
--     with signature (@msp_eq _) ==> (@msp_eq _) as Cap_weak_wd.
-- Proof.
--  intros x1 x2 Hx.
--  apply (@uc_wd _ _ (Cap Y H));assumption.
-- Qed.

-- Add Parametric Morphism X Y H : (@Cap_fun X Y H)
--     with signature (@msp_eq _) ==> (@msp_eq _) ==> (@msp_eq _) as Cap_wd.
-- Proof.
--  intros x1 x2 Hx y1 y2 Hy.
--  transitivity (Cap_fun H x1 y2).
--   apply (@uc_wd _ _ (Cap_weak H x1) _ _ Hy).
--  generalize y2.
--  apply (@uc_wd _ _ (Cap Y H));assumption.
-- Qed.
-- (* end hide *)

-- (** Similarly we define a new [Cmap2]. *)
-- Definition Cmap2 (X Y Z:MetricSpace)
--            (Xpl : PrelengthSpace X) (Ypl : PrelengthSpace Y)
--            (f : X --> Y --> Z) : Complete X --> Complete Y --> Complete Z
--   := uc_compose (@Cap Y Z Ypl) (Cmap Xpl f).

-- (** Completion of a metric space preserves the prelength property.
-- In fact the completion of a prelenght space is a length space, but
-- we have not formalized the notion of a length space yet. *)
-- Lemma CompletePL : forall X, PrelengthSpace X -> PrelengthSpace (Complete X).
-- Proof.
--  intros X Xpl x y e d1 d2 He Hxy.
--  destruct (Qpos_sub _ _ He) as [x0 q].
--  pose (exist (Qlt 0) (4#1) eq_refl) as four.
--  pose (exist (Qlt 0) (1#5) eq_refl) as fifth.
--  pose (gA := (fifth*x0)%Qpos).
--  pose (g := Qpos_min (Qpos_min ((1#2)*d1) ((1#2)*d2)) gA).
--  unfold PrelengthSpace in Xpl.
--  assert (Hd1: proj1_sig g < proj1_sig d1).
--  { unfold g.
--   eapply Qle_lt_trans.
--    apply Qpos_min_lb_l.
--   eapply Qle_lt_trans.
--    apply Qpos_min_lb_l.
--    simpl. rewrite <- (Qmult_1_l (proj1_sig d1)).
--    rewrite Qmult_assoc. apply Qmult_lt_r.
--    apply Qpos_ispos. reflexivity. }
--  assert (Hd2: proj1_sig g < proj1_sig d2).
--  { unfold g.
--   eapply Qle_lt_trans.
--    apply Qpos_min_lb_l.
--   eapply Qle_lt_trans.
--    apply Qpos_min_lb_r.
--    simpl. rewrite <- (Qmult_1_l (proj1_sig d2)).
--    rewrite Qmult_assoc. apply Qmult_lt_r.
--    apply Qpos_ispos. reflexivity. }
--  destruct (Qpos_sub _ _ Hd1) as [d1' Hd1'].
--  destruct (Qpos_sub _ _ Hd2) as [d2' Hd2'].
--  assert (He': proj1_sig (g + e + g)%Qpos < proj1_sig (d1' + d2')%Qpos).
--  { simpl.
--    apply (Qplus_lt_l _ _ (proj1_sig g+ proj1_sig g)).
--   setoid_replace (proj1_sig d1' + proj1_sig d2' + (proj1_sig g + proj1_sig g))
--     with (proj1_sig ((g+d1')%Qpos) + proj1_sig (g+d2')%Qpos)
--     by (simpl; ring).
--   unfold QposEq in *.
--   rewrite <- Hd1'.
--   rewrite <- Hd2'.
--   clear d1' Hd1' d2' Hd2'.
--   apply Qle_lt_trans with (proj1_sig (e + four*gA)%Qpos).
--   apply (Qle_trans _ (proj1_sig e+(4#1)*proj1_sig g)).
--   ring_simplify. apply Qle_refl. apply Qplus_le_r.
--   apply Qmult_le_l. reflexivity.
--     apply Qpos_min_lb_r.
--   rewrite -> q. apply Qplus_lt_r. simpl.
--   rewrite Qmult_assoc, <- (Qmult_1_l (proj1_sig x0)), Qmult_assoc.
--   apply Qmult_lt_r. destruct x0; exact q0.
--   reflexivity. }
--  destruct (Xpl _ _ _ _ _ He' (Hxy g g)) as [c Hc1 Hc2].
--  exists (Cunit c).
--  rewrite Hd1'.
--   eapply ball_triangle.
--    apply ball_approx_r.
--   rewrite -> ball_Cunit.
--   assumption.
--   rewrite Hd2'.
--   rewrite Qplus_comm.
--  eapply ball_triangle with (Cunit (approximate y g)).
--   rewrite -> ball_Cunit.
--   assumption.
--  apply ball_approx_l.
-- Qed.
