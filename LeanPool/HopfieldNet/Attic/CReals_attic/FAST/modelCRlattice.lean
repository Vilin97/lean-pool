/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

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

-- Require Import CoRN.algebra.RSetoid.
-- Require Import CoRN.metric2.Metric.
-- Require Import CoRN.metric2.UniformContinuity.
-- Require Export CoRN.model.partialorder.CRpartialorder.
-- Require Import CoRN.order.SemiLattice.
-- Require Import CoRN.order.Lattice.

-- (**
-- ** Example of a Lattice: <CR, CRle, CRmin, CRmax>
-- *)

-- Definition CRLattice : Lattice :=
-- makeLattice CRPartialOrder (ucFun2 CRmin) (ucFun2 CRmax)
--  CRmin_lb_l CRmin_lb_r CRmin_glb CRmax_ub_l CRmax_ub_r CRmax_lub.

-- Section CRLattice.

-- Let CRlat := CRLattice.

-- Local Open Scope CR_scope.

-- Definition CRmin_comm : forall x y : CR, CRmin x y == CRmin y x := @meet_comm (sl CRlat).
-- Definition CRmin_assoc : forall x y z : CR, CRmin x (CRmin y z) == CRmin (CRmin x y) z:=
--  @meet_assoc (sl CRlat).
-- Definition CRmin_idem : forall x : CR, CRmin x x == x := @meet_idem (sl CRlat).
-- Definition CRle_min_l : forall x y : CR, x <= y <-> CRmin x y == x := @le_meet_l (sl CRlat).
-- Definition CRle_min_r : forall x y : CR, y <= x <-> CRmin x y == y := @le_meet_r (sl CRlat).
-- Definition CRmin_monotone_r : forall a : CR, CRmonotone (CRmin a) :=
--  @meet_monotone_r (sl CRlat).
-- Definition CRmin_monotone_l : forall a : CR, CRmonotone (fun x => CRmin x a) :=
--  @meet_monotone_l (sl CRlat).
-- Definition CRmin_le_compat :
--  forall w x y z : CR, w <= y -> x <= z -> CRmin w x <= CRmin y z :=
--  @meet_le_compat (sl CRlat).

-- Definition CRmax_comm : forall x y : CR, CRmax x y == CRmax y x := @join_comm CRlat.
-- Definition CRmax_assoc : forall x y z : CR, CRmax x (CRmax y z) == CRmax (CRmax x y) z:=
--  @join_assoc CRlat.
-- Definition CRmax_idem : forall x : CR, CRmax x x == x := @join_idem CRlat.
-- Definition CRle_max_l : forall x y : CR, y <= x <-> CRmax x y == x := @le_join_l CRlat.
-- Definition CRle_max_r : forall x y : CR, x <= y <-> CRmax x y == y := @le_join_r CRlat.
-- Definition CRmax_monotone_r : forall a : CR, CRmonotone (CRmax a) :=
--  @join_monotone_r CRlat.
-- Definition CRmax_monotone_l : forall a : CR, CRmonotone (fun x => CRmax x a) :=
--  @join_monotone_l CRlat.
-- Definition CRmax_le_compat :
--  forall w x y z : CR, w<=y -> x<=z -> CRmax w x <= CRmax y z :=
--  @join_le_compat CRlat.

-- Definition CRmin_max_absorb_l_l : forall x y : CR, CRmin x (CRmax x y) == x :=
--  @meet_join_absorb_l_l CRlat.
-- Definition CRmax_min_absorb_l_l : forall x y : CR, CRmax x (CRmin x y) == x :=
--  @join_meet_absorb_l_l CRlat.
-- Definition CRmin_max_absorb_l_r : forall x y : CR, CRmin x (CRmax y x) == x :=
--  @meet_join_absorb_l_r CRlat.
-- Definition CRmax_min_absorb_l_r : forall x y : CR, CRmax x (CRmin y x) == x :=
--  @join_meet_absorb_l_r CRlat.
-- Definition CRmin_max_absorb_r_l : forall x y : CR, CRmin (CRmax x y) x == x :=
--  @meet_join_absorb_r_l CRlat.
-- Definition CRmax_min_absorb_r_l : forall x y : CR, CRmax (CRmin x y) x == x :=
--  @join_meet_absorb_r_l CRlat.
-- Definition CRmin_max_absorb_r_r : forall x y : CR, CRmin (CRmax y x) x == x :=
--  @meet_join_absorb_r_r CRlat.
-- Definition CRmax_min_absorb_r_r : forall x y : CR, CRmax (CRmin y x) x == x :=
--  @join_meet_absorb_r_r CRlat.

-- Definition CRmin_max_eq : forall x y : CR, CRmin x y == CRmax x y -> x == y :=
--  @meet_join_eq CRlat.

-- (* Distribution is has not been proven yet *)
-- (*
-- Definition CRmax_min_distr_r : forall x y z : CR,
--  CRmax x (CRmin y z) == CRmin (CRmax x y) (CRmax x z) :=
--  @join_meet_distr_r (sl CRlat).
-- Definition CRmax_min_distr_l : forall x y z : CR,
--  CRmax (CRmin y z) x == CRmin (CRmax y x) (CRmax z x) :=
--  @join_meet_distr_l (sl CRlat).
-- Definition CRmin_max_distr_r : forall x y z : CR,
--  CRmin x (CRmax y z) == CRmax (CRmin x y) (CRmin x z) :=
--  @meet_join_distr_r (sl CRlat).
-- Definition CRmin_max_distr_l : forall x y z : CR,
--  CRmin (CRmax y z) x == CRmax (CRmin y x) (CRmin z x) :=
--  @meet_join_distr_l (sl CRlat).

-- (*I don't know who wants modularity laws, but here they are *)
-- Definition CRmax_min_modular_r : forall x y z : CR,
--  CRmax x (CRmin y (CRmax x z)) == CRmin (CRmax x y) (CRmax x z) :=
--  @join_meet_modular_r (sl CRlat).
-- Definition CRmax_min_modular_l : forall x y z : CR,
--  CRmax (CRmin (CRmax x z) y) z == CRmin (CRmax x z) (CRmax y z) :=
--  @join_meet_modular_l (sl CRlat).
-- Definition CRmin_max_modular_r : forall x y z : CR,
--  CRmin x (CRmax y (CRmin x z)) == CRmax (CRmin x y) (CRmin x z) :=
--  @meet_join_modular_r (sl CRlat).
-- Definition CRmin_max_modular_l : forall x y z : CR,
--  CRmin (CRmax (CRmin x z) y) z == CRmax (CRmin x z) (CRmin y z) :=
--  @meet_join_modular_l (sl CRlat).

-- Definition CRmin_max_disassoc : forall x y z : CR, CRmin (CRmax x y) z <= CRmax x (CRmin y z) :=
--  @meet_join_disassoc (sl CRlat).

-- Lemma CRplus_monotone_r : forall a, CRmonotone (CRplus a).
-- Proof.
-- intros x y z H e.
-- simpl.
-- do 2 (unfold Cap_raw; simpl).
-- ring_simplify.
-- rapply Qle_trans;[|apply (H ((1#2)*e)%Qpos)].
-- rewrite Qle_minus_iff.
-- autorewrite with QposElim.
-- ring_simplify.
-- rapply mult_resp_nonneg.
-- discriminate.
-- rapply Qpos_nonneg.
-- Qed.

-- Lemma CRplus_monotone_l : forall a, CRmonotone (fun x => CRplus x a).
-- Proof.
-- intros x y z H e.
-- simpl.
-- do 2 (unfold Cap_raw; simpl).
-- ring_simplify.
-- rapply Qle_trans;[|apply (H ((1#2)*e)%Qpos)].
-- rewrite Qle_minus_iff.
-- autorewrite with QposElim.
-- ring_simplify.
-- rapply mult_resp_nonneg.
-- discriminate.
-- rapply Qpos_nonneg.
-- Qed.

-- Definition CRmin_plus_distr_r : forall x y z : CR, x + CRmin y z == CRmin (x+y) (x+z)  :=
--  fun a => @monotone_meet_distr (sl CRlat) _ (CRplus_monotone_r a).
-- Definition CRmin_plus_distr_l : forall x y z : CR, CRmin y z + x == CRmin (y+x) (z+x) :=
--  fun a => @monotone_meet_distr (sl CRlat) _ (CRplus_monotone_l a).
-- Definition CRmax_plus_distr_r : forall x y z : CR, x + CRmax y z == CRmax (x+y) (x+z)  :=
--  fun a => @monotone_join_distr (sl CRlat) _ (CRplus_monotone_r a).
-- Definition CRmax_plus_distr_l : forall x y z : CR, CRmax y z + x == CRmax (y+x) (z+x) :=
--  fun a => @monotone_join_distr (sl CRlat) _ (CRplus_monotone_l a).
-- Definition CRmin_minus_distr_l : forall x y z : CR, CRmin y z - x == CRmin (y-x) (z-x) :=
--  (fun x => CRmin_plus_distr_l (-x)).
-- Definition CRmax_minus_distr_l : forall x y z : CR, CRmax y z - x == CRmax (y-x) (z-x) :=
--  (fun x => CRmax_plus_distr_l (-x)).

-- Definition CRmin_max_de_morgan : forall x y : CR, -(CRmin x y) == CRmax (-x) (-y) :=
--  @antitone_meet_join_distr (sl CRlat) _ CRopp_le_compat.
-- Definition CRmax_min_de_morgan : forall x y : CR, -(CRmax x y) == CRmin (-x) (-y) :=
--  @antitone_join_meet_distr (sl CRlat) _ CRopp_le_compat.
-- *)

-- End CRLattice.
