/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.TableCheck
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

/-! ### The entries of Table 1 as numerals -/

public section

open Finset

namespace Zeta5Irrational

lemma aρ_1 : aρ 1 = (1953374043 / 500000000000 : ℝ) := by norm_num [aρ, table1]

lemma bρ_1 : bρ 1 = (8992695531 / 1000000000000 : ℝ) := by norm_num [bρ, table1]

lemma cρ_1 : cρ 1 = (525779809 / 50000000000 : ℝ) := by norm_num [cρ, table1]

lemma aρ_2 : aρ 2 = (289031033 / 125000000000 : ℝ) := by norm_num [aρ, table1]

lemma bρ_2 : bρ 2 = (3068199571 / 200000000000 : ℝ) := by norm_num [bρ, table1]

lemma cρ_2 : cρ 2 = (29471737793 / 1000000000000 : ℝ) := by norm_num [cρ, table1]

lemma aρ_3 : aρ 3 = (280457333 / 200000000000 : ℝ) := by norm_num [aρ, table1]

lemma bρ_3 : bρ 3 = (6432545181 / 250000000000 : ℝ) := by norm_num [bρ, table1]

lemma cρ_3 : cρ 3 = (42934365099 / 1000000000000 : ℝ) := by norm_num [cρ, table1]

lemma aρ_4 : aρ 4 = (220431339 / 250000000000 : ℝ) := by norm_num [aρ, table1]

lemma bρ_4 : bρ 4 = (20954789123 / 500000000000 : ℝ) := by norm_num [bρ, table1]

lemma cρ_4 : cρ 4 = (29102115983 / 500000000000 : ℝ) := by norm_num [cρ, table1]

lemma aρ_5 : aρ 5 = (289098953 / 500000000000 : ℝ) := by norm_num [aρ, table1]

lemma bρ_5 : bρ 5 = (65851089563 / 1000000000000 : ℝ) := by norm_num [bρ, table1]

lemma cρ_5 : cρ 5 = (6903762131 / 100000000000 : ℝ) := by norm_num [cρ, table1]

lemma aρ_6 : aρ 6 = (396324613 / 1000000000000 : ℝ) := by norm_num [aρ, table1]

lemma bρ_6 : bρ 6 = (24870259471 / 250000000000 : ℝ) := by norm_num [bρ, table1]

lemma cρ_6 : cρ 6 = (78873099189 / 1000000000000 : ℝ) := by norm_num [cρ, table1]

lemma aρ_7 : aρ 7 = (283911191 / 1000000000000 : ℝ) := by norm_num [aρ, table1]

lemma bρ_7 : bρ 7 = (72162863729 / 500000000000 : ℝ) := by norm_num [bρ, table1]

lemma cρ_7 : cρ 7 = (84856120711 / 1000000000000 : ℝ) := by norm_num [cρ, table1]

lemma aρ_8 : aρ 8 = (53051547 / 250000000000 : ℝ) := by norm_num [aρ, table1]

lemma bρ_8 : bρ 8 = (201105762729 / 1000000000000 : ℝ) := by norm_num [bρ, table1]

lemma cρ_8 : cρ 8 = (88396082127 / 1000000000000 : ℝ) := by norm_num [cρ, table1]

lemma aρ_9 : aρ 9 = (82548843 / 500000000000 : ℝ) := by norm_num [aρ, table1]

lemma bρ_9 : bρ 9 = (269345996903 / 1000000000000 : ℝ) := by norm_num [bρ, table1]

lemma cρ_9 : cρ 9 = (706427057 / 8000000000 : ℝ) := by norm_num [cρ, table1]

lemma aρ_10 : aρ 10 = (33336783 / 250000000000 : ℝ) := by norm_num [aρ, table1]

lemma bρ_10 : bρ 10 = (86772388539 / 250000000000 : ℝ) := by norm_num [bρ, table1]

lemma cρ_10 : cρ 10 = (17094464251 / 200000000000 : ℝ) := by norm_num [cρ, table1]

lemma aρ_11 : aρ 11 = (55761057 / 500000000000 : ℝ) := by norm_num [aρ, table1]

lemma bρ_11 : bρ 11 = (86161340883 / 200000000000 : ℝ) := by norm_num [bρ, table1]

lemma cρ_11 : cρ 11 = (39449592119 / 500000000000 : ℝ) := by norm_num [cρ, table1]

lemma aρ_12 : aρ 12 = (19269871 / 200000000000 : ℝ) := by norm_num [aρ, table1]

lemma bρ_12 : bρ 12 = (515561896511 / 1000000000000 : ℝ) := by norm_num [bρ, table1]

lemma cρ_12 : cρ 12 = (35176735959 / 500000000000 : ℝ) := by norm_num [cρ, table1]

lemma aρ_13 : aρ 13 = (85815639 / 1000000000000 : ℝ) := by norm_num [aρ, table1]

lemma bρ_13 : bρ 13 = (297724389273 / 500000000000 : ℝ) := by norm_num [bρ, table1]

lemma cρ_13 : cρ 13 = (11767795323 / 200000000000 : ℝ) := by norm_num [cρ, table1]

lemma aρ_14 : aρ 14 = (78667711 / 1000000000000 : ℝ) := by norm_num [aρ, table1]

lemma bρ_14 : bρ 14 = (664241383483 / 1000000000000 : ℝ) := by norm_num [bρ, table1]

lemma cρ_14 : cρ 14 = (22210660553 / 500000000000 : ℝ) := by norm_num [cρ, table1]

lemma aρ_15 : aρ 15 = (14825913 / 200000000000 : ℝ) := by norm_num [aρ, table1]

lemma bρ_15 : bρ 15 = (89520072139 / 125000000000 : ℝ) := by norm_num [bρ, table1]

lemma cρ_15 : cρ 15 = (30462865791 / 1000000000000 : ℝ) := by norm_num [cρ, table1]

lemma aρ_16 : aρ 16 = (7174131 / 100000000000 : ℝ) := by norm_num [aρ, table1]

lemma bρ_16 : bρ 16 = (746637295669 / 1000000000000 : ℝ) := by norm_num [bρ, table1]

lemma cρ_16 : cρ 16 = (5959622577 / 1000000000000 : ℝ) := by norm_num [cρ, table1]

/-! ### Upper bounds for the constant values `log ((b_j - a_j)/4)` -/

lemma Lmid_1 :
    Real.log ((bρ 1 - aρ 1) / 4) ≤ (-(66675683038238292067283 / 10000000000000000000000 : ℝ)) := by
  rw [aρ_1, bρ_1,
    show
      ((8992695531 / 1000000000000 : ℝ) - (1953374043 / 500000000000 : ℝ)) / 4 =
        (1017189489 / 800000000000 : ℝ)
      by norm_num]
  have h :
    Real.log (1017189489 / 800000000000 : ℝ) ≤
      (-(66675683038238292067283 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 10
        (show (1017189489 / 800000000000 : ℝ) = (1017189489 / 781250000 : ℝ) / 2 ^ 10 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1017189489 / 781250000 : ℝ) ≤
            (2639034991761707932717 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact h

lemma Lmid_2 :
    Real.log ((bρ 2 - aρ 2) / 4) ≤ (-(57268912150832389796717 / 10000000000000000000000 : ℝ)) := by
  rw [aρ_2, bρ_2,
    show
      ((3068199571 / 200000000000 : ℝ) - (289031033 / 125000000000 : ℝ)) / 4 =
        (13028749591 / 4000000000000 : ℝ)
      by norm_num]
  have h :
    Real.log (13028749591 / 4000000000000 : ℝ) ≤
      (-(57268912150832389796717 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 9
        (show (13028749591 / 4000000000000 : ℝ) = (13028749591 / 7812500000 : ℝ) / 2 ^ 9 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (13028749591 / 7812500000 : ℝ) ≤
            (5114334076167610203283 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact h

lemma Lmid_3 :
    Real.log ((bρ 3 - aρ 3) / 4) ≤ (-(25512130211755314637529 / 5000000000000000000000 : ℝ)) := by
  rw [aρ_3, bρ_3,
    show
      ((6432545181 / 250000000000 : ℝ) - (280457333 / 200000000000 : ℝ)) / 4 =
        (24327894059 / 4000000000000 : ℝ)
      by norm_num]
  have h :
    Real.log (24327894059 / 4000000000000 : ℝ) ≤
      (-(25512130211755314637529 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (24327894059 / 4000000000000 : ℝ) = (24327894059 / 15625000000 : ℝ) / 2 ^ 8 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (24327894059 / 15625000000 : ℝ) ≤
            (2213757000244685362471 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact h

lemma Lmid_4 :
    Real.log ((bρ 4 - aρ 4) / 4) ≤ (-(11449496158609380585237 / 2500000000000000000000 : ℝ)) := by
  rw [aρ_4, bρ_4,
    show
      ((20954789123 / 500000000000 : ℝ) - (220431339 / 250000000000 : ℝ)) / 4 =
        (4102785289 / 400000000000 : ℝ)
      by norm_num]
  have h :
    Real.log (4102785289 / 400000000000 : ℝ) ≤
      (-(11449496158609380585237 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show (4102785289 / 400000000000 : ℝ) = (4102785289 / 3125000000 : ℝ) / 2 ^ 7 by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4102785289 / 3125000000 : ℝ) ≤
            (680579496640619414763 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact h

lemma Lmid_5 :
    Real.log ((bρ 5 - aρ 5) / 4) ≤ (-(20577364119368339121527 / 5000000000000000000000 : ℝ)) := by
  rw [aρ_5, bρ_5,
    show
      ((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4 =
        (65272891657 / 4000000000000 : ℝ)
      by norm_num]
  have h :
    Real.log (65272891657 / 4000000000000 : ℝ) ≤
      (-(20577364119368339121527 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show (65272891657 / 4000000000000 : ℝ) = (65272891657 / 62500000000 : ℝ) / 2 ^ 6 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (65272891657 / 62500000000 : ℝ) ≤
            (217051289631660878473 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact h

lemma Lmid_6 :
    Real.log ((bρ 6 - aρ 6) / 4) ≤ (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) := by
  rw [aρ_6, bρ_6,
    show
      ((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4 =
        (99084713271 / 4000000000000 : ℝ)
      by norm_num]
  have h :
    Real.log (99084713271 / 4000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show (99084713271 / 4000000000000 : ℝ) = (99084713271 / 62500000000 : ℝ) / 2 ^ 6 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (99084713271 / 62500000000 : ℝ) ≤
            (460808617104656470757 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact h

lemma Lmid_7 :
    Real.log ((bρ 7 - aρ 7) / 4) ≤ (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) := by
  rw [aρ_7, bρ_7,
    show
      ((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4 =
        (144041816267 / 4000000000000 : ℝ)
      by norm_num]
  have h :
    Real.log (144041816267 / 4000000000000 : ℝ) ≤
      (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (144041816267 / 4000000000000 : ℝ) = (144041816267 / 125000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (144041816267 / 125000000000 : ℝ) ≤
            (1417899108615240212659 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact h

lemma Lmid_8 :
    Real.log ((bρ 8 - aρ 8) / 4) ≤ (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) := by
  rw [aρ_8, bρ_8,
    show
      ((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4 =
        (200893556541 / 4000000000000 : ℝ)
      by norm_num]
  have h :
    Real.log (200893556541 / 4000000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show (200893556541 / 4000000000000 : ℝ) = (200893556541 / 125000000000 : ℝ) / 2 ^ 5 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (200893556541 / 125000000000 : ℝ) ≤
            (2372307305187944700339 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact h

lemma Lmid_9 :
    Real.log ((bρ 9 - aρ 9) / 4) ≤ (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) := by
  rw [aρ_9, bρ_9,
    show
      ((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4 =
        (269180899217 / 4000000000000 : ℝ)
      by norm_num]
  have h :
    Real.log (269180899217 / 4000000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (269180899217 / 4000000000000 : ℝ) = (269180899217 / 250000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (269180899217 / 250000000000 : ℝ) ≤
            (739227235165382858631 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact h

lemma Lmid_10 :
    Real.log ((bρ 10 - aρ 10) / 4) ≤ (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) := by
  rw [aρ_10, bρ_10,
    show
      ((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4 =
        (21684762939 / 250000000000 : ℝ)
      by norm_num]
  have h :
    Real.log (21684762939 / 250000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (21684762939 / 250000000000 : ℝ) = (21684762939 / 15625000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (21684762939 / 15625000000 : ℝ) ≤
            (1638688247891813620441 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact h

lemma Lmid_11 :
    Real.log ((bρ 11 - aρ 11) / 4) ≤ (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) := by
  rw [aρ_11, bρ_11,
    show
      ((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4 =
        (430695182301 / 4000000000000 : ℝ)
      by norm_num]
  have h :
    Real.log (430695182301 / 4000000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show (430695182301 / 4000000000000 : ℝ) = (430695182301 / 250000000000 : ℝ) / 2 ^ 4 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (430695182301 / 250000000000 : ℝ) ≤
            (1087879376786883877841 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact h

lemma Lmid_12 :
    Real.log ((bρ 12 - aρ 12) / 4) ≤ (-(640305991230515290559 / 312500000000000000000 : ℝ)) := by
  rw [aρ_12, bρ_12,
    show
      ((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4 =
        (128866386789 / 1000000000000 : ℝ)
      by norm_num]
  have h :
    Real.log (128866386789 / 1000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (128866386789 / 1000000000000 : ℝ) = (128866386789 / 125000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (128866386789 / 125000000000 : ℝ) ≤
            (9519490300734709441 / 312500000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact h

lemma Lmid_13 :
    Real.log ((bρ 13 - aρ 13) / 4) ≤ (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) := by
  rw [aρ_13, bρ_13,
    show
      ((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4 =
        (595362962907 / 4000000000000 : ℝ)
      by norm_num]
  have h :
    Real.log (595362962907 / 4000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (595362962907 / 4000000000000 : ℝ) = (595362962907 / 500000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (595362962907 / 500000000000 : ℝ) ≤
            (436407857070690432561 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact h

lemma Lmid_14 :
    Real.log ((bρ 14 - aρ 14) / 4) ≤ (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) := by
  rw [aρ_14, bρ_14,
    show
      ((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4 =
        (166040678943 / 1000000000000 : ℝ)
      by norm_num]
  have h :
    Real.log (166040678943 / 1000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (166040678943 / 1000000000000 : ℝ) = (166040678943 / 125000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (166040678943 / 125000000000 : ℝ) ≤
            (1419595374534700017209 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact h

lemma Lmid_15 :
    Real.log ((bρ 15 - aρ 15) / 4) ≤ (-(268788866070650094343 / 156250000000000000000 : ℝ)) := by
  rw [aρ_15, bρ_15,
    show
      ((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4 =
        (716086447547 / 4000000000000 : ℝ)
      by norm_num]
  have h :
    Real.log (716086447547 / 4000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (716086447547 / 4000000000000 : ℝ) = (716086447547 / 500000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (716086447547 / 500000000000 : ℝ) ≤
            (56123874694974905657 / 156250000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact h

lemma Lmid_16 :
    Real.log ((bρ 16 - aρ 16) / 4) ≤ (-(419641552645073499393 / 250000000000000000000 : ℝ)) := by
  rw [aρ_16, bρ_16,
    show
      ((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4 =
        (746565554359 / 4000000000000 : ℝ)
      by norm_num]
  have h :
    Real.log (746565554359 / 4000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show (746565554359 / 4000000000000 : ℝ) = (746565554359 / 500000000000 : ℝ) / 2 ^ 3 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (746565554359 / 500000000000 : ℝ) ≤
            (100218832579926500607 / 250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact h

/-- Upper bound for the constant value of `Uρ` on `[a₁, b₁]`. -/
lemma Umid_le : Uρmid ≤ (-(28683108419825598767969 / 10000000000000000000000 : ℝ)) := by
  rw [Uρmid_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12,
    cρ_13, cρ_14, cρ_15, cρ_16]
  have h1 :
    (525779809 / 50000000000 : ℝ) * Real.log ((bρ 1 - aρ 1) / 4) ≤
      (525779809 / 50000000000 : ℝ) *
        (-(66675683038238292067283 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left Lmid_1 (by norm_num)
  have h2 :
    (29471737793 / 1000000000000 : ℝ) * Real.log ((bρ 2 - aρ 2) / 4) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(57268912150832389796717 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left Lmid_2 (by norm_num)
  have h3 :
    (42934365099 / 1000000000000 : ℝ) * Real.log ((bρ 3 - aρ 3) / 4) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(25512130211755314637529 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left Lmid_3 (by norm_num)
  have h4 :
    (29102115983 / 500000000000 : ℝ) * Real.log ((bρ 4 - aρ 4) / 4) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(11449496158609380585237 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left Lmid_4 (by norm_num)
  have h5 :
    (6903762131 / 100000000000 : ℝ) * Real.log ((bρ 5 - aρ 5) / 4) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(20577364119368339121527 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left Lmid_5 (by norm_num)
  have h6 :
    (78873099189 / 1000000000000 : ℝ) * Real.log ((bρ 6 - aρ 6) / 4) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left Lmid_6 (by norm_num)
  have h7 :
    (84856120711 / 1000000000000 : ℝ) * Real.log ((bρ 7 - aρ 7) / 4) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(33239459906384759787341 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left Lmid_7 (by norm_num)
  have h8 :
    (88396082127 / 1000000000000 : ℝ) * Real.log ((bρ 8 - aρ 8) / 4) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left Lmid_8 (by norm_num)
  have h9 :
    (706427057 / 8000000000 : ℝ) * Real.log ((bρ 9 - aρ 9) / 4) ≤
      (706427057 / 8000000000 : ℝ) * (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left Lmid_9 (by norm_num)
  have h10 :
    (17094464251 / 200000000000 : ℝ) * Real.log ((bρ 10 - aρ 10) / 4) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left Lmid_10 (by norm_num)
  have h11 :
    (39449592119 / 500000000000 : ℝ) * Real.log ((bρ 11 - aρ 11) / 4) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left Lmid_11 (by norm_num)
  have h12 :
    (35176735959 / 500000000000 : ℝ) * Real.log ((bρ 12 - aρ 12) / 4) ≤
      (35176735959 / 500000000000 : ℝ) * (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left Lmid_12 (by norm_num)
  have h13 :
    (11767795323 / 200000000000 : ℝ) * Real.log ((bρ 13 - aρ 13) / 4) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left Lmid_13 (by norm_num)
  have h14 :
    (22210660553 / 500000000000 : ℝ) * Real.log ((bρ 14 - aρ 14) / 4) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left Lmid_14 (by norm_num)
  have h15 :
    (30462865791 / 1000000000000 : ℝ) * Real.log ((bρ 15 - aρ 15) / 4) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left Lmid_15 (by norm_num)
  have h16 :
    (5959622577 / 1000000000000 : ℝ) * Real.log ((bρ 16 - aρ 16) / 4) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left Lmid_16 (by norm_num)
  linarith only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]

end Zeta5Irrational
