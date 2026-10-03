/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Table.UpperCertificate

/-! # Certified arcsine potential bounds (U00) -/

public section

open Finset

namespace Zeta5Irrational

lemma U_0_1 :
    Uω (aρ 1) (bρ 1) (0 : ℝ) ≤ (-(12712663703508542025099 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (123769636673849 / 20000000000000000 : ℝ) ≤
      (-(12712663703508542025099 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show
          (123769636673849 / 20000000000000000 : ℝ) =
            (123769636673849 / 78125000000000 : ℝ) / 2 ^ 8
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (123769636673849 / 78125000000000 : ℝ) ≤
            (1150279902491457974901 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (59272418588849 / 10000000000000000 : ℝ)) (q :=
      (123769636673849 / 20000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_0_2 :
    Uω (aρ 2) (bρ 2) (0 : ℝ) ≤ (-(1962983986998948336949 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (147824769578301 / 20000000000000000 : ℝ) ≤
      (-(1962983986998948336949 / 400000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show
          (147824769578301 / 20000000000000000 : ℝ) =
            (147824769578301 / 78125000000000 : ℝ) / 2 ^ 8
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (147824769578301 / 78125000000000 : ℝ) ≤
            (255086989961051663051 / 400000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (59558538983301 / 10000000000000000 : ℝ)) (q :=
      (147824769578301 / 20000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_0_3 :
    Uω (aρ 3) (bρ 3) (0 : ℝ) ≤ (-(46267520391835680481277 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (97864936683177 / 10000000000000000 : ℝ) ≤
      (-(46267520391835680481277 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show
          (97864936683177 / 10000000000000000 : ℝ) = (97864936683177 / 78125000000000 : ℝ) / 2 ^ 7
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (97864936683177 / 78125000000000 : ℝ) ≤
            (2252782229164319518723 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (30033768210677 / 5000000000000000 : ℝ)) (q :=
      (97864936683177 / 10000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_0_4 :
    Uω (aρ 4) (bρ 4) (0 : ℝ) ≤ (-(5359553913723040081263 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (17171580100553 / 1250000000000000 : ℝ) ≤
      (-(5359553913723040081263 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show
          (17171580100553 / 1250000000000000 : ℝ) = (17171580100553 / 9765625000000 : ℝ) / 2 ^ 7
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (17171580100553 / 9765625000000 : ℝ) ≤
            (705483913901959918737 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (7420503369 / 1220703125000 : ℝ)) (q :=
      (17171580100553 / 1250000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_0_5 :
    Uω (aρ 5) (bρ 5) (0 : ℝ) ≤ (-(39275139978819449528723 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (393851349704671 / 20000000000000000 : ℝ) ≤
      (-(39275139978819449528723 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show
          (393851349704671 / 20000000000000000 : ℝ) =
            (393851349704671 / 312500000000000 : ℝ) / 2 ^ 6
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (393851349704671 / 312500000000000 : ℝ) ≤
            (2313690839180550471277 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (61704912359671 / 10000000000000000 : ℝ)) (q :=
      (393851349704671 / 20000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_0_6 :
    Uω (aρ 6) (bρ 6) (0 : ℝ) ≤ (-(7143339604213661208809 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (281088781634513 / 10000000000000000 : ℝ) ≤
      (-(7143339604213661208809 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show
          (281088781634513 / 10000000000000000 : ℝ) =
            (281088781634513 / 156250000000000 : ℝ) / 2 ^ 6
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (281088781634513 / 156250000000000 : ℝ) ≤
            (1174426559386338791191 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (31395375392013 / 5000000000000000 : ℝ)) (q :=
      (281088781634513 / 10000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_0_7 :
    Uω (aρ 7) (bρ 7) (0 : ℝ) ≤ (-(32351824960621028314427 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (393530224619551 / 10000000000000000 : ℝ) ≤
      (-(32351824960621028314427 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show
          (393530224619551 / 10000000000000000 : ℝ) =
            (393530224619551 / 312500000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (393530224619551 / 312500000000000 : ℝ) ≤
            (2305534054378971685573 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (32006127997051 / 5000000000000000 : ℝ)) (q :=
      (393530224619551 / 10000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_0_8 :
    Uω (aρ 8) (bρ 8) (0 : ℝ) ≤ (-(7315709960795885799737 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (214383325750023 / 4000000000000000 : ℝ) ≤
      (-(7315709960795885799737 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show
          (214383325750023 / 4000000000000000 : ℝ) =
            (214383325750023 / 125000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (214383325750023 / 125000000000000 : ℝ) ≤
            (1348629792954114200263 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (13065356833023 / 2000000000000000 : ℝ)) (q :=
      (214383325750023 / 4000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_0_9 :
    Uω (aρ 9) (bρ 9) (0 : ℝ) ≤ (-(13245699571552860366621 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1414240104474349 / 20000000000000000 : ℝ) ≤
      (-(13245699571552860366621 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (1414240104474349 / 20000000000000000 : ℝ) =
            (1414240104474349 / 1250000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1414240104474349 / 1250000000000000 : ℝ) ≤
            (617244034447139633379 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (66684631529349 / 10000000000000000 : ℝ)) (q :=
      (1414240104474349 / 20000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_0_10 :
    Uω (aρ 10) (bρ 10) (0 : ℝ) ≤ (-(4811289393237367803367 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (902073204108467 / 10000000000000000 : ℝ) ≤
      (-(4811289393237367803367 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (902073204108467 / 10000000000000000 : ℝ) =
            (902073204108467 / 625000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (902073204108467 / 625000000000000 : ℝ) ≤
            (733888049162632196633 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (34015950888467 / 5000000000000000 : ℝ)) (q :=
      (902073204108467 / 10000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_0_11 :
    Uω (aρ 11) (bρ 11) (0 : ℝ) ≤ (-(21964674985840736154593 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2223905254151181 / 20000000000000000 : ℝ) ≤
      (-(21964674985840736154593 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (2223905254151181 / 20000000000000000 : ℝ) =
            (2223905254151181 / 1250000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2223905254151181 / 1250000000000000 : ℝ) ≤
            (5761212226159263845407 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (69314121506181 / 10000000000000000 : ℝ)) (q :=
      (2223905254151181 / 20000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_0_12 :
    Uω (aρ 12) (bρ 12) (0 : ℝ) ≤ (-(4043272987456227879851 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1324385526764569 / 10000000000000000 : ℝ) ≤
      (-(4043272987456227879851 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (1324385526764569 / 10000000000000000 : ℝ) =
            (1324385526764569 / 1250000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1324385526764569 / 1250000000000000 : ℝ) ≤
            (115610094343772120149 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (35239912099569 / 5000000000000000 : ℝ)) (q :=
      (1324385526764569 / 10000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_0_13 :
    Uω (aρ 13) (bρ 13) (0 : ℝ) ≤ (-(4702168270076774782451 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3049156407763681 / 20000000000000000 : ℝ) ≤
      (-(4702168270076774782451 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (3049156407763681 / 20000000000000000 : ℝ) =
            (3049156407763681 / 2500000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3049156407763681 / 2500000000000000 : ℝ) ≤
            (496435582173225217549 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (71483436838681 / 10000000000000000 : ℝ)) (q :=
      (3049156407763681 / 20000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_0_14 :
    Uω (aρ 14) (bρ 14) (0 : ℝ) ≤ (-(2217195343887504332233 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3393887425779091 / 20000000000000000 : ℝ) ≤
      (-(2217195343887504332233 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (3393887425779091 / 20000000000000000 : ℝ) =
            (3393887425779091 / 2500000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3393887425779091 / 2500000000000000 : ℝ) ≤
            (382106582237495667767 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (72287169809091 / 10000000000000000 : ℝ)) (q :=
      (3393887425779091 / 20000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_0_15 :
    Uω (aρ 15) (bρ 15) (0 : ℝ) ≤ (-(16999000975580328413317 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1827017753520839 / 10000000000000000 : ℝ) ≤
      (-(16999000975580328413317 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (1827017753520839 / 10000000000000000 : ℝ) =
            (1827017753520839 / 1250000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1827017753520839 / 1250000000000000 : ℝ) ≤
            (3795414433419671586683 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (36430986828339 / 5000000000000000 : ℝ)) (q :=
      (1827017753520839 / 10000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_0_16 :
    Uω (aρ 16) (bρ 16) (0 : ℝ) ≤ (-(1036850562756824007821 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1903366559739307 / 10000000000000000 : ℝ) ≤
      (-(1036850562756824007821 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (1903366559739307 / 10000000000000000 : ℝ) =
            (1903366559739307 / 1250000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1903366559739307 / 1250000000000000 : ℝ) ≤
            (262800400305675992179 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (36593967291807 / 5000000000000000 : ℝ)) (q :=
      (1903366559739307 / 10000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_0 : Uρ (0 : ℝ) ≤ (-(27385656762631359502577 / 10000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (0 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(12712663703508542025099 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_0_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (0 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(1962983986998948336949 / 400000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_0_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (0 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(46267520391835680481277 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_0_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (0 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(5359553913723040081263 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_0_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (0 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(39275139978819449528723 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_0_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (0 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(7143339604213661208809 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_0_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (0 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(32351824960621028314427 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_0_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (0 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(7315709960795885799737 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_0_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (0 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(13245699571552860366621 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_0_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (0 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(4811289393237367803367 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_0_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (0 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(21964674985840736154593 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_0_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (0 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(4043272987456227879851 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_0_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (0 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(4702168270076774782451 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_0_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (0 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(2217195343887504332233 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_0_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (0 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(16999000975580328413317 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_0_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (0 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(1036850562756824007821 / 625000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_0_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_1_1 :
    Uω (aρ 1) (bρ 1) (7174131 / 200000000000 : ℝ) ≤
      (-(50911373318893302541507 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (61510201432479 / 10000000000000000 : ℝ) ≤
      (-(50911373318893302541507 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show
          (61510201432479 / 10000000000000000 : ℝ) = (61510201432479 / 39062500000000 : ℝ) / 2 ^ 8
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (61510201432479 / 39062500000000 : ℝ) ≤
            (4540401105106697458493 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (29440945664979 / 5000000000000000 : ℝ)) (q :=
      (61510201432479 / 10000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_1_2 :
    Uω (aρ 2) (bρ 2) (7174131 / 200000000000 : ℝ) ≤
      (-(49135098078763348601453 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (146933153106433 / 20000000000000000 : ℝ) ≤
      (-(49135098078763348601453 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show
          (146933153106433 / 20000000000000000 : ℝ) =
            (146933153106433 / 78125000000000 : ℝ) / 2 ^ 8
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (146933153106433 / 78125000000000 : ℝ) ≤
            (6316676345236651398547 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (59025629061433 / 10000000000000000 : ℝ)) (q :=
      (146933153106433 / 20000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_1_3 :
    Uω (aρ 3) (bρ 3) (7174131 / 200000000000 : ℝ) ≤
      (-(46327645463733161241931 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (194556576856917 / 20000000000000000 : ℝ) ≤
      (-(46327645463733161241931 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show
          (194556576856917 / 20000000000000000 : ℝ) =
            (194556576856917 / 156250000000000 : ℝ) / 2 ^ 7
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (194556576856917 / 156250000000000 : ℝ) ≤
            (2192657157266838758069 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (59252946461917 / 10000000000000000 : ℝ)) (q :=
      (194556576856917 / 20000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_1_4 :
    Uω (aρ 4) (bρ 4) (7174131 / 200000000000 : ℝ) ≤
      (-(42936065490516840879561 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (273111736229039 / 20000000000000000 : ℝ) ≤
      (-(42936065490516840879561 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show
          (273111736229039 / 20000000000000000 : ℝ) =
            (273111736229039 / 156250000000000 : ℝ) / 2 ^ 7
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (273111736229039 / 156250000000000 : ℝ) ≤
            (5584237130483159120439 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (59513924769039 / 10000000000000000 : ℝ)) (q :=
      (273111736229039 / 20000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_1_5 :
    Uω (aρ 5) (bρ 5) (7174131 / 200000000000 : ℝ) ≤
      (-(7866842272424100993973 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (97882918342561 / 5000000000000000 : ℝ) ≤
      (-(7866842272424100993973 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show
          (97882918342561 / 5000000000000000 : ℝ) = (97882918342561 / 78125000000000 : ℝ) / 2 ^ 6
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (97882918342561 / 78125000000000 : ℝ) ≤
            (450923891175899006027 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (14935985643811 / 2500000000000000 : ℝ)) (q :=
      (97882918342561 / 5000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_1_6 :
    Uω (aρ 6) (bρ 6) (7174131 / 200000000000 : ℝ) ≤
      (-(1431007411209519275791 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (139724784359361 / 5000000000000000 : ℝ) ≤
      (-(1431007411209519275791 / 400000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show
          (139724784359361 / 5000000000000000 : ℝ) =
            (139724784359361 / 78125000000000 : ℝ) / 2 ^ 6
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (139724784359361 / 78125000000000 : ℝ) ≤
            (232545821510480724209 / 400000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (14967757875611 / 2500000000000000 : ℝ)) (q :=
      (139724784359361 / 5000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_1_7 :
    Uω (aρ 7) (bρ 7) (7174131 / 200000000000 : ℝ) ≤
      (-(40512196593284858497 / 12500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (195628501984759 / 5000000000000000 : ℝ) ≤
      (-(40512196593284858497 / 12500000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show
          (195628501984759 / 5000000000000000 : ℝ) =
            (195628501984759 / 156250000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (195628501984759 / 156250000000000 : ℝ) ≤
            (2809502175465141503 / 12500000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (14956130311009 / 2500000000000000 : ℝ)) (q :=
      (195628501984759 / 5000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_1_8 :
    Uω (aρ 8) (bρ 8) (7174131 / 200000000000 : ℝ) ≤
      (-(14660146048277734861007 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (266443970762523 / 5000000000000000 : ℝ) ≤
      (-(14660146048277734861007 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show
          (266443970762523 / 5000000000000000 : ℝ) =
            (266443970762523 / 156250000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (266443970762523 / 156250000000000 : ℝ) ≤
            (2668533459222265138993 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (14886186253773 / 2500000000000000 : ℝ)) (q :=
      (266443970762523 / 5000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_1_9 :
    Uω (aρ 9) (bρ 9) (7174131 / 200000000000 : ℝ) ≤
      (-(5309696547214735406207 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (70309505590531 / 1000000000000000 : ℝ) ≤
      (-(5309696547214735406207 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (70309505590531 / 1000000000000000 : ℝ) = (70309505590531 / 62500000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (70309505590531 / 62500000000000 : ℝ) ≤
            (235480895185264593793 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (2949667270781 / 500000000000000 : ℝ)) (q :=
      (70309505590531 / 1000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_1_10 :
    Uω (aρ 10) (bρ 10) (7174131 / 200000000000 : ℝ) ≤
      (-(24113296642670996497633 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1793918993060211 / 20000000000000000 : ℝ) ≤
      (-(24113296642670996497633 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (1793918993060211 / 20000000000000000 : ℝ) =
            (1793918993060211 / 1250000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1793918993060211 / 1250000000000000 : ℝ) ≤
            (3612590569329003502367 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (58163193170211 / 10000000000000000 : ℝ)) (q :=
      (1793918993060211 / 20000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_1_11 :
    Uω (aρ 11) (bρ 11) (7174131 / 200000000000 : ℝ) ≤
      (-(5505358080027453352527 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2211318713475239 / 20000000000000000 : ℝ) ≤
      (-(5505358080027453352527 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (2211318713475239 / 20000000000000000 : ℝ) =
            (2211318713475239 / 1250000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2211318713475239 / 1250000000000000 : ℝ) ≤
            (1426113722972546647473 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (57086287380239 / 10000000000000000 : ℝ)) (q :=
      (2211318713475239 / 20000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_1_12 :
    Uω (aρ 12) (bρ 12) (7174131 / 200000000000 : ℝ) ≤
      (-(10136579785760210337841 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (526754018847003 / 4000000000000000 : ℝ) ≤
      (-(10136579785760210337841 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (526754018847003 / 4000000000000000 : ℝ) =
            (526754018847003 / 500000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (526754018847003 / 500000000000000 : ℝ) ≤
            (260627918739789662159 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (11167514291003 / 2000000000000000 : ℝ)) (q :=
      (526754018847003 / 4000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12]) (by norm_num [aρ_12])
      (by norm_num) (by norm_num [aρ_12, bρ_12]) (by norm_num [aρ_12, bρ_12]) hlg

lemma U_1_13 :
    Uω (aρ 13) (bρ 13) (7174131 / 200000000000 : ℝ) ≤
      (-(75462414402452552303 / 40000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (606369344182109 / 4000000000000000 : ℝ) ≤
      (-(75462414402452552303 / 40000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (606369344182109 / 4000000000000000 : ℝ) =
            (606369344182109 / 500000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (606369344182109 / 500000000000000 : ℝ) ≤
            (7715247233547447697 / 40000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (10906491307109 / 2000000000000000 : ℝ)) (q :=
      (606369344182109 / 4000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13]) (by norm_num [aρ_13])
      (by norm_num) (by norm_num [aρ_13, bρ_13]) (by norm_num [aρ_13, bρ_13]) hlg

lemma U_1_14 :
    Uω (aρ 14) (bρ 14) (7174131 / 200000000000 : ℝ) ≤
      (-(8897340153662197454051 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3374557626289937 / 20000000000000000 : ℝ) ≤
      (-(8897340153662197454051 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (3374557626289937 / 20000000000000000 : ℝ) =
            (3374557626289937 / 2500000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3374557626289937 / 2500000000000000 : ℝ) ≤
            (1499867550837802545949 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (53316076869937 / 10000000000000000 : ℝ)) (q :=
      (3374557626289937 / 20000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_1_15 :
    Uω (aρ 15) (bρ 15) (7174131 / 200000000000 : ℝ) ≤
      (-(8528150055396143754779 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3633158069658803 / 20000000000000000 : ℝ) ≤
      (-(8528150055396143754779 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (3633158069658803 / 20000000000000000 : ℝ) =
            (3633158069658803 / 2500000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3633158069658803 / 2500000000000000 : ℝ) ≤
            (1869057649103856245221 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (52343242823803 / 10000000000000000 : ℝ)) (q :=
      (3633158069658803 / 20000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_1_16 :
    Uω (aρ 16) (bρ 16) (7174131 / 200000000000 : ℝ) ≤
      (-(16647030518034101616959 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3784936920023489 / 20000000000000000 : ℝ) ≤
      (-(16647030518034101616959 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (3784936920023489 / 20000000000000000 : ℝ) =
            (3784936920023489 / 2500000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3784936920023489 / 2500000000000000 : ℝ) ≤
            (4147384890965898383041 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (51750441678489 / 10000000000000000 : ℝ)) (q :=
      (3784936920023489 / 20000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_1 :
    Uρ (7174131 / 200000000000 : ℝ) ≤
      (-(27439164557690169188743 / 10000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (7174131 / 200000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) *
        (-(50911373318893302541507 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_1_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (7174131 / 200000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(49135098078763348601453 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_1_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (7174131 / 200000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(46327645463733161241931 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_1_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (7174131 / 200000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(42936065490516840879561 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_1_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (7174131 / 200000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(7866842272424100993973 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_1_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (7174131 / 200000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(1431007411209519275791 / 400000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_1_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (7174131 / 200000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) * (-(40512196593284858497 / 12500000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_1_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (7174131 / 200000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(14660146048277734861007 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_1_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (7174131 / 200000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(5309696547214735406207 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_1_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (7174131 / 200000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(24113296642670996497633 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_1_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (7174131 / 200000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(5505358080027453352527 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_1_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (7174131 / 200000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(10136579785760210337841 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_1_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (7174131 / 200000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) * (-(75462414402452552303 / 40000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_1_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (7174131 / 200000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(8897340153662197454051 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_1_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (7174131 / 200000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(8528150055396143754779 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_1_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (7174131 / 200000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(16647030518034101616959 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_1_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_2_1 :
    Uω (aρ 1) (bρ 1) (21522393 / 400000000000 : ℝ) ≤
      (-(25470941903623612969977 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (30661408404607 / 5000000000000000 : ℝ) ≤
      (-(25470941903623612969977 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show
          (30661408404607 / 5000000000000000 : ℝ) = (30661408404607 / 19531250000000 : ℝ) / 2 ^ 8
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (30661408404607 / 19531250000000 : ℝ) ≤
            (2254945308376387030023 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (14671618839607 / 2500000000000000 : ℝ)) (q :=
      (30661408404607 / 5000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_2_2 :
    Uω (aρ 2) (bρ 2) (21522393 / 400000000000 : ℝ) ≤
      (-(49165552758527775040867 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (18310794199513 / 2500000000000000 : ℝ) ≤
      (-(49165552758527775040867 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show
          (18310794199513 / 2500000000000000 : ℝ) = (18310794199513 / 9765625000000 : ℝ) / 2 ^ 8
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (18310794199513 / 9765625000000 : ℝ) ≤
            (6286221665472224959133 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (7344772853263 / 1250000000000000 : ℝ)) (q :=
      (18310794199513 / 2500000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_2_3 :
    Uω (aρ 3) (bρ 3) (21522393 / 400000000000 : ℝ) ≤
      (-(46358019844614904236579 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (38793303976897 / 4000000000000000 : ℝ) ≤
      (-(46358019844614904236579 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show
          (38793303976897 / 4000000000000000 : ℝ) = (38793303976897 / 31250000000000 : ℝ) / 2 ^ 7
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (38793303976897 / 31250000000000 : ℝ) ≤
            (2162282776385095763421 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (11768448552897 / 2000000000000000 : ℝ)) (q :=
      (38793303976897 / 4000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_2_4 :
    Uω (aρ 4) (bρ 4) (21522393 / 400000000000 : ℝ) ≤
      (-(2148318328187890160217 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (272285430885961 / 20000000000000000 : ℝ) ≤
      (-(2148318328187890160217 / 500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show
          (272285430885961 / 20000000000000000 : ℝ) =
            (272285430885961 / 156250000000000 : ℝ) / 2 ^ 7
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (272285430885961 / 156250000000000 : ℝ) ≤
            (277696802862109839783 / 500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (58866972700961 / 10000000000000000 : ℝ)) (q :=
      (272285430885961 / 20000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_2_5 :
    Uω (aρ 5) (bρ 5) (21522393 / 400000000000 : ℝ) ≤
      (-(19682243075206791475787 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (48793514003197 / 2500000000000000 : ℝ) ≤
      (-(19682243075206791475787 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show
          (48793514003197 / 2500000000000000 : ℝ) = (48793514003197 / 39062500000000 : ℝ) / 2 ^ 6
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (48793514003197 / 39062500000000 : ℝ) ≤
            (1112172333793208524213 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (7342466813197 / 1250000000000000 : ℝ)) (q :=
      (48793514003197 / 2500000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_2_6 :
    Uω (aρ 6) (bρ 6) (21522393 / 400000000000 : ℝ) ≤
      (-(35805525469465709732703 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (139301499171973 / 5000000000000000 : ℝ) ≤
      (-(35805525469465709732703 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show
          (139301499171973 / 5000000000000000 : ℝ) =
            (139301499171973 / 78125000000000 : ℝ) / 2 ^ 6
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (139301499171973 / 78125000000000 : ℝ) ≤
            (5783305348534290267297 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (14589311006973 / 2500000000000000 : ℝ)) (q :=
      (139301499171973 / 5000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_2_7 :
    Uω (aρ 7) (bρ 7) (21522393 / 400000000000 : ℝ) ≤
      (-(2027518787259263390593 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (390063798273459 / 10000000000000000 : ℝ) ≤
      (-(2027518787259263390593 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show
          (390063798273459 / 10000000000000000 : ℝ) =
            (390063798273459 / 312500000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (390063798273459 / 312500000000000 : ℝ) ≤
            (138566151178236609407 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (28808731563459 / 5000000000000000 : ℝ)) (q :=
      (390063798273459 / 10000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_2_8 :
    Uω (aρ 8) (bρ 8) (21522393 / 400000000000 : ℝ) ≤
      (-(183445131700844988143 / 62500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1062484639786859 / 20000000000000000 : ℝ) ≤
      (-(183445131700844988143 / 62500000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show
          (1062484639786859 / 20000000000000000 : ℝ) =
            (1062484639786859 / 625000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1062484639786859 / 625000000000000 : ℝ) ≤
            (33163362142905011857 / 62500000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (56432855026859 / 10000000000000000 : ℝ)) (q :=
      (1062484639786859 / 20000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_2_9 :
    Uω (aρ 9) (bρ 9) (21522393 / 400000000000 : ℝ) ≤
      (-(13290010338352078837471 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (700881131857547 / 10000000000000000 : ℝ) ≤
      (-(13290010338352078837471 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (700881131857547 / 10000000000000000 : ℝ) =
            (700881131857547 / 625000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (700881131857547 / 625000000000000 : ℝ) ≤
            (572933267647921162529 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (27372425297547 / 5000000000000000 : ℝ)) (q :=
      (700881131857547 / 10000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_2_10 :
    Uω (aρ 10) (bρ 10) (21522393 / 400000000000 : ℝ) ≤
      (-(24145699467680874899253 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1788115596139249 / 20000000000000000 : ℝ) ≤
      (-(24145699467680874899253 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (1788115596139249 / 20000000000000000 : ℝ) =
            (1788115596139249 / 1250000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1788115596139249 / 1250000000000000 : ℝ) ≤
            (3580187744319125100747 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (52539149524249 / 10000000000000000 : ℝ)) (q :=
      (1788115596139249 / 20000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_2_11 :
    Uω (aρ 11) (bρ 11) (21522393 / 400000000000 : ℝ) ≤
      (-(22054972789443236367197 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2203914271090737 / 20000000000000000 : ℝ) ≤
      (-(22054972789443236367197 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (2203914271090737 / 20000000000000000 : ℝ) =
            (2203914271090737 / 1250000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2203914271090737 / 1250000000000000 : ℝ) ≤
            (5670914422556763632803 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (49861198270737 / 10000000000000000 : ℝ)) (q :=
      (2203914271090737 / 20000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_2_12 :
    Uω (aρ 12) (bρ 12) (21522393 / 400000000000 : ℝ) ≤
      (-(20308097898670736143723 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (656146049612939 / 5000000000000000 : ℝ) ≤
      (-(20308097898670736143723 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (656146049612939 / 5000000000000000 : ℝ) =
            (656146049612939 / 625000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (656146049612939 / 625000000000000 : ℝ) ≤
            (486317510329263856277 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (11707757236689 / 2500000000000000 : ℝ)) (q :=
      (656146049612939 / 5000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12]) (by norm_num [aρ_12])
      (by norm_num) (by norm_num [aρ_12, bρ_12]) (by norm_num [aρ_12, bρ_12]) hlg

lemma U_2_13 :
    Uω (aρ 13) (bρ 13) (21522393 / 400000000000 : ℝ) ≤
      (-(18902136129446577859961 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (755197706355697 / 5000000000000000 : ℝ) ≤
      (-(18902136129446577859961 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (755197706355697 / 5000000000000000 : ℝ) =
            (755197706355697 / 625000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (755197706355697 / 625000000000000 : ℝ) ≤
            (1892279279553422140039 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (10913978580697 / 2500000000000000 : ℝ)) (q :=
      (755197706355697 / 5000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13]) (by norm_num [aρ_13])
      (by norm_num) (by norm_num [aρ_13, bρ_13]) (by norm_num [aρ_13, bρ_13]) hlg

lemma U_2_14 :
    Uω (aρ 14) (bρ 14) (21522393 / 400000000000 : ℝ) ≤
      (-(17832860086660498318657 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (840424550963387 / 5000000000000000 : ℝ) ≤
      (-(17832860086660498318657 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (840424550963387 / 5000000000000000 : ℝ) =
            (840424550963387 / 625000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (840424550963387 / 625000000000000 : ℝ) ≤
            (2961555322339501681343 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (10159001927137 / 2500000000000000 : ℝ)) (q :=
      (840424550963387 / 5000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14]) (by norm_num [aρ_14])
      (by norm_num) (by norm_num [aρ_14, bρ_14]) (by norm_num [aρ_14, bρ_14]) hlg

lemma U_2_15 :
    Uω (aρ 15) (bρ 15) (21522393 / 400000000000 : ℝ) ≤
      (-(17095939417607986453457 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (723756997736773 / 4000000000000000 : ℝ) ≤
      (-(17095939417607986453457 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (723756997736773 / 4000000000000000 : ℝ) =
            (723756997736773 / 500000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (723756997736773 / 500000000000000 : ℝ) ≤
            (3698475991392013546543 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (7629903024773 / 2000000000000000 : ℝ)) (q :=
      (723756997736773 / 4000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15]) (by norm_num [aρ_15])
      (by norm_num) (by norm_num [aρ_15, bρ_15]) (by norm_num [aρ_15, bρ_15]) hlg

lemma U_2_16 :
    Uω (aρ 16) (bρ 16) (21522393 / 400000000000 : ℝ) ≤
      (-(4171908594379160841333 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1884799886888283 / 10000000000000000 : ℝ) ≤
      (-(4171908594379160841333 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (1884799886888283 / 10000000000000000 : ℝ) =
            (1884799886888283 / 1250000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1884799886888283 / 1250000000000000 : ℝ) ≤
            (1026695257870839158667 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (18296324353283 / 5000000000000000 : ℝ)) (q :=
      (1884799886888283 / 10000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_2 :
    Uρ (21522393 / 400000000000 : ℝ) ≤
      (-(27469213456810556512581 / 10000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (21522393 / 400000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(25470941903623612969977 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_2_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (21522393 / 400000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(49165552758527775040867 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_2_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (21522393 / 400000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(46358019844614904236579 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_2_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (21522393 / 400000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(2148318328187890160217 / 500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_2_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (21522393 / 400000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(19682243075206791475787 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_2_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (21522393 / 400000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(35805525469465709732703 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_2_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (21522393 / 400000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(2027518787259263390593 / 625000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_2_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (21522393 / 400000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) * (-(183445131700844988143 / 62500000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_2_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (21522393 / 400000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(13290010338352078837471 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_2_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (21522393 / 400000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(24145699467680874899253 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_2_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (21522393 / 400000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(22054972789443236367197 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_2_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (21522393 / 400000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(20308097898670736143723 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_2_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (21522393 / 400000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(18902136129446577859961 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_2_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (21522393 / 400000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(17832860086660498318657 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_2_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (21522393 / 400000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(17095939417607986453457 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_2_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (21522393 / 400000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(4171908594379160841333 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_2_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_3_1 :
    Uω (aρ 1) (bρ 1) (7174131 / 100000000000 : ℝ) ≤
      (-(50972496086807483658427 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (61135380726717 / 10000000000000000 : ℝ) ≤
      (-(50972496086807483658427 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show
          (61135380726717 / 10000000000000000 : ℝ) = (61135380726717 / 39062500000000 : ℝ) / 2 ^ 8
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (61135380726717 / 39062500000000 : ℝ) ≤
            (4479278337192516341573 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (29245478234217 / 5000000000000000 : ℝ)) (q :=
      (61135380726717 / 10000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_3_2 :
    Uω (aρ 2) (bρ 2) (7174131 / 100000000000 : ℝ) ≤
      (-(49196146549098639705941 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (146038881156689 / 20000000000000000 : ℝ) ≤
      (-(49196146549098639705941 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show
          (146038881156689 / 20000000000000000 : ℝ) =
            (146038881156689 / 78125000000000 : ℝ) / 2 ^ 8
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (146038881156689 / 78125000000000 : ℝ) ≤
            (6255627874901360294059 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (58490063661689 / 10000000000000000 : ℝ)) (q :=
      (146038881156689 / 20000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_3_3 :
    Uω (aρ 3) (bρ 3) (7174131 / 100000000000 : ℝ) ≤
      (-(11597151895750616494561 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (193374126628239 / 20000000000000000 : ℝ) ≤
      (-(11597151895750616494561 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show
          (193374126628239 / 20000000000000000 : ℝ) =
            (193374126628239 / 156250000000000 : ℝ) / 2 ^ 7
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (193374126628239 / 156250000000000 : ℝ) ≤
            (532923759499383505439 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (58429202783239 / 10000000000000000 : ℝ)) (q :=
      (193374126628239 / 20000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_3_4 :
    Uω (aρ 4) (bρ 4) (7174131 / 100000000000 : ℝ) ≤
      (-(429970042250669996509 / 100000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (271452488626557 / 20000000000000000 : ℝ) ≤
      (-(429970042250669996509 / 100000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show
          (271452488626557 / 20000000000000000 : ℝ) =
            (271452488626557 / 156250000000000 : ℝ) / 2 ^ 7
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (271452488626557 / 156250000000000 : ℝ) ≤
            (55232983959330003491 / 100000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (58213383716557 / 10000000000000000 : ℝ)) (q :=
      (271452488626557 / 20000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_3_5 :
    Uω (aρ 5) (bρ 5) (7174131 / 100000000000 : ℝ) ≤
      (-(9848821862142350549383 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (194573819461431 / 10000000000000000 : ℝ) ≤
      (-(9848821862142350549383 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show
          (194573819461431 / 10000000000000000 : ℝ) =
            (194573819461431 / 156250000000000 : ℝ) / 2 ^ 6
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (194573819461431 / 156250000000000 : ℝ) ≤
            (548385842357649450617 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (28859307338931 / 5000000000000000 : ℝ)) (q :=
      (194573819461431 / 10000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_3_6 :
    Uω (aρ 6) (bρ 6) (7174131 / 100000000000 : ℝ) ≤
      (-(17918336888719840156369 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (277736547269241 / 10000000000000000 : ℝ) ≤
      (-(17918336888719840156369 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show
          (277736547269241 / 10000000000000000 : ℝ) =
            (277736547269241 / 156250000000000 : ℝ) / 2 ^ 6
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (277736547269241 / 156250000000000 : ℝ) ≤
            (2876078520280159843631 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (28401847576741 / 5000000000000000 : ℝ)) (q :=
      (277736547269241 / 10000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_3_7 :
    Uω (aρ 7) (bρ 7) (7174131 / 100000000000 : ℝ) ≤
      (-(32472061297251956228297 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (77765378718077 / 2000000000000000 : ℝ) ≤
      (-(32472061297251956228297 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show
          (77765378718077 / 2000000000000000 : ℝ) = (77765378718077 / 62500000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (77765378718077 / 62500000000000 : ℝ) ≤
            (2185297717748043771703 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (5532300703577 / 1000000000000000 : ℝ)) (q :=
      (77765378718077 / 2000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_3_8 :
    Uω (aρ 8) (bρ 8) (7174131 / 100000000000 : ℝ) ≤
      (-(14691979007557547771577 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (211802415407127 / 4000000000000000 : ℝ) ≤
      (-(14691979007557547771577 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show
          (211802415407127 / 4000000000000000 : ℝ) =
            (211802415407127 / 125000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (211802415407127 / 125000000000000 : ℝ) ≤
            (2636700499942452228423 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (10627929110127 / 2000000000000000 : ℝ)) (q :=
      (211802415407127 / 4000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_3_9 :
    Uω (aρ 9) (bρ 9) (7174131 / 100000000000 : ℝ) ≤
      (-(26614221306142328686011 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (698488168645371 / 10000000000000000 : ℝ) ≤
      (-(26614221306142328686011 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (698488168645371 / 10000000000000000 : ℝ) =
            (698488168645371 / 625000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (698488168645371 / 625000000000000 : ℝ) ≤
            (1111665905857671313989 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (25069138722871 / 5000000000000000 : ℝ)) (q :=
      (698488168645371 / 10000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_3_10 :
    Uω (aρ 10) (bρ 10) (7174131 / 100000000000 : ℝ) ≤
      (-(24182014718027931878799 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (89081689306903 / 1000000000000000 : ℝ) ≤
      (-(24182014718027931878799 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (89081689306903 / 1000000000000000 : ℝ) = (89081689306903 / 62500000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (89081689306903 / 62500000000000 : ℝ) ≤
            (3543872493972068121201 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (2311834639903 / 500000000000000 : ℝ)) (q :=
      (89081689306903 / 1000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10]) (by norm_num [aρ_10])
      (by norm_num) (by norm_num [aρ_10, bρ_10]) (by norm_num [aρ_10, bρ_10]) hlg

lemma U_3_11 :
    Uω (aρ 11) (bρ 11) (7174131 / 100000000000 : ℝ) ≤
      (-(22094280725116768354743 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2195268143255481 / 20000000000000000 : ℝ) ≤
      (-(22094280725116768354743 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (2195268143255481 / 20000000000000000 : ℝ) =
            (2195268143255481 / 1250000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2195268143255481 / 1250000000000000 : ℝ) ≤
            (5631606486883231645257 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (41394423710481 / 10000000000000000 : ℝ)) (q :=
      (2195268143255481 / 20000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_3_12 :
    Uω (aρ 12) (bρ 12) (7174131 / 100000000000 : ℝ) ≤
      (-(20351605328285829232061 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (653297527892073 / 5000000000000000 : ℝ) ≤
      (-(20351605328285829232061 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (653297527892073 / 5000000000000000 : ℝ) =
            (653297527892073 / 625000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (653297527892073 / 625000000000000 : ℝ) ≤
            (442810080714170767939 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (8904073834573 / 2500000000000000 : ℝ)) (q :=
      (653297527892073 / 5000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12]) (by norm_num [aρ_12])
      (by norm_num) (by norm_num [aρ_12, bρ_12]) (by norm_num [aρ_12, bρ_12]) hlg

lemma U_3_13 :
    Uω (aρ 13) (bρ 13) (7174131 / 100000000000 : ℝ) ≤
      (-(18951542575309468805869 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1502951489823239 / 10000000000000000 : ℝ) ≤
      (-(18951542575309468805869 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (1502951489823239 / 10000000000000000 : ℝ) =
            (1502951489823239 / 1250000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1502951489823239 / 1250000000000000 : ℝ) ≤
            (1842872833690531194131 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (14473710910739 / 5000000000000000 : ℝ)) (q :=
      (1502951489823239 / 10000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_3_14 :
    Uω (aρ 14) (bρ 14) (7174131 / 100000000000 : ℝ) ≤
      (-(4472659389032352227177 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3342331165120743 / 20000000000000000 : ℝ) ≤
      (-(4472659389032352227177 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (3342331165120743 / 20000000000000000 : ℝ) =
            (3342331165120743 / 2500000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3342331165120743 / 2500000000000000 : ℝ) ≤
            (725944463217647772823 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (21448322250743 / 10000000000000000 : ℝ)) (q :=
      (3342331165120743 / 20000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_3_15 :
    Uω (aρ 15) (bρ 15) (7174131 / 100000000000 : ℝ) ≤
      (-(17165962668190914916479 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (898383398074539 / 5000000000000000 : ℝ) ≤
      (-(17165962668190914916479 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (898383398074539 / 5000000000000000 : ℝ) =
            (898383398074539 / 625000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (898383398074539 / 625000000000000 : ℝ) ≤
            (3628452740809085083521 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (3269368003289 / 2500000000000000 : ℝ)) (q :=
      (898383398074539 / 5000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15]) (by norm_num [aρ_15])
      (by norm_num) (by norm_num [aρ_15, bρ_15]) (by norm_num [aρ_15, bρ_15]) hlg

lemma U_3_16 :
    Uω (aρ 16) (bρ 16) (7174131 / 100000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_3 :
    Uρ (7174131 / 100000000000 : ℝ) ≤
      (-(27504182777521718667561 / 10000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (7174131 / 100000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) *
        (-(50972496086807483658427 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_3_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (7174131 / 100000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(49196146549098639705941 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_3_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (7174131 / 100000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(11597151895750616494561 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_3_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (7174131 / 100000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) * (-(429970042250669996509 / 100000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_3_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (7174131 / 100000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(9848821862142350549383 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_3_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (7174131 / 100000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(17918336888719840156369 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_3_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (7174131 / 100000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(32472061297251956228297 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_3_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (7174131 / 100000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(14691979007557547771577 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_3_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (7174131 / 100000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(26614221306142328686011 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_3_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (7174131 / 100000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(24182014718027931878799 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_3_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (7174131 / 100000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(22094280725116768354743 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_3_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (7174131 / 100000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(20351605328285829232061 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_3_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (7174131 / 100000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(18951542575309468805869 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_3_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (7174131 / 100000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(4472659389032352227177 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_3_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (7174131 / 100000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(17165962668190914916479 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_3_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (7174131 / 100000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_3_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_4_1 :
    Uω (aρ 1) (bρ 1) (14825913 / 200000000000 : ℝ) ≤
      (-(50976580114456355348677 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (61110417965973 / 10000000000000000 : ℝ) ≤
      (-(50976580114456355348677 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show
          (61110417965973 / 10000000000000000 : ℝ) = (61110417965973 / 39062500000000 : ℝ) / 2 ^ 8
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (61110417965973 / 39062500000000 : ℝ) ≤
            (4475194309543644651323 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (29232456748473 / 5000000000000000 : ℝ)) (q :=
      (61110417965973 / 10000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_4_2 :
    Uω (aρ 2) (bρ 2) (14825913 / 200000000000 : ℝ) ≤
      (-(1968009239129451754533 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (145979244790401 / 20000000000000000 : ℝ) ≤
      (-(1968009239129451754533 / 400000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show
          (145979244790401 / 20000000000000000 : ℝ) =
            (145979244790401 / 78125000000000 : ℝ) / 2 ^ 8
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (145979244790401 / 78125000000000 : ℝ) ≤
            (250061737830548245467 / 400000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (58454309845401 / 10000000000000000 : ℝ)) (q :=
      (145979244790401 / 20000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_4_3 :
    Uω (aρ 3) (bρ 3) (14825913 / 200000000000 : ℝ) ≤
      (-(46392696947832317425569 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (193295065059677 / 20000000000000000 : ℝ) ≤
      (-(46392696947832317425569 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show
          (193295065059677 / 20000000000000000 : ℝ) =
            (193295065059677 / 156250000000000 : ℝ) / 2 ^ 7
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (193295065059677 / 156250000000000 : ℝ) ≤
            (2127605673167682574431 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (58374023764677 / 10000000000000000 : ℝ)) (q :=
      (193295065059677 / 20000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_4_4 :
    Uω (aρ 4) (bρ 4) (14825913 / 200000000000 : ℝ) ≤
      (-(21500554949887790778621 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (54268212388099 / 4000000000000000 : ℝ) ≤
      (-(21500554949887790778621 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show
          (54268212388099 / 4000000000000000 : ℝ) = (54268212388099 / 31250000000000 : ℝ) / 2 ^ 7
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (54268212388099 / 31250000000000 : ℝ) ≤
            (2759596360612209221379 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (11625167916099 / 2000000000000000 : ℝ)) (q :=
      (54268212388099 / 4000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_4_5 :
    Uω (aρ 5) (bρ 5) (14825913 / 200000000000 : ℝ) ≤
      (-(9849857532743252544909 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (194493230401519 / 10000000000000000 : ℝ) ≤
      (-(9849857532743252544909 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show
          (194493230401519 / 10000000000000000 : ℝ) =
            (194493230401519 / 156250000000000 : ℝ) / 2 ^ 6
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (194493230401519 / 156250000000000 : ℝ) ≤
            (547350171756747455091 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (28790659554019 / 5000000000000000 : ℝ)) (q :=
      (194493230401519 / 10000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_4_6 :
    Uω (aρ 6) (bρ 6) (14825913 / 200000000000 : ℝ) ≤
      (-(17920442983008148696533 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (277619584033359 / 10000000000000000 : ℝ) ≤
      (-(17920442983008148696533 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show
          (277619584033359 / 10000000000000000 : ℝ) =
            (277619584033359 / 156250000000000 : ℝ) / 2 ^ 6
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (277619584033359 / 156250000000000 : ℝ) ≤
            (2873972425991851303467 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (28296825615859 / 5000000000000000 : ℝ)) (q :=
      (277619584033359 / 10000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_4_7 :
    Uω (aρ 7) (bρ 7) (14825913 / 200000000000 : ℝ) ≤
      (-(8119097615340380036387 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (194329300239091 / 5000000000000000 : ℝ) ≤
      (-(8119097615340380036387 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show
          (194329300239091 / 5000000000000000 : ℝ) =
            (194329300239091 / 156250000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (194329300239091 / 156250000000000 : ℝ) ≤
            (545242138409619963613 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (13752575840341 / 2500000000000000 : ℝ)) (q :=
      (194329300239091 / 5000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_4_8 :
    Uω (aρ 8) (bρ 8) (14825913 / 200000000000 : ℝ) ≤
      (-(2938847159611171861641 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (264633547803489 / 5000000000000000 : ℝ) ≤
      (-(2938847159611171861641 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show
          (264633547803489 / 5000000000000000 : ℝ) =
            (264633547803489 / 156250000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (264633547803489 / 156250000000000 : ℝ) ≤
            (526888741888828138359 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (13171410569739 / 2500000000000000 : ℝ)) (q :=
      (264633547803489 / 5000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_4_9 :
    Uω (aρ 9) (bρ 9) (14825913 / 200000000000 : ℝ) ≤
      (-(26619015513642536754779 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1396306758365197 / 20000000000000000 : ℝ) ≤
      (-(26619015513642536754779 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (1396306758365197 / 20000000000000000 : ℝ) =
            (1396306758365197 / 1250000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1396306758365197 / 1250000000000000 : ℝ) ≤
            (1106871698357463245221 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (49492581070197 / 10000000000000000 : ℝ)) (q :=
      (1396306758365197 / 20000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_4_10 :
    Uω (aρ 10) (bρ 10) (14825913 / 200000000000 : ℝ) ≤
      (-(24187231062536165434337 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (890352333463911 / 10000000000000000 : ℝ) ≤
      (-(24187231062536165434337 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (890352333463911 / 10000000000000000 : ℝ) =
            (890352333463911 / 625000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (890352333463911 / 625000000000000 : ℝ) ≤
            (3538656149463834565663 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (22665728068911 / 5000000000000000 : ℝ)) (q :=
      (890352333463911 / 10000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_4_11 :
    Uω (aρ 11) (bρ 11) (14825913 / 200000000000 : ℝ) ≤
      (-(22100139537083282243419 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2193982353625503 / 20000000000000000 : ℝ) ≤
      (-(22100139537083282243419 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (2193982353625503 / 20000000000000000 : ℝ) =
            (2193982353625503 / 1250000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2193982353625503 / 1250000000000000 : ℝ) ≤
            (5625747674916717756581 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (40132516630503 / 10000000000000000 : ℝ)) (q :=
      (2193982353625503 / 20000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_4_12 :
    Uω (aρ 12) (bρ 12) (14825913 / 200000000000 : ℝ) ≤
      (-(20358481952867747024019 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2611393736553067 / 20000000000000000 : ℝ) ≤
      (-(20358481952867747024019 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (2611393736553067 / 20000000000000000 : ℝ) =
            (2611393736553067 / 2500000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2611393736553067 / 2500000000000000 : ℝ) ≤
            (435933456132252975981 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (33843802873067 / 10000000000000000 : ℝ)) (q :=
      (2611393736553067 / 20000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_4_13 :
    Uω (aρ 13) (bρ 13) (14825913 / 200000000000 : ℝ) ≤
      (-(1896017617456667321 / 1000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (750827230859117 / 5000000000000000 : ℝ) ≤
      (-(1896017617456667321 / 1000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (750827230859117 / 5000000000000000 : ℝ) =
            (750827230859117 / 625000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (750827230859117 / 625000000000000 : ℝ) ≤
            (183423923443332679 / 1000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (6594312040367 / 2500000000000000 : ℝ)) (q :=
      (750827230859117 / 5000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13]) (by norm_num [aρ_13])
      (by norm_num) (by norm_num [aρ_13, bρ_13]) (by norm_num [aρ_13, bρ_13]) hlg

lemma U_4_14 :
    Uω (aρ 14) (bρ 14) (14825913 / 200000000000 : ℝ) ≤
      (-(8951472576252204766649 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3338220089219641 / 20000000000000000 : ℝ) ≤
      (-(8951472576252204766649 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (3338220089219641 / 20000000000000000 : ℝ) =
            (3338220089219641 / 2500000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3338220089219641 / 2500000000000000 : ℝ) ≤
            (1445735128247795233351 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (17361128899641 / 10000000000000000 : ℝ)) (q :=
      (3338220089219641 / 20000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_4_15 :
    Uω (aρ 15) (bρ 15) (14825913 / 200000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_4_16 :
    Uω (aρ 16) (bρ 16) (14825913 / 200000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_4 :
    Uρ (14825913 / 200000000000 : ℝ) ≤
      (-(13755063908664878567303 / 5000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (14825913 / 200000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) *
        (-(50976580114456355348677 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_4_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (14825913 / 200000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(1968009239129451754533 / 400000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_4_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (14825913 / 200000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(46392696947832317425569 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_4_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (14825913 / 200000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(21500554949887790778621 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_4_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (14825913 / 200000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(9849857532743252544909 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_4_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (14825913 / 200000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(17920442983008148696533 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_4_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (14825913 / 200000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(8119097615340380036387 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_4_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (14825913 / 200000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(2938847159611171861641 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_4_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (14825913 / 200000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(26619015513642536754779 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_4_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (14825913 / 200000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(24187231062536165434337 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_4_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (14825913 / 200000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(22100139537083282243419 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_4_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (14825913 / 200000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(20358481952867747024019 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_4_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (14825913 / 200000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) * (-(1896017617456667321 / 1000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_4_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (14825913 / 200000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(8951472576252204766649 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_4_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (14825913 / 200000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_4_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (14825913 / 200000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_4_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_5_1 :
    Uω (aρ 1) (bρ 1) (78667711 / 1000000000000 : ℝ) ≤
      (-(50984345571698067906027 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (24425192541173 / 4000000000000000 : ℝ) ≤
      (-(50984345571698067906027 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show
          (24425192541173 / 4000000000000000 : ℝ) = (24425192541173 / 15625000000000 : ℝ) / 2 ^ 8
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (24425192541173 / 15625000000000 : ℝ) ≤
            (4467428852301932093973 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (11683084346173 / 2000000000000000 : ℝ)) (q :=
      (24425192541173 / 4000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_5_2 :
    Uω (aρ 2) (bρ 2) (78667711 / 1000000000000 : ℝ) ≤
      (-(24603999536613700227217 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (145865890759319 / 20000000000000000 : ℝ) ≤
      (-(24603999536613700227217 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show
          (145865890759319 / 20000000000000000 : ℝ) =
            (145865890759319 / 78125000000000 : ℝ) / 2 ^ 8
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (145865890759319 / 78125000000000 : ℝ) ≤
            (3121887675386299772783 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (58386337274319 / 10000000000000000 : ℝ)) (q :=
      (145865890759319 / 20000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_5_3 :
    Uω (aρ 3) (bρ 3) (78667711 / 1000000000000 : ℝ) ≤
      (-(11600119550061847085141 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (193144715793361 / 20000000000000000 : ℝ) ≤
      (-(11600119550061847085141 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show
          (193144715793361 / 20000000000000000 : ℝ) =
            (193144715793361 / 156250000000000 : ℝ) / 2 ^ 7
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (193144715793361 / 156250000000000 : ℝ) ≤
            (529956105188152914859 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (58269055958361 / 10000000000000000 : ℝ)) (q :=
      (193144715793361 / 20000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_5_4 :
    Uω (aρ 4) (bρ 4) (78667711 / 1000000000000 : ℝ) ≤
      (-(10752232140308635873551 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (271128992465947 / 20000000000000000 : ℝ) ≤
      (-(10752232140308635873551 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show
          (271128992465947 / 20000000000000000 : ℝ) =
            (271128992465947 / 156250000000000 : ℝ) / 2 ^ 7
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (271128992465947 / 156250000000000 : ℝ) ≤
            (1377843514941364126449 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (57959151565947 / 10000000000000000 : ℝ)) (q :=
      (271128992465947 / 20000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_5_5 :
    Uω (aρ 5) (bρ 5) (78667711 / 1000000000000 : ℝ) ≤
      (-(1231479042758063468317 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (388679312495423 / 20000000000000000 : ℝ) ≤
      (-(1231479042758063468317 / 312500000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show
          (388679312495423 / 20000000000000000 : ℝ) =
            (388679312495423 / 312500000000000 : ℝ) / 2 ^ 6
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (388679312495423 / 312500000000000 : ℝ) ≤
            (68171920304436531683 / 312500000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (57319552260423 / 10000000000000000 : ℝ)) (q :=
      (388679312495423 / 20000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_5_6 :
    Uω (aρ 6) (bρ 6) (78667711 / 1000000000000 : ℝ) ≤
      (-(17924466660160898289283 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (22191701086949 / 800000000000000 : ℝ) ≤
      (-(17924466660160898289283 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show
          (22191701086949 / 800000000000000 : ℝ) = (22191701086949 / 12500000000000 : ℝ) / 2 ^ 6
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (22191701086949 / 12500000000000 : ℝ) ≤
            (2869948748839101710717 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (2247695671949 / 400000000000000 : ℝ)) (q :=
      (22191701086949 / 800000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_5_7 :
    Uω (aρ 7) (bρ 7) (78667711 / 1000000000000 : ℝ) ≤
      (-(32484685260499643578059 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (776672699289057 / 20000000000000000 : ℝ) ≤
      (-(32484685260499643578059 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show
          (776672699289057 / 20000000000000000 : ℝ) =
            (776672699289057 / 625000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (776672699289057 / 625000000000000 : ℝ) ≤
            (2172673754500356421941 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (54411183154057 / 10000000000000000 : ℝ)) (q :=
      (776672699289057 / 20000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_5_8 :
    Uω (aρ 8) (bρ 8) (78667711 / 1000000000000 : ℝ) ≤
      (-(29397157238015419786121 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1057615185486693 / 20000000000000000 : ℝ) ≤
      (-(29397157238015419786121 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show
          (1057615185486693 / 20000000000000000 : ℝ) =
            (1057615185486693 / 625000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1057615185486693 / 625000000000000 : ℝ) ≤
            (5260201776984580213879 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (51812018011693 / 10000000000000000 : ℝ)) (q :=
      (1057615185486693 / 20000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_5_9 :
    Uω (aρ 9) (bρ 9) (78667711 / 1000000000000 : ℝ) ≤
      (-(13314151100942602912333 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (348752663432181 / 5000000000000000 : ℝ) ≤
      (-(13314151100942602912333 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (348752663432181 / 5000000000000000 : ℝ) =
            (348752663432181 / 312500000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (348752663432181 / 312500000000000 : ℝ) ≤
            (548792505057397087667 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (12060464473431 / 2500000000000000 : ℝ)) (q :=
      (348752663432181 / 5000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_5_10 :
    Uω (aρ 10) (bρ 10) (78667711 / 1000000000000 : ℝ) ≤
      (-(12098720823673483752803 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (177888739125561 / 2000000000000000 : ℝ) ≤
      (-(12098720823673483752803 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (177888739125561 / 2000000000000000 : ℝ) =
            (177888739125561 / 125000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (177888739125561 / 125000000000000 : ℝ) ≤
            (1764222782326516247197 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (4355956192561 / 1000000000000000 : ℝ)) (q :=
      (177888739125561 / 2000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10]) (by norm_num [aρ_10])
      (by norm_num) (by norm_num [aρ_10, bρ_10]) (by norm_num [aρ_10, bρ_10]) hlg

lemma U_5_11 :
    Uω (aρ 11) (bρ 11) (78667711 / 1000000000000 : ℝ) ≤
      (-(22111813113724319814737 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2191422685824679 / 20000000000000000 : ℝ) ≤
      (-(22111813113724319814737 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (2191422685824679 / 20000000000000000 : ℝ) =
            (2191422685824679 / 1250000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2191422685824679 / 1250000000000000 : ℝ) ≤
            (5614074098275680185263 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (37618230289679 / 10000000000000000 : ℝ)) (q :=
      (2191422685824679 / 20000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_5_12 :
    Uω (aρ 12) (bρ 12) (78667711 / 1000000000000 : ℝ) ≤
      (-(20372656090798980590323 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2607694933038421 / 20000000000000000 : ℝ) ≤
      (-(20372656090798980590323 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (2607694933038421 / 20000000000000000 : ℝ) =
            (2607694933038421 / 2500000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2607694933038421 / 2500000000000000 : ℝ) ≤
            (421759318201019409677 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (30190380818421 / 10000000000000000 : ℝ)) (q :=
      (2607694933038421 / 20000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_5_13 :
    Uω (aρ 13) (bρ 13) (78667711 / 1000000000000 : ℝ) ≤
      (-(74138612372821309739 / 39062500000000000000 : ℝ)) := by
  have hlg :
    Real.log (2997515551401257 / 20000000000000000 : ℝ) ≤
      (-(74138612372821309739 / 39062500000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (2997515551401257 / 20000000000000000 : ℝ) =
            (2997515551401257 / 2500000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2997515551401257 / 2500000000000000 : ℝ) ≤
            (7089572818584940261 / 39062500000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (20629257586257 / 10000000000000000 : ℝ)) (q :=
      (2997515551401257 / 20000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_5_14 :
    Uω (aρ 14) (bρ 14) (78667711 / 1000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_5_15 :
    Uω (aρ 15) (bρ 15) (78667711 / 1000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_5_16 :
    Uω (aρ 16) (bρ 16) (78667711 / 1000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_5 :
    Uρ (78667711 / 1000000000000 : ℝ) ≤
      (-(6880237177330760400461 / 2500000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (78667711 / 1000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) *
        (-(50984345571698067906027 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_5_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (78667711 / 1000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(24603999536613700227217 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_5_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (78667711 / 1000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(11600119550061847085141 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_5_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (78667711 / 1000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(10752232140308635873551 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_5_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (78667711 / 1000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) * (-(1231479042758063468317 / 312500000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_5_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (78667711 / 1000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(17924466660160898289283 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_5_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (78667711 / 1000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(32484685260499643578059 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_5_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (78667711 / 1000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(29397157238015419786121 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_5_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (78667711 / 1000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(13314151100942602912333 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_5_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (78667711 / 1000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(12098720823673483752803 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_5_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (78667711 / 1000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(22111813113724319814737 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_5_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (78667711 / 1000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(20372656090798980590323 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_5_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (78667711 / 1000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) * (-(74138612372821309739 / 39062500000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_5_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (78667711 / 1000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_5_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (78667711 / 1000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_5_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (78667711 / 1000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_5_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_6_1 :
    Uω (aρ 1) (bρ 1) (85815639 / 1000000000000 : ℝ) ≤
      (-(10199318023215378615661 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12197651654253 / 2000000000000000 : ℝ) ≤
      (-(10199318023215378615661 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show
          (12197651654253 / 2000000000000000 : ℝ) = (12197651654253 / 7812500000000 : ℝ) / 2 ^ 8
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (12197651654253 / 7812500000000 : ℝ) ≤
            (891036861584621384339 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (5833745484753 / 1000000000000000 : ℝ)) (q :=
      (12197651654253 / 2000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_6_2 :
    Uω (aρ 2) (bρ 2) (85815639 / 1000000000000 : ℝ) ≤
      (-(49220252785694328798381 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7284363017877 / 1000000000000000 : ℝ) ≤
      (-(49220252785694328798381 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (7284363017877 / 1000000000000000 : ℝ) = (7284363017877 / 3906250000000 : ℝ) / 2 ^ 8
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7284363017877 / 3906250000000 : ℝ) ≤
            (6231521638305671201619 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (2913959307627 / 500000000000000 : ℝ)) (q :=
      (7284363017877 / 1000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_6_3 :
    Uω (aρ 3) (bρ 3) (85815639 / 1000000000000 : ℝ) ≤
      (-(23206381385399735792023 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (38581518296581 / 4000000000000000 : ℝ) ≤
      (-(23206381385399735792023 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show
          (38581518296581 / 4000000000000000 : ℝ) = (38581518296581 / 31250000000000 : ℝ) / 2 ^ 7
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (38581518296581 / 31250000000000 : ℝ) ≤
            (1053769925100264207977 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (11620682185581 / 2000000000000000 : ℝ)) (q :=
      (38581518296581 / 4000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_6_4 :
    Uω (aρ 4) (bρ 4) (85815639 / 1000000000000 : ℝ) ≤
      (-(21510644677510011539679 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (135397031276029 / 10000000000000000 : ℝ) ≤
      (-(21510644677510011539679 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show
          (135397031276029 / 10000000000000000 : ℝ) =
            (135397031276029 / 78125000000000 : ℝ) / 2 ^ 7
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (135397031276029 / 78125000000000 : ℝ) ≤
            (2749506632989988460321 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (28847850466029 / 5000000000000000 : ℝ)) (q :=
      (135397031276029 / 10000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_6_5 :
    Uω (aρ 5) (bρ 5) (85815639 / 1000000000000 : ℝ) ≤
      (-(315358759639002277023 / 80000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (194096580910869 / 10000000000000000 : ℝ) ≤
      (-(315358759639002277023 / 80000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show
          (194096580910869 / 10000000000000000 : ℝ) =
            (194096580910869 / 156250000000000 : ℝ) / 2 ^ 6
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (194096580910869 / 156250000000000 : ℝ) ≤
            (17351886904997722977 / 80000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (28452440433369 / 5000000000000000 : ℝ)) (q :=
      (194096580910869 / 10000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_6_6 :
    Uω (aρ 6) (bρ 6) (85815639 / 1000000000000 : ℝ) ≤
      (-(35861726381563634540717 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (11081664629919 / 400000000000000 : ℝ) ≤
      (-(35861726381563634540717 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show
          (11081664629919 / 400000000000000 : ℝ) = (11081664629919 / 6250000000000 : ℝ) / 2 ^ 6 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (11081664629919 / 6250000000000 : ℝ) ≤
            (5727104436436365459283 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (1111091508019 / 200000000000000 : ℝ)) (q :=
      (11081664629919 / 400000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_6_7 :
    Uω (aρ 7) (bρ 7) (85815639 / 1000000000000 : ℝ) ≤
      (-(32497938712340042706679 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (775644021694503 / 20000000000000000 : ℝ) ≤
      (-(32497938712340042706679 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show
          (775644021694503 / 20000000000000000 : ℝ) =
            (775644021694503 / 625000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (775644021694503 / 625000000000000 : ℝ) ≤
            (2159420302659957293321 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (53453984839503 / 10000000000000000 : ℝ)) (q :=
      (775644021694503 / 20000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_6_8 :
    Uω (aρ 8) (bρ 8) (85815639 / 1000000000000 : ℝ) ≤
      (-(29411142977102807541847 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1056137066353147 / 20000000000000000 : ℝ) ≤
      (-(29411142977102807541847 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show
          (1056137066353147 / 20000000000000000 : ℝ) =
            (1056137066353147 / 625000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1056137066353147 / 625000000000000 : ℝ) ≤
            (5246216037897192458153 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (50405378158147 / 10000000000000000 : ℝ)) (q :=
      (1056137066353147 / 20000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_6_9 :
    Uω (aρ 9) (bρ 9) (85815639 / 1000000000000 : ℝ) ≤
      (-(6660859717657794390429 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1392900669621853 / 20000000000000000 : ℝ) ≤
      (-(6660859717657794390429 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (1392900669621853 / 20000000000000000 : ℝ) =
            (1392900669621853 / 1250000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1392900669621853 / 1250000000000000 : ℝ) ≤
            (270612085342205609571 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (46203353066853 / 10000000000000000 : ℝ)) (q :=
      (1392900669621853 / 20000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_6_10 :
    Uω (aρ 10) (bρ 10) (85815639 / 1000000000000 : ℝ) ≤
      (-(4842885154875601165287 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (887934335277677 / 10000000000000000 : ℝ) ≤
      (-(4842885154875601165287 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (887934335277677 / 10000000000000000 : ℝ) =
            (887934335277677 / 625000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (887934335277677 / 625000000000000 : ℝ) ≤
            (702292287524398834713 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (20306160252677 / 5000000000000000 : ℝ)) (q :=
      (887934335277677 / 10000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_6_11 :
    Uω (aρ 11) (bρ 11) (85815639 / 1000000000000 : ℝ) ≤
      (-(4426395685635096752489 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1093504032837657 / 10000000000000000 : ℝ) ≤
      (-(4426395685635096752489 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (1093504032837657 / 10000000000000000 : ℝ) =
            (1093504032837657 / 625000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1093504032837657 / 625000000000000 : ℝ) ≤
            (1118781756764903247511 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (16637544710157 / 5000000000000000 : ℝ)) (q :=
      (1093504032837657 / 10000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_6_12 :
    Uω (aρ 12) (bρ 12) (85815639 / 1000000000000 : ℝ) ≤
      (-(5099845272237973435631 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2600735172932703 / 20000000000000000 : ℝ) ≤
      (-(5099845272237973435631 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (2600735172932703 / 20000000000000000 : ℝ) =
            (2600735172932703 / 2500000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2600735172932703 / 2500000000000000 : ℝ) ≤
            (98758580012026564369 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (23302099992703 / 10000000000000000 : ℝ)) (q :=
      (2600735172932703 / 20000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_6_13 :
    Uω (aρ 13) (bρ 13) (85815639 / 1000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_6_14 :
    Uω (aρ 14) (bρ 14) (85815639 / 1000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_6_15 :
    Uω (aρ 15) (bρ 15) (85815639 / 1000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_6_16 :
    Uω (aρ 16) (bρ 16) (85815639 / 1000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_6 :
    Uρ (85815639 / 1000000000000 : ℝ) ≤
      (-(27537256492584381318183 / 10000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (85815639 / 1000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(10199318023215378615661 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_6_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (85815639 / 1000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(49220252785694328798381 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_6_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (85815639 / 1000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(23206381385399735792023 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_6_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (85815639 / 1000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(21510644677510011539679 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_6_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (85815639 / 1000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) * (-(315358759639002277023 / 80000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_6_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (85815639 / 1000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(35861726381563634540717 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_6_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (85815639 / 1000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(32497938712340042706679 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_6_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (85815639 / 1000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(29411142977102807541847 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_6_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (85815639 / 1000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(6660859717657794390429 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_6_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (85815639 / 1000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(4842885154875601165287 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_6_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (85815639 / 1000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(4426395685635096752489 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_6_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (85815639 / 1000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(5099845272237973435631 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_6_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (85815639 / 1000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_6_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (85815639 / 1000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_6_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (85815639 / 1000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_6_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (85815639 / 1000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_6_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_7_1 :
    Uω (aρ 1) (bρ 1) (19269871 / 200000000000 : ℝ) ≤
      (-(25507332223904240133213 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6087812562877 / 1000000000000000 : ℝ) ≤
      (-(25507332223904240133213 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (6087812562877 / 1000000000000000 : ℝ) = (6087812562877 / 3906250000000 : ℝ) / 2 ^ 8
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (6087812562877 / 3906250000000 : ℝ) ≤
            (2218554988095759866787 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (2911126336127 / 500000000000000 : ℝ)) (q :=
      (6087812562877 / 1000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_7_2 :
    Uω (aρ 2) (bρ 2) (19269871 / 200000000000 : ℝ) ≤
      (-(30773969948474174723 / 6250000000000000000 : ℝ)) := by
  have hlg :
    Real.log (145423817540153 / 20000000000000000 : ℝ) ≤
      (-(30773969948474174723 / 6250000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show
          (145423817540153 / 20000000000000000 : ℝ) =
            (145423817540153 / 78125000000000 : ℝ) / 2 ^ 8
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (145423817540153 / 78125000000000 : ℝ) ≤
            (3883389066525825277 / 6250000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (58121080495153 / 10000000000000000 : ℝ)) (q :=
      (145423817540153 / 20000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_7_3 :
    Uω (aρ 3) (bρ 3) (19269871 / 200000000000 : ℝ) ≤
      (-(23215465152356514085683 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (192557444123869 / 20000000000000000 : ℝ) ≤
      (-(23215465152356514085683 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show
          (192557444123869 / 20000000000000000 : ℝ) =
            (192557444123869 / 156250000000000 : ℝ) / 2 ^ 7
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (192557444123869 / 156250000000000 : ℝ) ≤
            (1044686158143485914317 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (57858600728869 / 10000000000000000 : ℝ)) (q :=
      (192557444123869 / 20000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_7_4 :
    Uω (aρ 4) (bρ 4) (19269871 / 200000000000 : ℝ) ≤
      (-(21519804344189444452201 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13514921999703 / 1000000000000000 : ℝ) ≤
      (-(21519804344189444452201 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show
          (13514921999703 / 1000000000000000 : ℝ) = (13514921999703 / 7812500000000 : ℝ) / 2 ^ 7
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (13514921999703 / 7812500000000 : ℝ) ≤
            (2740346966310555547799 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (2865270776703 / 500000000000000 : ℝ)) (q :=
      (13514921999703 / 1000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_7_5 :
    Uω (aρ 5) (bρ 5) (19269871 / 200000000000 : ℝ) ≤
      (-(315507654980808174019 / 80000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (77494266368633 / 4000000000000000 : ℝ) ≤
      (-(315507654980808174019 / 80000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show
          (77494266368633 / 4000000000000000 : ℝ) = (77494266368633 / 62500000000000 : ℝ) / 2 ^ 6
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (77494266368633 / 62500000000000 : ℝ) ≤
            (17202991563191825981 / 80000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (11257677609633 / 2000000000000000 : ℝ)) (q :=
      (77494266368633 / 4000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_7_6 :
    Uω (aρ 6) (bρ 6) (19269871 / 200000000000 : ℝ) ≤
      (-(8970212877133828550347 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (553024552971181 / 20000000000000000 : ℝ) ≤
      (-(8970212877133828550347 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show
          (553024552971181 / 20000000000000000 : ℝ) =
            (553024552971181 / 312500000000000 : ℝ) / 2 ^ 6
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (553024552971181 / 312500000000000 : ℝ) ≤
            (1426994827366171449653 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (54601234036181 / 10000000000000000 : ℝ)) (q :=
      (553024552971181 / 20000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_7_7 :
    Uω (aρ 7) (bρ 7) (19269871 / 200000000000 : ℝ) ≤
      (-(32517914390293590790913 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (154819233332697 / 4000000000000000 : ℝ) ≤
      (-(32517914390293590790913 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show
          (154819233332697 / 4000000000000000 : ℝ) =
            (154819233332697 / 125000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (154819233332697 / 125000000000000 : ℝ) ≤
            (2139444624706409209087 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (10402293393697 / 2000000000000000 : ℝ)) (q :=
      (154819233332697 / 4000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_7_8 :
    Uω (aρ 8) (bρ 8) (19269871 / 200000000000 : ℝ) ≤
      (-(5886499166201685248543 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (210776863658177 / 4000000000000000 : ℝ) ≤
      (-(5886499166201685248543 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show
          (210776863658177 / 4000000000000000 : ℝ) =
            (210776863658177 / 125000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (210776863658177 / 125000000000000 : ℝ) ≤
            (1044972636798314751457 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (9651593451177 / 2000000000000000 : ℝ)) (q :=
      (210776863658177 / 4000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_7_9 :
    Uω (aρ 9) (bρ 9) (19269871 / 200000000000 : ℝ) ≤
      (-(42667279831309115271 / 16000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (694807884018587 / 10000000000000000 : ℝ) ≤
      (-(42667279831309115271 / 16000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (694807884018587 / 10000000000000000 : ℝ) =
            (694807884018587 / 625000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (694807884018587 / 625000000000000 : ℝ) ≤
            (1694139707890884729 / 16000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (21511894321087 / 5000000000000000 : ℝ)) (q :=
      (694807884018587 / 10000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_7_10 :
    Uω (aρ 10) (bρ 10) (19269871 / 200000000000 : ℝ) ≤
      (-(606049641346655113191 / 250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (885490567993697 / 10000000000000000 : ℝ) ≤
      (-(606049641346655113191 / 250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (885490567993697 / 10000000000000000 : ℝ) =
            (885490567993697 / 625000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (885490567993697 / 625000000000000 : ℝ) ≤
            (87097538953344886809 / 250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (17915061548697 / 5000000000000000 : ℝ)) (q :=
      (885490567993697 / 10000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_7_11 :
    Uω (aρ 11) (bρ 11) (19269871 / 200000000000 : ℝ) ≤
      (-(22167783768353140953257 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2179191411148691 / 20000000000000000 : ℝ) ≤
      (-(22167783768353140953257 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (2179191411148691 / 20000000000000000 : ℝ) =
            (2179191411148691 / 1250000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2179191411148691 / 1250000000000000 : ℝ) ≤
            (5558103443646859046743 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (25563772053691 / 10000000000000000 : ℝ)) (q :=
      (2179191411148691 / 20000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_7_12 :
    Uω (aρ 12) (bρ 12) (19269871 / 200000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_7_13 :
    Uω (aρ 13) (bρ 13) (19269871 / 200000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_7_14 :
    Uω (aρ 14) (bρ 14) (19269871 / 200000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_7_15 :
    Uω (aρ 15) (bρ 15) (19269871 / 200000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_7_16 :
    Uω (aρ 16) (bρ 16) (19269871 / 200000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_7 :
    Uρ (19269871 / 200000000000 : ℝ) ≤ (-(6889957110960769864817 / 2500000000000000000000 : ℝ)) :=
  by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (19269871 / 200000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(25507332223904240133213 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_7_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (19269871 / 200000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) * (-(30773969948474174723 / 6250000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_7_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (19269871 / 200000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(23215465152356514085683 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_7_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (19269871 / 200000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(21519804344189444452201 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_7_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (19269871 / 200000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) * (-(315507654980808174019 / 80000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_7_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (19269871 / 200000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(8970212877133828550347 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_7_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (19269871 / 200000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(32517914390293590790913 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_7_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (19269871 / 200000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(5886499166201685248543 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_7_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (19269871 / 200000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(42667279831309115271 / 16000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_7_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (19269871 / 200000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) * (-(606049641346655113191 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_7_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (19269871 / 200000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(22167783768353140953257 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_7_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (19269871 / 200000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) * (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_7_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (19269871 / 200000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_7_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (19269871 / 200000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_7_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (19269871 / 200000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_7_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (19269871 / 200000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_7_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_8_1 :
    Uω (aρ 1) (bρ 1) (55761057 / 500000000000 : ℝ) ≤
      (-(51040761523417755773563 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (30359729325639 / 5000000000000000 : ℝ) ≤
      (-(51040761523417755773563 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show
          (30359729325639 / 5000000000000000 : ℝ) = (30359729325639 / 19531250000000 : ℝ) / 2 ^ 8
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (30359729325639 / 19531250000000 : ℝ) ≤
            (4411012900582244226437 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (14514230089389 / 2500000000000000 : ℝ)) (q :=
      (30359729325639 / 5000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_8_2 :
    Uω (aρ 2) (bρ 2) (55761057 / 500000000000 : ℝ) ≤
      (-(12316127176026878844577 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9065245788109 / 1250000000000000 : ℝ) ≤
      (-(12316127176026878844577 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show (9065245788109 / 1250000000000000 : ℝ) = (9065245788109 / 4882812500000 : ℝ) / 2 ^ 8
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9065245788109 / 4882812500000 : ℝ) ≤
            (1546816429973121155423 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (7236615394343 / 1250000000000000 : ℝ)) (q :=
      (9065245788109 / 1250000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_8_3 :
    Uω (aρ 3) (bρ 3) (55761057 / 500000000000 : ℝ) ≤
      (-(46457234677264518279157 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (96025799718557 / 10000000000000000 : ℝ) ≤
      (-(46457234677264518279157 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show
          (96025799718557 / 10000000000000000 : ℝ) = (96025799718557 / 78125000000000 : ℝ) / 2 ^ 7
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (96025799718557 / 78125000000000 : ℝ) ≤
            (2063067943735481720843 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (28752241816057 / 5000000000000000 : ℝ)) (q :=
      (96025799718557 / 10000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_8_4 :
    Uω (aρ 4) (bρ 4) (55761057 / 500000000000 : ℝ) ≤
      (-(21533108620975871780131 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (269580170970713 / 20000000000000000 : ℝ) ≤
      (-(21533108620975871780131 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show
          (269580170970713 / 20000000000000000 : ℝ) =
            (269580170970713 / 156250000000000 : ℝ) / 2 ^ 7
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (269580170970713 / 156250000000000 : ℝ) ≤
            (2727042689524128219869 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (56738874100713 / 10000000000000000 : ℝ)) (q :=
      (269580170970713 / 20000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_8_5 :
    Uω (aρ 5) (bρ 5) (55761057 / 500000000000 : ℝ) ≤
      (-(1578625177908711877893 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (96604975401611 / 5000000000000000 : ℝ) ≤
      (-(1578625177908711877893 / 400000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show
          (96604975401611 / 5000000000000000 : ℝ) = (96604975401611 / 78125000000000 : ℝ) / 2 ^ 6
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (96604975401611 / 78125000000000 : ℝ) ≤
            (84928054811288122107 / 400000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (13847171350361 / 2500000000000000 : ℝ)) (q :=
      (96604975401611 / 5000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_8_6 :
    Uω (aρ 6) (bρ 6) (55761057 / 500000000000 : ℝ) ≤
      (-(897725036415218135001 / 250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (275734990404539 / 10000000000000000 : ℝ) ≤
      (-(897725036415218135001 / 250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show
          (275734990404539 / 10000000000000000 : ℝ) =
            (275734990404539 / 156250000000000 : ℝ) / 2 ^ 6
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (275734990404539 / 156250000000000 : ℝ) ≤
            (141995734034781864999 / 250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (26599194732039 / 5000000000000000 : ℝ)) (q :=
      (275734990404539 / 10000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_8_7 :
    Uω (aρ 7) (bρ 7) (55761057 / 500000000000 : ℝ) ≤
      (-(16273851117356851483897 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (96474216497051 / 2500000000000000 : ℝ) ≤
      (-(16273851117356851483897 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show
          (96474216497051 / 2500000000000000 : ℝ) = (96474216497051 / 78125000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (96474216497051 / 78125000000000 : ℝ) ≤
            (1054828390143148516103 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (3116297491963 / 625000000000000 : ℝ)) (q :=
      (96474216497051 / 2500000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_8_8 :
    Uω (aρ 8) (bρ 8) (55761057 / 500000000000 : ℝ) ≤
      (-(7366260065742286983877 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (525230043323873 / 10000000000000000 : ℝ) ≤
      (-(7366260065742286983877 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show
          (525230043323873 / 10000000000000000 : ℝ) =
            (525230043323873 / 312500000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (525230043323873 / 312500000000000 : ℝ) ≤
            (1298079688007713016123 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (22492731601373 / 5000000000000000 : ℝ)) (q :=
      (525230043323873 / 10000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_8_9 :
    Uω (aρ 9) (bρ 9) (55761057 / 500000000000 : ℝ) ≤
      (-(26704512040091709661141 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (276883941615867 / 4000000000000000 : ℝ) ≤
      (-(26704512040091709661141 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (276883941615867 / 4000000000000000 : ℝ) =
            (276883941615867 / 250000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (276883941615867 / 250000000000000 : ℝ) ≤
            (1021375171908290338859 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (7595891254867 / 2000000000000000 : ℝ)) (q :=
      (276883941615867 / 4000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_8_10 :
    Uω (aρ 10) (bρ 10) (55761057 / 500000000000 : ℝ) ≤
      (-(24289887987277840384009 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1762518009461781 / 20000000000000000 : ℝ) ≤
      (-(24289887987277840384009 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (1762518009461781 / 20000000000000000 : ℝ) =
            (1762518009461781 / 1250000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1762518009461781 / 1250000000000000 : ℝ) ≤
            (3435999224722159615991 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (27518724161781 / 10000000000000000 : ℝ)) (q :=
      (1762518009461781 / 20000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_8_11 :
    Uω (aρ 11) (bρ 11) (55761057 / 500000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_8_12 :
    Uω (aρ 12) (bρ 12) (55761057 / 500000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_8_13 :
    Uω (aρ 13) (bρ 13) (55761057 / 500000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_8_14 :
    Uω (aρ 14) (bρ 14) (55761057 / 500000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_8_15 :
    Uω (aρ 15) (bρ 15) (55761057 / 500000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_8_16 :
    Uω (aρ 16) (bρ 16) (55761057 / 500000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_8 :
    Uρ (55761057 / 500000000000 : ℝ) ≤ (-(5517964148274383717247 / 2000000000000000000000 : ℝ)) :=
  by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (55761057 / 500000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) *
        (-(51040761523417755773563 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_8_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (55761057 / 500000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(12316127176026878844577 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_8_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (55761057 / 500000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(46457234677264518279157 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_8_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (55761057 / 500000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(21533108620975871780131 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_8_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (55761057 / 500000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) * (-(1578625177908711877893 / 400000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_8_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (55761057 / 500000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(897725036415218135001 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_8_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (55761057 / 500000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(16273851117356851483897 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_8_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (55761057 / 500000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(7366260065742286983877 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_8_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (55761057 / 500000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(26704512040091709661141 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_8_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (55761057 / 500000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(24289887987277840384009 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_8_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (55761057 / 500000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_8_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (55761057 / 500000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) * (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_8_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (55761057 / 500000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_8_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (55761057 / 500000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_8_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (55761057 / 500000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_8_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (55761057 / 500000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_8_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_9_1 :
    Uω (aρ 1) (bρ 1) (33336783 / 250000000000 : ℝ) ≤
      (-(10215686268319257150869 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (30245579911641 / 5000000000000000 : ℝ) ≤
      (-(10215686268319257150869 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show
          (30245579911641 / 5000000000000000 : ℝ) = (30245579911641 / 19531250000000 : ℝ) / 2 ^ 8
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (30245579911641 / 19531250000000 : ℝ) ≤
            (874668616480742849131 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (14454643220391 / 2500000000000000 : ℝ)) (q :=
      (30245579911641 / 5000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_9_2 :
    Uω (aρ 2) (bρ 2) (33336783 / 250000000000 : ℝ) ≤
      (-(9860463027542453411111 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (72248304249749 / 10000000000000000 : ℝ) ≤
      (-(9860463027542453411111 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show
          (72248304249749 / 10000000000000000 : ℝ) = (72248304249749 / 39062500000000 : ℝ) / 2 ^ 8
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (72248304249749 / 39062500000000 : ℝ) ≤
            (1229891857257546588889 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (28781924612249 / 5000000000000000 : ℝ)) (q :=
      (72248304249749 / 10000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_9_3 :
    Uω (aρ 3) (bρ 3) (33336783 / 250000000000 : ℝ) ≤
      (-(46495358210023539812961 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4783020619089 / 500000000000000 : ℝ) ≤
      (-(46495358210023539812961 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show (4783020619089 / 500000000000000 : ℝ) = (4783020619089 / 3906250000000 : ℝ) / 2 ^ 7
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4783020619089 / 3906250000000 : ℝ) ≤
            (2024944410976460187039 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (44524968077 / 7812500000000 : ℝ)) (q :=
      (4783020619089 / 500000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_9_4 :
    Uω (aρ 4) (bρ 4) (33336783 / 250000000000 : ℝ) ≤
      (-(21552482231997735895661 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (67134410938101 / 5000000000000000 : ℝ) ≤
      (-(21552482231997735895661 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show
          (67134410938101 / 5000000000000000 : ℝ) = (67134410938101 / 39062500000000 : ℝ) / 2 ^ 7
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (67134410938101 / 39062500000000 : ℝ) ≤
            (2707669078502264104339 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (13978649265601 / 2500000000000000 : ℝ)) (q :=
      (67134410938101 / 5000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_9_5 :
    Uω (aρ 5) (bρ 5) (33336783 / 250000000000 : ℝ) ≤
      (-(19752753975247025066761 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (240551240889 / 12500000000000 : ℝ) ≤
      (-(19752753975247025066761 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show (240551240889 / 12500000000000 : ℝ) = (240551240889 / 195312500000 : ℝ) / 2 ^ 6 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (240551240889 / 195312500000 : ℝ) ≤
            (1041661433752974933239 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (270345096987 / 50000000000000 : ℝ)) (q :=
      (240551240889 / 12500000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_9_6 :
    Uω (aρ 6) (bρ 6) (33336783 / 250000000000 : ℝ) ≤
      (-(17975423546595465917579 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13729178527969 / 500000000000000 : ℝ) ≤
      (-(17975423546595465917579 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show
          (13729178527969 / 500000000000000 : ℝ) = (13729178527969 / 7812500000000 : ℝ) / 2 ^ 6 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (13729178527969 / 7812500000000 : ℝ) ≤
            (2818991862404534082421 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (319461249711 / 62500000000000 : ℝ)) (q :=
      (13729178527969 / 500000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_9_7 :
    Uω (aρ 7) (bρ 7) (33336783 / 250000000000 : ℝ) ≤
      (-(6518591326819602089771 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (768308916905443 / 20000000000000000 : ℝ) ≤
      (-(6518591326819602089771 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show
          (768308916905443 / 20000000000000000 : ℝ) =
            (768308916905443 / 625000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (768308916905443 / 625000000000000 : ℝ) ≤
            (412880476180397910229 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (46594194980443 / 10000000000000000 : ℝ)) (q :=
      (768308916905443 / 20000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_9_8 :
    Uω (aρ 8) (bρ 8) (33336783 / 250000000000 : ℝ) ≤
      (-(14758258563778426940663 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1045066541533949 / 20000000000000000 : ℝ) ≤
      (-(14758258563778426940663 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show
          (1045066541533949 / 20000000000000000 : ℝ) =
            (1045066541533949 / 625000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1045066541533949 / 625000000000000 : ℝ) ≤
            (2570420943721573059337 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (39810168268949 / 10000000000000000 : ℝ)) (q :=
      (1045066541533949 / 20000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_9_9 :
    Uω (aρ 9) (bρ 9) (33336783 / 250000000000 : ℝ) ≤
      (-(5353890477833411319021 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1375458367291817 / 20000000000000000 : ℝ) ≤
      (-(5353890477833411319021 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 4
        (show
          (1375458367291817 / 20000000000000000 : ℝ) =
            (1375458367291817 / 1250000000000000 : ℝ) / 2 ^ 4
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1375458367291817 / 1250000000000000 : ℝ) ≤
            (191286964566588680979 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (29236365666817 / 10000000000000000 : ℝ)) (q :=
      (1375458367291817 / 20000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_9_10 :
    Uω (aρ 10) (bρ 10) (33336783 / 250000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_9_11 :
    Uω (aρ 11) (bρ 11) (33336783 / 250000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_9_12 :
    Uω (aρ 12) (bρ 12) (33336783 / 250000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_9_13 :
    Uω (aρ 13) (bρ 13) (33336783 / 250000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_9_14 :
    Uω (aρ 14) (bρ 14) (33336783 / 250000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_9_15 :
    Uω (aρ 15) (bρ 15) (33336783 / 250000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_9_16 :
    Uω (aρ 16) (bρ 16) (33336783 / 250000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_9 :
    Uρ (33336783 / 250000000000 : ℝ) ≤ (-(6907239882122678168379 / 2500000000000000000000 : ℝ)) :=
  by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (33336783 / 250000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(10215686268319257150869 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_9_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (33336783 / 250000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(9860463027542453411111 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_9_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (33336783 / 250000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(46495358210023539812961 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_9_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (33336783 / 250000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(21552482231997735895661 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_9_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (33336783 / 250000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(19752753975247025066761 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_9_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (33336783 / 250000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(17975423546595465917579 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_9_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (33336783 / 250000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(6518591326819602089771 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_9_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (33336783 / 250000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(14758258563778426940663 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_9_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (33336783 / 250000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(5353890477833411319021 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_9_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (33336783 / 250000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_9_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (33336783 / 250000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_9_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (33336783 / 250000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) * (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_9_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (33336783 / 250000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_9_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (33336783 / 250000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_9_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (33336783 / 250000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_9_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (33336783 / 250000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_9_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_10_1 :
    Uω (aρ 1) (bρ 1) (82548843 / 500000000000 : ℝ) ≤
      (-(51133510883215947535941 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (24063557272999 / 4000000000000000 : ℝ) ≤
      (-(51133510883215947535941 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show
          (24063557272999 / 4000000000000000 : ℝ) = (24063557272999 / 15625000000000 : ℝ) / 2 ^ 8
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (24063557272999 / 15625000000000 : ℝ) ≤
            (4318263540784052464059 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (11494309027999 / 2000000000000000 : ℝ)) (q :=
      (24063557272999 / 4000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_10_2 :
    Uω (aρ 2) (bρ 2) (82548843 / 500000000000 : ℝ) ≤
      (-(24678851808854408309657 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (143698476155901 / 20000000000000000 : ℝ) ≤
      (-(24678851808854408309657 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show
          (143698476155901 / 20000000000000000 : ℝ) =
            (143698476155901 / 78125000000000 : ℝ) / 2 ^ 8
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (143698476155901 / 78125000000000 : ℝ) ≤
            (3047035403145591690343 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (57083222420901 / 10000000000000000 : ℝ)) (q :=
      (143698476155901 / 20000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_10_3 :
    Uω (aρ 3) (bρ 3) (82548843 / 500000000000 : ℝ) ≤
      (-(5818929893213673684367 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (23781360331077 / 2500000000000000 : ℝ) ≤
      (-(5818929893213673684367 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show
          (23781360331077 / 2500000000000000 : ℝ) = (23781360331077 / 19531250000000 : ℝ) / 2 ^ 7
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (23781360331077 / 19531250000000 : ℝ) ≤
            (246107934411326315633 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (1757485080113 / 312500000000000 : ℝ)) (q :=
      (23781360331077 / 2500000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_10_4 :
    Uω (aρ 4) (bρ 4) (82548843 / 500000000000 : ℝ) ≤
      (-(43162374832339657159807 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (133500188112619 / 10000000000000000 : ℝ) ≤
      (-(43162374832339657159807 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show
          (133500188112619 / 10000000000000000 : ℝ) =
            (133500188112619 / 78125000000000 : ℝ) / 2 ^ 7
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (133500188112619 / 78125000000000 : ℝ) ≤
            (5357927788660342840193 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (27347417537619 / 5000000000000000 : ℝ)) (q :=
      (133500188112619 / 10000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_10_5 :
    Uω (aρ 5) (bρ 5) (82548843 / 500000000000 : ℝ) ≤
      (-(39565324440062555612331 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (95646657087479 / 5000000000000000 : ℝ) ≤
      (-(39565324440062555612331 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show
          (95646657087479 / 5000000000000000 : ℝ) = (95646657087479 / 78125000000000 : ℝ) / 2 ^ 6
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (95646657087479 / 78125000000000 : ℝ) ≤
            (2023506377937444387669 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (13022791966229 / 2500000000000000 : ℝ)) (q :=
      (95646657087479 / 5000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_10_6 :
    Uω (aρ 6) (bρ 6) (82548843 / 500000000000 : ℝ) ≤
      (-(36014967106290014530057 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (272828572881853 / 10000000000000000 : ℝ) ≤
      (-(36014967106290014530057 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show
          (272828572881853 / 10000000000000000 : ℝ) =
            (272828572881853 / 156250000000000 : ℝ) / 2 ^ 6
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (272828572881853 / 156250000000000 : ℝ) ≤
            (5573863711709985469943 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (23960655069353 / 5000000000000000 : ℝ)) (q :=
      (272828572881853 / 10000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_10_7 :
    Uω (aρ 7) (bρ 7) (82548843 / 500000000000 : ℝ) ≤
      (-(8166283330872021732883 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (762783481867911 / 20000000000000000 : ℝ) ≤
      (-(8166283330872021732883 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show
          (762783481867911 / 20000000000000000 : ℝ) =
            (762783481867911 / 625000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (762783481867911 / 625000000000000 : ℝ) ≤
            (498056422877978267117 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (41386265482911 / 10000000000000000 : ℝ)) (q :=
      (762783481867911 / 20000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_10_8 :
    Uω (aρ 8) (bρ 8) (82548843 / 500000000000 : ℝ) ≤
      (-(592129837744490728151 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (517852877658559 / 10000000000000000 : ℝ) ≤
      (-(592129837744490728151 / 200000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show
          (517852877658559 / 10000000000000000 : ℝ) =
            (517852877658559 / 312500000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (517852877658559 / 312500000000000 : ℝ) ≤
            (101017342555509271849 / 200000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (15383443796059 / 5000000000000000 : ℝ)) (q :=
      (517852877658559 / 10000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_10_9 :
    Uω (aρ 9) (bρ 9) (82548843 / 500000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_10_10 :
    Uω (aρ 10) (bρ 10) (82548843 / 500000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_10_11 :
    Uω (aρ 11) (bρ 11) (82548843 / 500000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_10_12 :
    Uω (aρ 12) (bρ 12) (82548843 / 500000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_10_13 :
    Uω (aρ 13) (bρ 13) (82548843 / 500000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_10_14 :
    Uω (aρ 14) (bρ 14) (82548843 / 500000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_10_15 :
    Uω (aρ 15) (bρ 15) (82548843 / 500000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_10_16 :
    Uω (aρ 16) (bρ 16) (82548843 / 500000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_10 :
    Uρ (82548843 / 500000000000 : ℝ) ≤ (-(1107174623610650247861 / 400000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (82548843 / 500000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) *
        (-(51133510883215947535941 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_10_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (82548843 / 500000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(24678851808854408309657 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_10_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (82548843 / 500000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(5818929893213673684367 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_10_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (82548843 / 500000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(43162374832339657159807 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_10_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (82548843 / 500000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(39565324440062555612331 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_10_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (82548843 / 500000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(36014967106290014530057 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_10_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (82548843 / 500000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(8166283330872021732883 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_10_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (82548843 / 500000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(592129837744490728151 / 200000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_10_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (82548843 / 500000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_10_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (82548843 / 500000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_10_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (82548843 / 500000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_10_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (82548843 / 500000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) * (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_10_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (82548843 / 500000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_10_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (82548843 / 500000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_10_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (82548843 / 500000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_10_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (82548843 / 500000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_10_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_11_1 :
    Uω (aρ 1) (bρ 1) (53051547 / 250000000000 : ℝ) ≤
      (-(10243169805498114481613 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (119331179383113 / 20000000000000000 : ℝ) ≤
      (-(10243169805498114481613 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show
          (119331179383113 / 20000000000000000 : ℝ) =
            (119331179383113 / 78125000000000 : ℝ) / 2 ^ 8
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (119331179383113 / 78125000000000 : ℝ) ≤
            (847185079301885518387 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (56956023178113 / 10000000000000000 : ℝ)) (q :=
      (119331179383113 / 20000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_11_2 :
    Uω (aρ 2) (bρ 2) (53051547 / 250000000000 : ℝ) ≤
      (-(24720375964658024966207 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (17813753292691 / 2500000000000000 : ℝ) ≤
      (-(24720375964658024966207 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 8
        (show
          (17813753292691 / 2500000000000000 : ℝ) = (17813753292691 / 9765625000000 : ℝ) / 2 ^ 8
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (17813753292691 / 9765625000000 : ℝ) ≤
            (3005511247341975033793 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (1761433050829 / 312500000000000 : ℝ)) (q :=
      (17813753292691 / 2500000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_11_3 :
    Uω (aρ 3) (bρ 3) (53051547 / 250000000000 : ℝ) ≤
      (-(46636055244366115624033 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (94323922802349 / 10000000000000000 : ℝ) ≤
      (-(46636055244366115624033 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show
          (94323922802349 / 10000000000000000 : ℝ) = (94323922802349 / 78125000000000 : ℝ) / 2 ^ 7
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (94323922802349 / 78125000000000 : ℝ) ≤
            (1884247376633884375967 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (27553785269849 / 5000000000000000 : ℝ)) (q :=
      (94323922802349 / 10000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_11_4 :
    Uω (aρ 4) (bρ 4) (53051547 / 250000000000 : ℝ) ≤
      (-(21624996699245277221649 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (33083897021511 / 2500000000000000 : ℝ) ≤
      (-(21624996699245277221649 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 7
        (show
          (33083897021511 / 2500000000000000 : ℝ) = (33083897021511 / 19531250000000 : ℝ) / 2 ^ 7
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (33083897021511 / 19531250000000 : ℝ) ≤
            (2635154611254722778351 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (6604590005261 / 1250000000000000 : ℝ)) (q :=
      (33083897021511 / 2500000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_11_5 :
    Uω (aρ 5) (bρ 5) (53051547 / 250000000000 : ℝ) ≤
      (-(39658512652531402453443 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (189518966230509 / 10000000000000000 : ℝ) ≤
      (-(39658512652531402453443 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show
          (189518966230509 / 10000000000000000 : ℝ) =
            (189518966230509 / 156250000000000 : ℝ) / 2 ^ 6
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (189518966230509 / 156250000000000 : ℝ) ≤
            (1930318165468597546557 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (24506778498009 / 5000000000000000 : ℝ)) (q :=
      (189518966230509 / 10000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_11_6 :
    Uω (aρ 6) (bρ 6) (53051547 / 250000000000 : ℝ) ≤
      (-(18059438196821077208529 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (135004154291197 / 5000000000000000 : ℝ) ≤
      (-(18059438196821077208529 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 6
        (show
          (135004154291197 / 5000000000000000 : ℝ) =
            (135004154291197 / 78125000000000 : ℝ) / 2 ^ 6
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (135004154291197 / 78125000000000 : ℝ) ≤
            (2734977212178922791471 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (10687966639947 / 2500000000000000 : ℝ)) (q :=
      (135004154291197 / 5000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_11_7 :
    Uω (aρ 7) (bρ 7) (53051547 / 250000000000 : ℝ) ≤
      (-(6558653041860765113421 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (150614428548557 / 4000000000000000 : ℝ) ≤
      (-(6558653041860765113421 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 5
        (show
          (150614428548557 / 4000000000000000 : ℝ) =
            (150614428548557 / 125000000000000 : ℝ) / 2 ^ 5
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (150614428548557 / 125000000000000 : ℝ) ≤
            (372818761139234886579 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_left_certificate (s := (6429202275557 / 2000000000000000 : ℝ)) (q :=
      (150614428548557 / 4000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_11_8 :
    Uω (aρ 8) (bρ 8) (53051547 / 250000000000 : ℝ) ≤
      (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_8]) (by norm_num [bρ_8])]; exact Lmid_8

lemma U_11_9 :
    Uω (aρ 9) (bρ 9) (53051547 / 250000000000 : ℝ) ≤
      (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_9]) (by norm_num [bρ_9])]; exact Lmid_9

lemma U_11_10 :
    Uω (aρ 10) (bρ 10) (53051547 / 250000000000 : ℝ) ≤
      (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_10]) (by norm_num [bρ_10])]; exact Lmid_10

lemma U_11_11 :
    Uω (aρ 11) (bρ 11) (53051547 / 250000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

lemma U_11_12 :
    Uω (aρ 12) (bρ 12) (53051547 / 250000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

lemma U_11_13 :
    Uω (aρ 13) (bρ 13) (53051547 / 250000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

lemma U_11_14 :
    Uω (aρ 14) (bρ 14) (53051547 / 250000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

lemma U_11_15 :
    Uω (aρ 15) (bρ 15) (53051547 / 250000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

lemma U_11_16 :
    Uω (aρ 16) (bρ 16) (53051547 / 250000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_11 :
    Uρ (53051547 / 250000000000 : ℝ) ≤
      (-(13871992575163789919237 / 5000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (53051547 / 250000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(10243169805498114481613 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_11_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (53051547 / 250000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(24720375964658024966207 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_11_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (53051547 / 250000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(46636055244366115624033 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_11_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (53051547 / 250000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(21624996699245277221649 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_11_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (53051547 / 250000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(39658512652531402453443 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_11_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (53051547 / 250000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(18059438196821077208529 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_11_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (53051547 / 250000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(6558653041860765113421 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_11_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (53051547 / 250000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(14956372202312055299661 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_11_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (53051547 / 250000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(26986659976834617141369 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_11_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (53051547 / 250000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(12224255358108186379559 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_11_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (53051547 / 250000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_11_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (53051547 / 250000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) * (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_11_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (53051547 / 250000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_11_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (53051547 / 250000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_11_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (53051547 / 250000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_11_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (53051547 / 250000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_11_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

end Zeta5Irrational
