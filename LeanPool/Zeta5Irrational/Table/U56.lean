/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Table.UpperCertificate

/-! # Certified arcsine potential bounds (U56) -/

public section

open Finset

namespace Zeta5Irrational

lemma U_676_1 :
    Uω (aρ 1) (bρ 1) (7226461069683 / 8000000000000 : ℝ) ≤
      (-(108859842802811722997 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (358742443718067 / 400000000000000 : ℝ) ≤
      (-(108859842802811722997 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (358742443718067 / 400000000000000 : ℝ) =
            (358742443718067 / 200000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (358742443718067 / 200000000000000 : ℝ) ≤
            (584287337497188277003 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (44842715334423 / 50000000000000 : ℝ)) (q :=
      (358742443718067 / 400000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_676_2 :
    Uω (aρ 2) (bρ 2) (7226461069683 / 8000000000000 : ℝ) ≤
      (-(223049730527027750149 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (17889382993662361 / 20000000000000000 : ℝ) ≤
      (-(223049730527027750149 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (17889382993662361 / 20000000000000000 : ℝ) =
            (17889382993662361 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (17889382993662361 / 10000000000000000 : ℝ) ≤
            (1163244630072972249851 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (8944572887153611 / 10000000000000000 : ℝ)) (q :=
      (17889382993662361 / 20000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_676_3 :
    Uω (aρ 3) (bρ 3) (7226461069683 / 8000000000000 : ℝ) ≤
      (-(1168711495788115444963 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3558799294975663 / 4000000000000000 : ℝ) ≤
      (-(1168711495788115444963 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (3558799294975663 / 4000000000000000 : ℝ) =
            (3558799294975663 / 2000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3558799294975663 / 2000000000000000 : ℝ) ≤
            (5762760307211884555037 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1779316494943913 / 2000000000000000 : ℝ)) (q :=
      (3558799294975663 / 4000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_676_4 :
    Uω (aρ 4) (bρ 4) (7226461069683 / 8000000000000 : ℝ) ≤
      (-(628991572116585160863 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8817926734849447 / 10000000000000000 : ℝ) ≤
      (-(628991572116585160863 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (8817926734849447 / 10000000000000000 : ℝ) =
            (8817926734849447 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (8817926734849447 / 5000000000000000 : ℝ) ≤
            (2836744329383414839137 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1102091706325643 / 1250000000000000 : ℝ)) (q :=
      (8817926734849447 / 10000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_676_5 :
    Uω (aρ 5) (bρ 5) (7226461069683 / 8000000000000 : ℝ) ≤
      (-(55802843000971698371 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1087233551180307 / 1250000000000000 : ℝ) ≤
      (-(55802843000971698371 / 400000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (1087233551180307 / 1250000000000000 : ℝ) =
            (1087233551180307 / 625000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1087233551180307 / 625000000000000 : ℝ) ≤
            (221456029119028301629 / 400000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4347403459563081 / 5000000000000000 : ℝ)) (q :=
      (1087233551180307 / 1250000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_676_6 :
    Uω (aρ 6) (bρ 6) (7226461069683 / 8000000000000 : ℝ) ≤
      (-(398517382703400588829 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1705298599747893 / 2000000000000000 : ℝ) ≤
      (-(398517382703400588829 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (1705298599747893 / 2000000000000000 : ℝ) =
            (1705298599747893 / 1000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1705298599747893 / 1000000000000000 : ℝ) ≤
            (1334350568046599411171 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (425964823643009 / 500000000000000 : ℝ)) (q :=
      (1705298599747893 / 2000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_676_7 :
    Uω (aρ 7) (bρ 7) (7226461069683 / 8000000000000 : ℝ) ≤
      (-(1870052209910470026807 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (16588788113255563 / 20000000000000000 : ℝ) ≤
      (-(1870052209910470026807 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (16588788113255563 / 20000000000000000 : ℝ) =
            (16588788113255563 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (16588788113255563 / 10000000000000000 : ℝ) ≤
            (5061419593089529973193 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (8278759969396813 / 10000000000000000 : ℝ)) (q :=
      (16588788113255563 / 20000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_676_8 :
    Uω (aρ 8) (bρ 8) (7226461069683 / 8000000000000 : ℝ) ≤
      (-(1118883342221099544697 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3997468331946279 / 5000000000000000 : ℝ) ≤
      (-(1118883342221099544697 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (3997468331946279 / 5000000000000000 : ℝ) =
            (3997468331946279 / 2500000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3997468331946279 / 2500000000000000 : ℝ) ≤
            (2346852559278900455303 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3981693417633183 / 5000000000000000 : ℝ)) (q :=
      (3997468331946279 / 5000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_676_9 :
    Uω (aρ 9) (bρ 9) (7226461069683 / 8000000000000 : ℝ) ≤
      (-(2710035841923158558309 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1906534407118849 / 2500000000000000 : ℝ) ≤
      (-(2710035841923158558309 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (1906534407118849 / 2500000000000000 : ℝ) =
            (1906534407118849 / 1250000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1906534407118849 / 1250000000000000 : ℝ) ≤
            (4221435961076841441691 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3783377196396021 / 5000000000000000 : ℝ)) (q :=
      (1906534407118849 / 2500000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_676_10 :
    Uω (aρ 10) (bρ 10) (7226461069683 / 8000000000000 : ℝ) ≤
      (-(3295663745591862291993 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7192355444655383 / 10000000000000000 : ℝ) ≤
      (-(3295663745591862291993 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (7192355444655383 / 10000000000000000 : ℝ) =
            (7192355444655383 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7192355444655383 / 5000000000000000 : ℝ) ≤
            (3635808057408137708007 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (885968632330877 / 1250000000000000 : ℝ)) (q :=
      (7192355444655383 / 10000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_676_11 :
    Uω (aρ 11) (bρ 11) (7226461069683 / 8000000000000 : ℝ) ≤
      (-(999108980076215164303 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6705589958471729 / 10000000000000000 : ℝ) ≤
      (-(999108980076215164303 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (6705589958471729 / 10000000000000000 : ℝ) =
            (6705589958471729 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (6705589958471729 / 5000000000000000 : ℝ) ≤
            (733758970673784835697 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1633173678121177 / 2500000000000000 : ℝ)) (q :=
      (6705589958471729 / 10000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_676_12 :
    Uω (aρ 12) (bρ 12) (7226461069683 / 8000000000000 : ℝ) ≤
      (-(4802404152764222826933 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (618634644546397 / 1000000000000000 : ℝ) ≤
      (-(4802404152764222826933 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (618634644546397 / 1000000000000000 : ℝ) =
            (618634644546397 / 500000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (618634644546397 / 500000000000000 : ℝ) ≤
            (2129067650235777173067 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (591790778315419 / 1000000000000000 : ℝ)) (q :=
      (618634644546397 / 1000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12]) (by norm_num [bρ_12])
      (by norm_num) (by norm_num [aρ_12, bρ_12]) (by norm_num [aρ_12, bρ_12]) hlg

lemma U_676_13 :
    Uω (aρ 13) (bρ 13) (7226461069683 / 8000000000000 : ℝ) ≤
      (-(2842013848850894396079 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (11328588692629349 / 20000000000000000 : ℝ) ≤
      (-(2842013848850894396079 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (11328588692629349 / 20000000000000000 : ℝ) =
            (11328588692629349 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (11328588692629349 / 10000000000000000 : ℝ) ≤
            (623722052649105603921 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (5273185326450599 / 10000000000000000 : ℝ)) (q :=
      (11328588692629349 / 20000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_676_14 :
    Uω (aρ 14) (bρ 14) (7226461069683 / 8000000000000 : ℝ) ≤
      (-(6579422346950211503277 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1294789970322837 / 2500000000000000 : ℝ) ≤
      (-(6579422346950211503277 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (1294789970322837 / 2500000000000000 : ℝ) =
            (1294789970322837 / 1250000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1294789970322837 / 1250000000000000 : ℝ) ≤
            (352049456049788496723 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2323421840724473 / 5000000000000000 : ℝ)) (q :=
      (1294789970322837 / 2500000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_676_15 :
    Uω (aρ 15) (bρ 15) (7226461069683 / 8000000000000 : ℝ) ≤
      (-(7377973537692901902479 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4781659866852911 / 10000000000000000 : ℝ) ≤
      (-(7377973537692901902479 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (4781659866852911 / 10000000000000000 : ℝ) =
            (4781659866852911 / 2500000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4781659866852911 / 2500000000000000 : ℝ) ≤
            (6484970068307098097521 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (8030111191381 / 19531250000000 : ℝ)) (q :=
      (4781659866852911 / 10000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_676_16 :
    Uω (aρ 16) (bρ 16) (7226461069683 / 8000000000000 : ℝ) ≤
      (-(7917178800593945107141 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4530658134130151 / 10000000000000000 : ℝ) ≤
      (-(7917178800593945107141 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (4530658134130151 / 10000000000000000 : ℝ) =
            (4530658134130151 / 2500000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4530658134130151 / 2500000000000000 : ℝ) ≤
            (5945764805406054892859 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (117555784876611 / 312500000000000 : ℝ)) (q :=
      (4530658134130151 / 10000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_676 :
    Uρ (7226461069683 / 8000000000000 : ℝ) ≤
      (-(352383937996564167861 / 1250000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (7226461069683 / 8000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(108859842802811722997 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_676_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (7226461069683 / 8000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(223049730527027750149 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_676_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (7226461069683 / 8000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(1168711495788115444963 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_676_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (7226461069683 / 8000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(628991572116585160863 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_676_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (7226461069683 / 8000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) * (-(55802843000971698371 / 400000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_676_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (7226461069683 / 8000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(398517382703400588829 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_676_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (7226461069683 / 8000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(1870052209910470026807 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_676_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (7226461069683 / 8000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(1118883342221099544697 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_676_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (7226461069683 / 8000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(2710035841923158558309 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_676_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (7226461069683 / 8000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(3295663745591862291993 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_676_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (7226461069683 / 8000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(999108980076215164303 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_676_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (7226461069683 / 8000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(4802404152764222826933 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_676_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (7226461069683 / 8000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(2842013848850894396079 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_676_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (7226461069683 / 8000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(6579422346950211503277 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_676_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (7226461069683 / 8000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(7377973537692901902479 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_676_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (7226461069683 / 8000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(7917178800593945107141 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_676_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_677_1 :
    Uω (aρ 1) (bρ 1) (30159206983063 / 32000000000000 : ℝ) ≤
      (-(82643010106364090371 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (37440950769403939 / 40000000000000000 : ℝ) ≤
      (-(82643010106364090371 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (37440950769403939 / 40000000000000000 : ℝ) =
            (37440950769403939 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (37440950769403939 / 20000000000000000 : ℝ) ≤
            (783790965268635909629 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4680110210289891 / 5000000000000000 : ℝ)) (q :=
      (37440950769403939 / 40000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_677_2 :
    Uω (aρ 2) (bρ 2) (30159206983063 / 32000000000000 : ℝ) ≤
      (-(85834148424330625231 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (37345489271458807 / 40000000000000000 : ℝ) ≤
      (-(85834148424330625231 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (37345489271458807 / 40000000000000000 : ℝ) =
            (37345489271458807 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (37345489271458807 / 20000000000000000 : ℝ) ≤
            (780599826950669374769 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (291758083878663 / 312500000000000 : ℝ)) (q :=
      (37345489271458807 / 40000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_677_3 :
    Uω (aρ 3) (bρ 3) (30159206983063 / 32000000000000 : ℝ) ≤
      (-(368936939244914093781 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7430953291820317 / 8000000000000000 : ℝ) ≤
      (-(368936939244914093781 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (7430953291820317 / 8000000000000000 : ℝ) =
            (7430953291820317 / 4000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7430953291820317 / 4000000000000000 : ℝ) ≤
            (3096798962255085906219 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1857658676857721 / 2000000000000000 : ℝ)) (q :=
      (7430953291820317 / 8000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_677_4 :
    Uω (aρ 4) (bρ 4) (30159206983063 / 32000000000000 : ℝ) ≤
      (-(82332884107747569223 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (36838613308049463 / 40000000000000000 : ℝ) ≤
      (-(82332884107747569223 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (36838613308049463 / 40000000000000000 : ℝ) =
            (36838613308049463 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (36838613308049463 / 20000000000000000 : ℝ) ≤
            (610814296192252430777 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1151063873728443 / 1250000000000000 : ℝ)) (q :=
      (36838613308049463 / 40000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_677_5 :
    Uω (aρ 5) (bρ 5) (30159206983063 / 32000000000000 : ℝ) ≤
      (-(477229023155082316277 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (36358704876728341 / 40000000000000000 : ℝ) ≤
      (-(477229023155082316277 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (36358704876728341 / 40000000000000000 : ℝ) =
            (36358704876728341 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (36358704876728341 / 20000000000000000 : ℝ) ≤
            (2988506878344917683723 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (9086746693501983 / 10000000000000000 : ℝ)) (q :=
      (36358704876728341 / 40000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_677_6 :
    Uω (aρ 6) (bρ 6) (30159206983063 / 32000000000000 : ℝ) ≤
      (-(1144589866729602112133 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (35673940604441891 / 40000000000000000 : ℝ) ≤
      (-(1144589866729602112133 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (35673940604441891 / 40000000000000000 : ℝ) =
            (35673940604441891 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (35673940604441891 / 20000000000000000 : ℝ) ≤
            (5786881936270397887867 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4455802466249379 / 5000000000000000 : ℝ)) (q :=
      (35673940604441891 / 40000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_677_7 :
    Uω (aρ 7) (bρ 7) (30159206983063 / 32000000000000 : ℝ) ≤
      (-(1407832126127480045027 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (34747104376406801 / 40000000000000000 : ℝ) ≤
      (-(1407832126127480045027 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (34747104376406801 / 40000000000000000 : ℝ) =
            (34747104376406801 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (34747104376406801 / 20000000000000000 : ℝ) ≤
            (5523639676872519954973 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (8671848199241213 / 10000000000000000 : ℝ)) (q :=
      (34747104376406801 / 40000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_677_8 :
    Uω (aρ 8) (bρ 8) (30159206983063 / 32000000000000 : ℝ) ≤
      (-(1757720990443800197271 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6710473013911293 / 8000000000000000 : ℝ) ≤
      (-(1757720990443800197271 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (6710473013911293 / 8000000000000000 : ℝ) =
            (6710473013911293 / 4000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (6710473013911293 / 4000000000000000 : ℝ) ≤
            (5173750812556199802729 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1671604039431209 / 2000000000000000 : ℝ)) (q :=
      (6710473013911293 / 8000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_677_9 :
    Uω (aρ 9) (bρ 9) (30159206983063 / 32000000000000 : ℝ) ≤
      (-(2205550341869910017897 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1283317593561117 / 1600000000000000 : ℝ) ≤
      (-(2205550341869910017897 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (1283317593561117 / 1600000000000000 : ℝ) =
            (1283317593561117 / 800000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1283317593561117 / 800000000000000 : ℝ) ≤
            (4725921461130089982103 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (318570928410071 / 400000000000000 : ℝ)) (q :=
      (1283317593561117 / 1600000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_677_10 :
    Uω (aρ 10) (bρ 10) (30159206983063 / 32000000000000 : ℝ) ≤
      (-(2758186921991172196263 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (30358020869620537 / 40000000000000000 : ℝ) ≤
      (-(2758186921991172196263 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (30358020869620537 / 40000000000000000 : ℝ) =
            (30358020869620537 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (30358020869620537 / 20000000000000000 : ℝ) ≤
            (4173284881008827803737 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7490372759043081 / 10000000000000000 : ℝ)) (q :=
      (30358020869620537 / 40000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_677_11 :
    Uω (aρ 11) (bρ 11) (30159206983063 / 32000000000000 : ℝ) ≤
      (-(426875502031516809391 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28428127279949587 / 40000000000000000 : ℝ) ≤
      (-(426875502031516809391 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (28428127279949587 / 40000000000000000 : ℝ) =
            (28428127279949587 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (28428127279949587 / 20000000000000000 : ℝ) ≤
            (439558473343483190609 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3471951295206303 / 5000000000000000 : ℝ)) (q :=
      (28428127279949587 / 40000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_677_12 :
    Uω (aρ 12) (bρ 12) (30159206983063 / 32000000000000 : ℝ) ≤
      (-(4163275610179741765353 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (26378568806350523 / 40000000000000000 : ℝ) ≤
      (-(4163275610179741765353 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (26378568806350523 / 40000000000000000 : ℝ) =
            (26378568806350523 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (26378568806350523 / 20000000000000000 : ℝ) ≤
            (2768196192820258234647 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3171411725149037 / 5000000000000000 : ℝ)) (q :=
      (26378568806350523 / 40000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_677_13 :
    Uω (aρ 13) (bρ 13) (30159206983063 / 32000000000000 : ℝ) ≤
      (-(4971061494768781944211 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4866307285834539 / 8000000000000000 : ℝ) ≤
      (-(4971061494768781944211 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (4866307285834539 / 8000000000000000 : ℝ) =
            (4866307285834539 / 4000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4866307285834539 / 4000000000000000 : ℝ) ≤
            (1960410308231218055789 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (35741806270651 / 62500000000000 : ℝ)) (q :=
      (4866307285834539 / 8000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_677_14 :
    Uω (aρ 14) (bρ 14) (30159206983063 / 32000000000000 : ℝ) ≤
      (-(2888495107361552193757 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4489505310941811 / 8000000000000000 : ℝ) ≤
      (-(2888495107361552193757 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (4489505310941811 / 8000000000000000 : ℝ) =
            (4489505310941811 / 4000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4489505310941811 / 4000000000000000 : ℝ) ≤
            (577240794138447806243 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (256030567555867 / 500000000000000 : ℝ)) (q :=
      (4489505310941811 / 8000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_677_15 :
    Uω (aρ 15) (bρ 15) (30159206983063 / 32000000000000 : ℝ) ≤
      (-(810002854756473131841 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (20923588733206163 / 40000000000000000 : ℝ) ≤
      (-(810002854756473131841 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (20923588733206163 / 40000000000000000 : ℝ) =
            (20923588733206163 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (20923588733206163 / 20000000000000000 : ℝ) ≤
            (56431120618526868159 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2309107858890447 / 5000000000000000 : ℝ)) (q :=
      (20923588733206163 / 40000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_677_16 :
    Uω (aρ 16) (bρ 16) (30159206983063 / 32000000000000 : ℝ) ≤
      (-(434015474906195459093 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3994892943791167 / 8000000000000000 : ℝ) ≤
      (-(434015474906195459093 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (3994892943791167 / 8000000000000000 : ℝ) =
            (3994892943791167 / 2000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 15
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3994892943791167 / 2000000000000000 : ℝ) ≤
            (432418500468804540907 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (429602536216573 / 1000000000000000 : ℝ)) (q :=
      (3994892943791167 / 8000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_677 :
    Uρ (30159206983063 / 32000000000000 : ℝ) ≤
      (-(2318547818050359873459 / 10000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (30159206983063 / 32000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(82643010106364090371 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_677_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (30159206983063 / 32000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(85834148424330625231 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_677_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (30159206983063 / 32000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(368936939244914093781 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_677_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (30159206983063 / 32000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) * (-(82332884107747569223 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_677_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (30159206983063 / 32000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) * (-(477229023155082316277 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_677_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (30159206983063 / 32000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(1144589866729602112133 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_677_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (30159206983063 / 32000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(1407832126127480045027 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_677_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (30159206983063 / 32000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(1757720990443800197271 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_677_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (30159206983063 / 32000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(2205550341869910017897 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_677_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (30159206983063 / 32000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(2758186921991172196263 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_677_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (30159206983063 / 32000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(426875502031516809391 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_677_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (30159206983063 / 32000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(4163275610179741765353 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_677_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (30159206983063 / 32000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(4971061494768781944211 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_677_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (30159206983063 / 32000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(2888495107361552193757 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_677_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (30159206983063 / 32000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(810002854756473131841 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_677_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (30159206983063 / 32000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(434015474906195459093 / 625000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_677_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_678_1 :
    Uω (aρ 1) (bρ 1) (15706284843697 / 16000000000000 : ℝ) ≤
      (-(31401869492385685679 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4875957115579501 / 5000000000000000 : ℝ) ≤
      (-(31401869492385685679 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (4875957115579501 / 5000000000000000 : ℝ) =
            (4875957115579501 / 2500000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4875957115579501 / 2500000000000000 : ℝ) ≤
            (835032105882614314321 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (9751897653092379 / 10000000000000000 : ℝ)) (q :=
      (4875957115579501 / 5000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_678_2 :
    Uω (aρ 2) (bρ 2) (15706284843697 / 16000000000000 : ℝ) ≤
      (-(275713462460201346549 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9728052738201763 / 10000000000000000 : ℝ) ≤
      (-(275713462460201346549 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (9728052738201763 / 10000000000000000 : ℝ) =
            (9728052738201763 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9728052738201763 / 5000000000000000 : ℝ) ≤
            (6655758340539798653451 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (9727943679687901 / 10000000000000000 : ℝ)) (q :=
      (9728052738201763 / 10000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_678_3 :
    Uω (aρ 3) (bρ 3) (15706284843697 / 16000000000000 : ℝ) ≤
      (-(20302229308895077003 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3872153429302717 / 4000000000000000 : ℝ) ≤
      (-(20302229308895077003 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (3872153429302717 / 4000000000000000 : ℝ) =
            (3872153429302717 / 2000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3872153429302717 / 2000000000000000 : ℝ) ≤
            (412914758378604922997 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (242000036403699 / 250000000000000 : ℝ)) (q :=
      (3872153429302717 / 4000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_678_4 :
    Uω (aρ 4) (bρ 4) (15706284843697 / 16000000000000 : ℝ) ≤
      (-(81357388672044063251 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9601375777845239 / 10000000000000000 : ℝ) ≤
      (-(81357388672044063251 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (9601375777845239 / 10000000000000000 : ℝ) =
            (9601375777845239 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9601375777845239 / 5000000000000000 : ℝ) ≤
            (1304936971927955936749 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (9600280046389853 / 10000000000000000 : ℝ)) (q :=
      (9601375777845239 / 10000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_678_5 :
    Uω (aρ 5) (bρ 5) (15706284843697 / 16000000000000 : ℝ) ≤
      (-(532453962168235848837 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (592592069951071 / 625000000000000 : ℝ) ≤
      (-(532453962168235848837 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (592592069951071 / 625000000000000 : ℝ) =
            (592592069951071 / 312500000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (592592069951071 / 312500000000000 : ℝ) ≤
            (6399017840831764151163 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (9478664648468647 / 10000000000000000 : ℝ)) (q :=
      (592592069951071 / 625000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_678_6 :
    Uω (aρ 6) (bρ 6) (15706284843697 / 16000000000000 : ℝ) ≤
      (-(357237988318402216991 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3724180260044697 / 4000000000000000 : ℝ) ≤
      (-(357237988318402216991 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (3724180260044697 / 4000000000000000 : ℝ) =
            (3724180260044697 / 2000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3724180260044697 / 2000000000000000 : ℝ) ≤
            (3108497913181597783009 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (465193004269893 / 500000000000000 : ℝ)) (q :=
      (3724180260044697 / 4000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_678_7 :
    Uω (aρ 7) (bρ 7) (15706284843697 / 16000000000000 : ℝ) ≤
      (-(966103549437018389189 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1815819399022757 / 2000000000000000 : ℝ) ≤
      (-(966103549437018389189 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (1815819399022757 / 2000000000000000 : ℝ) =
            (1815819399022757 / 1000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1815819399022757 / 1000000000000000 : ℝ) ≤
            (5965368253562981610811 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1812962831232389 / 2000000000000000 : ℝ)) (q :=
      (1815819399022757 / 2000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_678_8 :
    Uω (aρ 8) (bρ 8) (15706284843697 / 16000000000000 : ℝ) ≤
      (-(1299819252231914866819 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (17562226044293351 / 20000000000000000 : ℝ) ≤
      (-(1299819252231914866819 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (17562226044293351 / 20000000000000000 : ℝ) =
            (17562226044293351 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (17562226044293351 / 10000000000000000 : ℝ) ≤
            (5631652550768085133181 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4376193930783863 / 5000000000000000 : ℝ)) (q :=
      (17562226044293351 / 20000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_678_9 :
    Uω (aρ 9) (bρ 9) (15706284843697 / 16000000000000 : ℝ) ≤
      (-(172562545086624586799 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (16830113098059219 / 20000000000000000 : ℝ) ≤
      (-(172562545086624586799 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (16830113098059219 / 20000000000000000 : ℝ) =
            (16830113098059219 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (16830113098059219 / 10000000000000000 : ℝ) ≤
            (520584635213375413201 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4180620271846797 / 5000000000000000 : ℝ)) (q :=
      (16830113098059219 / 20000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_678_10 :
    Uω (aρ 10) (bρ 10) (15706284843697 / 16000000000000 : ℝ) ≤
      (-(2248820499400769661627 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7986104091424179 / 10000000000000000 : ℝ) ≤
      (-(2248820499400769661627 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (7986104091424179 / 10000000000000000 : ℝ) =
            (7986104091424179 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7986104091424179 / 5000000000000000 : ℝ) ≤
            (4682651303599230338373 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7891894661977733 / 10000000000000000 : ℝ)) (q :=
      (7986104091424179 / 10000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_678_11 :
    Uω (aρ 11) (bρ 11) (15706284843697 / 16000000000000 : ℝ) ≤
      (-(286694897106712835459 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7507407468771171 / 10000000000000000 : ℝ) ≤
      (-(286694897106712835459 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (7507407468771171 / 10000000000000000 : ℝ) =
            (7507407468771171 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7507407468771171 / 5000000000000000 : ℝ) ≤
            (406452283193287164541 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7352978042876717 / 10000000000000000 : ℝ)) (q :=
      (7507407468771171 / 10000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_678_12 :
    Uω (aρ 12) (bρ 12) (15706284843697 / 16000000000000 : ℝ) ≤
      (-(44567725956253433693 / 125000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3500466007121139 / 5000000000000000 : ℝ) ≤
      (-(44567725956253433693 / 125000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (3500466007121139 / 5000000000000000 : ℝ) =
            (3500466007121139 / 2500000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3500466007121139 / 2500000000000000 : ℝ) ≤
            (42075671581246566307 / 125000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6763727230503931 / 10000000000000000 : ℝ)) (q :=
      (3500466007121139 / 5000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_678_13 :
    Uω (aρ 13) (bρ 13) (15706284843697 / 16000000000000 : ℝ) ≤
      (-(4311189061635353508999 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12995632859396249 / 20000000000000000 : ℝ) ≤
      (-(4311189061635353508999 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (12995632859396249 / 20000000000000000 : ℝ) =
            (12995632859396249 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (12995632859396249 / 10000000000000000 : ℝ) ≤
            (2620282741364646491001 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (96201215672041 / 156250000000000 : ℝ)) (q :=
      (12995632859396249 / 20000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_678_14 :
    Uω (aρ 14) (bρ 14) (15706284843697 / 16000000000000 : ℝ) ≤
      (-(504471450642891062021 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3019123210339151 / 5000000000000000 : ℝ) ≤
      (-(504471450642891062021 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (3019123210339151 / 5000000000000000 : ℝ) =
            (3019123210339151 / 2500000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3019123210339151 / 2500000000000000 : ℝ) ≤
            (188675729657108937979 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (5581665070015979 / 10000000000000000 : ℝ)) (q :=
      (3019123210339151 / 5000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_678_15 :
    Uω (aρ 15) (bρ 15) (15706284843697 / 16000000000000 : ℝ) ≤
      (-(1134783711466407468651 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5670023356259313 / 10000000000000000 : ℝ) ≤
      (-(1134783711466407468651 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (5670023356259313 / 10000000000000000 : ℝ) =
            (5670023356259313 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5670023356259313 / 5000000000000000 : ℝ) ≤
            (251510649133592531349 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (5104792218593001 / 10000000000000000 : ℝ)) (q :=
      (5670023356259313 / 10000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_678_16 :
    Uω (aρ 16) (bρ 16) (15706284843697 / 16000000000000 : ℝ) ≤
      (-(1520695928810576621543 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (435429698376879 / 800000000000000 : ℝ) ≤
      (-(1520695928810576621543 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (435429698376879 / 800000000000000 : ℝ) =
            (435429698376879 / 400000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (435429698376879 / 400000000000000 : ℝ) ≤
            (212172021939423378457 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (96057192340127 / 200000000000000 : ℝ)) (q :=
      (435429698376879 / 800000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16]) (by norm_num [bρ_16])
      (by norm_num) (by norm_num [aρ_16, bρ_16]) (by norm_num [aρ_16, bρ_16]) hlg

lemma U_678 :
    Uρ (15706284843697 / 16000000000000 : ℝ) ≤
      (-(92343274023702849147 / 500000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (15706284843697 / 16000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(31401869492385685679 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_678_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (15706284843697 / 16000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(275713462460201346549 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_678_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (15706284843697 / 16000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) * (-(20302229308895077003 / 625000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_678_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (15706284843697 / 16000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) * (-(81357388672044063251 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_678_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (15706284843697 / 16000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(532453962168235848837 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_678_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (15706284843697 / 16000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(357237988318402216991 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_678_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (15706284843697 / 16000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(966103549437018389189 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_678_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (15706284843697 / 16000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(1299819252231914866819 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_678_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (15706284843697 / 16000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(172562545086624586799 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_678_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (15706284843697 / 16000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(2248820499400769661627 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_678_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (15706284843697 / 16000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(286694897106712835459 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_678_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (15706284843697 / 16000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) * (-(44567725956253433693 / 125000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_678_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (15706284843697 / 16000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(4311189061635353508999 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_678_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (15706284843697 / 16000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(504471450642891062021 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_678_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (15706284843697 / 16000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(1134783711466407468651 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_678_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (15706284843697 / 16000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(1520695928810576621543 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_678_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_679_1 :
    Uω (aρ 1) (bρ 1) (4239911887007 / 4000000000000 : ℝ) ≤
      (32589570407983029189 / 625000000000000000000 : ℝ) := by
  have hlg :
    Real.log (1316908394254119 / 1250000000000000 : ℝ) ≤
      (32589570407983029189 / 625000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (2633812952158351 / 2500000000000000 : ℝ)) (q :=
      (1316908394254119 / 1250000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_679_2 :
    Uω (aρ 2) (bρ 2) (4239911887007 / 4000000000000 : ℝ) ≤
      (99752968003727494617 / 2000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (164240821186893 / 156250000000000 : ℝ) ≤
      (99752968003727494617 / 2000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (2627827906249951 / 2500000000000000 : ℝ)) (q :=
      (164240821186893 / 156250000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_679_3 :
    Uω (aρ 3) (bρ 3) (4239911887007 / 4000000000000 : ℝ) ≤
      (226665678130179312083 / 5000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (20927527742097363 / 20000000000000000 : ℝ) ≤
      (226665678130179312083 / 5000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (10463410361524863 / 10000000000000000 : ℝ)) (q :=
      (20927527742097363 / 20000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_679_4 :
    Uω (aρ 4) (bρ 4) (4239911887007 / 4000000000000 : ℝ) ≤
      (75518162225807609173 / 2000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (20769620260968647 / 20000000000000000 : ℝ) ≤
      (75518162225807609173 / 2000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (10383797061461147 / 10000000000000000 : ℝ)) (q :=
      (20769620260968647 / 20000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_679_5 :
    Uω (aρ 5) (bρ 5) (4239911887007 / 4000000000000 : ℝ) ≤
      (261587752722163667687 / 10000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (4106015675897693 / 4000000000000000 : ℝ) ≤
      (261587752722163667687 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (2052489019863193 / 2000000000000000 : ℝ)) (q :=
      (4106015675897693 / 4000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_679_6 :
    Uω (aρ 6) (bρ 6) (4239911887007 / 4000000000000 : ℝ) ≤
      (23468035726243644037 / 2500000000000000000000 : ℝ) := by
  have hlg :
    Real.log (20188628247545629 / 20000000000000000 : ℝ) ≤
      (23468035726243644037 / 2500000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (10088235342513129 / 10000000000000000 : ℝ)) (q :=
      (20188628247545629 / 20000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_679_7 :
    Uω (aρ 7) (bρ 7) (4239911887007 / 4000000000000 : ℝ) ≤
      (-(17169293930414594967 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (19727169305494247 / 20000000000000000 : ℝ) ≤
      (-(17169293930414594967 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (19727169305494247 / 20000000000000000 : ℝ) =
            (19727169305494247 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (19727169305494247 / 10000000000000000 : ℝ) ≤
            (849264681444585405033 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (9850437781221747 / 10000000000000000 : ℝ)) (q :=
      (19727169305494247 / 20000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_679_8 :
    Uω (aρ 8) (bρ 8) (4239911887007 / 4000000000000 : ℝ) ≤
      (-(13838695655646965701 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (19133647745154483 / 20000000000000000 : ℝ) ≤
      (-(13838695655646965701 / 312500000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (19133647745154483 / 20000000000000000 : ℝ) =
            (19133647745154483 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (19133647745154483 / 10000000000000000 : ℝ) ≤
            (202769798188103034299 / 312500000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (9540457872221983 / 10000000000000000 : ℝ)) (q :=
      (19133647745154483 / 20000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_679_9 :
    Uω (aρ 9) (bρ 9) (4239911887007 / 4000000000000 : ℝ) ≤
      (-(4152692092358634187 / 50000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9203015949090823 / 10000000000000000 : ℝ) ≤
      (-(4152692092358634187 / 50000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (9203015949090823 / 10000000000000000 : ℝ) =
            (9203015949090823 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9203015949090823 / 5000000000000000 : ℝ) ≤
            (30504666922641365813 / 50000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4576903826804573 / 5000000000000000 : ℝ)) (q :=
      (9203015949090823 / 10000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_679_10 :
    Uω (aρ 10) (bρ 10) (4239911887007 / 4000000000000 : ℝ) ≤
      (-(325854264266228926319 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8777954317313903 / 10000000000000000 : ℝ) ≤
      (-(325854264266228926319 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (8777954317313903 / 10000000000000000 : ℝ) =
            (8777954317313903 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (8777954317313903 / 5000000000000000 : ℝ) ≤
            (1407013686483771073681 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4346121711775153 / 5000000000000000 : ℝ)) (q :=
      (8777954317313903 / 10000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_679_11 :
    Uω (aρ 11) (bρ 11) (4239911887007 / 4000000000000 : ℝ) ≤
      (-(928275361804200092781 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8305600284736179 / 10000000000000000 : ℝ) ≤
      (-(928275361804200092781 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (8305600284736179 / 10000000000000000 : ℝ) =
            (8305600284736179 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (8305600284736179 / 5000000000000000 : ℝ) ≤
            (2537460539695799907219 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4083005992299929 / 5000000000000000 : ℝ)) (q :=
      (8305600284736179 / 10000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_679_12 :
    Uω (aρ 12) (bρ 12) (4239911887007 / 4000000000000 : ℝ) ≤
      (-(98932252879129752837 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3123529863022419 / 4000000000000000 : ℝ) ≤
      (-(98932252879129752837 / 400000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (3123529863022419 / 4000000000000000 : ℝ) =
            (3123529863022419 / 2000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3123529863022419 / 2000000000000000 : ℝ) ≤
            (178326619240870247163 / 400000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1519232165384919 / 2000000000000000 : ℝ)) (q :=
      (3123529863022419 / 4000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_679_13 :
    Uω (aρ 13) (bρ 13) (4239911887007 / 4000000000000 : ℝ) ≤
      (-(1560256889330704127261 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3659719606775781 / 5000000000000000 : ℝ) ≤
      (-(1560256889330704127261 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (3659719606775781 / 5000000000000000 : ℝ) =
            (3659719606775781 / 2500000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3659719606775781 / 2500000000000000 : ℝ) ≤
            (1905479012169295872739 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (219274115015957 / 312500000000000 : ℝ)) (q :=
      (3659719606775781 / 5000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_679_14 :
    Uω (aρ 14) (bρ 14) (4239911887007 / 4000000000000 : ℝ) ≤
      (-(748717128402485919173 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13754605439581289 / 20000000000000000 : ℝ) ≤
      (-(748717128402485919173 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (13754605439581289 / 20000000000000000 : ℝ) =
            (13754605439581289 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (13754605439581289 / 10000000000000000 : ℝ) ≤
            (637577232197514080827 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6476425978033789 / 10000000000000000 : ℝ)) (q :=
      (13754605439581289 / 20000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_679_15 :
    Uω (aρ 15) (bρ 15) (4239911887007 / 4000000000000 : ℝ) ≤
      (-(2132701068385280181461 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2611054459411399 / 4000000000000000 : ℝ) ≤
      (-(2132701068385280181461 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (2611054459411399 / 4000000000000000 : ℝ) =
            (2611054459411399 / 2000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2611054459411399 / 2000000000000000 : ℝ) ≤
            (1333034833114719818539 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1207333222584899 / 2000000000000000 : ℝ)) (q :=
      (2611054459411399 / 4000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_679_16 :
    Uω (aρ 16) (bρ 16) (4239911887007 / 4000000000000 : ℝ) ≤
      (-(2298623924628737086939 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3157287040140563 / 5000000000000000 : ℝ) ≤
      (-(2298623924628737086939 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (3157287040140563 / 5000000000000000 : ℝ) =
            (3157287040140563 / 2500000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3157287040140563 / 2500000000000000 : ℝ) ≤
            (1167111976871262913061 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (720364203492469 / 1250000000000000 : ℝ)) (q :=
      (3157287040140563 / 5000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_679 :
    Uρ (4239911887007 / 4000000000000 : ℝ) ≤
      (-(976182167040415310791 / 10000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (4239911887007 / 4000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (32589570407983029189 / 625000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_679_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (4239911887007 / 4000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) * (99752968003727494617 / 2000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_679_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (4239911887007 / 4000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) * (226665678130179312083 / 5000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_679_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (4239911887007 / 4000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) * (75518162225807609173 / 2000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_679_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (4239911887007 / 4000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) * (261587752722163667687 / 10000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_679_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (4239911887007 / 4000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) * (23468035726243644037 / 2500000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_679_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (4239911887007 / 4000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(17169293930414594967 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_679_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (4239911887007 / 4000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) * (-(13838695655646965701 / 312500000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_679_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (4239911887007 / 4000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(4152692092358634187 / 50000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_679_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (4239911887007 / 4000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(325854264266228926319 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_679_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (4239911887007 / 4000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(928275361804200092781 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_679_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (4239911887007 / 4000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) * (-(98932252879129752837 / 400000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_679_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (4239911887007 / 4000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(1560256889330704127261 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_679_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (4239911887007 / 4000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(748717128402485919173 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_679_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (4239911887007 / 4000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(2132701068385280181461 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_679_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (4239911887007 / 4000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(2298623924628737086939 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_679_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_680_1 :
    Uω (aρ 1) (bρ 1) (18213010252359 / 16000000000000 : ℝ) ≤
      (1238640559424707941031 / 10000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (22637239812565641 / 20000000000000000 : ℝ) ≤
      (1238640559424707941031 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (5659302811463133 / 5000000000000000 : ℝ)) (q :=
      (22637239812565641 / 20000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_680_2 :
    Uω (aρ 2) (bρ 2) (18213010252359 / 16000000000000 : ℝ) ≤
      (121754804071227033031 / 1000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (5647385623161349 / 5000000000000000 : ℝ) ≤
      (121754804071227033031 / 1000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (11294677315516021 / 10000000000000000 : ℝ)) (q :=
      (5647385623161349 / 5000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_680_3 :
    Uω (aρ 3) (bρ 3) (18213010252359 / 16000000000000 : ℝ) ≤
      (117528797438582498587 / 1000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (22494280367204911 / 20000000000000000 : ℝ) ≤
      (117528797438582498587 / 1000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (175731426506649 / 156250000000000 : ℝ)) (q :=
      (22494280367204911 / 20000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_680_4 :
    Uω (aρ 4) (bρ 4) (18213010252359 / 16000000000000 : ℝ) ≤
      (17263797762555920119 / 156250000000000000000 : ℝ) := by
  have hlg :
    Real.log (22336465769744637 / 20000000000000000 : ℝ) ≤
      (17263797762555920119 / 156250000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (5583645440015131 / 5000000000000000 : ℝ)) (q :=
      (22336465769744637 / 20000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_680_5 :
    Uω (aρ 5) (bρ 5) (18213010252359 / 16000000000000 : ℝ) ≤
      (49858176718355945399 / 500000000000000000000 : ℝ) := by
  have hlg :
    Real.log (22097149691943109 / 20000000000000000 : ℝ) ≤
      (49858176718355945399 / 500000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (5523082360781867 / 5000000000000000 : ℝ)) (q :=
      (22097149691943109 / 20000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_680_6 :
    Uω (aρ 6) (bρ 6) (18213010252359 / 16000000000000 : ℝ) ≤
      (841668503982988491161 / 10000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (21756207605261641 / 20000000000000000 : ℝ) ≤
      (841668503982988491161 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (5436231505011133 / 5000000000000000 : ℝ)) (q :=
      (21756207605261641 / 20000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_680_7 :
    Uω (aρ 7) (bρ 7) (18213010252359 / 16000000000000 : ℝ) ≤
      (125556082777140847159 / 2000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (10647904735856001 / 10000000000000000 : ℝ) ≤
      (125556082777140847159 / 2000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (10635726257232627 / 10000000000000000 : ℝ)) (q :=
      (10647904735856001 / 10000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_680_8 :
    Uω (aρ 8) (bρ 8) (18213010252359 / 16000000000000 : ℝ) ≤
      (34611624805998184127 / 1000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (10352175778881961 / 10000000000000000 : ℝ) ≤
      (34611624805998184127 / 1000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (10327809994624547 / 10000000000000000 : ℝ)) (q :=
      (10352175778881961 / 10000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_680_9 :
    Uω (aρ 9) (bρ 9) (18213010252359 / 16000000000000 : ℝ) ≤
      (-(9759515284691867981 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (19980490485952811 / 20000000000000000 : ℝ) ≤
      (-(9759515284691867981 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (19980490485952811 / 20000000000000000 : ℝ) =
            (19980490485952811 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 15
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (19980490485952811 / 10000000000000000 : ℝ) ≤
            (6921712287715308132019 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2486228637793359 / 2500000000000000 : ℝ)) (q :=
      (19980490485952811 / 20000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_680_10 :
    Uω (aρ 10) (bρ 10) (18213010252359 / 16000000000000 : ℝ) ≤
      (-(441205039158688405329 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9568386474729171 / 10000000000000000 : ℝ) ≤
      (-(441205039158688405329 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (9568386474729171 / 10000000000000000 : ℝ) =
            (9568386474729171 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9568386474729171 / 5000000000000000 : ℝ) ≤
            (6490266763841311594671 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (9489756048173967 / 10000000000000000 : ℝ)) (q :=
      (9568386474729171 / 10000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_680_11 :
    Uω (aρ 11) (bρ 11) (18213010252359 / 16000000000000 : ℝ) ≤
      (-(235459762249886509823 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (18202307438725301 / 20000000000000000 : ℝ) ≤
      (-(235459762249886509823 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (18202307438725301 / 20000000000000000 : ℝ) =
            (18202307438725301 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (18202307438725301 / 10000000000000000 : ℝ) ≤
            (1497408188500113490177 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4486883581822963 / 5000000000000000 : ℝ)) (q :=
      (18202307438725301 / 20000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_680_12 :
    Uω (aρ 12) (bρ 12) (18213010252359 / 16000000000000 : ℝ) ≤
      (-(186784175247454332741 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2153002525543727 / 2500000000000000 : ℝ) ≤
      (-(186784175247454332741 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (2153002525543727 / 2500000000000000 : ℝ) =
            (2153002525543727 / 1250000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2153002525543727 / 1250000000000000 : ℝ) ≤
            (679649800127545667259 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (8419180025955441 / 10000000000000000 : ℝ)) (q :=
      (2153002525543727 / 2500000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_680_13 :
    Uω (aρ 13) (bρ 13) (18213010252359 / 16000000000000 : ℝ) ≤
      (-(2066466640027391588759 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (16266139392844263 / 20000000000000000 : ℝ) ≤
      (-(2066466640027391588759 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (16266139392844263 / 20000000000000000 : ℝ) =
            (16266139392844263 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (16266139392844263 / 10000000000000000 : ℝ) ≤
            (4865005162972608411241 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (982585119505611 / 1250000000000000 : ℝ)) (q :=
      (16266139392844263 / 20000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_680_14 :
    Uω (aρ 14) (bρ 14) (18213010252359 / 16000000000000 : ℝ) ≤
      (-(521780271597462009859 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (15407311007233661 / 20000000000000000 : ℝ) ≤
      (-(521780271597462009859 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (15407311007233661 / 20000000000000000 : ℝ) =
            (15407311007233661 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (15407311007233661 / 10000000000000000 : ℝ) ≤
            (864514089002537990141 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3672889927739643 / 5000000000000000 : ℝ)) (q :=
      (15407311007233661 / 20000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_680_15 :
    Uω (aρ 15) (bρ 15) (18213010252359 / 16000000000000 : ℝ) ≤
      (-(3055850814904569992253 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (46043263943697 / 62500000000000 : ℝ) ≤
      (-(3055850814904569992253 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (46043263943697 / 62500000000000 : ℝ) = (46043263943697 / 31250000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (46043263943697 / 31250000000000 : ℝ) ≤
            (3875620988095430007747 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1386377317528733 / 2000000000000000 : ℝ)) (q :=
      (46043263943697 / 62500000000000 : ℝ)) (by norm_num [aρ_15, bρ_15]) (by norm_num [bρ_15])
      (by norm_num) (by norm_num [aρ_15, bρ_15]) (by norm_num [aρ_15, bρ_15]) hlg

lemma U_680_16 :
    Uω (aρ 16) (bρ 16) (18213010252359 / 16000000000000 : ℝ) ≤
      (-(834040341612878975103 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14326574032209963 / 20000000000000000 : ℝ) ≤
      (-(834040341612878975103 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (14326574032209963 / 20000000000000000 : ℝ) =
            (14326574032209963 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14326574032209963 / 10000000000000000 : ℝ) ≤
            (898827609137121024897 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1669246952345147 / 2500000000000000 : ℝ)) (q :=
      (14326574032209963 / 20000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_680 :
    Uρ (18213010252359 / 16000000000000 : ℝ) ≤
      (-(185691588642492027487 / 10000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (18213010252359 / 16000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (1238640559424707941031 / 10000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_680_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (18213010252359 / 16000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) * (121754804071227033031 / 1000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_680_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (18213010252359 / 16000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) * (117528797438582498587 / 1000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_680_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (18213010252359 / 16000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) * (17263797762555920119 / 156250000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_680_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (18213010252359 / 16000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) * (49858176718355945399 / 500000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_680_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (18213010252359 / 16000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) * (841668503982988491161 / 10000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_680_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (18213010252359 / 16000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) * (125556082777140847159 / 2000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_680_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (18213010252359 / 16000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) * (34611624805998184127 / 1000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_680_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (18213010252359 / 16000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(9759515284691867981 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_680_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (18213010252359 / 16000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(441205039158688405329 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_680_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (18213010252359 / 16000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(235459762249886509823 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_680_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (18213010252359 / 16000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(186784175247454332741 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_680_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (18213010252359 / 16000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(2066466640027391588759 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_680_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (18213010252359 / 16000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(521780271597462009859 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_680_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (18213010252359 / 16000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(3055850814904569992253 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_680_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (18213010252359 / 16000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(834040341612878975103 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_680_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_681_1 :
    Uω (aρ 1) (bρ 1) (1946637295669 / 1600000000000 : ℝ) ≤
      (381566729181073695513 / 2000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (2420394504208369 / 2000000000000000 : ℝ) ≤
      (381566729181073695513 / 2000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (4727327797749 / 3906250000000 : ℝ)) (q :=
      (2420394504208369 / 2000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_681_2 :
    Uω (aρ 2) (bρ 2) (1946637295669 / 1600000000000 : ℝ) ≤
      (944056028915092092057 / 5000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (603906451432549 / 500000000000000 : ℝ) ≤
      (944056028915092092057 / 5000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (1207804118996571 / 1000000000000000 : ℝ)) (q :=
      (603906451432549 / 500000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_681_3 :
    Uω (aρ 3) (bρ 3) (1946637295669 / 1600000000000 : ℝ) ≤
      (1848611035360319879371 / 10000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (4812205315787301 / 4000000000000000 : ℝ) ≤
      (1848611035360319879371 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (2406041163590051 / 2000000000000000 : ℝ)) (q :=
      (4812205315787301 / 4000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_681_4 :
    Uω (aρ 4) (bρ 4) (1946637295669 / 1600000000000 : ℝ) ≤
      (44570985859756852759 / 250000000000000000000 : ℝ) := by
  have hlg :
    Real.log (23903292644316659 / 20000000000000000 : ℝ) ≤
      (44570985859756852759 / 250000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (11950766064395409 / 10000000000000000 : ℝ)) (q :=
      (23903292644316659 / 20000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_681_5 :
    Uω (aρ 5) (bρ 5) (1946637295669 / 1600000000000 : ℝ) ≤
      (210287390033879084137 / 1250000000000000000000 : ℝ) := by
  have hlg :
    Real.log (739505383293149 / 625000000000000 : ℝ) ≤
      (210287390033879084137 / 1250000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (5914917802397259 / 5000000000000000 : ℝ)) (q :=
      (739505383293149 / 625000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_681_6 :
    Uω (aρ 6) (bρ 6) (1946637295669 / 1600000000000 : ℝ) ≤
      (38434103813816542803 / 250000000000000000000 : ℝ) := by
  have hlg :
    Real.log (2915458645235873 / 2500000000000000 : ℝ) ≤
      (38434103813816542803 / 250000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (5828286438220367 / 5000000000000000 : ℝ)) (q :=
      (2915458645235873 / 2500000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_681_7 :
    Uω (aρ 7) (bρ 7) (1946637295669 / 1600000000000 : ℝ) ≤
      (1338393787175108167323 / 10000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (22864183623441699 / 20000000000000000 : ℝ) ≤
      (1338393787175108167323 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (11420748718755449 / 10000000000000000 : ℝ)) (q :=
      (22864183623441699 / 20000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_681_8 :
    Uω (aρ 8) (bρ 8) (1946637295669 / 1600000000000 : ℝ) ≤
      (538549030281882261609 / 5000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (22274490047633971 / 20000000000000000 : ℝ) ≤
      (538549030281882261609 / 5000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (11114596794287721 / 10000000000000000 : ℝ)) (q :=
      (22274490047633971 / 20000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_681_9 :
    Uω (aρ 9) (bρ 9) (1946637295669 / 1600000000000 : ℝ) ≤
      (748204042513207311507 / 10000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (10776905848559021 / 10000000000000000 : ℝ) ≤
      (748204042513207311507 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (670930254508237 / 625000000000000 : ℝ)) (q :=
      (10776905848559021 / 10000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_681_10 :
    Uω (aρ 10) (bρ 10) (1946637295669 / 1600000000000 : ℝ) ≤
      (351480511177384359847 / 10000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (20715460896111329 / 20000000000000000 : ℝ) ≤
      (351480511177384359847 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 4
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (10285092304620079 / 10000000000000000 : ℝ)) (q :=
      (20715460896111329 / 20000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_681_11 :
    Uω (aρ 11) (bρ 11) (1946637295669 / 1600000000000 : ℝ) ≤
      (-(26459032811501839539 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (19789443919795677 / 20000000000000000 : ℝ) ≤
      (-(26459032811501839539 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (19789443919795677 / 20000000000000000 : ℝ) =
            (19789443919795677 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (19789443919795677 / 10000000000000000 : ℝ) ≤
            (1706408917938498160461 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (9777551954509427 / 10000000000000000 : ℝ)) (q :=
      (19789443919795677 / 20000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_681_12 :
    Uω (aρ 12) (bρ 12) (1946637295669 / 1600000000000 : ℝ) ≤
      (-(151566259945222584619 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (18823493977979713 / 20000000000000000 : ℝ) ≤
      (-(151566259945222584619 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (18823493977979713 / 20000000000000000 : ℝ) =
            (18823493977979713 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (18823493977979713 / 10000000000000000 : ℝ) ≤
            (1581301690804777415381 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (9235302109378463 / 10000000000000000 : ℝ)) (q :=
      (18823493977979713 / 20000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_681_13 :
    Uω (aρ 13) (bρ 13) (1946637295669 / 1600000000000 : ℝ) ≤
      (-(1119336165660419824783 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1788207217931651 / 2000000000000000 : ℝ) ≤
      (-(1119336165660419824783 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (1788207217931651 / 2000000000000000 : ℝ) =
            (1788207217931651 / 1000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1788207217931651 / 1000000000000000 : ℝ) ≤
            (5812135637339580175217 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (434663102615513 / 500000000000000 : ℝ)) (q :=
      (1788207217931651 / 2000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_681_14 :
    Uω (aρ 14) (bρ 14) (1946637295669 / 1600000000000 : ℝ) ≤
      (-(800052579600481050621 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (17042696554316489 / 20000000000000000 : ℝ) ≤
      (-(800052579600481050621 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (17042696554316489 / 20000000000000000 : ℝ) =
            (17042696554316489 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (17042696554316489 / 10000000000000000 : ℝ) ≤
            (2665683321899518949379 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (8197813712355239 / 10000000000000000 : ℝ)) (q :=
      (17042696554316489 / 20000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_681_15 :
    Uω (aρ 15) (bρ 15) (1946637295669 / 1600000000000 : ℝ) ≤
      (-(1991591901709806684277 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (16388388784320793 / 20000000000000000 : ℝ) ≤
      (-(1991591901709806684277 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (16388388784320793 / 20000000000000000 : ℝ) =
            (16388388784320793 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (16388388784320793 / 10000000000000000 : ℝ) ≤
            (4939879901290193315723 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7803079219774543 / 10000000000000000 : ℝ)) (q :=
      (16388388784320793 / 20000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_681_16 :
    Uω (aρ 16) (bρ 16) (1946637295669 / 1600000000000 : ℝ) ≤
      (-(1117370294237785446319 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7997356374547131 / 10000000000000000 : ℝ) ≤
      (-(1117370294237785446319 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (7997356374547131 / 10000000000000000 : ℝ) =
            (7997356374547131 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7997356374547131 / 5000000000000000 : ℝ) ≤
            (2348365607262214553681 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1890443709014503 / 2500000000000000 : ℝ)) (q :=
      (7997356374547131 / 10000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_681 :
    Uρ (1946637295669 / 1600000000000 : ℝ) ≤
      (539206832017378636869 / 10000000000000000000000 : ℝ) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (1946637295669 / 1600000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (381566729181073695513 / 2000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_681_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (1946637295669 / 1600000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) * (944056028915092092057 / 5000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_681_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (1946637295669 / 1600000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (1848611035360319879371 / 10000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_681_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (1946637295669 / 1600000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) * (44570985859756852759 / 250000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_681_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (1946637295669 / 1600000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) * (210287390033879084137 / 1250000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_681_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (1946637295669 / 1600000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) * (38434103813816542803 / 250000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_681_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (1946637295669 / 1600000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (1338393787175108167323 / 10000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_681_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (1946637295669 / 1600000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) * (538549030281882261609 / 5000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_681_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (1946637295669 / 1600000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (748204042513207311507 / 10000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_681_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (1946637295669 / 1600000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) * (351480511177384359847 / 10000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_681_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (1946637295669 / 1600000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) * (-(26459032811501839539 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_681_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (1946637295669 / 1600000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(151566259945222584619 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_681_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (1946637295669 / 1600000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(1119336165660419824783 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_681_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (1946637295669 / 1600000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(800052579600481050621 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_681_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (1946637295669 / 1600000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(1991591901709806684277 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_681_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (1946637295669 / 1600000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(1117370294237785446319 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_681_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_682_1 :
    Uω (aρ 1) (bρ 1) (2746637295669 / 2000000000000 : ℝ) ≤
      (1562609017187395006033 / 5000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (2733735486528567 / 2000000000000000 : ℝ) ≤
      (1562609017187395006033 / 5000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (1366866560502567 / 1000000000000000 : ℝ)) (q :=
      (2733735486528567 / 2000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_682_2 :
    Uω (aρ 2) (bρ 2) (2746637295669 / 2000000000000 : ℝ) ≤
      (621553036055481657661 / 2000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (13644842494784013 / 10000000000000000 : ℝ) ≤
      (621553036055481657661 / 2000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (6822382370909013 / 5000000000000000 : ℝ)) (q :=
      (13644842494784013 / 10000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_682_3 :
    Uω (aρ 3) (bρ 3) (2746637295669 / 2000000000000 : ℝ) ≤
      (768206569321752291863 / 2500000000000000000000 : ℝ) := by
  have hlg :
    Real.log (5438900839273781 / 4000000000000000 : ℝ) ≤
      (768206569321752291863 / 2500000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (2719396010993781 / 2000000000000000 : ℝ)) (q :=
      (5438900839273781 / 4000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_682_4 :
    Uω (aρ 4) (bρ 4) (2746637295669 / 2000000000000 : ℝ) ≤
      (3014704537217327050923 / 10000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (1351845172554389 / 1000000000000000 : ℝ) ≤
      (3014704537217327050923 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (675883674537639 / 500000000000000 : ℝ)) (q :=
      (1351845172554389 / 1000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_682_5 :
    Uω (aρ 5) (bρ 5) (2746637295669 / 2000000000000 : ℝ) ≤
      (585197835390417916143 / 2000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (1339905270349957 / 1000000000000000 : ℝ) ≤
      (585197835390417916143 / 2000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (669853268299957 / 500000000000000 : ℝ)) (q :=
      (1339905270349957 / 1000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_682_6 :
    Uω (aρ 6) (bρ 6) (2746637295669 / 2000000000000 : ℝ) ≤
      (1399192462686000616281 / 5000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (26458322685085169 / 20000000000000000 : ℝ) ≤
      (1399192462686000616281 / 5000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (13224523019225169 / 10000000000000000 : ℝ)) (q :=
      (26458322685085169 / 20000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_682_7 :
    Uω (aρ 7) (bρ 7) (2746637295669 / 2000000000000 : ℝ) ≤
      (40996380119763539301 / 156250000000000000000 : ℝ) := by
  have hlg :
    Real.log (13000163388913701 / 10000000000000000 : ℝ) ≤
      (40996380119763539301 / 156250000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (6495094246363701 / 5000000000000000 : ℝ)) (q :=
      (13000163388913701 / 10000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_682_8 :
    Uω (aρ 8) (bρ 8) (2746637295669 / 2000000000000 : ℝ) ≤
      (2395479286330499915887 / 10000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (25413491697247327 / 20000000000000000 : ℝ) ≤
      (2395479286330499915887 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (12686895063487327 / 10000000000000000 : ℝ)) (q :=
      (25413491697247327 / 20000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_682_9 :
    Uω (aρ 9) (bρ 9) (2746637295669 / 2000000000000 : ℝ) ≤
      (2109866511084314583863 / 10000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (24697917409205917 / 20000000000000000 : ℝ) ≤
      (2109866511084314583863 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (12312286403805917 / 10000000000000000 : ℝ)) (q :=
      (24697917409205917 / 20000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_682_10 :
    Uω (aρ 10) (bρ 10) (2746637295669 / 2000000000000 : ℝ) ≤
      (1768087379828123108613 / 10000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (11934028186673021 / 10000000000000000 : ℝ) ≤
      (1768087379828123108613 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 7
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (5935492200720521 / 5000000000000000 : ℝ)) (q :=
      (11934028186673021 / 10000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_682_11 :
    Uω (aρ 11) (bρ 11) (2746637295669 / 2000000000000 : ℝ) ≤
      (1378108348866220666213 / 10000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (11477584138870181 / 10000000000000000 : ℝ) ≤
      (1378108348866220666213 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 6
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (5688286466020181 / 5000000000000000 : ℝ)) (q :=
      (11477584138870181 / 10000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_682_12 :
    Uω (aρ 12) (bρ 12) (2746637295669 / 2000000000000 : ℝ) ≤
      (956720482436799679737 / 10000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (22007962546276019 / 20000000000000000 : ℝ) ≤
      (956720482436799679737 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (10853067297261019 / 10000000000000000 : ℝ)) (q :=
      (22007962546276019 / 20000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_682_13 :
    Uω (aρ 13) (bρ 13) (2746637295669 / 2000000000000 : ℝ) ≤
      (531080877900712560969 / 10000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (21090872444982791 / 20000000000000000 : ℝ) ≤
      (531080877900712560969 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 5
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (10335358937562791 / 10000000000000000 : ℝ)) (q :=
      (21090872444982791 / 20000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_682_14 :
    Uω (aρ 14) (bρ 14) (2746637295669 / 2000000000000 : ℝ) ≤
      (34680649393365873701 / 2500000000000000000000 : ℝ) := by
  have hlg :
    Real.log (20279378520574633 / 20000000000000000 : ℝ) ≤
      (34680649393365873701 / 2500000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 3
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (9867792298199633 / 10000000000000000 : ℝ)) (q :=
      (20279378520574633 / 20000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_682_15 :
    Uω (aρ 15) (bρ 15) (2746637295669 / 2000000000000 : ℝ) ≤
      (-(175689130303678076623 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1965169040399109 / 2000000000000000 : ℝ) ≤
      (-(175689130303678076623 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (1965169040399109 / 2000000000000000 : ℝ) =
            (1965169040399109 / 1000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1965169040399109 / 1000000000000000 : ℝ) ≤
            (6755782672696321923377 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (949967745903109 / 1000000000000000 : ℝ)) (q :=
      (1965169040399109 / 2000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_682_16 :
    Uω (aρ 16) (bρ 16) (2746637295669 / 2000000000000 : ℝ) ≤
      (-(368491277579048029599 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (19276430760921297 / 20000000000000000 : ℝ) ≤
      (-(368491277579048029599 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (19276430760921297 / 20000000000000000 : ℝ) =
            (19276430760921297 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (19276430760921297 / 10000000000000000 : ℝ) ≤
            (6562980525420951970401 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (9276789467471297 / 10000000000000000 : ℝ)) (q :=
      (19276430760921297 / 20000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_682 :
    Uρ (2746637295669 / 2000000000000 : ℝ) ≤
      (1832301135489243993659 / 10000000000000000000000 : ℝ) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (2746637295669 / 2000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (1562609017187395006033 / 5000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_682_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (2746637295669 / 2000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) * (621553036055481657661 / 2000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_682_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (2746637295669 / 2000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) * (768206569321752291863 / 2500000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_682_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (2746637295669 / 2000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) * (3014704537217327050923 / 10000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_682_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (2746637295669 / 2000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) * (585197835390417916143 / 2000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_682_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (2746637295669 / 2000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) * (1399192462686000616281 / 5000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_682_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (2746637295669 / 2000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) * (40996380119763539301 / 156250000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_682_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (2746637295669 / 2000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (2395479286330499915887 / 10000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_682_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (2746637295669 / 2000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (2109866511084314583863 / 10000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_682_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (2746637295669 / 2000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) * (1768087379828123108613 / 10000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_682_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (2746637295669 / 2000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) * (1378108348866220666213 / 10000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_682_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (2746637295669 / 2000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) * (956720482436799679737 / 10000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_682_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (2746637295669 / 2000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) * (531080877900712560969 / 10000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_682_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (2746637295669 / 2000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) * (34680649393365873701 / 2500000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_682_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (2746637295669 / 2000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(175689130303678076623 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_682_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (2746637295669 / 2000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(368491277579048029599 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_682_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_683_1 :
    Uω (aρ 1) (bρ 1) (6746637295669 / 4000000000000 : ℝ) ≤
      (648647470165495546441 / 1250000000000000000000 : ℝ) := by
  have hlg :
    Real.log (33604172798388249 / 20000000000000000 : ℝ) ≤
      (648647470165495546441 / 1250000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (16802076777300749 / 10000000000000000 : ℝ)) (q :=
      (33604172798388249 / 20000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_683_2 :
    Uω (aρ 2) (bρ 2) (6746637295669 / 4000000000000 : ℝ) ≤
      (646873916084388180027 / 1250000000000000000000 : ℝ) := by
  have hlg :
    Real.log (16778263776351059 / 10000000000000000 : ℝ) ≤
      (646873916084388180027 / 1250000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (8389100272062309 / 5000000000000000 : ℝ)) (q :=
      (16778263776351059 / 10000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_683_3 :
    Uω (aρ 3) (bρ 3) (6746637295669 / 4000000000000 : ℝ) ≤
      (5146608484439031249377 / 10000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (16730709809385323 / 10000000000000000 : ℝ) ≤
      (5146608484439031249377 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (8365244358271573 / 5000000000000000 : ℝ)) (q :=
      (16730709809385323 / 10000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_683_4 :
    Uω (aρ 4) (bρ 4) (6746637295669 / 4000000000000 : ℝ) ≤
      (637431915769893316069 / 1250000000000000000000 : ℝ) := by
  have hlg :
    Real.log (16652004933609187 / 10000000000000000 : ℝ) ≤
      (637431915769893316069 / 1250000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (8325686573027937 / 5000000000000000 : ℝ)) (q :=
      (16652004933609187 / 10000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_683_5 :
    Uω (aρ 5) (bρ 5) (6746637295669 / 4000000000000 : ℝ) ≤
      (15711355649568528379 / 31250000000000000000 : ℝ) := by
  have hlg :
    Real.log (16532836162270769 / 10000000000000000 : ℝ) ≤
      (15711355649568528379 / 31250000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (8265612761357019 / 5000000000000000 : ℝ)) (q :=
      (16532836162270769 / 10000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_683_6 :
    Uω (aρ 6) (bρ 6) (6746637295669 / 4000000000000 : ℝ) ≤
      (1231163739354149495203 / 2500000000000000000000 : ℝ) := by
  have hlg :
    Real.log (2045432067349599 / 1250000000000000 : ℝ) ≤
      (1231163739354149495203 / 2500000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (4089926662726521 / 2500000000000000 : ℝ)) (q :=
      (2045432067349599 / 1250000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_683_7 :
    Uω (aρ 7) (bρ 7) (6746637295669 / 4000000000000 : ℝ) ≤
      (4784372414919632677529 / 10000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (16135508405435549 / 10000000000000000 : ℝ) ≤
      (4784372414919632677529 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (8063735882471799 / 5000000000000000 : ℝ)) (q :=
      (16135508405435549 / 10000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_683_8 :
    Uω (aρ 8) (bρ 8) (6746637295669 / 4000000000000 : ℝ) ≤
      (1150527614874777660297 / 2500000000000000000000 : ℝ) := by
  have hlg :
    Real.log (15844083326734951 / 10000000000000000 : ℝ) ≤
      (1150527614874777660297 / 2500000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (7914081629441201 / 5000000000000000 : ℝ)) (q :=
      (15844083326734951 / 10000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_683_9 :
    Uω (aρ 9) (bρ 9) (6746637295669 / 4000000000000 : ℝ) ≤
      (4375967434278497798067 / 10000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (15489801450345909 / 10000000000000000 : ℝ) ≤
      (4375967434278497798067 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (7730282567232159 / 5000000000000000 : ℝ)) (q :=
      (15489801450345909 / 10000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_683_10 :
    Uω (aρ 10) (bρ 10) (6746637295669 / 4000000000000 : ℝ) ≤
      (4108233282580037516371 / 10000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (6032235606512157 / 4000000000000000 : ℝ) ≤
      (4108233282580037516371 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (3006139859965657 / 2000000000000000 : ℝ)) (q :=
      (6032235606512157 / 4000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_683_11 :
    Uω (aρ 11) (bρ 11) (6746637295669 / 4000000000000 : ℝ) ≤
      (761357075335845670987 / 2000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (29265542826264307 / 20000000000000000 : ℝ) ≤
      (761357075335845670987 / 2000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 10
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (14553540719736807 / 10000000000000000 : ℝ)) (q :=
      (29265542826264307 / 20000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_683_12 :
    Uω (aρ 12) (bρ 12) (6746637295669 / 4000000000000 : ℝ) ≤
      (139448290184602758597 / 400000000000000000000 : ℝ) := by
  have hlg :
    Real.log (28342232281010363 / 20000000000000000 : ℝ) ≤
      (139448290184602758597 / 400000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (14053930271167863 / 10000000000000000 : ℝ)) (q :=
      (28342232281010363 / 20000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_683_13 :
    Uω (aρ 13) (bρ 13) (6746637295669 / 4000000000000 : ℝ) ≤
      (3168189274869361871549 / 10000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (6863769907032257 / 5000000000000000 : ℝ) ≤
      (3168189274869361871549 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 9
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (1695769919985191 / 1250000000000000 : ℝ)) (q :=
      (6863769907032257 / 5000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_683_14 :
    Uω (aρ 14) (bρ 14) (6746637295669 / 4000000000000 : ℝ) ≤
      (288054402101994101473 / 1000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (13338298652980011 / 10000000000000000 : ℝ) ≤
      (288054402101994101473 / 1000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (6565802161378761 / 5000000000000000 : ℝ)) (q :=
      (13338298652980011 / 10000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_683_15 :
    Uω (aρ 15) (bρ 15) (6746637295669 / 4000000000000 : ℝ) ≤
      (1327044432574458074269 / 5000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (3259910100253591 / 2500000000000000 : ℝ) ≤
      (1327044432574458074269 / 5000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (3198465274060307 / 2500000000000000 : ℝ)) (q :=
      (3259910100253591 / 2500000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_683_16 :
    Uω (aρ 16) (bρ 16) (6746637295669 / 4000000000000 : ℝ) ≤
      (2517089256916817378273 / 10000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (803888497956787 / 625000000000000 : ℝ) ≤
      (2517089256916817378273 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 8
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (3147845970084921 / 2500000000000000 : ℝ)) (q :=
      (803888497956787 / 625000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16]) (by norm_num [bρ_16])
      (by norm_num) (by norm_num [aρ_16, bρ_16]) (by norm_num [aρ_16, bρ_16]) hlg

lemma U_683 :
    Uρ (6746637295669 / 4000000000000 : ℝ) ≤
      (991641173695049392639 / 2500000000000000000000 : ℝ) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (6746637295669 / 4000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (648647470165495546441 / 1250000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_683_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (6746637295669 / 4000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) * (646873916084388180027 / 1250000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_683_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (6746637295669 / 4000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (5146608484439031249377 / 10000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_683_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (6746637295669 / 4000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) * (637431915769893316069 / 1250000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_683_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (6746637295669 / 4000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) * (15711355649568528379 / 31250000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_683_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (6746637295669 / 4000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) * (1231163739354149495203 / 2500000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_683_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (6746637295669 / 4000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (4784372414919632677529 / 10000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_683_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (6746637295669 / 4000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) * (1150527614874777660297 / 2500000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_683_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (6746637295669 / 4000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (4375967434278497798067 / 10000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_683_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (6746637295669 / 4000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) * (4108233282580037516371 / 10000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_683_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (6746637295669 / 4000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) * (761357075335845670987 / 2000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_683_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (6746637295669 / 4000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) * (139448290184602758597 / 400000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_683_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (6746637295669 / 4000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) * (3168189274869361871549 / 10000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_683_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (6746637295669 / 4000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) * (288054402101994101473 / 1000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_683_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (6746637295669 / 4000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) * (1327044432574458074269 / 5000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_683_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (6746637295669 / 4000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (2517089256916817378273 / 10000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_683_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_684_1 : Uω (aρ 1) (bρ 1) (2 : ℝ) ≤ (431197938622519678389 / 625000000000000000000 : ℝ) := by
  have hlg :
    Real.log (19935494672365351 / 10000000000000000 : ℝ) ≤
      (431197938622519678389 / 625000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 14
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (9967743281407851 / 5000000000000000 : ℝ)) (q :=
      (19935494672365351 / 10000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_684_2 :
    Uω (aρ 2) (bρ 2) (2 : ℝ) ≤ (1721803564318625397281 / 2500000000000000000000 : ℝ) := by
  have hlg :
    Real.log (39823360975531723 / 20000000000000000 : ℝ) ≤
      (1721803564318625397281 / 2500000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 14
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (19911627206126723 / 10000000000000000 : ℝ)) (q :=
      (39823360975531723 / 20000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_684_3 :
    Uω (aρ 3) (bρ 3) (2 : ℝ) ≤ (3431657896680287743107 / 5000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (993207572309059 / 500000000000000 : ℝ) ≤
      (3431657896680287743107 / 5000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 14
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (124149782683171 / 62500000000000 : ℝ)) (q :=
      (993207572309059 / 500000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_684_4 :
    Uω (aρ 4) (bρ 4) (2 : ℝ) ≤ (6823648472170288821807 / 10000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (39571023506073419 / 20000000000000000 : ℝ) ≤
      (6823648472170288821807 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 14
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (19784980024083419 / 10000000000000000 : ℝ)) (q :=
      (39571023506073419 / 20000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_684_5 :
    Uω (aρ 5) (bρ 5) (2 : ℝ) ≤ (6763315653946060878467 / 10000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (7866599825072169 / 4000000000000000 : ℝ) ≤
      (6763315653946060878467 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 14
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (3933029112541169 / 2000000000000000 : ℝ)) (q :=
      (7866599825072169 / 4000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_684_6 : Uω (aρ 6) (bρ 6) (2 : ℝ) ≤ (333849709093393011791 / 500000000000000000000 : ℝ) := by
  have hlg :
    Real.log (1949746605406931 / 1000000000000000 : ℝ) ≤
      (333849709093393011791 / 500000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 14
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (974715946031181 / 500000000000000 : ℝ)) (q :=
      (1949746605406931 / 1000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_684_7 :
    Uω (aρ 7) (bρ 7) (2 : ℝ) ≤ (3279879678491493456121 / 5000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (38540444995663327 / 20000000000000000 : ℝ) ≤
      (3279879678491493456121 / 5000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 14
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (19263493188908327 / 10000000000000000 : ℝ)) (q :=
      (38540444995663327 / 20000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_684_8 :
    Uω (aρ 8) (bρ 8) (2 : ℝ) ≤ (6408070500101273547501 / 10000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (37960241040023251 / 20000000000000000 : ℝ) ≤
      (6408070500101273547501 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 14
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (18966830884608251 / 10000000000000000 : ℝ)) (q :=
      (37960241040023251 / 20000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_684_9 :
    Uω (aρ 9) (bρ 9) (2 : ℝ) ≤ (3110439556119279087301 / 5000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (298050139723413 / 160000000000000 : ℝ) ≤
      (3110439556119279087301 / 5000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 13
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (148830583506973 / 80000000000000 : ℝ)) (q :=
      (298050139723413 / 160000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_684_10 :
    Uω (aρ 10) (bρ 10) (2 : ℝ) ≤ (6000773764786687711391 / 10000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (3644519589963523 / 2000000000000000 : ℝ) ≤
      (6000773764786687711391 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 13
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (1818131040607523 / 1000000000000000 : ℝ)) (q :=
      (3644519589963523 / 2000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_684_11 :
    Uω (aρ 11) (bρ 11) (2 : ℝ) ≤ (5755005827102536483859 / 10000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (35560407008524539 / 20000000000000000 : ℝ) ≤
      (5755005827102536483859 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 13
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (17714998141169539 / 10000000000000000 : ℝ)) (q :=
      (35560407008524539 / 20000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_684_12 :
    Uω (aρ 12) (bρ 12) (2 : ℝ) ≤ (1099230232572658765387 / 2000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (34651720907416137 / 20000000000000000 : ℝ) ≤
      (1099230232572658765387 / 2000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (17230012136746137 / 10000000000000000 : ℝ)) (q :=
      (34651720907416137 / 20000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_684_13 :
    Uω (aρ 13) (bρ 13) (2 : ℝ) ≤ (2621030225880535406049 / 5000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (8445586165416359 / 5000000000000000 : ℝ) ≤
      (2621030225880535406049 / 5000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 12
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (4190004408147609 / 2500000000000000 : ℝ)) (q :=
      (8445586165416359 / 5000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_684_14 :
    Uω (aρ 14) (bρ 14) (2 : ℝ) ≤ (250733810854960598567 / 500000000000000000000 : ℝ) := by
  have hlg :
    Real.log (16511427463010601 / 10000000000000000 : ℝ) ≤
      (250733810854960598567 / 500000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (8172227590995601 / 5000000000000000 : ℝ)) (q :=
      (16511427463010601 / 10000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_684_15 :
    Uω (aρ 15) (bρ 15) (2 : ℝ) ≤ (2418686312017971573191 / 5000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (16221253963311517 / 10000000000000000 : ℝ) ≤
      (2418686312017971573191 / 5000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (8011840730004017 / 5000000000000000 : ℝ)) (q :=
      (16221253963311517 / 10000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_684_16 :
    Uω (aρ 16) (bρ 16) (2 : ℝ) ≤ (4730867613563951102639 / 10000000000000000000000 : ℝ) := by
  have hlg :
    Real.log (1604940623761263 / 1000000000000000 : ℝ) ≤
      (4730867613563951102639 / 10000000000000000000000 : ℝ) :=
    log_le_of_ge_one (by norm_num) 11
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)
  exact
    Uω_le_right_certificate (s := (791617883006013 / 500000000000000 : ℝ)) (q :=
      (1604940623761263 / 1000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_684 : Uρ (2 : ℝ) ≤ (1138744120442109294651 / 2000000000000000000000 : ℝ) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (2 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (431197938622519678389 / 625000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_684_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (2 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) * (1721803564318625397281 / 2500000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_684_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (2 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) * (3431657896680287743107 / 5000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_684_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (2 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) * (6823648472170288821807 / 10000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_684_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (2 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) * (6763315653946060878467 / 10000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_684_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (2 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) * (333849709093393011791 / 500000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_684_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (2 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) * (3279879678491493456121 / 5000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_684_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (2 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (6408070500101273547501 / 10000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_684_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (2 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (3110439556119279087301 / 5000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_684_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (2 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) * (6000773764786687711391 / 10000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_684_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (2 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) * (5755005827102536483859 / 10000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_684_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (2 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) * (1099230232572658765387 / 2000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_684_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (2 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) * (2621030225880535406049 / 5000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_684_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (2 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) * (250733810854960598567 / 500000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_684_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (2 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) * (2418686312017971573191 / 5000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_684_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (2 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (4730867613563951102639 / 10000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left U_684_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

end Zeta5Irrational
