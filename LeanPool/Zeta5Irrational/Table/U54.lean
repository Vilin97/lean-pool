/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Table.UpperCertificate

/-! # Certified arcsine potential bounds (U54) -/

public section

open Finset

namespace Zeta5Irrational

lemma U_652_1 :
    Uω (aρ 1) (bρ 1) (773330129695373 / 1024000000000000 : ℝ) ≤
      (-(2893456901553794808471 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (191680850895698137 / 256000000000000000 : ℝ) ≤
      (-(2893456901553794808471 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (191680850895698137 / 256000000000000000 : ℝ) =
            (191680850895698137 / 128000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (191680850895698137 / 128000000000000000 : ℝ) ≤
            (4038014901446205191529 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (93593895581313 / 125000000000000 : ℝ)) (q :=
      (191680850895698137 / 256000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1])
      (by norm_num [bρ_1]) (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_652_2 :
    Uω (aρ 2) (bρ 2) (773330129695373 / 1024000000000000 : ℝ) ≤
      (-(1462706849909965999691 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (191069277983419033 / 256000000000000000 : ℝ) ≤
      (-(1462706849909965999691 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (191069277983419033 / 256000000000000000 : ℝ) =
            (191069277983419033 / 128000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (191069277983419033 / 128000000000000000 : ℝ) ≤
            (2003029051590034000309 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1492700305048647 / 2000000000000000 : ℝ)) (q :=
      (191069277983419033 / 256000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2])
      (by norm_num [bρ_2]) (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_652_3 :
    Uω (aρ 3) (bρ 3) (773330129695373 / 1024000000000000 : ℝ) ≤
      (-(1494799872180451229579 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (189846807339465497 / 256000000000000000 : ℝ) ≤
      (-(1494799872180451229579 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (189846807339465497 / 256000000000000000 : ℝ) =
            (189846807339465497 / 128000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (189846807339465497 / 128000000000000000 : ℝ) ≤
            (1970936029319548770421 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1483078422506873 / 2000000000000000 : ℝ)) (q :=
      (189846807339465497 / 256000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3])
      (by norm_num [bρ_3]) (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_652_4 :
    Uω (aρ 4) (bρ 4) (773330129695373 / 1024000000000000 : ℝ) ≤
      (-(3097011815094364335053 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (187818536011483673 / 256000000000000000 : ℝ) ≤
      (-(3097011815094364335053 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (187818536011483673 / 256000000000000000 : ℝ) =
            (187818536011483673 / 128000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (187818536011483673 / 128000000000000000 : ℝ) ≤
            (3834459987905635664947 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1467045519220157 / 2000000000000000 : ℝ)) (q :=
      (187818536011483673 / 256000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4])
      (by norm_num [bρ_4]) (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_652_5 :
    Uω (aρ 5) (bρ 5) (773330129695373 / 1024000000000000 : ℝ) ≤
      (-(3262544425323638530593 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (923675587414507837 / 1280000000000000000 : ℝ) ≤
      (-(3262544425323638530593 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (923675587414507837 / 1280000000000000000 : ℝ) =
            (923675587414507837 / 640000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (923675587414507837 / 640000000000000000 : ℝ) ≤
            (3668927377676361469407 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1803131360722577 / 2500000000000000 : ℝ)) (q :=
      (923675587414507837 / 1280000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5])
      (by norm_num [bρ_5]) (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_652_6 :
    Uω (aρ 6) (bρ 6) (773330129695373 / 1024000000000000 : ℝ) ≤
      (-(1752077120803032959657 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (901626119520754429 / 1280000000000000000 : ℝ) ≤
      (-(1752077120803032959657 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (901626119520754429 / 1280000000000000000 : ℝ) =
            (901626119520754429 / 640000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (901626119520754429 / 640000000000000000 : ℝ) ≤
            (1713658780696967040343 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7035242882190411 / 10000000000000000 : ℝ)) (q :=
      (901626119520754429 / 1280000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6])
      (by norm_num [bρ_6]) (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_652_7 :
    Uω (aρ 7) (bρ 7) (773330129695373 / 1024000000000000 : ℝ) ≤
      (-(3841985736840612427921 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (871675117636903997 / 1280000000000000000 : ℝ) ≤
      (-(3841985736840612427921 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (871675117636903997 / 1280000000000000000 : ℝ) =
            (871675117636903997 / 640000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (871675117636903997 / 640000000000000000 : ℝ) ≤
            (3089486066159387572079 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (424432491157203 / 625000000000000 : ℝ)) (q :=
      (871675117636903997 / 1280000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7])
      (by norm_num [bρ_7]) (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_652_8 :
    Uω (aρ 8) (bρ 8) (773330129695373 / 1024000000000000 : ℝ) ≤
      (-(4297532680459312403669 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (832857108142459837 / 1280000000000000000 : ℝ) ≤
      (-(4297532680459312403669 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (832857108142459837 / 1280000000000000000 : ℝ) =
            (832857108142459837 / 640000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (832857108142459837 / 640000000000000000 : ℝ) ≤
            (2633939122540687596331 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3233965055752279 / 5000000000000000 : ℝ)) (q :=
      (832857108142459837 / 1280000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8])
      (by norm_num [bρ_8]) (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_652_9 :
    Uω (aρ 9) (bρ 9) (773330129695373 / 1024000000000000 : ℝ) ≤
      (-(2446440040483157550377 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (784720299999318333 / 1280000000000000000 : ℝ) ≤
      (-(2446440040483157550377 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (784720299999318333 / 1280000000000000000 : ℝ) =
            (784720299999318333 / 640000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (784720299999318333 / 640000000000000000 : ℝ) ≤
            (1019295861016842449623 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1514189528156993 / 2500000000000000 : ℝ)) (q :=
      (784720299999318333 / 1280000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9])
      (by norm_num [bρ_9]) (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_652_10 :
    Uω (aρ 10) (bρ 10) (773330129695373 / 1024000000000000 : ℝ) ≤
      (-(5650069981818022359461 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (145499179298836569 / 256000000000000000 : ℝ) ≤
      (-(5650069981818022359461 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (145499179298836569 / 256000000000000000 : ℝ) =
            (145499179298836569 / 128000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (145499179298836569 / 128000000000000000 : ℝ) ≤
            (1281401821181977640539 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (555118584135523 / 1000000000000000 : ℝ)) (q :=
      (145499179298836569 / 256000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_652_11 :
    Uω (aρ 11) (bρ 11) (773330129695373 / 1024000000000000 : ℝ) ≤
      (-(6590630992571855497951 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (662189823576252669 / 1280000000000000000 : ℝ) ≤
      (-(6590630992571855497951 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (662189823576252669 / 1280000000000000000 : ℝ) =
            (662189823576252669 / 640000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (662189823576252669 / 640000000000000000 : ℝ) ≤
            (340840810428144502049 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4949255078217571 / 10000000000000000 : ℝ)) (q :=
      (662189823576252669 / 1280000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_652_12 :
    Uω (aρ 12) (bρ 12) (773330129695373 / 1024000000000000 : ℝ) ≤
      (-(7735265208020603162373 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (590570391768275581 / 1280000000000000000 : ℝ) ≤
      (-(7735265208020603162373 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (590570391768275581 / 1280000000000000000 : ℝ) =
            (590570391768275581 / 320000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (590570391768275581 / 320000000000000000 : ℝ) ≤
            (6127678397979396837627 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4253901552902929 / 10000000000000000 : ℝ)) (q :=
      (590570391768275581 / 1280000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_652_13 :
    Uω (aρ 13) (bρ 13) (773330129695373 / 1024000000000000 : ℝ) ≤
      (-(9103538205482609527087 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (515048739424809981 / 1280000000000000000 : ℝ) ≤
      (-(9103538205482609527087 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (515048739424809981 / 1280000000000000000 : ℝ) =
            (515048739424809981 / 320000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (515048739424809981 / 320000000000000000 : ℝ) ≤
            (4759405400517390472913 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3473257476631279 / 10000000000000000 : ℝ)) (q :=
      (515048739424809981 / 1280000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_652_14 :
    Uω (aρ 14) (bρ 14) (773330129695373 / 1024000000000000 : ℝ) ≤
      (-(10712917914125938837233 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (438484106052634813 / 1280000000000000000 : ℝ) ≤
      (-(10712917914125938837233 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (438484106052634813 / 1280000000000000000 : ℝ) =
            (438484106052634813 / 320000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (438484106052634813 / 320000000000000000 : ℝ) ≤
            (3150025691874061162767 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1310431182618021 / 5000000000000000 : ℝ)) (q :=
      (438484106052634813 / 1280000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_652_15 :
    Uω (aρ 15) (bρ 15) (773330129695373 / 1024000000000000 : ℝ) ≤
      (-(1571724976514098835237 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2912237359646401 / 10240000000000000 : ℝ) ≤
      (-(1571724976514098835237 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (2912237359646401 / 10240000000000000 : ℝ) =
            (2912237359646401 / 2560000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2912237359646401 / 2560000000000000 : ℝ) ≤
            (161142974235901164763 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (858542539319 / 5000000000000 : ℝ)) (q :=
      (2912237359646401 / 10240000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_652_16 :
    Uω (aρ 16) (bρ 16) (773330129695373 / 1024000000000000 : ℝ) ≤
      (-(7323588502680710169883 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (295863339134328381 / 1280000000000000000 : ℝ) ≤
      (-(7323588502680710169883 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (295863339134328381 / 1280000000000000000 : ℝ) =
            (295863339134328381 / 160000000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (295863339134328381 / 160000000000000000 : ℝ) ≤
            (3073619201819289830117 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (100544726382813 / 1250000000000000 : ℝ)) (q :=
      (295863339134328381 / 1280000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_652 :
    Uρ (773330129695373 / 1024000000000000 : ℝ) ≤
      (-(636726646180617477787 / 1250000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (773330129695373 / 1024000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(2893456901553794808471 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_652_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) *
        Uω (aρ 2) (bρ 2) (773330129695373 / 1024000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(1462706849909965999691 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_652_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) *
        Uω (aρ 3) (bρ 3) (773330129695373 / 1024000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(1494799872180451229579 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_652_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (773330129695373 / 1024000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(3097011815094364335053 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_652_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (773330129695373 / 1024000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(3262544425323638530593 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_652_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) *
        Uω (aρ 6) (bρ 6) (773330129695373 / 1024000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(1752077120803032959657 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_652_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) *
        Uω (aρ 7) (bρ 7) (773330129695373 / 1024000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(3841985736840612427921 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_652_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) *
        Uω (aρ 8) (bρ 8) (773330129695373 / 1024000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(4297532680459312403669 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_652_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (773330129695373 / 1024000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(2446440040483157550377 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_652_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) *
        Uω (aρ 10) (bρ 10) (773330129695373 / 1024000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(5650069981818022359461 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_652_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) *
        Uω (aρ 11) (bρ 11) (773330129695373 / 1024000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(6590630992571855497951 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_652_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) *
        Uω (aρ 12) (bρ 12) (773330129695373 / 1024000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(7735265208020603162373 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_652_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) *
        Uω (aρ 13) (bρ 13) (773330129695373 / 1024000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(9103538205482609527087 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_652_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) *
        Uω (aρ 14) (bρ 14) (773330129695373 / 1024000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(10712917914125938837233 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_652_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) *
        Uω (aρ 15) (bρ 15) (773330129695373 / 1024000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(1571724976514098835237 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_652_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) *
        Uω (aρ 16) (bρ 16) (773330129695373 / 1024000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(7323588502680710169883 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_652_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_653_1 :
    Uω (aρ 1) (bρ 1) (96822936549963 / 128000000000000 : ℝ) ≤
      (-(2877123201811696091637 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (119996370296175819 / 160000000000000000 : ℝ) ≤
      (-(2877123201811696091637 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (119996370296175819 / 160000000000000000 : ℝ) =
            (119996370296175819 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (119996370296175819 / 80000000000000000 : ℝ) ≤
            (4054348601188303908363 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3749875793570559 / 5000000000000000 : ℝ)) (q :=
      (119996370296175819 / 160000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1])
      (by norm_num [bρ_1]) (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_653_2 :
    Uω (aρ 2) (bρ 2) (96822936549963 / 128000000000000 : ℝ) ≤
      (-(1454513748973133960733 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (119614140385909363 / 160000000000000000 : ℝ) ≤
      (-(1454513748973133960733 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (119614140385909363 / 160000000000000000 : ℝ) =
            (119614140385909363 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (119614140385909363 / 80000000000000000 : ℝ) ≤
            (2011222152526866039267 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7475741860867811 / 10000000000000000 : ℝ)) (q :=
      (119614140385909363 / 160000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2])
      (by norm_num [bρ_2]) (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_653_3 :
    Uω (aρ 3) (bρ 3) (96822936549963 / 128000000000000 : ℝ) ≤
      (-(185819207586795205137 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (118850105661120603 / 160000000000000000 : ℝ) ≤
      (-(185819207586795205137 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (118850105661120603 / 160000000000000000 : ℝ) =
            (118850105661120603 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (118850105661120603 / 80000000000000000 : ℝ) ≤
            (247397780100704794863 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (464227101663701 / 625000000000000 : ℝ)) (q :=
      (118850105661120603 / 160000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3])
      (by norm_num [bρ_3]) (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_653_4 :
    Uω (aρ 4) (bρ 4) (96822936549963 / 128000000000000 : ℝ) ≤
      (-(3080339305095248653731 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (117582461150381027 / 160000000000000000 : ℝ) ≤
      (-(3080339305095248653731 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (117582461150381027 / 160000000000000000 : ℝ) =
            (117582461150381027 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (117582461150381027 / 80000000000000000 : ℝ) ≤
            (3851132497904751346269 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7347472243841769 / 10000000000000000 : ℝ)) (q :=
      (117582461150381027 / 160000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4])
      (by norm_num [bρ_4]) (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_653_5 :
    Uω (aρ 5) (bρ 5) (96822936549963 / 128000000000000 : ℝ) ≤
      (-(64911770518235379883 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (115655386374443651 / 160000000000000000 : ℝ) ≤
      (-(64911770518235379883 / 200000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (115655386374443651 / 160000000000000000 : ℝ) =
            (115655386374443651 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (115655386374443651 / 80000000000000000 : ℝ) ≤
            (73717665541764620117 / 200000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7224777816184597 / 10000000000000000 : ℝ)) (q :=
      (115655386374443651 / 160000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5])
      (by norm_num [bρ_5]) (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_653_6 :
    Uω (aρ 6) (bρ 6) (96822936549963 / 128000000000000 : ℝ) ≤
      (-(174338573018717726637 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (22579868986271223 / 32000000000000000 : ℝ) ≤
      (-(174338573018717726637 / 500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (22579868986271223 / 32000000000000000 : ℝ) =
            (22579868986271223 / 16000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (22579868986271223 / 16000000000000000 : ℝ) ≤
            (172235017131282273363 / 500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1409502602187731 / 2000000000000000 : ℝ)) (q :=
      (22579868986271223 / 32000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_653_7 :
    Uω (aρ 7) (bρ 7) (96822936549963 / 128000000000000 : ℝ) ≤
      (-(1911989087255013801439 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (109155775773423779 / 160000000000000000 : ℝ) ≤
      (-(1911989087255013801439 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (109155775773423779 / 160000000000000000 : ℝ) =
            (109155775773423779 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (109155775773423779 / 80000000000000000 : ℝ) ≤
            (1553746814244986198561 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6803228246957113 / 10000000000000000 : ℝ)) (q :=
      (109155775773423779 / 160000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7])
      (by norm_num [bρ_7]) (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_653_8 :
    Uω (aρ 8) (bρ 8) (96822936549963 / 128000000000000 : ℝ) ≤
      (-(2139313420275157981527 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (20860829596002847 / 32000000000000000 : ℝ) ≤
      (-(2139313420275157981527 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (20860829596002847 / 32000000000000000 : ℝ) =
            (20860829596002847 / 16000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (20860829596002847 / 16000000000000000 : ℝ) ≤
            (1326422481224842018473 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (162007910603023 / 250000000000000 : ℝ)) (q :=
      (20860829596002847 / 32000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_653_9 :
    Uω (aρ 9) (bρ 9) (96822936549963 / 128000000000000 : ℝ) ≤
      (-(1218173088127056917877 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (786306072150831 / 1280000000000000 : ℝ) ≤
      (-(1218173088127056917877 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (786306072150831 / 1280000000000000 : ℝ) =
            (786306072150831 / 640000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (786306072150831 / 640000000000000 : ℝ) ≤
            (514694862622943082123 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (48554367458687 / 80000000000000 : ℝ)) (q :=
      (786306072150831 / 1280000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_653_10 :
    Uω (aρ 10) (bρ 10) (96822936549963 / 128000000000000 : ℝ) ≤
      (-(5628046299432133914873 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (91137484497341187 / 160000000000000000 : ℝ) ≤
      (-(5628046299432133914873 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (91137484497341187 / 160000000000000000 : ℝ) =
            (91137484497341187 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (91137484497341187 / 80000000000000000 : ℝ) ≤
            (1303425503567866085127 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (5564008150641789 / 10000000000000000 : ℝ)) (q :=
      (91137484497341187 / 160000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_653_11 :
    Uω (aρ 11) (bρ 11) (96822936549963 / 128000000000000 : ℝ) ≤
      (-(6565933545682449290393 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (82978410574888283 / 160000000000000000 : ℝ) ≤
      (-(6565933545682449290393 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (82978410574888283 / 160000000000000000 : ℝ) =
            (82978410574888283 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (82978410574888283 / 80000000000000000 : ℝ) ≤
            (365538257317550709607 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (310162533533761 / 625000000000000 : ℝ)) (q :=
      (82978410574888283 / 160000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_653_12 :
    Uω (aρ 12) (bρ 12) (96822936549963 / 128000000000000 : ℝ) ≤
      (-(7706540205108390999763 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (74033655524941171 / 160000000000000000 : ℝ) ≤
      (-(7706540205108390999763 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (74033655524941171 / 160000000000000000 : ℝ) =
            (74033655524941171 / 40000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (74033655524941171 / 40000000000000000 : ℝ) ≤
            (6156403400891609000237 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4268206251981787 / 10000000000000000 : ℝ)) (q :=
      (74033655524941171 / 160000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_653_13 :
    Uω (aρ 13) (bρ 13) (96822936549963 / 128000000000000 : ℝ) ≤
      (-(2267094840206635581753 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (64607847299227699 / 160000000000000000 : ℝ) ≤
      (-(2267094840206635581753 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (64607847299227699 / 160000000000000000 : ℝ) =
            (64607847299227699 / 40000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (64607847299227699 / 40000000000000000 : ℝ) ≤
            (1198641061293364418247 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3489361965362603 / 10000000000000000 : ℝ)) (q :=
      (64607847299227699 / 160000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_653_14 :
    Uω (aρ 14) (bρ 14) (96822936549963 / 128000000000000 : ℝ) ≤
      (-(10666391102895760677611 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (55066123271789059 / 160000000000000000 : ℝ) ≤
      (-(10666391102895760677611 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (55066123271789059 / 160000000000000000 : ℝ) =
            (55066123271789059 / 40000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (55066123271789059 / 40000000000000000 : ℝ) ≤
            (3196552503104239322389 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2640573746977773 / 10000000000000000 : ℝ)) (q :=
      (55066123271789059 / 160000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_653_15 :
    Uω (aρ 15) (bρ 15) (96822936549963 / 128000000000000 : ℝ) ≤
      (-(12503095599865301573741 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (45826579202610331 / 160000000000000000 : ℝ) ≤
      (-(12503095599865301573741 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (45826579202610331 / 160000000000000000 : ℝ) =
            (45826579202610331 / 40000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (45826579202610331 / 40000000000000000 : ℝ) ≤
            (1359848006134698426259 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (218150501968179 / 1250000000000000 : ℝ)) (q :=
      (45826579202610331 / 160000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_653_16 :
    Uω (aρ 16) (bρ 16) (96822936549963 / 128000000000000 : ℝ) ≤
      (-(14500144393995872475567 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (37530704140993003 / 160000000000000000 : ℝ) ≤
      (-(14500144393995872475567 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (37530704140993003 / 160000000000000000 : ℝ) =
            (37530704140993003 / 20000000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (37530704140993003 / 20000000000000000 : ℝ) ≤
            (6294271015004127524433 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (430295642276633 / 5000000000000000 : ℝ)) (q :=
      (37530704140993003 / 160000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_653 :
    Uρ (96822936549963 / 128000000000000 : ℝ) ≤
      (-(2535469459548085995737 / 5000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (96822936549963 / 128000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(2877123201811696091637 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_653_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (96822936549963 / 128000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(1454513748973133960733 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_653_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (96822936549963 / 128000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(185819207586795205137 / 625000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_653_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (96822936549963 / 128000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(3080339305095248653731 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_653_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (96822936549963 / 128000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) * (-(64911770518235379883 / 200000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_653_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (96822936549963 / 128000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(174338573018717726637 / 500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_653_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (96822936549963 / 128000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(1911989087255013801439 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_653_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (96822936549963 / 128000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(2139313420275157981527 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_653_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (96822936549963 / 128000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(1218173088127056917877 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_653_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (96822936549963 / 128000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(5628046299432133914873 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_653_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (96822936549963 / 128000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(6565933545682449290393 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_653_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (96822936549963 / 128000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(7706540205108390999763 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_653_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (96822936549963 / 128000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(2267094840206635581753 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_653_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (96822936549963 / 128000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(10666391102895760677611 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_653_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) *
        Uω (aρ 15) (bρ 15) (96822936549963 / 128000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(12503095599865301573741 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_653_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (96822936549963 / 128000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(14500144393995872475567 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_653_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_654_1 :
    Uω (aρ 1) (bρ 1) (155167371020807 / 204800000000000 : ℝ) ≤
      (-(178801008606094785107 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (192307534049124759 / 256000000000000000 : ℝ) ≤
      (-(178801008606094785107 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (192307534049124759 / 256000000000000000 : ℝ) =
            (192307534049124759 / 128000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (192307534049124759 / 128000000000000000 : ℝ) ≤
            (254415979081405214893 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (751199152754753 / 1000000000000000 : ℝ)) (q :=
      (192307534049124759 / 256000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1])
      (by norm_num [bρ_1]) (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_654_2 :
    Uω (aρ 2) (bρ 2) (155167371020807 / 204800000000000 : ℝ) ≤
      (-(180791756495602557493 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (958479856160063987 / 1280000000000000000 : ℝ) ≤
      (-(180791756495602557493 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (958479856160063987 / 1280000000000000000 : ℝ) =
            (958479856160063987 / 640000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (958479856160063987 / 640000000000000000 : ℝ) ≤
            (252425231191897442507 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3743991097485329 / 5000000000000000 : ℝ)) (q :=
      (958479856160063987 / 1280000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2])
      (by norm_num [bρ_2]) (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_654_3 :
    Uω (aρ 3) (bρ 3) (155167371020807 / 204800000000000 : ℝ) ≤
      (-(2956642057273893298753 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7618941228275183 / 10240000000000000 : ℝ) ≤
      (-(2956642057273893298753 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (7618941228275183 / 10240000000000000 : ℝ) =
            (7618941228275183 / 5120000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7618941228275183 / 5120000000000000 : ℝ) ≤
            (3974829745726106701247 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (59519001082357 / 80000000000000 : ℝ)) (q :=
      (7618941228275183 / 10240000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_654_4 :
    Uω (aρ 4) (bρ 4) (155167371020807 / 204800000000000 : ℝ) ≤
      (-(612738911377929143541 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (942226697331449523 / 1280000000000000000 : ℝ) ≤
      (-(612738911377929143541 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (942226697331449523 / 1280000000000000000 : ℝ) =
            (942226697331449523 / 640000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (942226697331449523 / 640000000000000000 : ℝ) ≤
            (773555449222070856459 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7359716875688557 / 10000000000000000 : ℝ)) (q :=
      (942226697331449523 / 1280000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4])
      (by norm_num [bρ_4]) (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_654_5 :
    Uω (aρ 5) (bρ 5) (155167371020807 / 204800000000000 : ℝ) ≤
      (-(3228661357312839731263 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (926810591868475827 / 1280000000000000000 : ℝ) ≤
      (-(3228661357312839731263 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (926810591868475827 / 1280000000000000000 : ℝ) =
            (926810591868475827 / 640000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (926810591868475827 / 640000000000000000 : ℝ) ≤
            (3702810445687160268737 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7237030147164593 / 10000000000000000 : ℝ)) (q :=
      (926810591868475827 / 1280000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5])
      (by norm_num [bρ_5]) (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_654_6 :
    Uω (aρ 6) (bρ 6) (155167371020807 / 204800000000000 : ℝ) ≤
      (-(1734709458567699032261 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (904763392657673011 / 1280000000000000000 : ℝ) ≤
      (-(1734709458567699032261 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (904763392657673011 / 1280000000000000000 : ℝ) =
            (904763392657673011 / 640000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (904763392657673011 / 640000000000000000 : ℝ) ≤
            (1731026442932300967739 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7059783034635799 / 10000000000000000 : ℝ)) (q :=
      (904763392657673011 / 1280000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6])
      (by norm_num [bρ_6]) (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_654_7 :
    Uω (aρ 7) (bρ 7) (155167371020807 / 204800000000000 : ℝ) ≤
      (-(761200632335293118429 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (874817278943332787 / 1280000000000000000 : ℝ) ≤
      (-(761200632335293118429 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (874817278943332787 / 1280000000000000000 : ℝ) =
            (874817278943332787 / 640000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (874817278943332787 / 640000000000000000 : ℝ) ≤
            (625093728264706881571 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6815536388609233 / 10000000000000000 : ℝ)) (q :=
      (874817278943332787 / 1280000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7])
      (by norm_num [bρ_7]) (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_654_8 :
    Uω (aρ 8) (bρ 8) (155167371020807 / 204800000000000 : ℝ) ≤
      (-(425975710149634223111 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (33440368959579563 / 51200000000000000 : ℝ) ≤
      (-(425975710149634223111 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (33440368959579563 / 51200000000000000 : ℝ) =
            (33440368959579563 / 25600000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (33440368959579563 / 25600000000000000 : ℝ) ≤
            (267171470150365776889 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (259708087251817 / 400000000000000 : ℝ)) (q :=
      (33440368959579563 / 51200000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_654_9 :
    Uω (aρ 9) (bρ 9) (155167371020807 / 204800000000000 : ℝ) ≤
      (-(4852546282406263118157 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (787891766615224371 / 1280000000000000000 : ℝ) ≤
      (-(4852546282406263118157 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (787891766615224371 / 1280000000000000000 : ℝ) =
            (787891766615224371 / 640000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (787891766615224371 / 640000000000000000 : ℝ) ≤
            (2078925520593736881843 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6081832538182539 / 10000000000000000 : ℝ)) (q :=
      (787891766615224371 / 1280000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9])
      (by norm_num [bρ_9]) (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_654_10 :
    Uω (aρ 10) (bρ 10) (155167371020807 / 204800000000000 : ℝ) ≤
      (-(2803036653647281027841 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (146140737589014167 / 256000000000000000 : ℝ) ≤
      (-(2803036653647281027841 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (146140737589014167 / 256000000000000000 : ℝ) =
            (146140737589014167 / 128000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (146140737589014167 / 128000000000000000 : ℝ) ≤
            (662699247852718972159 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (557682784245639 / 1000000000000000 : ℝ)) (q :=
      (146140737589014167 / 256000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_654_11 :
    Uω (aρ 11) (bρ 11) (155167371020807 / 204800000000000 : ℝ) ≤
      (-(817662801515715558399 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (665464381799973043 / 1280000000000000000 : ℝ) ≤
      (-(817662801515715558399 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (665464381799973043 / 1280000000000000000 : ℝ) =
            (665464381799973043 / 640000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (665464381799973043 / 640000000000000000 : ℝ) ≤
            (48771173859284441601 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4975940310144237 / 10000000000000000 : ℝ)) (q :=
      (665464381799973043 / 1280000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_654_12 :
    Uω (aρ 12) (bρ 12) (155167371020807 / 204800000000000 : ℝ) ≤
      (-(239934727155107788411 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (23758691100856299 / 51200000000000000 : ℝ) ≤
      (-(239934727155107788411 / 312500000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (23758691100856299 / 51200000000000000 : ℝ) =
            (23758691100856299 / 12800000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (23758691100856299 / 12800000000000000 : ℝ) ≤
            (193282260532392211589 / 312500000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (85649963049533 / 200000000000000 : ℝ)) (q :=
      (23758691100856299 / 51200000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_654_13 :
    Uω (aρ 13) (bρ 13) (155167371020807 / 204800000000000 : ℝ) ≤
      (-(2258345563885136111871 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (518674817457819507 / 1280000000000000000 : ℝ) ≤
      (-(2258345563885136111871 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (518674817457819507 / 1280000000000000000 : ℝ) =
            (518674817457819507 / 320000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (518674817457819507 / 320000000000000000 : ℝ) ≤
            (1207390337614863888129 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (438179400697261 / 1250000000000000 : ℝ)) (q :=
      (518674817457819507 / 1280000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_654_14 :
    Uω (aρ 14) (bρ 14) (155167371020807 / 204800000000000 : ℝ) ≤
      (-(5310104766705545786437 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (442568123075821491 / 1280000000000000000 : ℝ) ≤
      (-(5310104766705545786437 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (442568123075821491 / 1280000000000000000 : ℝ) =
            (442568123075821491 / 320000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (442568123075821491 / 320000000000000000 : ℝ) ≤
            (1621367036294454213563 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2660195390904369 / 10000000000000000 : ℝ)) (q :=
      (442568123075821491 / 1280000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_654_15 :
    Uω (aρ 15) (bρ 15) (155167371020807 / 204800000000000 : ℝ) ≤
      (-(12433514339998384626713 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (369172466004084083 / 1280000000000000000 : ℝ) ≤
      (-(12433514339998384626713 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (369172466004084083 / 1280000000000000000 : ℝ) =
            (369172466004084083 / 320000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (369172466004084083 / 320000000000000000 : ℝ) ≤
            (1429429266001615373287 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (55405047705421 / 312500000000000 : ℝ)) (q :=
      (369172466004084083 / 1280000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_654_16 :
    Uω (aρ 16) (bρ 16) (155167371020807 / 204800000000000 : ℝ) ≤
      (-(14362160113274664036023 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (304417265698092147 / 1280000000000000000 : ℝ) ≤
      (-(14362160113274664036023 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (304417265698092147 / 1280000000000000000 : ℝ) =
            (304417265698092147 / 160000000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (304417265698092147 / 160000000000000000 : ℝ) ≤
            (6432255295725335963977 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (228383293325587 / 2500000000000000 : ℝ)) (q :=
      (304417265698092147 / 1280000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_654 :
    Uρ (155167371020807 / 204800000000000 : ℝ) ≤
      (-(5048211830024685695573 / 10000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (155167371020807 / 204800000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(178801008606094785107 / 625000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_654_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (155167371020807 / 204800000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(180791756495602557493 / 625000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_654_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (155167371020807 / 204800000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(2956642057273893298753 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_654_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (155167371020807 / 204800000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(612738911377929143541 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_654_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (155167371020807 / 204800000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(3228661357312839731263 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_654_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (155167371020807 / 204800000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(1734709458567699032261 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_654_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (155167371020807 / 204800000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(761200632335293118429 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_654_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (155167371020807 / 204800000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(425975710149634223111 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_654_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (155167371020807 / 204800000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(4852546282406263118157 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_654_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) *
        Uω (aρ 10) (bρ 10) (155167371020807 / 204800000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(2803036653647281027841 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_654_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) *
        Uω (aρ 11) (bρ 11) (155167371020807 / 204800000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(817662801515715558399 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_654_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) *
        Uω (aρ 12) (bρ 12) (155167371020807 / 204800000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) * (-(239934727155107788411 / 312500000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_654_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) *
        Uω (aρ 13) (bρ 13) (155167371020807 / 204800000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(2258345563885136111871 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_654_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) *
        Uω (aρ 14) (bρ 14) (155167371020807 / 204800000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(5310104766705545786437 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_654_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) *
        Uω (aρ 15) (bρ 15) (155167371020807 / 204800000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(12433514339998384626713 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_654_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) *
        Uω (aρ 16) (bρ 16) (155167371020807 / 204800000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(14362160113274664036023 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_654_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_655_1 :
    Uω (aρ 1) (bρ 1) (388545108904183 / 512000000000000 : ℝ) ≤
      (-(44445869101279289721 / 156250000000000000000 : ℝ)) := by
  have hlg :
    Real.log (481552189053607047 / 640000000000000000 : ℝ) ≤
      (-(44445869101279289721 / 156250000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (481552189053607047 / 640000000000000000 : ℝ) =
            (481552189053607047 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (481552189053607047 / 320000000000000000 : ℝ) ≤
            (63858377820595710279 / 156250000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1881057866931349 / 2500000000000000 : ℝ)) (q :=
      (481552189053607047 / 640000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1])
      (by norm_num [bρ_1]) (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_655_2 :
    Uω (aρ 2) (bρ 2) (388545108904183 / 512000000000000 : ℝ) ≤
      (-(2876335430194582704191 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (480023294567969607 / 640000000000000000 : ℝ) ≤
      (-(2876335430194582704191 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (480023294567969607 / 640000000000000000 : ℝ) =
            (480023294567969607 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (480023294567969607 / 320000000000000000 : ℝ) ≤
            (4055136372805417295809 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3750111263779613 / 5000000000000000 : ℝ)) (q :=
      (480023294567969607 / 640000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2])
      (by norm_num [bρ_2]) (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_655_3 :
    Uω (aρ 3) (bρ 3) (388545108904183 / 512000000000000 : ℝ) ≤
      (-(2940203862703970074569 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (476967230717666407 / 640000000000000000 : ℝ) ≤
      (-(2940203862703970074569 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (476967230717666407 / 640000000000000000 : ℝ) =
            (476967230717666407 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (476967230717666407 / 320000000000000000 : ℝ) ≤
            (3991267940296029925431 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7452116638587251 / 10000000000000000 : ℝ)) (q :=
      (476967230717666407 / 640000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3])
      (by norm_num [bρ_3]) (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_655_4 :
    Uω (aρ 4) (bρ 4) (388545108904183 / 512000000000000 : ℝ) ≤
      (-(3047077478141810132203 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (471896852223845543 / 640000000000000000 : ℝ) ≤
      (-(3047077478141810132203 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (471896852223845543 / 640000000000000000 : ℝ) =
            (471896852223845543 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (471896852223845543 / 320000000000000000 : ℝ) ≤
            (3884394324858189867797 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7371961491720349 / 10000000000000000 : ℝ)) (q :=
      (471896852223845543 / 640000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4])
      (by norm_num [bρ_4]) (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_655_5 :
    Uω (aρ 5) (bρ 5) (388545108904183 / 512000000000000 : ℝ) ≤
      (-(80294070555689559269 / 250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (464189045023509479 / 640000000000000000 : ℝ) ≤
      (-(80294070555689559269 / 250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (464189045023509479 / 640000000000000000 : ℝ) =
            (464189045023509479 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (464189045023509479 / 320000000000000000 : ℝ) ≤
            (92992724519310440731 / 250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7249282436044847 / 10000000000000000 : ℝ)) (q :=
      (464189045023509479 / 640000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5])
      (by norm_num [bρ_5]) (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_655_6 :
    Uω (aρ 6) (bρ 6) (388545108904183 / 512000000000000 : ℝ) ≤
      (-(1726048253307382550747 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (453166009588110663 / 640000000000000000 : ℝ) ≤
      (-(1726048253307382550747 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (453166009588110663 / 640000000000000000 : ℝ) =
            (453166009588110663 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (453166009588110663 / 320000000000000000 : ℝ) ≤
            (1739687648192617449253 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3536026476914317 / 5000000000000000 : ℝ)) (q :=
      (453166009588110663 / 640000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6])
      (by norm_num [bρ_6]) (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_655_7 :
    Uω (aρ 7) (bρ 7) (388545108904183 / 512000000000000 : ℝ) ≤
      (-(3788060580235419980457 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (438194167995073671 / 640000000000000000 : ℝ) ≤
      (-(3788060580235419980457 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (438194167995073671 / 640000000000000000 : ℝ) =
            (438194167995073671 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (438194167995073671 / 320000000000000000 : ℝ) ≤
            (3143411222764580019543 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1706961071201557 / 2500000000000000 : ℝ)) (q :=
      (438194167995073671 / 640000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7])
      (by norm_num [bρ_7]) (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_655_8 :
    Uω (aρ 8) (bρ 8) (388545108904183 / 512000000000000 : ℝ) ≤
      (-(4240923324085287446963 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (16751704575872767 / 25600000000000000 : ℝ) ≤
      (-(4240923324085287446963 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (16751704575872767 / 25600000000000000 : ℝ) =
            (16751704575872767 / 12800000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (16751704575872767 / 12800000000000000 : ℝ) ≤
            (2690548478914712553037 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (260203495448031 / 400000000000000 : ℝ)) (q :=
      (16751704575872767 / 25600000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_655_9 :
    Uω (aρ 9) (bρ 9) (388545108904183 / 512000000000000 : ℝ) ≤
      (-(966488339018040144383 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (394738691935962311 / 640000000000000000 : ℝ) ≤
      (-(966488339018040144383 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (394738691935962311 / 640000000000000000 : ℝ) =
            (394738691935962311 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (394738691935962311 / 320000000000000000 : ℝ) ≤
            (419806021581959855617 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3047183968829499 / 5000000000000000 : ℝ)) (q :=
      (394738691935962311 / 640000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9])
      (by norm_num [bρ_9]) (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_655_10 :
    Uω (aρ 10) (bρ 10) (388545108904183 / 512000000000000 : ℝ) ≤
      (-(5584150762359065444067 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14646146670916031 / 25600000000000000 : ℝ) ≤
      (-(5584150762359065444067 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (14646146670916031 / 25600000000000000 : ℝ) =
            (14646146670916031 / 12800000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14646146670916031 / 12800000000000000 : ℝ) ≤
            (1347321040640934555933 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (223585797392333 / 400000000000000 : ℝ)) (q :=
      (14646146670916031 / 25600000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_655_11 :
    Uω (aρ 11) (bρ 11) (388545108904183 / 512000000000000 : ℝ) ≤
      (-(6516737208834470122621 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (333550559048547303 / 640000000000000000 : ℝ) ≤
      (-(6516737208834470122621 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (333550559048547303 / 640000000000000000 : ℝ) =
            (333550559048547303 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (333550559048547303 / 320000000000000000 : ℝ) ≤
            (414734594165529877379 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4989274444627279 / 10000000000000000 : ℝ)) (q :=
      (333550559048547303 / 640000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_655_12 :
    Uω (aρ 12) (bρ 12) (388545108904183 / 512000000000000 : ℝ) ≤
      (-(7649377674455245816967 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (297832249953725863 / 640000000000000000 : ℝ) ≤
      (-(7649377674455245816967 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (297832249953725863 / 640000000000000000 : ℝ) =
            (297832249953725863 / 160000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (297832249953725863 / 160000000000000000 : ℝ) ≤
            (6213565931544754183033 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4296777382099109 / 10000000000000000 : ℝ)) (q :=
      (297832249953725863 / 640000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_655_13 :
    Uω (aρ 13) (bρ 13) (388545108904183 / 512000000000000 : ℝ) ≤
      (-(8998545100638613692049 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (52048488400157723 / 128000000000000000 : ℝ) ≤
      (-(8998545100638613692049 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (52048488400157723 / 128000000000000000 : ℝ) =
            (52048488400157723 / 32000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (52048488400157723 / 32000000000000000 : ℝ) ≤
            (4864398505361386307951 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (176073881258241 / 500000000000000 : ℝ)) (q :=
      (52048488400157723 / 128000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_655_14 :
    Uω (aρ 14) (bρ 14) (388545108904183 / 512000000000000 : ℝ) ≤
      (-(10574366596004491116633 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (44460164291706619 / 128000000000000000 : ℝ) ≤
      (-(10574366596004491116633 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (44460164291706619 / 128000000000000000 : ℝ) =
            (44460164291706619 / 32000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (44460164291706619 / 32000000000000000 : ℝ) ≤
            (3288577009995508883367 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (535945853652867 / 2000000000000000 : ℝ)) (q :=
      (44460164291706619 / 128000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_655_15 :
    Uω (aρ 15) (bρ 15) (388545108904183 / 512000000000000 : ℝ) ≤
      (-(247300147688838586911 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (185855118499611463 / 640000000000000000 : ℝ) ≤
      (-(247300147688838586911 / 200000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (185855118499611463 / 640000000000000000 : ℝ) =
            (185855118499611463 / 160000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (185855118499611463 / 160000000000000000 : ℝ) ≤
            (29958724431161413089 / 200000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (900187164106517 / 5000000000000000 : ℝ)) (q :=
      (185855118499611463 / 640000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_655_16 :
    Uω (aρ 16) (bρ 16) (388545108904183 / 512000000000000 : ℝ) ≤
      (-(889484798547236706907 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (154206482206035719 / 640000000000000000 : ℝ) ≤
      (-(889484798547236706907 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (154206482206035719 / 640000000000000000 : ℝ) =
            (154206482206035719 / 80000000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (154206482206035719 / 80000000000000000 : ℝ) ≤
            (410166164515263293093 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (120465761943599 / 1250000000000000 : ℝ)) (q :=
      (154206482206035719 / 640000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_655 :
    Uρ (388545108904183 / 512000000000000 : ℝ) ≤
      (-(5025621108762662119411 / 10000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (388545108904183 / 512000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(44445869101279289721 / 156250000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_655_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (388545108904183 / 512000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(2876335430194582704191 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_655_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (388545108904183 / 512000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(2940203862703970074569 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_655_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (388545108904183 / 512000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(3047077478141810132203 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_655_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (388545108904183 / 512000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) * (-(80294070555689559269 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_655_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (388545108904183 / 512000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(1726048253307382550747 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_655_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (388545108904183 / 512000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(3788060580235419980457 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_655_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (388545108904183 / 512000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(4240923324085287446963 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_655_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (388545108904183 / 512000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(966488339018040144383 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_655_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) *
        Uω (aρ 10) (bρ 10) (388545108904183 / 512000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(5584150762359065444067 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_655_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) *
        Uω (aρ 11) (bρ 11) (388545108904183 / 512000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(6516737208834470122621 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_655_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) *
        Uω (aρ 12) (bρ 12) (388545108904183 / 512000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(7649377674455245816967 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_655_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) *
        Uω (aρ 13) (bρ 13) (388545108904183 / 512000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(8998545100638613692049 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_655_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) *
        Uω (aρ 14) (bρ 14) (388545108904183 / 512000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(10574366596004491116633 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_655_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) *
        Uω (aρ 15) (bρ 15) (388545108904183 / 512000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(247300147688838586911 / 200000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_655_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) *
        Uω (aρ 16) (bρ 16) (388545108904183 / 512000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(889484798547236706907 / 625000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_655_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_656_1 :
    Uω (aρ 1) (bρ 1) (194899235804257 / 256000000000000 : ℝ) ≤
      (-(703013473485130443647 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (241559448446699633 / 320000000000000000 : ℝ) ≤
      (-(703013473485130443647 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (241559448446699633 / 320000000000000000 : ℝ) =
            (241559448446699633 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (241559448446699633 / 160000000000000000 : ℝ) ≤
            (1029854477264869556353 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3774355673699969 / 5000000000000000 : ℝ)) (q :=
      (241559448446699633 / 320000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1])
      (by norm_num [bρ_1]) (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_656_2 :
    Uω (aρ 2) (bρ 2) (194899235804257 / 256000000000000 : ℝ) ≤
      (-(568749979081353075301 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (48159002739941997 / 64000000000000000 : ℝ) ≤
      (-(568749979081353075301 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (48159002739941997 / 64000000000000000 : ℝ) =
            (48159002739941997 / 32000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (48159002739941997 / 32000000000000000 : ℝ) ≤
            (817544381518646924699 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1504940637644617 / 2000000000000000 : ℝ)) (q :=
      (48159002739941997 / 64000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_656_3 :
    Uω (aρ 3) (bρ 3) (194899235804257 / 256000000000000 : ℝ) ≤
      (-(2907408327145662851251 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (239267019052619217 / 320000000000000000 : ℝ) ≤
      (-(2907408327145662851251 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (239267019052619217 / 320000000000000000 : ℝ) =
            (239267019052619217 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (239267019052619217 / 160000000000000000 : ℝ) ≤
            (4024063475854337148749 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (934574953641239 / 1250000000000000 : ℝ)) (q :=
      (239267019052619217 / 320000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3])
      (by norm_num [bρ_3]) (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_656_4 :
    Uω (aρ 4) (bρ 4) (194899235804257 / 256000000000000 : ℝ) ≤
      (-(3013925961973787554127 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (47346385783190109 / 64000000000000000 : ℝ) ≤
      (-(3013925961973787554127 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (47346385783190109 / 64000000000000000 : ℝ) =
            (47346385783190109 / 32000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (47346385783190109 / 32000000000000000 : ℝ) ≤
            (3917545841026212445873 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (23113908364541 / 31250000000000 : ℝ)) (q :=
      (47346385783190109 / 64000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_656_5 :
    Uω (aρ 5) (bρ 5) (194899235804257 / 256000000000000 : ℝ) ≤
      (-(1589025632933657282791 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (232878269593854273 / 320000000000000000 : ℝ) ≤
      (-(1589025632933657282791 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (232878269593854273 / 320000000000000000 : ℝ) =
            (232878269593854273 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (232878269593854273 / 160000000000000000 : ℝ) ≤
            (1876710268566342717209 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7273786888357103 / 10000000000000000 : ℝ)) (q :=
      (232878269593854273 / 320000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5])
      (by norm_num [bρ_5]) (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_656_6 :
    Uω (aρ 6) (bρ 6) (194899235804257 / 256000000000000 : ℝ) ≤
      (-(1708770832688818507607 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (227367313071814481 / 320000000000000000 : ℝ) ≤
      (-(1708770832688818507607 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (227367313071814481 / 320000000000000000 : ℝ) =
            (227367313071814481 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (227367313071814481 / 160000000000000000 : ℝ) ≤
            (1756965068811181492393 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (443537030054351 / 625000000000000 : ℝ)) (q :=
      (227367313071814481 / 320000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6])
      (by norm_num [bρ_6]) (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_656_7 :
    Uω (aρ 7) (bρ 7) (194899235804257 / 256000000000000 : ℝ) ≤
      (-(1876136121166841495429 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (43976520164748893 / 64000000000000000 : ℝ) ≤
      (-(1876136121166841495429 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (43976520164748893 / 64000000000000000 : ℝ) =
            (43976520164748893 / 32000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (43976520164748893 / 32000000000000000 : ℝ) ≤
            (1589599780333158504571 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (171311483653131 / 250000000000000 : ℝ)) (q :=
      (43976520164748893 / 64000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_656_8 :
    Uω (aρ 8) (bρ 8) (194899235804257 / 256000000000000 : ℝ) ≤
      (-(420336310140069993621 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (42036856658536173 / 64000000000000000 : ℝ) ≤
      (-(420336310140069993621 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (42036856658536173 / 64000000000000000 : ℝ) =
            (42036856658536173 / 32000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (42036856658536173 / 32000000000000000 : ℝ) ≤
            (272810870159930006379 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1305971230354753 / 2000000000000000 : ℝ)) (q :=
      (42036856658536173 / 64000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_656_9 :
    Uω (aρ 9) (bρ 9) (194899235804257 / 256000000000000 : ℝ) ≤
      (-(2396178136091364650849 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (198162097165019857 / 320000000000000000 : ℝ) ≤
      (-(2396178136091364650849 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (198162097165019857 / 320000000000000000 : ℝ) =
            (198162097165019857 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (198162097165019857 / 160000000000000000 : ℝ) ≤
            (1069557765408635349151 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (764929393394369 / 1250000000000000 : ℝ)) (q :=
      (198162097165019857 / 320000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9])
      (by norm_num [bρ_9]) (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_656_10 :
    Uω (aρ 10) (bρ 10) (194899235804257 / 256000000000000 : ℝ) ≤
      (-(692557006368090820231 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (36775706510351901 / 64000000000000000 : ℝ) ≤
      (-(692557006368090820231 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (36775706510351901 / 64000000000000000 : ℝ) =
            (36775706510351901 / 32000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (36775706510351901 / 32000000000000000 : ℝ) ≤
            (173876969006909179769 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (280763569616059 / 500000000000000 : ℝ)) (q :=
      (36775706510351901 / 64000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_656_11 :
    Uω (aρ 11) (bρ 11) (194899235804257 / 256000000000000 : ℝ) ≤
      (-(6467803078306683504167 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (167593379872956993 / 320000000000000000 : ℝ) ≤
      (-(6467803078306683504167 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (167593379872956993 / 320000000000000000 : ℝ) =
            (167593379872956993 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (167593379872956993 / 160000000000000000 : ℝ) ≤
            (463668724693316495833 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (5015925976101023 / 10000000000000000 : ℝ)) (q :=
      (167593379872956993 / 320000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_656_12 :
    Uω (aρ 12) (bρ 12) (194899235804257 / 256000000000000 : ℝ) ≤
      (-(237268551693682025271 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (29952827199544909 / 64000000000000000 : ℝ) ≤
      (-(237268551693682025271 / 312500000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (29952827199544909 / 64000000000000000 : ℝ) =
            (29952827199544909 / 16000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (29952827199544909 / 16000000000000000 : ℝ) ≤
            (195948435993817974729 / 312500000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (865059666116799 / 2000000000000000 : ℝ)) (q :=
      (29952827199544909 / 64000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_656_13 :
    Uω (aρ 13) (bρ 13) (194899235804257 / 256000000000000 : ℝ) ≤
      (-(4464671824597859984033 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (131024801584548321 / 320000000000000000 : ℝ) ≤
      (-(4464671824597859984033 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (131024801584548321 / 320000000000000000 : ℝ) =
            (131024801584548321 / 80000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (131024801584548321 / 80000000000000000 : ℝ) ≤
            (2466799978402140015967 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3553471671355481 / 10000000000000000 : ℝ)) (q :=
      (131024801584548321 / 320000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_656_14 :
    Uω (aρ 14) (bρ 14) (194899235804257 / 256000000000000 : ℝ) ≤
      (-(163807362855826435447 / 156250000000000000000 : ℝ)) := by
  have hlg :
    Real.log (112163078801764561 / 320000000000000000 : ℝ) ≤
      (-(163807362855826435447 / 156250000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (112163078801764561 / 320000000000000000 : ℝ) =
            (112163078801764561 / 80000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (112163078801764561 / 80000000000000000 : ℝ) ≤
            (52801130987923564553 / 156250000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (169908830154781 / 625000000000000 : ℝ)) (q :=
      (112163078801764561 / 320000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_656_15 :
    Uω (aρ 15) (bρ 15) (194899235804257 / 256000000000000 : ℝ) ≤
      (-(2446207738464103347739 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (94180874109960769 / 320000000000000000 : ℝ) ≤
      (-(2446207738464103347739 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (94180874109960769 / 320000000000000000 : ℝ) =
            (94180874109960769 / 80000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (94180874109960769 / 80000000000000000 : ℝ) ≤
            (326380982735896652261 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1854226766653759 / 10000000000000000 : ℝ)) (q :=
      (94180874109960769 / 320000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_656_16 :
    Uω (aρ 16) (bρ 16) (194899235804257 / 256000000000000 : ℝ) ≤
      (-(559580302932836820887 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (78993868669915009 / 320000000000000000 : ℝ) ≤
      (-(559580302932836820887 / 400000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (78993868669915009 / 320000000000000000 : ℝ) =
            (78993868669915009 / 40000000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (78993868669915009 / 40000000000000000 : ℝ) ≤
            (272196313427163179113 / 400000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1057410578160899 / 10000000000000000 : ℝ)) (q :=
      (78993868669915009 / 320000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_656 :
    Uρ (194899235804257 / 256000000000000 : ℝ) ≤
      (-(498081621074527344563 / 1000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (194899235804257 / 256000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(703013473485130443647 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_656_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (194899235804257 / 256000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(568749979081353075301 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_656_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (194899235804257 / 256000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(2907408327145662851251 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_656_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (194899235804257 / 256000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(3013925961973787554127 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_656_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (194899235804257 / 256000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(1589025632933657282791 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_656_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (194899235804257 / 256000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(1708770832688818507607 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_656_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (194899235804257 / 256000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(1876136121166841495429 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_656_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (194899235804257 / 256000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(420336310140069993621 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_656_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (194899235804257 / 256000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(2396178136091364650849 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_656_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) *
        Uω (aρ 10) (bρ 10) (194899235804257 / 256000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(692557006368090820231 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_656_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) *
        Uω (aρ 11) (bρ 11) (194899235804257 / 256000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(6467803078306683504167 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_656_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) *
        Uω (aρ 12) (bρ 12) (194899235804257 / 256000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) * (-(237268551693682025271 / 312500000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_656_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) *
        Uω (aρ 13) (bρ 13) (194899235804257 / 256000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(4464671824597859984033 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_656_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) *
        Uω (aρ 14) (bρ 14) (194899235804257 / 256000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) * (-(163807362855826435447 / 156250000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_656_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) *
        Uω (aρ 15) (bρ 15) (194899235804257 / 256000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(2446207738464103347739 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_656_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) *
        Uω (aρ 16) (bρ 16) (194899235804257 / 256000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(559580302932836820887 / 400000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_656_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_657_1 :
    Uω (aρ 1) (bρ 1) (78210366862569 / 102400000000000 : ℝ) ≤
      (-(1389838665380847924577 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (96937120940872441 / 128000000000000000 : ℝ) ≤
      (-(1389838665380847924577 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (96937120940872441 / 128000000000000000 : ℝ) =
            (96937120940872441 / 64000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (96937120940872441 / 64000000000000000 : ℝ) ≤
            (2075897236119152075423 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1514638245234713 / 2000000000000000 : ℝ)) (q :=
      (96937120940872441 / 128000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1])
      (by norm_num [bρ_1]) (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_657_2 :
    Uω (aρ 2) (bρ 2) (78210366862569 / 102400000000000 : ℝ) ≤
      (-(2811270201498031012067 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (483156760039864957 / 640000000000000000 : ℝ) ≤
      (-(2811270201498031012067 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (483156760039864957 / 640000000000000000 : ℝ) =
            (483156760039864957 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (483156760039864957 / 320000000000000000 : ℝ) ≤
            (4120201601501968987933 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3774591921459013 / 5000000000000000 : ℝ)) (q :=
      (483156760039864957 / 640000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2])
      (by norm_num [bρ_2]) (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_657_3 :
    Uω (aρ 3) (bρ 3) (78210366862569 / 102400000000000 : ℝ) ≤
      (-(57494400179207807219 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (480100844813911869 / 640000000000000000 : ℝ) ≤
      (-(57494400179207807219 / 200000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (480100844813911869 / 640000000000000000 : ℝ) =
            (480100844813911869 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (480100844813911869 / 320000000000000000 : ℝ) ≤
            (81135035880792192781 / 200000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (234408831201781 / 312500000000000 : ℝ)) (q :=
      (480100844813911869 / 640000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3])
      (by norm_num [bρ_3]) (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_657_4 :
    Uω (aρ 4) (bρ 4) (78210366862569 / 102400000000000 : ℝ) ≤
      (-(1490442013525983607791 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (475030861445632029 / 640000000000000000 : ℝ) ≤
      (-(1490442013525983607791 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (475030861445632029 / 640000000000000000 : ℝ) =
            (475030861445632029 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (475030861445632029 / 320000000000000000 : ℝ) ≤
            (1975293887974016392209 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7420939799263247 / 10000000000000000 : ℝ)) (q :=
      (475030861445632029 / 640000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4])
      (by norm_num [bρ_4]) (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_657_5 :
    Uω (aρ 5) (bρ 5) (78210366862569 / 102400000000000 : ℝ) ≤
      (-(3144453088255461251677 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (467324028044376893 / 640000000000000000 : ℝ) ≤
      (-(3144453088255461251677 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (467324028044376893 / 640000000000000000 : ℝ) =
            (467324028044376893 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (467324028044376893 / 320000000000000000 : ℝ) ≤
            (3787018714744538748323 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (114035799606391 / 156250000000000 : ℝ)) (q :=
      (467324028044376893 / 640000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5])
      (by norm_num [bρ_5]) (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_657_6 :
    Uω (aρ 6) (bρ 6) (78210366862569 / 102400000000000 : ℝ) ≤
      (-(3383106105401640094821 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (456303229529549373 / 640000000000000000 : ℝ) ≤
      (-(3383106105401640094821 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (456303229529549373 / 640000000000000000 : ℝ) =
            (456303229529549373 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (456303229529549373 / 320000000000000000 : ℝ) ≤
            (3548365697598359905179 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (890141449545083 / 1250000000000000 : ℝ)) (q :=
      (456303229529549373 / 640000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6])
      (by norm_num [bρ_6]) (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_657_7 :
    Uω (aρ 7) (bρ 7) (78210366862569 / 102400000000000 : ℝ) ≤
      (-(1858306114393186210517 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (441336204386488477 / 640000000000000000 : ℝ) ≤
      (-(1858306114393186210517 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (441336204386488477 / 640000000000000000 : ℝ) =
            (441336204386488477 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (441336204386488477 / 320000000000000000 : ℝ) ≤
            (1607429787106813789483 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6877073441400011 / 10000000000000000 : ℝ)) (q :=
      (441336204386488477 / 640000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7])
      (by norm_num [bρ_7]) (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_657_8 :
    Uω (aρ 8) (bρ 8) (78210366862569 / 102400000000000 : ℝ) ≤
      (-(2082972537469778711169 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (421944449282505021 / 640000000000000000 : ℝ) ≤
      (-(2082972537469778711169 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (421944449282505021 / 640000000000000000 : ℝ) =
            (421944449282505021 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (421944449282505021 / 320000000000000000 : ℝ) ≤
            (1382763364030221288831 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (409663921608783 / 625000000000000 : ℝ)) (q :=
      (421944449282505021 / 640000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8])
      (by norm_num [bρ_8]) (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_657_9 :
    Uω (aρ 9) (bρ 9) (78210366862569 / 102400000000000 : ℝ) ≤
      (-(4752434701677612012609 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (397909545135901917 / 640000000000000000 : ℝ) ≤
      (-(4752434701677612012609 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (397909545135901917 / 640000000000000000 : ℝ) =
            (397909545135901917 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (397909545135901917 / 320000000000000000 : ℝ) ≤
            (2179037101322387987391 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6144497619519181 / 10000000000000000 : ℝ)) (q :=
      (397909545135901917 / 640000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9])
      (by norm_num [bρ_9]) (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_657_10 :
    Uω (aρ 10) (bρ 10) (78210366862569 / 102400000000000 : ℝ) ≤
      (-(1374240064175814711503 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (369360137484945533 / 640000000000000000 : ℝ) ≤
      (-(1374240064175814711503 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (369360137484945533 / 640000000000000000 : ℝ) =
            (369360137484945533 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (369360137484945533 / 320000000000000000 : ℝ) ≤
            (358627886574185288497 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2820443831960897 / 5000000000000000 : ℝ)) (q :=
      (369360137484945533 / 640000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_657_11 :
    Uω (aρ 11) (bρ 11) (78210366862569 / 102400000000000 : ℝ) ≤
      (-(6419128159047950867803 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (67364451149068953 / 128000000000000000 : ℝ) ≤
      (-(6419128159047950867803 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (67364451149068953 / 128000000000000000 : ℝ) =
            (67364451149068953 / 64000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (67364451149068953 / 64000000000000000 : ℝ) ≤
            (512343643952049132197 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (504255548576427 / 1000000000000000 : ℝ)) (q :=
      (67364451149068953 / 128000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_657_12 :
    Uω (aρ 12) (bρ 12) (78210366862569 / 102400000000000 : ℝ) ≤
      (-(942022814831744407111 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (301222719783302717 / 640000000000000000 : ℝ) ≤
      (-(942022814831744407111 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (301222719783302717 / 640000000000000000 : ℝ) =
            (301222719783302717 / 160000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (301222719783302717 / 160000000000000000 : ℝ) ≤
            (790845135918255592889 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (17006914389201 / 39062500000000 : ℝ)) (q :=
      (301222719783302717 / 640000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_657_13 :
    Uω (aρ 13) (bρ 13) (78210366862569 / 102400000000000 : ℝ) ≤
      (-(4430380667806009793779 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (263852976883560349 / 640000000000000000 : ℝ) ≤
      (-(4430380667806009793779 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (263852976883560349 / 640000000000000000 : ℝ) =
            (263852976883560349 / 160000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (263852976883560349 / 160000000000000000 : ℝ) ≤
            (2501091135193990206221 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3585347359613507 / 10000000000000000 : ℝ)) (q :=
      (263852976883560349 / 640000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_657_14 :
    Uω (aρ 14) (bρ 14) (78210366862569 / 102400000000000 : ℝ) ≤
      (-(5197128077412783468093 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (45268193150524441 / 128000000000000000 : ℝ) ≤
      (-(5197128077412783468093 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (45268193150524441 / 128000000000000000 : ℝ) =
            (45268193150524441 / 32000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (45268193150524441 / 32000000000000000 : ℝ) ≤
            (1734343725587216531907 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (275702429681669 / 1000000000000000 : ℝ)) (q :=
      (45268193150524441 / 128000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_657_15 :
    Uω (aρ 15) (bρ 15) (78210366862569 / 102400000000000 : ℝ) ≤
      (-(12100863543607861278483 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (190829779040784189 / 640000000000000000 : ℝ) ≤
      (-(12100863543607861278483 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (190829779040784189 / 640000000000000000 : ℝ) =
            (190829779040784189 / 160000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (190829779040784189 / 160000000000000000 : ℝ) ≤
            (1762080062392138721517 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (59589780921461 / 312500000000000 : ℝ)) (q :=
      (190829779040784189 / 640000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_657_16 :
    Uω (aρ 16) (bρ 16) (78210366862569 / 102400000000000 : ℝ) ≤
      (-(6883547383324041154463 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (161540954567697789 / 640000000000000000 : ℝ) ≤
      (-(6883547383324041154463 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (161540954567697789 / 640000000000000000 : ℝ) =
            (161540954567697789 / 160000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 3
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (161540954567697789 / 160000000000000000 : ℝ) ≤
            (47924419675958845537 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (571984438106401 / 5000000000000000 : ℝ)) (q :=
      (161540954567697789 / 640000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_657 :
    Uρ (78210366862569 / 102400000000000 : ℝ) ≤
      (-(4936472451356495359701 / 10000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (78210366862569 / 102400000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(1389838665380847924577 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_657_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (78210366862569 / 102400000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(2811270201498031012067 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_657_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (78210366862569 / 102400000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) * (-(57494400179207807219 / 200000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_657_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (78210366862569 / 102400000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(1490442013525983607791 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_657_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (78210366862569 / 102400000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(3144453088255461251677 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_657_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (78210366862569 / 102400000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(3383106105401640094821 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_657_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (78210366862569 / 102400000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(1858306114393186210517 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_657_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (78210366862569 / 102400000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(2082972537469778711169 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_657_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (78210366862569 / 102400000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(4752434701677612012609 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_657_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (78210366862569 / 102400000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(1374240064175814711503 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_657_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (78210366862569 / 102400000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(6419128159047950867803 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_657_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (78210366862569 / 102400000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(942022814831744407111 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_657_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (78210366862569 / 102400000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(4430380667806009793779 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_657_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (78210366862569 / 102400000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(5197128077412783468093 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_657_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) *
        Uω (aρ 15) (bρ 15) (78210366862569 / 102400000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(12100863543607861278483 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_657_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (78210366862569 / 102400000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(6883547383324041154463 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_657_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_658_1 :
    Uω (aρ 1) (bρ 1) (49038149627147 / 64000000000000 : ℝ) ≤
      (-(171712828384726161937 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (60781539060846823 / 80000000000000000 : ℝ) ≤
      (-(171712828384726161937 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (60781539060846823 / 80000000000000000 : ℝ) =
            (60781539060846823 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (60781539060846823 / 40000000000000000 : ℝ) ≤
            (261504159302773838063 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7597671104054987 / 10000000000000000 : ℝ)) (q :=
      (60781539060846823 / 80000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_658_2 :
    Uω (aρ 2) (bρ 2) (49038149627147 / 64000000000000 : ℝ) ≤
      (-(2778895663106141822649 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (60590436561394599 / 80000000000000000 : ℝ) ≤
      (-(2778895663106141822649 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (60590436561394599 / 80000000000000000 : ℝ) =
            (60590436561394599 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (60590436561394599 / 40000000000000000 : ℝ) ≤
            (4152576139893858177351 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7573664491701931 / 10000000000000000 : ℝ)) (q :=
      (60590436561394599 / 80000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_658_3 :
    Uω (aρ 3) (bρ 3) (49038149627147 / 64000000000000 : ℝ) ≤
      (-(2842138209295904021429 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (60208456356289091 / 80000000000000000 : ℝ) ≤
      (-(2842138209295904021429 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (60208456356289091 / 80000000000000000 : ℝ) =
            (60208456356289091 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (60208456356289091 / 40000000000000000 : ℝ) ≤
            (4089333593704095978571 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3762782773387777 / 5000000000000000 : ℝ)) (q :=
      (60208456356289091 / 80000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_658_4 :
    Uω (aρ 4) (bρ 4) (49038149627147 / 64000000000000 : ℝ) ≤
      (-(1473975475526614955667 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (59574732885589659 / 80000000000000000 : ℝ) ≤
      (-(1473975475526614955667 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (59574732885589659 / 80000000000000000 : ℝ) =
            (59574732885589659 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (59574732885589659 / 40000000000000000 : ℝ) ≤
            (1991760425973385044333 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (116334825940089 / 156250000000000 : ℝ)) (q :=
      (59574732885589659 / 80000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_658_5 :
    Uω (aρ 5) (bρ 5) (49038149627147 / 64000000000000 : ℝ) ≤
      (-(12443870114242395501 / 40000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (11722287791169907 / 16000000000000000 : ℝ) ≤
      (-(12443870114242395501 / 40000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (11722287791169907 / 16000000000000000 : ℝ) =
            (11722287791169907 / 8000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (11722287791169907 / 8000000000000000 : ℝ) ≤
            (15282017097757604499 / 40000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1464559059413133 / 2000000000000000 : ℝ)) (q :=
      (11722287791169907 / 16000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_658_6 :
    Uω (aρ 6) (bρ 6) (49038149627147 / 64000000000000 : ℝ) ≤
      (-(3348789004045531172871 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (57233977485193759 / 80000000000000000 : ℝ) ≤
      (-(3348789004045531172871 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (57233977485193759 / 80000000000000000 : ℝ) =
            (57233977485193759 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (57233977485193759 / 40000000000000000 : ℝ) ≤
            (3582682798954468827129 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7145670304541721 / 10000000000000000 : ℝ)) (q :=
      (57233977485193759 / 80000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_658_7 :
    Uω (aρ 7) (bρ 7) (49038149627147 / 64000000000000 : ℝ) ≤
      (-(3681079617672882922721 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (11072679413570503 / 16000000000000000 : ℝ) ≤
      (-(3681079617672882922721 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (11072679413570503 / 16000000000000000 : ℝ) =
            (11072679413570503 / 8000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (11072679413570503 / 8000000000000000 : ℝ) ≤
            (3250392185327117077279 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (690168658096641 / 1000000000000000 : ℝ)) (q :=
      (11072679413570503 / 16000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_658_8 :
    Uω (aρ 8) (bρ 8) (49038149627147 / 64000000000000 : ℝ) ≤
      (-(3225521999879289743 / 7812500000000000000 : ℝ)) := by
  have hlg :
    Real.log (52940032909125299 / 80000000000000000 : ℝ) ≤
      (-(3225521999879289743 / 7812500000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (52940032909125299 / 80000000000000000 : ℝ) =
            (52940032909125299 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (52940032909125299 / 40000000000000000 : ℝ) ≤
            (2189690346214460257 / 7812500000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3289693596312303 / 5000000000000000 : ℝ)) (q :=
      (52940032909125299 / 80000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_658_9 :
    Uω (aρ 9) (bρ 9) (49038149627147 / 64000000000000 : ℝ) ≤
      (-(4712675619102600426311 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (49936843275116379 / 80000000000000000 : ℝ) ≤
      (-(4712675619102600426311 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (49936843275116379 / 80000000000000000 : ℝ) =
            (49936843275116379 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (49936843275116379 / 40000000000000000 : ℝ) ≤
            (2218796183897399573689 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (771194426560297 / 1250000000000000 : ℝ)) (q :=
      (49936843275116379 / 80000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_658_10 :
    Uω (aρ 10) (bρ 10) (49038149627147 / 64000000000000 : ℝ) ≤
      (-(2726830749623017945813 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (46370361042211667 / 80000000000000000 : ℝ) ≤
      (-(2726830749623017945813 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (46370361042211667 / 80000000000000000 : ℝ) =
            (46370361042211667 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (46370361042211667 / 40000000000000000 : ℝ) ≤
            (738905151876982054187 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2833246943875599 / 5000000000000000 : ℝ)) (q :=
      (46370361042211667 / 80000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_658_11 :
    Uω (aρ 11) (bρ 11) (49038149627147 / 64000000000000 : ℝ) ≤
      (-(6370709510127633117299 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (42307132269084127 / 80000000000000000 : ℝ) ≤
      (-(6370709510127633117299 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (42307132269084127 / 80000000000000000 : ℝ) =
            (42307132269084127 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (42307132269084127 / 40000000000000000 : ℝ) ≤
            (560762292872366882701 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (5069163320674313 / 10000000000000000 : ℝ)) (q :=
      (42307132269084127 / 80000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_658_12 :
    Uω (aρ 12) (bρ 12) (49038149627147 / 64000000000000 : ℝ) ≤
      (-(7480138777450943837259 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7572890600044083 / 16000000000000000 : ℝ) ≤
      (-(7480138777450943837259 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (7572890600044083 / 16000000000000000 : ℝ) =
            (7572890600044083 / 4000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7572890600044083 / 4000000000000000 : ℝ) ≤
            (6382804828549056162741 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (876438720028677 / 2000000000000000 : ℝ)) (q :=
      (7572890600044083 / 16000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_658_13 :
    Uω (aρ 13) (bρ 13) (49038149627147 / 64000000000000 : ℝ) ≤
      (-(8792784974843993706773 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (33206582909350039 / 80000000000000000 : ℝ) ≤
      (-(8792784974843993706773 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (33206582909350039 / 80000000000000000 : ℝ) =
            (33206582909350039 / 20000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (33206582909350039 / 20000000000000000 : ℝ) ≤
            (5070158631156006293227 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3617107819020791 / 10000000000000000 : ℝ)) (q :=
      (33206582909350039 / 80000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_658_14 :
    Uω (aρ 14) (bρ 14) (49038149627147 / 64000000000000 : ℝ) ≤
      (-(644129719662722860471 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28543210092723919 / 80000000000000000 : ℝ) ≤
      (-(644129719662722860471 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (28543210092723919 / 80000000000000000 : ℝ) =
            (28543210092723919 / 20000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (28543210092723919 / 20000000000000000 : ℝ) ≤
            (222304255712277139529 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2795191899909261 / 10000000000000000 : ℝ)) (q :=
      (28543210092723919 / 80000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_658_15 :
    Uω (aρ 15) (bρ 15) (49038149627147 / 64000000000000 : ℝ) ≤
      (-(11974197185992771512583 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (24157790487552283 / 80000000000000000 : ℝ) ≤
      (-(11974197185992771512583 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (24157790487552283 / 80000000000000000 : ℝ) =
            (24157790487552283 / 20000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (24157790487552283 / 20000000000000000 : ℝ) ≤
            (1888746420007228487417 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (244801284503919 / 1250000000000000 : ℝ)) (q :=
      (24157790487552283 / 80000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_658_16 :
    Uω (aρ 16) (bρ 16) (49038149627147 / 64000000000000 : ℝ) ≤
      (-(13560409783495217840437 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (20614313318481031 / 80000000000000000 : ℝ) ≤
      (-(13560409783495217840437 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (20614313318481031 / 80000000000000000 : ℝ) =
            (20614313318481031 / 20000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (20614313318481031 / 20000000000000000 : ℝ) ≤
            (302533822504782159563 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1224912635273539 / 10000000000000000 : ℝ)) (q :=
      (20614313318481031 / 80000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_658 :
    Uρ (49038149627147 / 64000000000000 : ℝ) ≤
      (-(1223138141627158991151 / 2500000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (49038149627147 / 64000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(171712828384726161937 / 625000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_658_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (49038149627147 / 64000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(2778895663106141822649 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_658_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (49038149627147 / 64000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(2842138209295904021429 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_658_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (49038149627147 / 64000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(1473975475526614955667 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_658_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (49038149627147 / 64000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) * (-(12443870114242395501 / 40000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_658_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (49038149627147 / 64000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(3348789004045531172871 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_658_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (49038149627147 / 64000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(3681079617672882922721 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_658_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (49038149627147 / 64000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) * (-(3225521999879289743 / 7812500000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_658_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (49038149627147 / 64000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(4712675619102600426311 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_658_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (49038149627147 / 64000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(2726830749623017945813 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_658_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (49038149627147 / 64000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(6370709510127633117299 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_658_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (49038149627147 / 64000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(7480138777450943837259 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_658_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (49038149627147 / 64000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(8792784974843993706773 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_658_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (49038149627147 / 64000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) * (-(644129719662722860471 / 625000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_658_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (49038149627147 / 64000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(11974197185992771512583 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_658_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (49038149627147 / 64000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(13560409783495217840437 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_658_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_659_1 :
    Uω (aρ 1) (bρ 1) (393558559721507 / 512000000000000 : ℝ) ≤
      (-(2715236991883287655507 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (487819020240911443 / 640000000000000000 : ℝ) ≤
      (-(2715236991883287655507 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (487819020240911443 / 640000000000000000 : ℝ) =
            (487819020240911443 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (487819020240911443 / 320000000000000000 : ℝ) ≤
            (4216234811116712344493 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7622150981052799 / 10000000000000000 : ℝ)) (q :=
      (487819020240911443 / 640000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1])
      (by norm_num [bρ_1]) (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_659_2 :
    Uω (aρ 2) (bρ 2) (393558559721507 / 512000000000000 : ℝ) ≤
      (-(10986502406018490339 / 40000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (486290224755123731 / 640000000000000000 : ℝ) ≤
      (-(10986502406018490339 / 40000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (486290224755123731 / 640000000000000000 : ℝ) =
            (486290224755123731 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (486290224755123731 / 320000000000000000 : ℝ) ≤
            (16739384805981509661 / 40000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7598145134631933 / 10000000000000000 : ℝ)) (q :=
      (486290224755123731 / 640000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2])
      (by norm_num [bρ_2]) (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_659_3 :
    Uω (aρ 3) (bρ 3) (393558559721507 / 512000000000000 : ℝ) ≤
      (-(2809662236111423922899 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (483234456220980979 / 640000000000000000 : ℝ) ≤
      (-(2809662236111423922899 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (483234456220980979 / 640000000000000000 : ℝ) =
            (483234456220980979 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (483234456220980979 / 320000000000000000 : ℝ) ≤
            (4121809566888576077101 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1887512118572493 / 2500000000000000 : ℝ)) (q :=
      (483234456220980979 / 640000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3])
      (by norm_num [bρ_3]) (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_659_4 :
    Uω (aρ 4) (bρ 4) (393558559721507 / 512000000000000 : ℝ) ≤
      (-(1457563009387830351699 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (478164862768577587 / 640000000000000000 : ℝ) ≤
      (-(1457563009387830351699 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (478164862768577587 / 640000000000000000 : ℝ) =
            (478164862768577587 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (478164862768577587 / 320000000000000000 : ℝ) ≤
            (2008172892112169648301 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3734958929983683 / 5000000000000000 : ℝ)) (q :=
      (478164862768577587 / 640000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4])
      (by norm_num [bρ_4]) (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_659_5 :
    Uω (aρ 5) (bρ 5) (393558559721507 / 512000000000000 : ℝ) ≤
      (-(3077593833591589989139 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (470458990047537363 / 640000000000000000 : ℝ) ≤
      (-(3077593833591589989139 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (470458990047537363 / 640000000000000000 : ℝ) =
            (470458990047537363 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (470458990047537363 / 320000000000000000 : ℝ) ≤
            (3853877969408410010861 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7347299256769859 / 10000000000000000 : ℝ)) (q :=
      (470458990047537363 / 640000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5])
      (by norm_num [bρ_5]) (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_659_6 :
    Uω (aρ 6) (bρ 6) (393558559721507 / 512000000000000 : ℝ) ≤
      (-(1657294773584553884893 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (459440397333449523 / 640000000000000000 : ℝ) ≤
      (-(1657294773584553884893 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (459440397333449523 / 640000000000000000 : ℝ) =
            (459440397333449523 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (459440397333449523 / 320000000000000000 : ℝ) ≤
            (1808441127915446115107 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3585104304797307 / 5000000000000000 : ℝ)) (q :=
      (459440397333449523 / 640000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6])
      (by norm_num [bρ_6]) (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_659_7 :
    Uω (aρ 7) (bρ 7) (393558559721507 / 512000000000000 : ℝ) ≤
      (-(729134699404871384131 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (444478118442517427 / 640000000000000000 : ℝ) ≤
      (-(729134699404871384131 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (444478118442517427 / 640000000000000000 : ℝ) =
            (444478118442517427 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (444478118442517427 / 320000000000000000 : ℝ) ≤
            (657159661195128615869 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3463149387506493 / 5000000000000000 : ℝ)) (q :=
      (444478118442517427 / 640000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7])
      (by norm_num [bρ_7]) (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_659_8 :
    Uω (aρ 8) (bρ 8) (393558559721507 / 512000000000000 : ℝ) ≤
      (-(4091531283765524748763 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (425096009329768787 / 640000000000000000 : ℝ) ≤
      (-(4091531283765524748763 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (425096009329768787 / 640000000000000000 : ℝ) =
            (425096009329768787 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (425096009329768787 / 320000000000000000 : ℝ) ≤
            (2839940519234475251237 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6604149516579591 / 10000000000000000 : ℝ)) (q :=
      (425096009329768787 / 640000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8])
      (by norm_num [bρ_8]) (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_659_9 :
    Uω (aρ 9) (bρ 9) (393558559721507 / 512000000000000 : ℝ) ≤
      (-(2336538838658455572537 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (401079799342275667 / 640000000000000000 : ℝ) ≤
      (-(2336538838658455572537 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (401079799342275667 / 640000000000000000 : ℝ) =
            (401079799342275667 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (401079799342275667 / 320000000000000000 : ℝ) ≤
            (1129197062841544427463 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6194608582830431 / 10000000000000000 : ℝ)) (q :=
      (401079799342275667 / 640000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9])
      (by norm_num [bρ_9]) (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_659_10 :
    Uω (aρ 10) (bρ 10) (393558559721507 / 512000000000000 : ℝ) ≤
      (-(2705278962857846117447 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (372565322001013043 / 640000000000000000 : ℝ) ≤
      (-(2705278962857846117447 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (372565322001013043 / 640000000000000000 : ℝ) =
            (372565322001013043 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (372565322001013043 / 320000000000000000 : ℝ) ≤
            (760456938642153882553 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2846045099705487 / 5000000000000000 : ℝ)) (q :=
      (372565322001013043 / 640000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_659_11 :
    Uω (aρ 11) (bρ 11) (393558559721507 / 512000000000000 : ℝ) ≤
      (-(1580636060845473348809 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (340091177832826643 / 640000000000000000 : ℝ) ≤
      (-(1580636060845473348809 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (340091177832826643 / 640000000000000000 : ℝ) =
            (340091177832826643 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (340091177832826643 / 320000000000000000 : ℝ) ≤
            (152231889904526651191 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (5095749820360149 / 10000000000000000 : ℝ)) (q :=
      (340091177832826643 / 640000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_659_12 :
    Uω (aρ 12) (bρ 12) (393558559721507 / 512000000000000 : ℝ) ≤
      (-(742445707098810187001 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (304607014493012307 / 640000000000000000 : ℝ) ≤
      (-(742445707098810187001 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (304607014493012307 / 640000000000000000 : ℝ) =
            (304607014493012307 / 160000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (304607014493012307 / 160000000000000000 : ℝ) ≤
            (643848653501189812999 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4410569812675951 / 10000000000000000 : ℝ)) (q :=
      (304607014493012307 / 640000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_659_13 :
    Uω (aρ 13) (bρ 13) (393558559721507 / 512000000000000 : ℝ) ≤
      (-(8725401843653626065141 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (267448758631353747 / 640000000000000000 : ℝ) ≤
      (-(8725401843653626065141 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (267448758631353747 / 640000000000000000 : ℝ) =
            (267448758631353747 / 160000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (267448758631353747 / 160000000000000000 : ℝ) ≤
            (5137541762346373934859 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3648756058594121 / 10000000000000000 : ℝ)) (q :=
      (267448758631353747 / 640000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_659_14 :
    Uω (aρ 14) (bρ 14) (393558559721507 / 512000000000000 : ℝ) ≤
      (-(5109543065045329487741 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (230340710504174291 / 640000000000000000 : ℝ) ≤
      (-(5109543065045329487741 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (230340710504174291 / 640000000000000000 : ℝ) =
            (230340710504174291 / 160000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (230340710504174291 / 160000000000000000 : ℝ) ≤
            (1821928737954670512259 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2833056839664763 / 10000000000000000 : ℝ)) (q :=
      (230340710504174291 / 640000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_659_15 :
    Uω (aρ 15) (bρ 15) (393558559721507 / 512000000000000 : ℝ) ≤
      (-(5925394563411376445939 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (195662113945982771 / 640000000000000000 : ℝ) ≤
      (-(5925394563411376445939 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (195662113945982771 / 640000000000000000 : ℝ) =
            (195662113945982771 / 160000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (195662113945982771 / 160000000000000000 : ℝ) ≤
            (1006077239588623554061 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1004461987318139 / 5000000000000000 : ℝ)) (q :=
      (195662113945982771 / 640000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_659_16 :
    Uω (aρ 16) (bρ 16) (393558559721507 / 512000000000000 : ℝ) ≤
      (-(6683298545853789424627 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (168141933781848243 / 640000000000000000 : ℝ) ≤
      (-(6683298545853789424627 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (168141933781848243 / 640000000000000000 : ℝ) =
            (168141933781848243 / 160000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (168141933781848243 / 160000000000000000 : ℝ) ≤
            (248173257146210575373 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (650644998008537 / 5000000000000000 : ℝ)) (q :=
      (168141933781848243 / 640000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_659 :
    Uρ (393558559721507 / 512000000000000 : ℝ) ≤
      (-(2424513986067734309671 / 5000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (393558559721507 / 512000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(2715236991883287655507 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_659_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (393558559721507 / 512000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) * (-(10986502406018490339 / 40000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_659_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (393558559721507 / 512000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(2809662236111423922899 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_659_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (393558559721507 / 512000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(1457563009387830351699 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_659_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (393558559721507 / 512000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(3077593833591589989139 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_659_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (393558559721507 / 512000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(1657294773584553884893 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_659_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (393558559721507 / 512000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(729134699404871384131 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_659_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (393558559721507 / 512000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(4091531283765524748763 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_659_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (393558559721507 / 512000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(2336538838658455572537 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_659_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) *
        Uω (aρ 10) (bρ 10) (393558559721507 / 512000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(2705278962857846117447 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_659_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) *
        Uω (aρ 11) (bρ 11) (393558559721507 / 512000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(1580636060845473348809 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_659_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) *
        Uω (aρ 12) (bρ 12) (393558559721507 / 512000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(742445707098810187001 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_659_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) *
        Uω (aρ 13) (bρ 13) (393558559721507 / 512000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(8725401843653626065141 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_659_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) *
        Uω (aρ 14) (bρ 14) (393558559721507 / 512000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(5109543065045329487741 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_659_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) *
        Uω (aρ 15) (bρ 15) (393558559721507 / 512000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(5925394563411376445939 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_659_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) *
        Uω (aρ 16) (bρ 16) (393558559721507 / 512000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(6683298545853789424627 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_659_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_660_1 :
    Uω (aρ 1) (bρ 1) (197405961212919 / 256000000000000 : ℝ) ≤
      (-(2683171878172451050851 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (244692863983522167 / 320000000000000000 : ℝ) ≤
      (-(2683171878172451050851 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (244692863983522167 / 320000000000000000 : ℝ) =
            (244692863983522167 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (244692863983522167 / 160000000000000000 : ℝ) ≤
            (4248299924827548949149 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7646630857175487 / 10000000000000000 : ℝ)) (q :=
      (244692863983522167 / 320000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1])
      (by norm_num [bρ_1]) (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_660_2 :
    Uω (aρ 2) (bρ 2) (197405961212919 / 256000000000000 : ℝ) ≤
      (-(1357229672258682030653 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (48785695683357067 / 64000000000000000 : ℝ) ≤
      (-(1357229672258682030653 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (48785695683357067 / 64000000000000000 : ℝ) =
            (48785695683357067 / 32000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (48785695683357067 / 32000000000000000 : ℝ) ≤
            (2108506229241317969347 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1524525154352887 / 2000000000000000 : ℝ)) (q :=
      (48785695683357067 / 64000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_660_3 :
    Uω (aρ 3) (bρ 3) (197405961212919 / 256000000000000 : ℝ) ≤
      (-(1388645702044695172863 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (242400630466186087 / 320000000000000000 : ℝ) ≤
      (-(1388645702044695172863 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (242400630466186087 / 320000000000000000 : ℝ) =
            (242400630466186087 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (242400630466186087 / 160000000000000000 : ℝ) ≤
            (2077090199455304827137 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3787265690600991 / 5000000000000000 : ℝ)) (q :=
      (242400630466186087 / 320000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3])
      (by norm_num [bρ_3]) (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_660_4 :
    Uω (aρ 4) (bρ 4) (197405961212919 / 256000000000000 : ℝ) ≤
      (-(720602130511302706029 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (239865930258189943 / 320000000000000000 : ℝ) ≤
      (-(720602130511302706029 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (239865930258189943 / 320000000000000000 : ℝ) =
            (239865930258189943 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (239865930258189943 / 160000000000000000 : ℝ) ≤
            (1012265820238697293971 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7494406799267223 / 10000000000000000 : ℝ)) (q :=
      (239865930258189943 / 320000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4])
      (by norm_num [bρ_4]) (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_660_5 :
    Uω (aρ 5) (bρ 5) (197405961212919 / 256000000000000 : ℝ) ≤
      (-(1522165628847763865193 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (47202646329847147 / 64000000000000000 : ℝ) ≤
      (-(1522165628847763865193 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (47202646329847147 / 64000000000000000 : ℝ) =
            (47202646329847147 / 32000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (47202646329847147 / 32000000000000000 : ℝ) ≤
            (1943570272652236134807 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1474360611108517 / 2000000000000000 : ℝ)) (q :=
      (47202646329847147 / 64000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_660_6 :
    Uω (aρ 6) (bρ 6) (197405961212919 / 256000000000000 : ℝ) ≤
      (-(20503168306351268131 / 62500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (230504481008619239 / 320000000000000000 : ℝ) ≤
      (-(20503168306351268131 / 62500000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (230504481008619239 / 320000000000000000 : ℝ) =
            (230504481008619239 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (230504481008619239 / 160000000000000000 : ℝ) ≤
            (22818530462398731869 / 62500000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3597373257822027 / 5000000000000000 : ℝ)) (q :=
      (230504481008619239 / 320000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6])
      (by norm_num [bρ_6]) (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_660_7 :
    Uω (aρ 7) (bρ 7) (197405961212919 / 256000000000000 : ℝ) ≤
      (-(1805196482340114028887 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (223024515203491959 / 320000000000000000 : ℝ) ≤
      (-(1805196482340114028887 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (223024515203491959 / 320000000000000000 : ℝ) =
            (223024515203491959 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (223024515203491959 / 160000000000000000 : ℝ) ≤
            (1660539419159885971113 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6950910033583599 / 10000000000000000 : ℝ)) (q :=
      (223024515203491959 / 320000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7])
      (by norm_num [bρ_7]) (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_660_8 :
    Uω (aρ 8) (bρ 8) (197405961212919 / 256000000000000 : ℝ) ≤
      (-(4054533386656685392731 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (42667168821410459 / 64000000000000000 : ℝ) ≤
      (-(4054533386656685392731 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (42667168821410459 / 64000000000000000 : ℝ) =
            (42667168821410459 / 32000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (42667168821410459 / 32000000000000000 : ℝ) ≤
            (2876938416343314607269 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (165722743534903 / 250000000000000 : ℝ)) (q :=
      (42667168821410459 / 64000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_660_9 :
    Uω (aρ 9) (bρ 9) (197405961212919 / 256000000000000 : ℝ) ≤
      (-(1158409886553347536791 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (201332353173736791 / 320000000000000000 : ℝ) ≤
      (-(1158409886553347536791 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (201332353173736791 / 320000000000000000 : ℝ) =
            (201332353173736791 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (201332353173736791 / 160000000000000000 : ℝ) ≤
            (574458064196652463209 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6219657186423901 / 10000000000000000 : ℝ)) (q :=
      (201332353173736791 / 320000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9])
      (by norm_num [bρ_9]) (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_660_10 :
    Uω (aρ 10) (bρ 10) (197405961212919 / 256000000000000 : ℝ) ≤
      (-(5367647710234672246907 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (187083721367394247 / 320000000000000000 : ℝ) ≤
      (-(5367647710234672246907 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (187083721367394247 / 320000000000000000 : ℝ) =
            (187083721367394247 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (187083721367394247 / 160000000000000000 : ℝ) ≤
            (1563824092765327753093 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1429419183005623 / 2500000000000000 : ℝ)) (q :=
      (187083721367394247 / 320000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_660_11 :
    Uω (aρ 11) (bρ 11) (197405961212919 / 256000000000000 : ℝ) ≤
      (-(1568657380525846977687 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (170862312708270567 / 320000000000000000 : ℝ) ≤
      (-(1568657380525846977687 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (170862312708270567 / 320000000000000000 : ℝ) =
            (170862312708270567 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (170862312708270567 / 160000000000000000 : ℝ) ≤
            (164210570224153022313 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2561157658516131 / 5000000000000000 : ℝ)) (q :=
      (170862312708270567 / 320000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_660_12 :
    Uω (aρ 12) (bρ 12) (197405961212919 / 256000000000000 : ℝ) ≤
      (-(3684566083047103674919 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (153148460143557719 / 320000000000000000 : ℝ) ≤
      (-(3684566083047103674919 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (153148460143557719 / 320000000000000000 : ℝ) =
            (153148460143557719 / 80000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (153148460143557719 / 80000000000000000 : ℝ) ≤
            (3246905719952896325081 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4438899628422709 / 10000000000000000 : ℝ)) (q :=
      (153148460143557719 / 320000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_660_13 :
    Uω (aρ 13) (bρ 13) (197405961212919 / 256000000000000 : ℝ) ≤
      (-(4329299829043131844737 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (134620677797613799 / 320000000000000000 : ℝ) ≤
      (-(4329299829043131844737 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (134620677797613799 / 320000000000000000 : ℝ) =
            (134620677797613799 / 80000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (134620677797613799 / 80000000000000000 : ℝ) ≤
            (2602171973956868155263 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1840147486698107 / 5000000000000000 : ℝ)) (q :=
      (134620677797613799 / 320000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_660_14 :
    Uω (aρ 14) (bρ 14) (197405961212919 / 256000000000000 : ℝ) ≤
      (-(1013324731520483938837 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (116163219149155479 / 320000000000000000 : ℝ) ≤
      (-(1013324731520483938837 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (116163219149155479 / 320000000000000000 : ℝ) =
            (116163219149155479 / 80000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (116163219149155479 / 80000000000000000 : ℝ) ≤
            (372969629079516061163 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2870631092912569 / 10000000000000000 : ℝ)) (q :=
      (116163219149155479 / 320000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_660_15 :
    Uω (aρ 15) (bρ 15) (197405961212919 / 256000000000000 : ℝ) ≤
      (-(11730417611087330118851 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (99015780276553943 / 320000000000000000 : ℝ) ≤
      (-(11730417611087330118851 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (99015780276553943 / 320000000000000000 : ℝ) =
            (99015780276553943 / 80000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (99015780276553943 / 80000000000000000 : ℝ) ≤
            (2132525994912669881149 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2058489440789973 / 10000000000000000 : ℝ)) (q :=
      (99015780276553943 / 320000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_660_16 :
    Uω (aρ 16) (bρ 16) (197405961212919 / 256000000000000 : ℝ) ≤
      (-(659178816886656724683 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (85623806816932631 / 320000000000000000 : ℝ) ≤
      (-(659178816886656724683 / 500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (85623806816932631 / 320000000000000000 : ℝ) =
            (85623806816932631 / 80000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (85623806816932631 / 80000000000000000 : ℝ) ≤
            (33968363413343275317 / 500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1373862751073641 / 10000000000000000 : ℝ)) (q :=
      (85623806816932631 / 320000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_660 :
    Uρ (197405961212919 / 256000000000000 : ℝ) ≤
      (-(2402937868237377408313 / 5000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (197405961212919 / 256000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(2683171878172451050851 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_660_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (197405961212919 / 256000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(1357229672258682030653 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_660_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (197405961212919 / 256000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(1388645702044695172863 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_660_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (197405961212919 / 256000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(720602130511302706029 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_660_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (197405961212919 / 256000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(1522165628847763865193 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_660_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (197405961212919 / 256000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) * (-(20503168306351268131 / 62500000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_660_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (197405961212919 / 256000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(1805196482340114028887 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_660_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (197405961212919 / 256000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(4054533386656685392731 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_660_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (197405961212919 / 256000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(1158409886553347536791 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_660_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) *
        Uω (aρ 10) (bρ 10) (197405961212919 / 256000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(5367647710234672246907 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_660_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) *
        Uω (aρ 11) (bρ 11) (197405961212919 / 256000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(1568657380525846977687 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_660_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) *
        Uω (aρ 12) (bρ 12) (197405961212919 / 256000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(3684566083047103674919 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_660_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) *
        Uω (aρ 13) (bρ 13) (197405961212919 / 256000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(4329299829043131844737 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_660_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) *
        Uω (aρ 14) (bρ 14) (197405961212919 / 256000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(1013324731520483938837 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_660_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) *
        Uω (aρ 15) (bρ 15) (197405961212919 / 256000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(11730417611087330118851 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_660_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) *
        Uω (aρ 16) (bρ 16) (197405961212919 / 256000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(659178816886656724683 / 500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_660_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_661_1 :
    Uω (aρ 1) (bρ 1) (396065285130169 / 512000000000000 : ℝ) ≤
      (-(662802313408731620701 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (490952435665441417 / 640000000000000000 : ℝ) ≤
      (-(662802313408731620701 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (490952435665441417 / 640000000000000000 : ℝ) =
            (490952435665441417 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (490952435665441417 / 320000000000000000 : ℝ) ≤
            (1070065637341268379299 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7671110732431431 / 10000000000000000 : ℝ)) (q :=
      (490952435665441417 / 640000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1])
      (by norm_num [bρ_1]) (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_661_2 :
    Uω (aρ 2) (bρ 2) (396065285130169 / 512000000000000 : ℝ) ≤
      (-(2682396226434606046731 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (489423688728279241 / 640000000000000000 : ℝ) ≤
      (-(2682396226434606046731 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (489423688728279241 / 640000000000000000 : ℝ) =
            (489423688728279241 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (489423688728279241 / 320000000000000000 : ℝ) ≤
            (4249075576565393953269 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7647106403155113 / 10000000000000000 : ℝ)) (q :=
      (489423688728279241 / 640000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2])
      (by norm_num [bρ_2]) (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_661_3 :
    Uω (aρ 3) (bρ 3) (396065285130169 / 512000000000000 : ℝ) ≤
      (-(54900500690973011711 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (486368064990858537 / 640000000000000000 : ℝ) ≤
      (-(54900500690973011711 / 200000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (486368064990858537 / 640000000000000000 : ℝ) =
            (486368064990858537 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (486368064990858537 / 320000000000000000 : ℝ) ≤
            (83728935369026988289 / 200000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1899753566927679 / 2500000000000000 : ℝ)) (q :=
      (486368064990858537 / 640000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3])
      (by norm_num [bρ_3]) (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_661_4 :
    Uω (aρ 4) (bρ 4) (396065285130169 / 512000000000000 : ℝ) ≤
      (-(2849797759623886644061 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (481298856347041321 / 640000000000000000 : ℝ) ≤
      (-(2849797759623886644061 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (481298856347041321 / 640000000000000000 : ℝ) =
            (481298856347041321 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (481298856347041321 / 320000000000000000 : ℝ) ≤
            (4081674043376113355939 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1879723919664107 / 2500000000000000 : ℝ)) (q :=
      (481298856347041321 / 640000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4])
      (by norm_num [bρ_4]) (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_661_5 :
    Uω (aρ 5) (bρ 5) (396065285130169 / 512000000000000 : ℝ) ≤
      (-(301117906265737937309 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (94718786290156437 / 128000000000000000 : ℝ) ≤
      (-(301117906265737937309 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (94718786290156437 / 128000000000000000 : ℝ) =
            (94718786290156437 / 64000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (94718786290156437 / 64000000000000000 : ℝ) ≤
            (392029274034262062691 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (739630669498333 / 1000000000000000 : ℝ)) (q :=
      (94718786290156437 / 128000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5])
      (by norm_num [bρ_5]) (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_661_6 :
    Uω (aρ 6) (bρ 6) (396065285130169 / 512000000000000 : ℝ) ≤
      (-(1623270176049848597967 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (462577514063111017 / 640000000000000000 : ℝ) ≤
      (-(1623270176049848597967 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (462577514063111017 / 640000000000000000 : ℝ) =
            (462577514063111017 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (462577514063111017 / 320000000000000000 : ℝ) ≤
            (1842465725450151402033 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3609642013379303 / 5000000000000000 : ℝ)) (q :=
      (462577514063111017 / 640000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6])
      (by norm_num [bρ_6]) (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_661_7 :
    Uω (aρ 7) (bρ 7) (396065285130169 / 512000000000000 : ℝ) ≤
      (-(3575237128147365079751 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (447619912753074921 / 640000000000000000 : ℝ) ≤
      (-(3575237128147365079751 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (447619912753074921 / 640000000000000000 : ℝ) =
            (447619912753074921 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (447619912753074921 / 320000000000000000 : ℝ) ≤
            (3356234674852634920249 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3487760183289989 / 5000000000000000 : ℝ)) (q :=
      (447619912753074921 / 640000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7])
      (by norm_num [bρ_7]) (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_661_8 :
    Uω (aρ 8) (bρ 8) (396065285130169 / 512000000000000 : ℝ) ≤
      (-(803534684119275944343 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (428247300675913961 / 640000000000000000 : ℝ) ≤
      (-(803534684119275944343 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (428247300675913961 / 640000000000000000 : ℝ) =
            (428247300675913961 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (428247300675913961 / 320000000000000000 : ℝ) ≤
            (582759676480724055657 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3326833945254349 / 5000000000000000 : ℝ)) (q :=
      (428247300675913961 / 640000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8])
      (by norm_num [bρ_8]) (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_661_9 :
    Uω (aρ 9) (bρ 9) (396065285130169 / 512000000000000 : ℝ) ≤
      (-(459435991242715682401 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (404249468975058729 / 640000000000000000 : ℝ) ≤
      (-(459435991242715682401 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (404249468975058729 / 640000000000000000 : ℝ) =
            (404249468975058729 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (404249468975058729 / 320000000000000000 : ℝ) ≤
            (233711189057284317599 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1561175319554243 / 2500000000000000 : ℝ)) (q :=
      (404249468975058729 / 640000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9])
      (by norm_num [bρ_9]) (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_661_10 :
    Uω (aρ 10) (bρ 10) (396065285130169 / 512000000000000 : ℝ) ≤
      (-(5324929053367865177511 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (375769254721378313 / 640000000000000000 : ℝ) ≤
      (-(5324929053367865177511 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (375769254721378313 / 640000000000000000 : ℝ) =
            (375769254721378313 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (375769254721378313 / 320000000000000000 : ℝ) ≤
            (1606542749632134822489 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (5743253616284459 / 10000000000000000 : ℝ)) (q :=
      (375769254721378313 / 640000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_661_11 :
    Uω (aρ 11) (bρ 11) (396065285130169 / 512000000000000 : ℝ) ≤
      (-(15567406399431601151 / 25000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (343357411306843081 / 640000000000000000 : ℝ) ≤
      (-(15567406399431601151 / 25000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (343357411306843081 / 640000000000000000 : ℝ) =
            (343357411306843081 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (343357411306843081 / 320000000000000000 : ℝ) ≤
            (1761273108068398849 / 25000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (5148860135785233 / 10000000000000000 : ℝ)) (q :=
      (343357411306843081 / 640000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_661_12 :
    Uω (aρ 12) (bρ 12) (396065285130169 / 512000000000000 : ℝ) ≤
      (-(3657079475934853258049 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (307985369630861833 / 640000000000000000 : ℝ) ≤
      (-(3657079475934853258049 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (307985369630861833 / 640000000000000000 : ℝ) =
            (307985369630861833 / 160000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (307985369630861833 / 160000000000000000 : ℝ) ≤
            (3274392327065146741951 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4467183930095819 / 10000000000000000 : ℝ)) (q :=
      (307985369630861833 / 640000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_661_13 :
    Uω (aρ 13) (bρ 13) (396065285130169 / 512000000000000 : ℝ) ≤
      (-(4296183276173925836353 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (271030543345022249 / 640000000000000000 : ℝ) ≤
      (-(4296183276173925836353 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (271030543345022249 / 640000000000000000 : ℝ) =
            (271030543345022249 / 160000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (271030543345022249 / 160000000000000000 : ℝ) ≤
            (2635288526826074163647 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (927931837564583 / 2500000000000000 : ℝ)) (q :=
      (271030543345022249 / 640000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_661_14 :
    Uω (aρ 14) (bρ 14) (396065285130169 / 512000000000000 : ℝ) ≤
      (-(5024260336321951904853 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (234303224706138217 / 640000000000000000 : ℝ) ≤
      (-(5024260336321951904853 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (234303224706138217 / 640000000000000000 : ℝ) =
            (234303224706138217 / 160000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (234303224706138217 / 160000000000000000 : ℝ) ≤
            (1907211466678048095147 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1453962963919103 / 5000000000000000 : ℝ)) (q :=
      (234303224706138217 / 640000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_661_15 :
    Uω (aρ 15) (bρ 15) (396065285130169 / 512000000000000 : ℝ) ≤
      (-(11612885194558307579307 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (200372804993721609 / 640000000000000000 : ℝ) ≤
      (-(11612885194558307579307 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (200372804993721609 / 640000000000000000 : ℝ) =
            (200372804993721609 / 160000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (200372804993721609 / 160000000000000000 : ℝ) ≤
            (2250058411441692420693 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2107173589240187 / 10000000000000000 : ℝ)) (q :=
      (200372804993721609 / 640000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_661_16 :
    Uω (aρ 16) (bρ 16) (396065285130169 / 512000000000000 : ℝ) ≤
      (-(13009776067628077066779 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (174249916260764873 / 640000000000000000 : ℝ) ≤
      (-(13009776067628077066779 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (174249916260764873 / 640000000000000000 : ℝ) =
            (174249916260764873 / 160000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (174249916260764873 / 160000000000000000 : ℝ) ≤
            (853167538371922933221 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1443204967845289 / 10000000000000000 : ℝ)) (q :=
      (174249916260764873 / 640000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_661 :
    Uρ (396065285130169 / 512000000000000 : ℝ) ≤
      (-(4763076847769005740497 / 10000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (396065285130169 / 512000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(662802313408731620701 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_661_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (396065285130169 / 512000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(2682396226434606046731 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_661_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (396065285130169 / 512000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) * (-(54900500690973011711 / 200000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_661_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (396065285130169 / 512000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(2849797759623886644061 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_661_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (396065285130169 / 512000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) * (-(301117906265737937309 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_661_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (396065285130169 / 512000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(1623270176049848597967 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_661_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (396065285130169 / 512000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(3575237128147365079751 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_661_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (396065285130169 / 512000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(803534684119275944343 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_661_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (396065285130169 / 512000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(459435991242715682401 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_661_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) *
        Uω (aρ 10) (bρ 10) (396065285130169 / 512000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(5324929053367865177511 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_661_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) *
        Uω (aρ 11) (bρ 11) (396065285130169 / 512000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) * (-(15567406399431601151 / 25000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_661_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) *
        Uω (aρ 12) (bρ 12) (396065285130169 / 512000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(3657079475934853258049 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_661_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) *
        Uω (aρ 13) (bρ 13) (396065285130169 / 512000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(4296183276173925836353 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_661_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) *
        Uω (aρ 14) (bρ 14) (396065285130169 / 512000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(5024260336321951904853 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_661_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) *
        Uω (aρ 15) (bρ 15) (396065285130169 / 512000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(11612885194558307579307 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_661_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) *
        Uω (aρ 16) (bρ 16) (396065285130169 / 512000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(13009776067628077066779 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_661_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_662_1 :
    Uω (aρ 1) (bρ 1) (794637295669 / 1024000000000 : ℝ) ≤
      (-(2619348465185242405921 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (123129785834091833 / 160000000000000000 : ℝ) ≤
      (-(2619348465185242405921 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (123129785834091833 / 160000000000000000 : ℝ) =
            (123129785834091833 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (123129785834091833 / 80000000000000000 : ℝ) ≤
            (4312123337814757594079 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7695590606828901 / 10000000000000000 : ℝ)) (q :=
      (123129785834091833 / 160000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1])
      (by norm_num [bρ_1]) (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_662_2 :
    Uω (aρ 2) (bρ 2) (794637295669 / 1024000000000 : ℝ) ≤
      (-(530087117586050276873 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (122747605110252121 / 160000000000000000 : ℝ) ≤
      (-(530087117586050276873 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (122747605110252121 / 160000000000000000 : ℝ) =
            (122747605110252121 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (122747605110252121 / 80000000000000000 : ℝ) ≤
            (856207243013949723127 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7671587028858937 / 10000000000000000 : ℝ)) (q :=
      (122747605110252121 / 160000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2])
      (by norm_num [bρ_2]) (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_662_3 :
    Uω (aρ 3) (bρ 3) (794637295669 / 1024000000000 : ℝ) ≤
      (-(1356431227679515851249 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (121983717100682641 / 160000000000000000 : ℝ) ≤
      (-(1356431227679515851249 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (121983717100682641 / 160000000000000000 : ℝ) =
            (121983717100682641 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (121983717100682641 / 80000000000000000 : ℝ) ≤
            (2109304673820484148751 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (476468570875797 / 625000000000000 : ℝ)) (q :=
      (121983717100682641 / 160000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3])
      (by norm_num [bρ_3]) (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_662_4 :
    Uω (aρ 4) (bρ 4) (794637295669 / 1024000000000 : ℝ) ≤
      (-(56345860742388664727 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (120716462569808329 / 160000000000000000 : ℝ) ≤
      (-(56345860742388664727 / 200000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (120716462569808329 / 160000000000000000 : ℝ) =
            (120716462569808329 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (120716462569808329 / 80000000000000000 : ℝ) ≤
            (82283575317611335273 / 200000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7543384498718463 / 10000000000000000 : ℝ)) (q :=
      (120716462569808329 / 160000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4])
      (by norm_num [bρ_4]) (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_662_5 :
    Uω (aρ 5) (bρ 5) (794637295669 / 1024000000000 : ℝ) ≤
      (-(1489068258800647595981 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (23758069727748837 / 32000000000000000 : ℝ) ≤
      (-(1489068258800647595981 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (23758069727748837 / 32000000000000000 : ℝ) =
            (23758069727748837 / 16000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (23758069727748837 / 16000000000000000 : ℝ) ≤
            (1976667642699352404019 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1484162035334089 / 2000000000000000 : ℝ)) (q :=
      (23758069727748837 / 32000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_662_6 :
    Uω (aρ 6) (bρ 6) (794637295669 / 1024000000000 : ℝ) ≤
      (-(401586128386062271131 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (116036513399873761 / 160000000000000000 : ℝ) ≤
      (-(401586128386062271131 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (116036513399873761 / 160000000000000000 : ℝ) =
            (116036513399873761 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (116036513399873761 / 80000000000000000 : ℝ) ≤
            (464847846988937728869 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3621910573475821 / 5000000000000000 : ℝ)) (q :=
      (116036513399873761 / 160000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6])
      (by norm_num [bρ_6]) (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_662_7 :
    Uω (aρ 7) (bρ 7) (794637295669 / 1024000000000 : ℝ) ≤
      (-(442525638057717244647 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (112297691448294529 / 160000000000000000 : ℝ) ≤
      (-(442525638057717244647 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (112297691448294529 / 160000000000000000 : ℝ) =
            (112297691448294529 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (112297691448294529 / 80000000000000000 : ℝ) ≤
            (423908337317282755353 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3500064891882119 / 5000000000000000 : ℝ)) (q :=
      (112297691448294529 / 160000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7])
      (by norm_num [bρ_7]) (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_662_8 :
    Uω (aρ 8) (bρ 8) (794637295669 / 1024000000000 : ℝ) ≤
      (-(39809503495964381451 / 100000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (107455711863479641 / 160000000000000000 : ℝ) ≤
      (-(39809503495964381451 / 100000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (107455711863479641 / 160000000000000000 : ℝ) =
            (107455711863479641 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (107455711863479641 / 80000000000000000 : ℝ) ≤
            (29505214534035618549 / 100000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6678423987002377 / 10000000000000000 : ℝ)) (q :=
      (107455711863479641 / 160000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8])
      (by norm_num [bρ_8]) (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_662_9 :
    Uω (aρ 9) (bρ 9) (794637295669 / 1024000000000 : ℝ) ≤
      (-(455523747905055093527 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (20291704447757669 / 32000000000000000 : ℝ) ≤
      (-(455523747905055093527 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (20291704447757669 / 32000000000000000 : ℝ) =
            (20291704447757669 / 16000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (20291704447757669 / 16000000000000000 : ℝ) ≤
            (237623432394944906473 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1253948182455193 / 2000000000000000 : ℝ)) (q :=
      (20291704447757669 / 32000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_662_10 :
    Uω (aρ 10) (bρ 10) (794637295669 / 1024000000000 : ℝ) ≤
      (-(1056480036319776071903 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (94342690516851393 / 160000000000000000 : ℝ) ≤
      (-(1056480036319776071903 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (94342690516851393 / 160000000000000000 : ℝ) =
            (94342690516851393 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (94342690516851393 / 80000000000000000 : ℝ) ≤
            (329814324280223928097 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2884410490264423 / 5000000000000000 : ℝ)) (q :=
      (94342690516851393 / 160000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_662_11 :
    Uω (aρ 11) (bρ 11) (794637295669 / 1024000000000 : ℝ) ≤
      (-(1235908123765897962347 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (86247386421328329 / 160000000000000000 : ℝ) ≤
      (-(1235908123765897962347 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (86247386421328329 / 160000000000000000 : ℝ) =
            (86247386421328329 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (86247386421328329 / 80000000000000000 : ℝ) ≤
            (150386236834102037653 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (5175384594793463 / 10000000000000000 : ℝ)) (q :=
      (86247386421328329 / 160000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_662_12 :
    Uω (aρ 12) (bρ 12) (794637295669 / 1024000000000 : ℝ) ≤
      (-(7259532435704126432831 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3096723900153329 / 6400000000000000 : ℝ) ≤
      (-(7259532435704126432831 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (3096723900153329 / 6400000000000000 : ℝ) =
            (3096723900153329 / 1600000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3096723900153329 / 1600000000000000 : ℝ) ≤
            (6603411170295873567169 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (179816943071663 / 400000000000000 : ℝ)) (q :=
      (3096723900153329 / 6400000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_662_13 :
    Uω (aρ 13) (bρ 13) (794637295669 / 1024000000000 : ℝ) ≤
      (-(8526691058976463844233 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13640820388378613 / 32000000000000000 : ℝ) ≤
      (-(8526691058976463844233 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (13640820388378613 / 32000000000000000 : ℝ) =
            (13640820388378613 / 8000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (13640820388378613 / 8000000000000000 : ℝ) ≤
            (5336252547023536155767 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (748611174628811 / 2000000000000000 : ℝ)) (q :=
      (13640820388378613 / 32000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_662_14 :
    Uω (aρ 14) (bρ 14) (794637295669 / 1024000000000 : ℝ) ≤
      (-(4982434958219247805323 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (59067852357270697 / 160000000000000000 : ℝ) ≤
      (-(4982434958219247805323 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (59067852357270697 / 160000000000000000 : ℝ) =
            (59067852357270697 / 40000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (59067852357270697 / 40000000000000000 : ℝ) ≤
            (1949036844780752194677 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2944951960111259 / 10000000000000000 : ℝ)) (q :=
      (59067852357270697 / 160000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_662_15 :
    Uω (aρ 15) (bρ 15) (794637295669 / 1024000000000 : ℝ) ≤
      (-(11498015157682552696681 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (50671939657254177 / 160000000000000000 : ℝ) ≤
      (-(11498015157682552696681 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (50671939657254177 / 160000000000000000 : ℝ) =
            (50671939657254177 / 40000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (50671939657254177 / 40000000000000000 : ℝ) ≤
            (2364928448317447303319 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1077518075012097 / 5000000000000000 : ℝ)) (q :=
      (50671939657254177 / 160000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_662_16 :
    Uω (aρ 16) (bρ 16) (794637295669 / 1024000000000 : ℝ) ≤
      (-(50171776057069747423 / 39062500000000000000 : ℝ)) := by
  have hlg :
    Real.log (44290771968930889 / 160000000000000000 : ℝ) ≤
      (-(50171776057069747423 / 39062500000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (44290771968930889 / 160000000000000000 : ℝ) =
            (44290771968930889 / 40000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (44290771968930889 / 40000000000000000 : ℝ) ≤
            (3980347403867752577 / 39062500000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1509761840493783 / 10000000000000000 : ℝ)) (q :=
      (44290771968930889 / 160000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_662 :
    Uρ (794637295669 / 1024000000000 : ℝ) ≤
      (-(590076893444211888841 / 1250000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (794637295669 / 1024000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(2619348465185242405921 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_662_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (794637295669 / 1024000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(530087117586050276873 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_662_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (794637295669 / 1024000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(1356431227679515851249 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_662_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (794637295669 / 1024000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) * (-(56345860742388664727 / 200000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_662_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (794637295669 / 1024000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(1489068258800647595981 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_662_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (794637295669 / 1024000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(401586128386062271131 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_662_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (794637295669 / 1024000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(442525638057717244647 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_662_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (794637295669 / 1024000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) * (-(39809503495964381451 / 100000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_662_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (794637295669 / 1024000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(455523747905055093527 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_662_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (794637295669 / 1024000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(1056480036319776071903 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_662_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (794637295669 / 1024000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(1235908123765897962347 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_662_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (794637295669 / 1024000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(7259532435704126432831 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_662_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (794637295669 / 1024000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(8526691058976463844233 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_662_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (794637295669 / 1024000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(4982434958219247805323 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_662_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (794637295669 / 1024000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(11498015157682552696681 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_662_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (794637295669 / 1024000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(50171776057069747423 / 39062500000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_662_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_663_1 :
    Uω (aρ 1) (bρ 1) (398572010538831 / 512000000000000 : ℝ) ≤
      (-(1293794432980282284923 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (494085850980083391 / 640000000000000000 : ℝ) ≤
      (-(1293794432980282284923 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (494085850980083391 / 640000000000000000 : ℝ) =
            (494085850980083391 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (494085850980083391 / 320000000000000000 : ℝ) ≤
            (2171941468519717715077 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7720070480376063 / 10000000000000000 : ℝ)) (q :=
      (494085850980083391 / 640000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1])
      (by norm_num [bρ_1]) (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_663_2 :
    Uω (aρ 2) (bρ 2) (398572010538831 / 512000000000000 : ℝ) ≤
      (-(654644193995127234473 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (492557151973494943 / 640000000000000000 : ℝ) ≤
      (-(654644193995127234473 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (492557151973494943 / 640000000000000000 : ℝ) =
            (492557151973494943 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (492557151973494943 / 320000000000000000 : ℝ) ≤
            (1078223756754872765527 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3848033824465087 / 5000000000000000 : ℝ)) (q :=
      (492557151973494943 / 640000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2])
      (by norm_num [bρ_2]) (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_663_3 :
    Uω (aρ 3) (bρ 3) (398572010538831 / 512000000000000 : ℝ) ≤
      (-(2680803000857294788523 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (489501671174198047 / 640000000000000000 : ℝ) ≤
      (-(2680803000857294788523 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (489501671174198047 / 640000000000000000 : ℝ) =
            (489501671174198047 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (489501671174198047 / 320000000000000000 : ℝ) ≤
            (4250668802142705211477 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3823989990151073 / 5000000000000000 : ℝ)) (q :=
      (489501671174198047 / 640000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3])
      (by norm_num [bρ_3]) (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_663_4 :
    Uω (aρ 4) (bρ 4) (398572010538831 / 512000000000000 : ℝ) ≤
      (-(2784893666896482135699 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (484432842331385599 / 640000000000000000 : ℝ) ≤
      (-(2784893666896482135699 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (484432842331385599 / 640000000000000000 : ℝ) =
            (484432842331385599 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (484432842331385599 / 320000000000000000 : ℝ) ≤
            (4146578136103517864301 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7567873260029257 / 10000000000000000 : ℝ)) (q :=
      (484432842331385599 / 640000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4])
      (by norm_num [bρ_4]) (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_663_5 :
    Uω (aρ 5) (bρ 5) (398572010538831 / 512000000000000 : ℝ) ≤
      (-(368150362361694042147 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (476728852660897087 / 640000000000000000 : ℝ) ≤
      (-(368150362361694042147 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (476728852660897087 / 640000000000000000 : ℝ) =
            (476728852660897087 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (476728852660897087 / 320000000000000000 : ℝ) ≤
            (498283613013305957853 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7445313502161491 / 10000000000000000 : ℝ)) (q :=
      (476728852660897087 / 640000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5])
      (by norm_num [bρ_5]) (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_663_6 :
    Uω (aρ 6) (bρ 6) (398572010538831 / 512000000000000 : ℝ) ≤
      (-(1589476086348222504551 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (465714580753082303 / 640000000000000000 : ℝ) ≤
      (-(1589476086348222504551 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (465714580753082303 / 640000000000000000 : ℝ) =
            (465714580753082303 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (465714580753082303 / 320000000000000000 : ℝ) ≤
            (1876259815151777495449 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7268357880182279 / 10000000000000000 : ℝ)) (q :=
      (465714580753082303 / 640000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6])
      (by norm_num [bρ_6]) (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_663_7 :
    Uω (aρ 7) (bρ 7) (398572010538831 / 512000000000000 : ℝ) ≤
      (-(3505296020052566257047 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (450761589835292159 / 640000000000000000 : ℝ) ≤
      (-(3505296020052566257047 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (450761589835292159 / 640000000000000000 : ℝ) =
            (450761589835292159 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (450761589835292159 / 320000000000000000 : ℝ) ≤
            (3426175782947433742953 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7024738294761337 / 10000000000000000 : ℝ)) (q :=
      (450761589835292159 / 640000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7])
      (by norm_num [bρ_7]) (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_663_8 :
    Uω (aρ 8) (bρ 8) (398572010538831 / 512000000000000 : ℝ) ≤
      (-(493045393677593413659 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (86279665855173267 / 128000000000000000 : ℝ) ≤
      (-(493045393677593413659 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (86279665855173267 / 128000000000000000 : ℝ) =
            (86279665855173267 / 64000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (86279665855173267 / 64000000000000000 : ℝ) ≤
            (373388581697406586341 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (83789725670241 / 125000000000000 : ℝ)) (q :=
      (86279665855173267 / 128000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8])
      (by norm_num [bρ_8]) (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_663_9 :
    Uω (aρ 9) (bρ 9) (398572010538831 / 512000000000000 : ℝ) ≤
      (-(903254193070843639721 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (407418567990045727 / 640000000000000000 : ℝ) ≤
      (-(903254193070843639721 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (407418567990045727 / 640000000000000000 : ℝ) =
            (407418567990045727 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (407418567990045727 / 320000000000000000 : ℝ) ≤
            (483040167529156360279 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3147388070898693 / 5000000000000000 : ℝ)) (q :=
      (407418567990045727 / 640000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9])
      (by norm_num [bρ_9]) (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_663_10 :
    Uω (aρ 10) (bρ 10) (398572010538831 / 512000000000000 : ℝ) ≤
      (-(5240059346819541959201 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (378971968805497247 / 640000000000000000 : ℝ) ≤
      (-(5240059346819541959201 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (378971968805497247 / 640000000000000000 : ℝ) =
            (378971968805497247 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (378971968805497247 / 320000000000000000 : ℝ) ≤
            (1691412456180458040799 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2897189475387623 / 5000000000000000 : ℝ)) (q :=
      (378971968805497247 / 640000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_663_11 :
    Uω (aρ 11) (bρ 11) (398572010538831 / 512000000000000 : ℝ) ≤
      (-(6132361009483060921937 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (346621038518138783 / 640000000000000000 : ℝ) ≤
      (-(6132361009483060921937 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (346621038518138783 / 640000000000000000 : ℝ) =
            (346621038518138783 / 320000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (346621038518138783 / 320000000000000000 : ℝ) ≤
            (799110793516939078063 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2600944502750147 / 5000000000000000 : ℝ)) (q :=
      (346621038518138783 / 640000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_663_12 :
    Uω (aρ 12) (bρ 12) (398572010538831 / 512000000000000 : ℝ) ≤
      (-(1441049547891940481097 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (311358008202268671 / 640000000000000000 : ℝ) ≤
      (-(1441049547891940481097 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (311358008202268671 / 640000000000000000 : ℝ) =
            (311358008202268671 / 160000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (311358008202268671 / 160000000000000000 : ℝ) ≤
            (1331539173308059518903 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4523619404814353 / 10000000000000000 : ℝ)) (q :=
      (311358008202268671 / 640000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_663_13 :
    Uω (aρ 13) (bρ 13) (398572010538831 / 512000000000000 : ℝ) ≤
      (-(2115390522553072752363 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (274599031618965983 / 640000000000000000 : ℝ) ≤
      (-(2115390522553072752363 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (274599031618965983 / 640000000000000000 : ℝ) =
            (274599031618965983 / 160000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (274599031618965983 / 160000000000000000 : ℝ) ≤
            (1350345378946927247637 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (471785391022643 / 1250000000000000 : ℝ)) (q :=
      (274599031618965983 / 640000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_663_14 :
    Uω (aρ 14) (bρ 14) (398572010538831 / 512000000000000 : ℝ) ≤
      (-(9882260711854623304547 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (238231312906570783 / 640000000000000000 : ℝ) ≤
      (-(9882260711854623304547 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (238231312906570783 / 640000000000000000 : ℝ) =
            (238231312906570783 / 160000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (238231312906570783 / 160000000000000000 : ℝ) ≤
            (3980682894145376695453 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1490859601731897 / 5000000000000000 : ℝ)) (q :=
      (238231312906570783 / 640000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_663_15 :
    Uω (aρ 15) (bρ 15) (398572010538831 / 512000000000000 : ℝ) ≤
      (-(11385648572861481335083 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (204978135744948383 / 640000000000000000 : ℝ) ≤
      (-(11385648572861481335083 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (204978135744948383 / 640000000000000000 : ℝ) =
            (204978135744948383 / 160000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (204978135744948383 / 160000000000000000 : ℝ) ≤
            (2477295033138518664917 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1101065347289047 / 5000000000000000 : ℝ)) (q :=
      (204978135744948383 / 640000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_663_16 :
    Uω (aρ 16) (bρ 16) (398572010538831 / 512000000000000 : ℝ) ≤
      (-(3171300016281540266367 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (179998437324363327 / 640000000000000000 : ℝ) ≤
      (-(3171300016281540266367 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (179998437324363327 / 640000000000000000 : ℝ) =
            (179998437324363327 / 160000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (179998437324363327 / 160000000000000000 : ℝ) ≤
            (294435885218459733633 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1573886770444811 / 10000000000000000 : ℝ)) (q :=
      (179998437324363327 / 640000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_663 :
    Uρ (398572010538831 / 512000000000000 : ℝ) ≤
      (-(4678476634791325595441 / 10000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (398572010538831 / 512000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(1293794432980282284923 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_663_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (398572010538831 / 512000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(654644193995127234473 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_663_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (398572010538831 / 512000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(2680803000857294788523 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_663_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (398572010538831 / 512000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(2784893666896482135699 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_663_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (398572010538831 / 512000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) * (-(368150362361694042147 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_663_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (398572010538831 / 512000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(1589476086348222504551 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_663_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (398572010538831 / 512000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(3505296020052566257047 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_663_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (398572010538831 / 512000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(493045393677593413659 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_663_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (398572010538831 / 512000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(903254193070843639721 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_663_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) *
        Uω (aρ 10) (bρ 10) (398572010538831 / 512000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(5240059346819541959201 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_663_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) *
        Uω (aρ 11) (bρ 11) (398572010538831 / 512000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(6132361009483060921937 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_663_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) *
        Uω (aρ 12) (bρ 12) (398572010538831 / 512000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(1441049547891940481097 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_663_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) *
        Uω (aρ 13) (bρ 13) (398572010538831 / 512000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(2115390522553072752363 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_663_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) *
        Uω (aρ 14) (bρ 14) (398572010538831 / 512000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(9882260711854623304547 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_663_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) *
        Uω (aρ 15) (bρ 15) (398572010538831 / 512000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(11385648572861481335083 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_663_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) *
        Uω (aρ 16) (bρ 16) (398572010538831 / 512000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(3171300016281540266367 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_663_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

end Zeta5Irrational
