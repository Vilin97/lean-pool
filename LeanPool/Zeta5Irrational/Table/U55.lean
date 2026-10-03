/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Table.UpperCertificate

/-! # Certified arcsine potential bounds (U55) -/

public section

open Finset

namespace Zeta5Irrational

lemma U_664_1 :
    Uω (aρ 1) (bρ 1) (199912686621581 / 256000000000000 : ℝ) ≤
      (-(1277964907620946027673 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (247826279298423837 / 320000000000000000 : ℝ) ≤
      (-(1277964907620946027673 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (247826279298423837 / 320000000000000000 : ℝ) =
            (247826279298423837 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (247826279298423837 / 160000000000000000 : ℝ) ≤
            (2187770993879053972327 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3872275176540491 / 5000000000000000 : ℝ)) (q :=
      (247826279298423837 / 320000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1])
      (by norm_num [bρ_1]) (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_664_2 :
    Uω (aρ 2) (bρ 2) (199912686621581 / 256000000000000 : ℝ) ≤
      (-(103472765751352777257 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (49412388332745321 / 64000000000000000 : ℝ) ≤
      (-(103472765751352777257 / 400000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (49412388332745321 / 64000000000000000 : ℝ) =
            (49412388332745321 / 32000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (49412388332745321 / 32000000000000000 : ℝ) ≤
            (173786106368647222743 / 400000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1544109652684481 / 2000000000000000 : ℝ)) (q :=
      (49412388332745321 / 64000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_664_3 :
    Uω (aρ 3) (bρ 3) (199912686621581 / 256000000000000 : ℝ) ≤
      (-(2648846011764422714851 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (245534236655695789 / 320000000000000000 : ℝ) ≤
      (-(2648846011764422714851 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (245534236655695789 / 320000000000000000 : ℝ) =
            (245534236655695789 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (245534236655695789 / 160000000000000000 : ℝ) ≤
            (4282625791235577285149 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7672462806770479 / 10000000000000000 : ℝ)) (q :=
      (245534236655695789 / 320000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3])
      (by norm_num [bρ_3]) (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_664_4 :
    Uω (aρ 4) (bρ 4) (199912686621581 / 256000000000000 : ℝ) ≤
      (-(2752598967989138191723 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (242999916260845037 / 320000000000000000 : ℝ) ≤
      (-(2752598967989138191723 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (242999916260845037 / 320000000000000000 : ℝ) =
            (242999916260845037 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (242999916260845037 / 160000000000000000 : ℝ) ≤
            (4178872835010861808277 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7592361963157307 / 10000000000000000 : ℝ)) (q :=
      (242999916260845037 / 320000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4])
      (by norm_num [bρ_4]) (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_664_5 :
    Uω (aρ 5) (bρ 5) (199912686621581 / 256000000000000 : ℝ) ≤
      (-(291237749004709474387 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (47829630581773097 / 64000000000000000 : ℝ) ≤
      (-(291237749004709474387 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (47829630581773097 / 64000000000000000 : ℝ) =
            (47829630581773097 / 32000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (47829630581773097 / 32000000000000000 : ℝ) ≤
            (401909431295290525613 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1493963334598717 / 2000000000000000 : ℝ)) (q :=
      (47829630581773097 / 64000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_664_6 :
    Uω (aρ 6) (bρ 6) (199912686621581 / 256000000000000 : ℝ) ≤
      (-(3145329015573109930877 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (233641547824428733 / 320000000000000000 : ℝ) ≤
      (-(3145329015573109930877 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (233641547824428733 / 320000000000000000 : ℝ) =
            (233641547824428733 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (233641547824428733 / 160000000000000000 : ℝ) ≤
            (3786142787426890069123 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (113951472349317 / 156250000000000 : ℝ)) (q :=
      (233641547824428733 / 320000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6])
      (by norm_num [bρ_6]) (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_664_7 :
    Uω (aρ 7) (bρ 7) (199912686621581 / 256000000000000 : ℝ) ≤
      (-(3470509010608891617659 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (226166192591551821 / 320000000000000000 : ℝ) ≤
      (-(3470509010608891617659 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (226166192591551821 / 320000000000000000 : ℝ) =
            (226166192591551821 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (226166192591551821 / 160000000000000000 : ℝ) ≤
            (3460962792391108382341 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7049345909061481 / 10000000000000000 : ℝ)) (q :=
      (226166192591551821 / 320000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7])
      (by norm_num [bρ_7]) (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_664_8 :
    Uω (aρ 8) (bρ 8) (199912686621581 / 256000000000000 : ℝ) ≤
      (-(1953955403703193484059 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (216486873429367757 / 320000000000000000 : ℝ) ≤
      (-(1953955403703193484059 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (216486873429367757 / 320000000000000000 : ℝ) =
            (216486873429367757 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (216486873429367757 / 160000000000000000 : ℝ) ≤
            (1511780497796806515941 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6727930112764977 / 10000000000000000 : ℝ)) (q :=
      (216486873429367757 / 320000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8])
      (by norm_num [bρ_8]) (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_664_9 :
    Uω (aρ 9) (bρ 9) (199912686621581 / 256000000000000 : ℝ) ≤
      (-(4477459106514180083733 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (204501453877376573 / 320000000000000000 : ℝ) ≤
      (-(4477459106514180083733 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (204501453877376573 / 320000000000000000 : ℝ) =
            (204501453877376573 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (204501453877376573 / 160000000000000000 : ℝ) ≤
            (2454012696485819916267 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (789975877390691 / 1250000000000000 : ℝ)) (q :=
      (204501453877376573 / 320000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9])
      (by norm_num [bρ_9]) (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_664_10 :
    Uω (aρ 10) (bρ 10) (199912686621581 / 256000000000000 : ℝ) ≤
      (-(1299476206458049317223 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (38057287889597513 / 64000000000000000 : ℝ) ≤
      (-(1299476206458049317223 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (38057287889597513 / 64000000000000000 : ℝ) =
            (38057287889597513 / 32000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (38057287889597513 / 32000000000000000 : ℝ) ≤
            (433391744291950682777 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1163985530156743 / 2000000000000000 : ℝ)) (q :=
      (38057287889597513 / 64000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_664_11 :
    Uω (aρ 11) (bρ 11) (199912686621581 / 256000000000000 : ℝ) ≤
      (-(6085421088558797644903 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (174125949780980637 / 320000000000000000 : ℝ) ≤
      (-(6085421088558797644903 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (174125949780980637 / 320000000000000000 : ℝ) =
            (174125949780980637 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (174125949780980637 / 160000000000000000 : ℝ) ≤
            (846050714441202355097 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2614186836400391 / 5000000000000000 : ℝ)) (q :=
      (174125949780980637 / 320000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_664_12 :
    Uω (aρ 12) (bρ 12) (199912686621581 / 256000000000000 : ℝ) ≤
      (-(3575650047906401257211 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (156521125124646877 / 320000000000000000 : ℝ) ≤
      (-(3575650047906401257211 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (156521125124646877 / 320000000000000000 : ℝ) =
            (156521125124646877 / 80000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (156521125124646877 / 80000000000000000 : ℝ) ≤
            (3355821755093598742789 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2275886114232461 / 5000000000000000 : ℝ)) (q :=
      (156521125124646877 / 320000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_664_13 :
    Uω (aρ 13) (bρ 13) (199912686621581 / 256000000000000 : ℝ) ≤
      (-(4198484460239256737569 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27637849467573129 / 64000000000000000 : ℝ) ≤
      (-(4198484460239256737569 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (27637849467573129 / 64000000000000000 : ℝ) =
            (27637849467573129 / 16000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (27637849467573129 / 16000000000000000 : ℝ) ≤
            (2732987342760743262431 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (761082321677219 / 2000000000000000 : ℝ)) (q :=
      (27637849467573129 / 64000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_664_14 :
    Uω (aρ 14) (bρ 14) (199912686621581 / 256000000000000 : ℝ) ≤
      (-(1960132106122831270009 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (120091618888945197 / 320000000000000000 : ℝ) ≤
      (-(1960132106122831270009 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (120091618888945197 / 320000000000000000 : ℝ) =
            (120091618888945197 / 80000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (120091618888945197 / 80000000000000000 : ℝ) ≤
            (812456615077168729991 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3018237115373567 / 10000000000000000 : ℝ)) (q :=
      (120091618888945197 / 320000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_664_15 :
    Uω (aρ 15) (bρ 15) (199912686621581 / 256000000000000 : ℝ) ≤
      (-(225512837703902044943 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (165796384488381 / 512000000000000 : ℝ) ≤
      (-(225512837703902044943 / 200000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (165796384488381 / 512000000000000 : ℝ) =
            (165796384488381 / 128000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (165796384488381 / 128000000000000 : ℝ) ≤
            (51746034416097955057 / 200000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3597608770091 / 16000000000000 : ℝ)) (q :=
      (165796384488381 / 512000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15]) (by norm_num [bρ_15])
      (by norm_num) (by norm_num [aρ_15, bρ_15]) (by norm_num [aρ_15, bρ_15]) hlg

lemma U_664_16 :
    Uω (aρ 16) (bρ 16) (199912686621581 / 256000000000000 : ℝ) ≤
      (-(1253266360243979778637 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (91382558574823133 / 320000000000000000 : ℝ) ≤
      (-(1253266360243979778637 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (91382558574823133 / 320000000000000000 : ℝ) =
            (91382558574823133 / 80000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (91382558574823133 / 80000000000000000 : ℝ) ≤
            (133028000356020221363 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (817932887332969 / 5000000000000000 : ℝ)) (q :=
      (91382558574823133 / 320000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_664 :
    Uρ (199912686621581 / 256000000000000 : ℝ) ≤
      (-(4636648990333002156281 / 10000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (199912686621581 / 256000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(1277964907620946027673 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_664_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (199912686621581 / 256000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(103472765751352777257 / 400000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_664_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (199912686621581 / 256000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(2648846011764422714851 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_664_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (199912686621581 / 256000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(2752598967989138191723 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_664_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (199912686621581 / 256000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) * (-(291237749004709474387 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_664_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (199912686621581 / 256000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(3145329015573109930877 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_664_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (199912686621581 / 256000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(3470509010608891617659 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_664_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (199912686621581 / 256000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(1953955403703193484059 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_664_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (199912686621581 / 256000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(4477459106514180083733 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_664_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) *
        Uω (aρ 10) (bρ 10) (199912686621581 / 256000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(1299476206458049317223 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_664_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) *
        Uω (aρ 11) (bρ 11) (199912686621581 / 256000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(6085421088558797644903 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_664_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) *
        Uω (aρ 12) (bρ 12) (199912686621581 / 256000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(3575650047906401257211 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_664_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) *
        Uω (aρ 13) (bρ 13) (199912686621581 / 256000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(4198484460239256737569 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_664_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) *
        Uω (aρ 14) (bρ 14) (199912686621581 / 256000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(1960132106122831270009 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_664_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) *
        Uω (aρ 15) (bρ 15) (199912686621581 / 256000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(225512837703902044943 / 200000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_664_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) *
        Uω (aρ 16) (bρ 16) (199912686621581 / 256000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(1253266360243979778637 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_664_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_665_1 :
    Uω (aρ 1) (bρ 1) (25145756165739 / 32000000000000 : ℝ) ≤
      (-(249291082670160325427 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (31174123359408541 / 40000000000000000 : ℝ) ≤
      (-(249291082670160325427 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (31174123359408541 / 40000000000000000 : ℝ) =
            (31174123359408541 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (31174123359408541 / 20000000000000000 : ℝ) ≤
            (443856097629839674573 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7793510095995833 / 10000000000000000 : ℝ)) (q :=
      (31174123359408541 / 40000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_665_2 :
    Uω (aρ 2) (bρ 2) (25145756165739 / 32000000000000 : ℝ) ≤
      (-(252360486208296023661 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (31078584094158457 / 40000000000000000 : ℝ) ≤
      (-(252360486208296023661 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (31078584094158457 / 40000000000000000 : ℝ) =
            (31078584094158457 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (31078584094158457 / 20000000000000000 : ℝ) ≤
            (440786694091703976339 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7769509475880791 / 10000000000000000 : ℝ)) (q :=
      (31078584094158457 / 40000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_665_3 :
    Uω (aρ 3) (bρ 3) (25145756165739 / 32000000000000 : ℝ) ≤
      (-(2585236824123272191887 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (30887629731693159 / 40000000000000000 : ℝ) ≤
      (-(2585236824123272191887 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (30887629731693159 / 40000000000000000 : ℝ) =
            (30887629731693159 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (30887629731693159 / 20000000000000000 : ℝ) ≤
            (4346234978876727808113 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3860714200499071 / 5000000000000000 : ℝ)) (q :=
      (30887629731693159 / 40000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_665_4 :
    Uω (aρ 4) (bρ 4) (25145756165739 / 32000000000000 : ℝ) ≤
      (-(1344160446545207092199 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (30570862961772313 / 40000000000000000 : ℝ) ≤
      (-(1344160446545207092199 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (30570862961772313 / 40000000000000000 : ℝ) =
            (30570862961772313 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (30570862961772313 / 20000000000000000 : ℝ) ≤
            (2121575454954792907801 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7641339197102719 / 10000000000000000 : ℝ)) (q :=
      (30570862961772313 / 40000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_665_5 :
    Uω (aρ 5) (bρ 5) (25145756165739 / 32000000000000 : ℝ) ≤
      (-(355881058895171594713 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (30089449842355157 / 40000000000000000 : ℝ) ≤
      (-(355881058895171594713 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (30089449842355157 / 40000000000000000 : ℝ) =
            (30089449842355157 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (30089449842355157 / 20000000000000000 : ℝ) ≤
            (510552916479828405287 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7518822556729141 / 10000000000000000 : ℝ)) (q :=
      (30089449842355157 / 40000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_665_6 :
    Uω (aρ 6) (bρ 6) (25145756165739 / 32000000000000 : ℝ) ≤
      (-(3078420738767238145273 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1176050222896367 / 1600000000000000 : ℝ) ≤
      (-(3078420738767238145273 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (1176050222896367 / 1600000000000000 : ℝ) =
            (1176050222896367 / 800000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1176050222896367 / 800000000000000 : ℝ) ≤
            (3853051064232761854727 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (146839315937923 / 200000000000000 : ℝ)) (q :=
      (1176050222896367 / 1600000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_665_7 :
    Uω (aρ 7) (bρ 7) (25145756165739 / 32000000000000 : ℝ) ≤
      (-(340129780488928500307 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5693423637368201 / 8000000000000000 : ℝ) ≤
      (-(340129780488928500307 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (5693423637368201 / 8000000000000000 : ℝ) =
            (5693423637368201 / 4000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5693423637368201 / 4000000000000000 : ℝ) ≤
            (353017399811071499693 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1419711696974413 / 2000000000000000 : ℝ)) (q :=
      (5693423637368201 / 8000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_665_8 :
    Uω (aρ 8) (bρ 8) (25145756165739 / 32000000000000 : ℝ) ≤
      (-(3835406704026617134509 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27257774507655987 / 40000000000000000 : ℝ) ≤
      (-(3835406704026617134509 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (27257774507655987 / 40000000000000000 : ℝ) =
            (27257774507655987 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (27257774507655987 / 20000000000000000 : ℝ) ≤
            (3096065098973382865491 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1694357074154889 / 2500000000000000 : ℝ)) (q :=
      (27257774507655987 / 40000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_665_9 :
    Uω (aρ 9) (bρ 9) (25145756165739 / 32000000000000 : ℝ) ≤
      (-(4400294372036981046643 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25760698502538297 / 40000000000000000 : ℝ) ≤
      (-(4400294372036981046643 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (25760698502538297 / 40000000000000000 : ℝ) =
            (25760698502538297 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (25760698502538297 / 20000000000000000 : ℝ) ≤
            (2531177430963018953357 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6369855922420711 / 10000000000000000 : ℝ)) (q :=
      (25760698502538297 / 40000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_665_10 :
    Uω (aρ 10) (bρ 10) (25145756165739 / 32000000000000 : ℝ) ≤
      (-(2557073977047964558419 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (23985864038979301 / 40000000000000000 : ℝ) ≤
      (-(2557073977047964558419 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (23985864038979301 / 40000000000000000 : ℝ) =
            (23985864038979301 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (23985864038979301 / 20000000000000000 : ℝ) ≤
            (908661924452035441581 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (5870997724136213 / 10000000000000000 : ℝ)) (q :=
      (23985864038979301 / 40000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_665_11 :
    Uω (aρ 11) (bρ 11) (25145756165739 / 32000000000000 : ℝ) ≤
      (-(5992249965690502151559 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4393897053689701 / 8000000000000000 : ℝ) ≤
      (-(5992249965690502151559 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (4393897053689701 / 8000000000000000 : ℝ) =
            (4393897053689701 / 4000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4393897053689701 / 4000000000000000 : ℝ) ≤
            (939221837309497848441 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1056256993015163 / 2000000000000000 : ℝ)) (q :=
      (4393897053689701 / 8000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_665_12 :
    Uω (aρ 12) (bρ 12) (25145756165739 / 32000000000000 : ℝ) ≤
      (-(1408879486035550407403 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (19775419173586063 / 40000000000000000 : ℝ) ≤
      (-(1408879486035550407403 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (19775419173586063 / 40000000000000000 : ℝ) =
            (19775419173586063 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (19775419173586063 / 10000000000000000 : ℝ) ≤
            (1363709235164449592597 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2303976007164797 / 5000000000000000 : ℝ)) (q :=
      (19775419173586063 / 40000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_665_13 :
    Uω (aρ 13) (bρ 13) (25145756165739 / 32000000000000 : ℝ) ≤
      (-(4134674394368595173987 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (17495515216103551 / 40000000000000000 : ℝ) ≤
      (-(4134674394368595173987 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (17495515216103551 / 40000000000000000 : ℝ) =
            (17495515216103551 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (17495515216103551 / 10000000000000000 : ℝ) ≤
            (2796797408631404826013 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1933690888591669 / 5000000000000000 : ℝ)) (q :=
      (17495515216103551 / 40000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_665_14 :
    Uω (aρ 14) (bρ 14) (25145756165739 / 32000000000000 : ℝ) ≤
      (-(9640365382064048121153 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (15254017567212007 / 40000000000000000 : ℝ) ≤
      (-(9640365382064048121153 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (15254017567212007 / 40000000000000000 : ℝ) =
            (15254017567212007 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (15254017567212007 / 10000000000000000 : ℝ) ≤
            (4222578223935951878847 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1545280118891283 / 5000000000000000 : ℝ)) (q :=
      (15254017567212007 / 40000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_665_15 :
    Uω (aρ 15) (bρ 15) (25145756165739 / 32000000000000 : ℝ) ≤
      (-(442487964087878460311 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13232283235222089 / 40000000000000000 : ℝ) ≤
      (-(442487964087878460311 / 400000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (13232283235222089 / 40000000000000000 : ℝ) =
            (13232283235222089 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (13232283235222089 / 10000000000000000 : ℝ) ≤
            (112029780152121539689 / 400000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2339266349202607 / 10000000000000000 : ℝ)) (q :=
      (13232283235222089 / 40000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_665_16 :
    Uω (aρ 16) (bρ 16) (25145756165739 / 32000000000000 : ℝ) ≤
      (-(12243810141211648147373 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (11757583533052329 / 40000000000000000 : ℝ) ≤
      (-(12243810141211648147373 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (11757583533052329 / 40000000000000000 : ℝ) =
            (11757583533052329 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (11757583533052329 / 10000000000000000 : ℝ) ≤
            (1619133464788351852627 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1754288149627727 / 10000000000000000 : ℝ)) (q :=
      (11757583533052329 / 40000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_665 :
    Uρ (25145756165739 / 32000000000000 : ℝ) ≤
      (-(4553883503740599041333 / 10000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (25145756165739 / 32000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(249291082670160325427 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_665_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (25145756165739 / 32000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(252360486208296023661 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_665_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (25145756165739 / 32000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(2585236824123272191887 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_665_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (25145756165739 / 32000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(1344160446545207092199 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_665_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (25145756165739 / 32000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) * (-(355881058895171594713 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_665_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (25145756165739 / 32000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(3078420738767238145273 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_665_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (25145756165739 / 32000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(340129780488928500307 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_665_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (25145756165739 / 32000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(3835406704026617134509 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_665_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (25145756165739 / 32000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(4400294372036981046643 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_665_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (25145756165739 / 32000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(2557073977047964558419 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_665_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (25145756165739 / 32000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(5992249965690502151559 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_665_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (25145756165739 / 32000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(1408879486035550407403 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_665_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (25145756165739 / 32000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(4134674394368595173987 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_665_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (25145756165739 / 32000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(9640365382064048121153 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_665_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (25145756165739 / 32000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(442487964087878460311 / 400000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_665_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (25145756165739 / 32000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(12243810141211648147373 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_665_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_666_1 :
    Uω (aρ 1) (bρ 1) (202419412030243 / 256000000000000 : ℝ) ≤
      (-(2430286493772126347773 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (250959694399717187 / 320000000000000000 : ℝ) ≤
      (-(2430286493772126347773 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (250959694399717187 / 320000000000000000 : ℝ) =
            (250959694399717187 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (250959694399717187 / 160000000000000000 : ℝ) ≤
            (4501185309227873652227 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7842469835635957 / 10000000000000000 : ℝ)) (q :=
      (250959694399717187 / 320000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1])
      (by norm_num [bρ_1]) (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_666_2 :
    Uω (aρ 2) (bρ 2) (202419412030243 / 256000000000000 : ℝ) ≤
      (-(49215753797925468473 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (250195403495771923 / 320000000000000000 : ℝ) ≤
      (-(49215753797925468473 / 200000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (250195403495771923 / 320000000000000000 : ℝ) =
            (250195403495771923 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (250195403495771923 / 160000000000000000 : ℝ) ≤
            (89413682262074531527 / 200000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3909235333324689 / 5000000000000000 : ℝ)) (q :=
      (250195403495771923 / 320000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2])
      (by norm_num [bρ_2]) (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_666_3 :
    Uω (aρ 3) (bρ 3) (202419412030243 / 256000000000000 : ℝ) ≤
      (-(1261014871413616783293 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (248667837818667059 / 320000000000000000 : ℝ) ≤
      (-(1261014871413616783293 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (248667837818667059 / 320000000000000000 : ℝ) =
            (248667837818667059 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (248667837818667059 / 160000000000000000 : ℝ) ≤
            (2204721030086383216707 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1942598479545081 / 2500000000000000 : ℝ)) (q :=
      (248667837818667059 / 320000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3])
      (by norm_num [bρ_3]) (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_666_4 :
    Uω (aρ 4) (bρ 4) (202419412030243 / 256000000000000 : ℝ) ≤
      (-(656113373712938037237 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (246133887510078227 / 320000000000000000 : ℝ) ≤
      (-(656113373712938037237 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (246133887510078227 / 320000000000000000 : ℝ) =
            (246133887510078227 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (246133887510078227 / 160000000000000000 : ℝ) ≤
            (1076754577037061962763 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3845158102479261 / 5000000000000000 : ℝ)) (q :=
      (246133887510078227 / 320000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4])
      (by norm_num [bρ_4]) (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_666_5 :
    Uω (aρ 5) (bρ 5) (202419412030243 / 256000000000000 : ℝ) ≤
      (-(1391071934225770335259 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (242283034957824227 / 320000000000000000 : ℝ) ≤
      (-(1391071934225770335259 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (242283034957824227 / 320000000000000000 : ℝ) =
            (242283034957824227 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (242283034957824227 / 160000000000000000 : ℝ) ≤
            (2074663967274229664741 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7567827839777647 / 10000000000000000 : ℝ)) (q :=
      (242283034957824227 / 320000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5])
      (by norm_num [bρ_5]) (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_666_6 :
    Uω (aρ 6) (bρ 6) (202419412030243 / 256000000000000 : ℝ) ≤
      (-(1505979082273865270421 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (236778517547688323 / 320000000000000000 : ℝ) ≤
      (-(1505979082273865270421 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (236778517547688323 / 320000000000000000 : ℝ) =
            (236778517547688323 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (236778517547688323 / 160000000000000000 : ℝ) ≤
            (1959756819226134729579 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7391035876784153 / 10000000000000000 : ℝ)) (q :=
      (236778517547688323 / 320000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6])
      (by norm_num [bρ_6]) (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_666_7 :
    Uω (aρ 7) (bρ 7) (202419412030243 / 256000000000000 : ℝ) ≤
      (-(208285297068072753121 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (45861528555831351 / 64000000000000000 : ℝ) ≤
      (-(208285297068072753121 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (45861528555831351 / 64000000000000000 : ℝ) =
            (45861528555831351 / 32000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (45861528555831351 / 32000000000000000 : ℝ) ≤
            (224931690619427246879 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (714776758451093 / 1000000000000000 : ℝ)) (q :=
      (45861528555831351 / 64000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_666_8 :
    Uω (aρ 8) (bρ 8) (202419412030243 / 256000000000000 : ℝ) ≤
      (-(37634301630337236271 / 100000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (219637394386552531 / 320000000000000000 : ℝ) ≤
      (-(37634301630337236271 / 100000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (219637394386552531 / 320000000000000000 : ℝ) =
            (219637394386552531 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (219637394386552531 / 160000000000000000 : ℝ) ≤
            (31680416399662763729 / 100000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3413459355656583 / 5000000000000000 : ℝ)) (q :=
      (219637394386552531 / 320000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8])
      (by norm_num [bρ_8]) (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_666_9 :
    Uω (aρ 9) (bρ 9) (202419412030243 / 256000000000000 : ℝ) ≤
      (-(864746693025047178221 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (41533890668800807 / 64000000000000000 : ℝ) ≤
      (-(864746693025047178221 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (41533890668800807 / 64000000000000000 : ℝ) =
            (41533890668800807 / 32000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (41533890668800807 / 32000000000000000 : ℝ) ≤
            (521547667574952821779 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1283977604902777 / 2000000000000000 : ℝ)) (q :=
      (41533890668800807 / 64000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_666_10 :
    Uω (aρ 10) (bρ 10) (202419412030243 / 256000000000000 : ℝ) ≤
      (-(31444476630483468137 / 62500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (193486814774151011 / 320000000000000000 : ℝ) ≤
      (-(31444476630483468137 / 62500000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (193486814774151011 / 320000000000000000 : ℝ) =
            (193486814774151011 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (193486814774151011 / 160000000000000000 : ℝ) ≤
            (11877222138266531863 / 62500000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (5922032147393071 / 10000000000000000 : ℝ)) (q :=
      (193486814774151011 / 320000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_666_11 :
    Uω (aρ 11) (bρ 11) (202419412030243 / 256000000000000 : ℝ) ≤
      (-(2950003497771861187207 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (177384606978711139 / 320000000000000000 : ℝ) ≤
      (-(2950003497771861187207 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (177384606978711139 / 320000000000000000 : ℝ) =
            (177384606978711139 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (177384606978711139 / 160000000000000000 : ℝ) ≤
            (515732403728138812793 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (5334120786383079 / 10000000000000000 : ℝ)) (q :=
      (177384606978711139 / 320000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_666_12 :
    Uω (aρ 12) (bρ 12) (202419412030243 / 256000000000000 : ℝ) ≤
      (-(3469394193332567164563 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (159882977435271507 / 320000000000000000 : ℝ) ≤
      (-(3469394193332567164563 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (159882977435271507 / 320000000000000000 : ℝ) =
            (159882977435271507 / 80000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 15
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (159882977435271507 / 80000000000000000 : ℝ) ≤
            (3462077609667432835437 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2331984518301551 / 5000000000000000 : ℝ)) (q :=
      (159882977435271507 / 320000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_666_13 :
    Uω (aρ 13) (bρ 13) (202419412030243 / 256000000000000 : ℝ) ≤
      (-(8143751499644154206229 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (141733118963215363 / 320000000000000000 : ℝ) ≤
      (-(8143751499644154206229 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (141733118963215363 / 320000000000000000 : ℝ) =
            (141733118963215363 / 80000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (141733118963215363 / 80000000000000000 : ℝ) ≤
            (5719192106355845793771 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3928984623694593 / 10000000000000000 : ℝ)) (q :=
      (141733118963215363 / 320000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_666_14 :
    Uω (aρ 14) (bρ 14) (202419412030243 / 256000000000000 : ℝ) ≤
      (-(9483755677962245212443 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (123958325876728179 / 320000000000000000 : ℝ) ≤
      (-(9483755677962245212443 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (123958325876728179 / 320000000000000000 : ℝ) =
            (123958325876728179 / 80000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (123958325876728179 / 80000000000000000 : ℝ) ≤
            (4379187928037754787557 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (98812104401067 / 312500000000000 : ℝ)) (q :=
      (123958325876728179 / 320000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_666_15 :
    Uω (aρ 15) (bρ 15) (202419412030243 / 256000000000000 : ℝ) ≤
      (-(5428388530800015652507 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (108055316856504243 / 320000000000000000 : ℝ) ≤
      (-(5428388530800015652507 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (108055316856504243 / 320000000000000000 : ℝ) =
            (108055316856504243 / 80000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (108055316856504243 / 80000000000000000 : ℝ) ≤
            (1503083272199984347493 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (606905638621287 / 2500000000000000 : ℝ)) (q :=
      (108055316856504243 / 320000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_666_16 :
    Uω (aρ 16) (bρ 16) (202419412030243 / 256000000000000 : ℝ) ≤
      (-(748334846524065932333 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (96639275845260099 / 320000000000000000 : ℝ) ≤
      (-(748334846524065932333 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (96639275845260099 / 320000000000000000 : ℝ) =
            (96639275845260099 / 80000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (96639275845260099 / 80000000000000000 : ℝ) ≤
            (118099128850934067667 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1866491642792389 / 10000000000000000 : ℝ)) (q :=
      (96639275845260099 / 320000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_666 :
    Uρ (202419412030243 / 256000000000000 : ℝ) ≤
      (-(4472242976673732246981 / 10000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (202419412030243 / 256000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(2430286493772126347773 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_666_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (202419412030243 / 256000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) * (-(49215753797925468473 / 200000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_666_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (202419412030243 / 256000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(1261014871413616783293 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_666_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (202419412030243 / 256000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(656113373712938037237 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_666_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (202419412030243 / 256000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(1391071934225770335259 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_666_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (202419412030243 / 256000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(1505979082273865270421 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_666_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (202419412030243 / 256000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(208285297068072753121 / 625000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_666_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (202419412030243 / 256000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) * (-(37634301630337236271 / 100000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_666_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (202419412030243 / 256000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(864746693025047178221 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_666_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) *
        Uω (aρ 10) (bρ 10) (202419412030243 / 256000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) * (-(31444476630483468137 / 62500000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_666_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) *
        Uω (aρ 11) (bρ 11) (202419412030243 / 256000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(2950003497771861187207 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_666_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) *
        Uω (aρ 12) (bρ 12) (202419412030243 / 256000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(3469394193332567164563 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_666_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) *
        Uω (aρ 13) (bρ 13) (202419412030243 / 256000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(8143751499644154206229 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_666_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) *
        Uω (aρ 14) (bρ 14) (202419412030243 / 256000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(9483755677962245212443 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_666_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) *
        Uω (aρ 15) (bρ 15) (202419412030243 / 256000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(5428388530800015652507 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_666_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) *
        Uω (aρ 16) (bρ 16) (202419412030243 / 256000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(748334846524065932333 / 625000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_666_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_667_1 :
    Uω (aρ 1) (bρ 1) (101836387367287 / 128000000000000 : ℝ) ≤
      (-(1184025952061820073691 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25252640187274563 / 32000000000000000 : ℝ) ≤
      (-(1184025952061820073691 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (25252640187274563 / 32000000000000000 : ℝ) =
            (25252640187274563 / 16000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (25252640187274563 / 16000000000000000 : ℝ) ≤
            (2281709949438179926309 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1578285914412461 / 2000000000000000 : ℝ)) (q :=
      (25252640187274563 / 32000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_667_2 :
    Uω (aρ 2) (bρ 2) (101836387367287 / 128000000000000 : ℝ) ≤
      (-(149897666808250901199 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25176213389771851 / 32000000000000000 : ℝ) ≤
      (-(149897666808250901199 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (25176213389771851 / 32000000000000000 : ℝ) =
            (25176213389771851 / 16000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (25176213389771851 / 16000000000000000 : ℝ) ≤
            (283319320879249098801 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (786743183613311 / 1000000000000000 : ℝ)) (q :=
      (25176213389771851 / 32000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_667_3 :
    Uω (aρ 3) (bρ 3) (101836387367287 / 128000000000000 : ℝ) ≤
      (-(2459219715338930544141 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (125117318287109767 / 160000000000000000 : ℝ) ≤
      (-(2459219715338930544141 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (125117318287109767 / 160000000000000000 : ℝ) =
            (125117318287109767 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (125117318287109767 / 80000000000000000 : ℝ) ≤
            (4472252087661069455859 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (977419919970553 / 1250000000000000 : ℝ)) (q :=
      (125117318287109767 / 160000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3])
      (by norm_num [bρ_3]) (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_667_4 :
    Uω (aρ 4) (bρ 4) (101836387367287 / 128000000000000 : ℝ) ≤
      (-(2560991557050394938723 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (123850433888610727 / 160000000000000000 : ℝ) ≤
      (-(2560991557050394938723 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (123850433888610727 / 160000000000000000 : ℝ) =
            (123850433888610727 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (123850433888610727 / 80000000000000000 : ℝ) ≤
            (4370480245949605061277 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1934823247754261 / 2500000000000000 : ℝ)) (q :=
      (123850433888610727 / 160000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4])
      (by norm_num [bρ_4]) (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_667_5 :
    Uω (aρ 5) (bρ 5) (101836387367287 / 128000000000000 : ℝ) ≤
      (-(1358829098960116310293 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (121925230875660191 / 160000000000000000 : ℝ) ≤
      (-(1358829098960116310293 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (121925230875660191 / 160000000000000000 : ℝ) =
            (121925230875660191 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (121925230875660191 / 80000000000000000 : ℝ) ≤
            (2106906802539883689707 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7616832533733227 / 10000000000000000 : ℝ)) (q :=
      (121925230875660191 / 160000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5])
      (by norm_num [bρ_5]) (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_667_6 :
    Uω (aρ 6) (bρ 6) (101836387367287 / 128000000000000 : ℝ) ≤
      (-(2945935381077970403423 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (23834696720031283 / 32000000000000000 : ℝ) ≤
      (-(2945935381077970403423 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (23834696720031283 / 32000000000000000 : ℝ) =
            (23834696720031283 / 16000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (23834696720031283 / 16000000000000000 : ℝ) ≤
            (3985536421922029596577 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1488020899887051 / 2000000000000000 : ℝ)) (q :=
      (23834696720031283 / 32000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_667_7 :
    Uω (aρ 7) (bρ 7) (101836387367287 / 128000000000000 : ℝ) ≤
      (-(130572130440057185229 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (115439142792856383 / 160000000000000000 : ℝ) ≤
      (-(130572130440057185229 / 400000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (115439142792856383 / 160000000000000000 : ℝ) =
            (115439142792856383 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (115439142792856383 / 80000000000000000 : ℝ) ≤
            (146686741679942814771 / 400000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7196973279282751 / 10000000000000000 : ℝ)) (q :=
      (115439142792856383 / 160000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7])
      (by norm_num [bρ_7]) (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_667_8 :
    Uω (aρ 8) (bρ 8) (101836387367287 / 128000000000000 : ℝ) ≤
      (-(1845986741144000437987 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (22121247108923667 / 32000000000000000 : ℝ) ≤
      (-(1845986741144000437987 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (22121247108923667 / 32000000000000000 : ℝ) =
            (22121247108923667 / 16000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (22121247108923667 / 16000000000000000 : ℝ) ≤
            (1619749160355999562013 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1375280304918599 / 2000000000000000 : ℝ)) (q :=
      (22121247108923667 / 32000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_667_9 :
    Uω (aρ 9) (bρ 9) (101836387367287 / 128000000000000 : ℝ) ≤
      (-(2123883406626890648073 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (20925305608484907 / 32000000000000000 : ℝ) ≤
      (-(2123883406626890648073 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (20925305608484907 / 32000000000000000 : ℝ) =
            (20925305608484907 / 16000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (20925305608484907 / 16000000000000000 : ℝ) ≤
            (1341852494873109351927 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (646990371517877 / 1000000000000000 : ℝ)) (q :=
      (20925305608484907 / 32000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_667_10 :
    Uω (aρ 10) (bρ 10) (101836387367287 / 128000000000000 : ℝ) ≤
      (-(618599601174517764213 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (19508616145571099 / 32000000000000000 : ℝ) ≤
      (-(618599601174517764213 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (19508616145571099 / 32000000000000000 : ℝ) =
            (19508616145571099 / 16000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (19508616145571099 / 16000000000000000 : ℝ) ≤
            (247834374200482235787 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1166607780147 / 1953125000000 : ℝ)) (q :=
      (19508616145571099 / 32000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_667_11 :
    Uω (aρ 11) (bρ 11) (101836387367287 / 128000000000000 : ℝ) ≤
      (-(1452168150311807516473 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (89506079902867479 / 160000000000000000 : ℝ) ≤
      (-(1452168150311807516473 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (89506079902867479 / 160000000000000000 : ℝ) =
            (89506079902867479 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (89506079902867479 / 80000000000000000 : ℝ) ≤
            (280699800438192483527 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2693441678717069 / 5000000000000000 : ℝ)) (q :=
      (89506079902867479 / 160000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_667_12 :
    Uω (aρ 12) (bρ 12) (101836387367287 / 128000000000000 : ℝ) ≤
      (-(6834438478415439925663 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (80780044994235911 / 160000000000000000 : ℝ) ≤
      (-(6834438478415439925663 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (80780044994235911 / 160000000000000000 : ℝ) =
            (80780044994235911 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 3
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (80780044994235911 / 80000000000000000 : ℝ) ≤
            (97033324584560074337 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (147494659079381 / 312500000000000 : ℝ)) (q :=
      (80780044994235911 / 160000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_667_13 :
    Uω (aρ 13) (bρ 13) (101836387367287 / 128000000000000 : ℝ) ≤
      (-(802010272264151745109 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14349651124315259 / 32000000000000000 : ℝ) ≤
      (-(802010272264151745109 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (14349651124315259 / 32000000000000000 : ℝ) =
            (14349651124315259 / 8000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14349651124315259 / 8000000000000000 : ℝ) ≤
            (584284088335848254891 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (199511858027637 / 500000000000000 : ℝ)) (q :=
      (14349651124315259 / 32000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_667_14 :
    Uω (aρ 14) (bρ 14) (101836387367287 / 128000000000000 : ℝ) ≤
      (-(4665312136517286567177 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12587112524091627 / 32000000000000000 : ℝ) ≤
      (-(4665312136517286567177 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (12587112524091627 / 32000000000000000 : ℝ) =
            (12587112524091627 / 8000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (12587112524091627 / 8000000000000000 : ℝ) ≤
            (2266159666482713432823 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (323257782045797 / 1000000000000000 : ℝ)) (q :=
      (12587112524091627 / 32000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_667_15 :
    Uω (aρ 15) (bρ 15) (101836387367287 / 128000000000000 : ℝ) ≤
      (-(10658612229026117417291 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (55108975179349567 / 160000000000000000 : ℝ) ≤
      (-(10658612229026117417291 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (55108975179349567 / 160000000000000000 : ℝ) =
            (55108975179349567 / 40000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (55108975179349567 / 40000000000000000 : ℝ) ≤
            (3204331376973882582709 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2513827667734399 / 10000000000000000 : ℝ)) (q :=
      (55108975179349567 / 160000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_667_16 :
    Uω (aρ 16) (bρ 16) (101836387367287 / 128000000000000 : ℝ) ≤
      (-(5859174174619187689721 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (49567678580104111 / 160000000000000000 : ℝ) ≤
      (-(5859174174619187689721 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (49567678580104111 / 160000000000000000 : ℝ) =
            (49567678580104111 / 40000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (49567678580104111 / 40000000000000000 : ℝ) ≤
            (1072297628380812310279 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1973537244338717 / 10000000000000000 : ℝ)) (q :=
      (49567678580104111 / 160000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_667 :
    Uρ (101836387367287 / 128000000000000 : ℝ) ≤
      (-(1097916055907063284131 / 2500000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (101836387367287 / 128000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(1184025952061820073691 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_667_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (101836387367287 / 128000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(149897666808250901199 / 625000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_667_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (101836387367287 / 128000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(2459219715338930544141 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_667_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (101836387367287 / 128000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(2560991557050394938723 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_667_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (101836387367287 / 128000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(1358829098960116310293 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_667_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (101836387367287 / 128000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(2945935381077970403423 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_667_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (101836387367287 / 128000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(130572130440057185229 / 400000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_667_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (101836387367287 / 128000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(1845986741144000437987 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_667_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (101836387367287 / 128000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(2123883406626890648073 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_667_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) *
        Uω (aρ 10) (bρ 10) (101836387367287 / 128000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(618599601174517764213 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_667_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) *
        Uω (aρ 11) (bρ 11) (101836387367287 / 128000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(1452168150311807516473 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_667_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) *
        Uω (aρ 12) (bρ 12) (101836387367287 / 128000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(6834438478415439925663 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_667_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) *
        Uω (aρ 13) (bρ 13) (101836387367287 / 128000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(802010272264151745109 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_667_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) *
        Uω (aρ 14) (bρ 14) (101836387367287 / 128000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(4665312136517286567177 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_667_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) *
        Uω (aρ 15) (bρ 15) (101836387367287 / 128000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(10658612229026117417291 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_667_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) *
        Uω (aρ 16) (bρ 16) (101836387367287 / 128000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(5859174174619187689721 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_667_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_668_1 :
    Uω (aρ 1) (bρ 1) (40985227487781 / 51200000000000 : ℝ) ≤
      (-(28827527957205322453 / 125000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (254093109295304793 / 320000000000000000 : ℝ) ≤
      (-(28827527957205322453 / 125000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (254093109295304793 / 320000000000000000 : ℝ) =
            (254093109295304793 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (254093109295304793 / 160000000000000000 : ℝ) ≤
            (57815869580294677547 / 125000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7940389305334323 / 10000000000000000 : ℝ)) (q :=
      (254093109295304793 / 320000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1])
      (by norm_num [bρ_1]) (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_668_2 :
    Uω (aρ 2) (bρ 2) (40985227487781 / 51200000000000 : ℝ) ≤
      (-(46726498663784903531 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (253328863965426249 / 320000000000000000 : ℝ) ≤
      (-(46726498663784903531 / 200000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (253328863965426249 / 320000000000000000 : ℝ) =
            (253328863965426249 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (253328863965426249 / 160000000000000000 : ℝ) ≤
            (91902937396215096469 / 200000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3958196492363457 / 5000000000000000 : ℝ)) (q :=
      (253328863965426249 / 320000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2])
      (by norm_num [bρ_2]) (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_668_3 :
    Uω (aρ 3) (bρ 3) (40985227487781 / 51200000000000 : ℝ) ≤
      (-(2396801783767159707439 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (50360286828556901 / 64000000000000000 : ℝ) ≤
      (-(2396801783767159707439 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (50360286828556901 / 64000000000000000 : ℝ) =
            (50360286828556901 / 32000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (50360286828556901 / 32000000000000000 : ℝ) ≤
            (4534670019232840292561 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1573664945432361 / 2000000000000000 : ℝ)) (q :=
      (50360286828556901 / 64000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_668_4 :
    Uω (aρ 4) (bρ 4) (40985227487781 / 51200000000000 : ℝ) ≤
      (-(312241245281524448941 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (249267844562557577 / 320000000000000000 : ℝ) ≤
      (-(312241245281524448941 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (249267844562557577 / 320000000000000000 : ℝ) =
            (249267844562557577 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (249267844562557577 / 160000000000000000 : ℝ) ≤
            (554192730093475551059 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3894134779731311 / 5000000000000000 : ℝ)) (q :=
      (249267844562557577 / 320000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4])
      (by norm_num [bρ_4]) (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_668_5 :
    Uω (aρ 5) (bρ 5) (40985227487781 / 51200000000000 : ℝ) ≤
      (-(663396520318592504421 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (49083575860018021 / 64000000000000000 : ℝ) ≤
      (-(663396520318592504421 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (49083575860018021 / 64000000000000000 : ℝ) =
            (49083575860018021 / 32000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (49083575860018021 / 32000000000000000 : ℝ) ≤
            (1069471430431407495579 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1533167329978681 / 2000000000000000 : ℝ)) (q :=
      (49083575860018021 / 64000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_668_6 :
    Uω (aρ 6) (bρ 6) (40985227487781 / 51200000000000 : ℝ) ≤
      (-(115213863744958042733 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (47983078799087621 / 64000000000000000 : ℝ) ≤
      (-(115213863744958042733 / 400000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (47983078799087621 / 64000000000000000 : ℝ) =
            (47983078799087621 / 32000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (47983078799087621 / 32000000000000000 : ℝ) ≤
            (162045008375041957267 / 400000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1497834338698531 / 2000000000000000 : ℝ)) (q :=
      (47983078799087621 / 64000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_668_7 :
    Uω (aρ 7) (bρ 7) (40985227487781 / 51200000000000 : ℝ) ≤
      (-(3196506870553017259521 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (232448875024204217 / 320000000000000000 : ℝ) ≤
      (-(3196506870553017259521 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (232448875024204217 / 320000000000000000 : ℝ) =
            (232448875024204217 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (232448875024204217 / 160000000000000000 : ℝ) ≤
            (3734964932446982740479 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7246175638550537 / 10000000000000000 : ℝ)) (q :=
      (232448875024204217 / 320000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7])
      (by norm_num [bρ_7]) (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_668_8 :
    Uω (aρ 8) (bρ 8) (40985227487781 / 51200000000000 : ℝ) ≤
      (-(3621029128780322054959 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (222787428776145417 / 320000000000000000 : ℝ) ≤
      (-(3621029128780322054959 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (222787428776145417 / 320000000000000000 : ℝ) =
            (222787428776145417 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (222787428776145417 / 160000000000000000 : ℝ) ≤
            (3310442674219677945041 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3462938449693431 / 5000000000000000 : ℝ)) (q :=
      (222787428776145417 / 320000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8])
      (by norm_num [bρ_8]) (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_668_9 :
    Uω (aρ 9) (bρ 9) (40985227487781 / 51200000000000 : ℝ) ≤
      (-(2086192537048560607821 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (210836402285843529 / 320000000000000000 : ℝ) ≤
      (-(2086192537048560607821 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (210836402285843529 / 320000000000000000 : ℝ) =
            (210836402285843529 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (210836402285843529 / 160000000000000000 : ℝ) ≤
            (1379543364451439392179 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3259951686051497 / 5000000000000000 : ℝ)) (q :=
      (210836402285843529 / 320000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9])
      (by norm_num [bρ_9]) (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_668_10 :
    Uω (aρ 10) (bρ 10) (40985227487781 / 51200000000000 : ℝ) ≤
      (-(4867177017714833062951 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (39336993294475941 / 64000000000000000 : ℝ) ≤
      (-(4867177017714833062951 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (39336993294475941 / 64000000000000000 : ℝ) =
            (39336993294475941 / 32000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (39336993294475941 / 32000000000000000 : ℝ) ≤
            (2064294785285166937049 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1204799533451301 / 2000000000000000 : ℝ)) (q :=
      (39336993294475941 / 64000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_668_11 :
    Uω (aρ 11) (bρ 11) (40985227487781 / 51200000000000 : ℝ) ≤
      (-(571822785259138887833 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (180638574733142217 / 320000000000000000 : ℝ) ≤
      (-(571822785259138887833 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (180638574733142217 / 320000000000000000 : ℝ) =
            (180638574733142217 / 160000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (180638574733142217 / 160000000000000000 : ℝ) ≤
            (121324395040861112167 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2719787404879581 / 5000000000000000 : ℝ)) (q :=
      (180638574733142217 / 320000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_668_12 :
    Uω (aρ 12) (bρ 12) (40985227487781 / 51200000000000 : ℝ) ≤
      (-(420707167491835697151 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6529391167203393 / 12800000000000000 : ℝ) ≤
      (-(420707167491835697151 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (6529391167203393 / 12800000000000000 : ℝ) =
            (6529391167203393 / 6400000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (6529391167203393 / 6400000000000000 : ℝ) ≤
            (12509820195664302849 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (191021507375123 / 400000000000000 : ℝ)) (q :=
      (6529391167203393 / 12800000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_668_13 :
    Uω (aρ 13) (bρ 13) (40985227487781 / 51200000000000 : ℝ) ≤
      (-(1579666510826825980323 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (145254552806008569 / 320000000000000000 : ℝ) ≤
      (-(1579666510826825980323 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (145254552806008569 / 320000000000000000 : ℝ) =
            (145254552806008569 / 80000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (145254552806008569 / 80000000000000000 : ℝ) ≤
            (1192922210373174019677 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4051155277593309 / 10000000000000000 : ℝ)) (q :=
      (145254552806008569 / 320000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_668_14 :
    Uω (aρ 14) (bρ 14) (40985227487781 / 51200000000000 : ℝ) ≤
      (-(1836156577461968690781 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (127771397037108601 / 320000000000000000 : ℝ) ≤
      (-(1836156577461968690781 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (127771397037108601 / 320000000000000000 : ℝ) =
            (127771397037108601 / 80000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (127771397037108601 / 80000000000000000 : ℝ) ≤
            (936432143738031309219 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3302385327082061 / 10000000000000000 : ℝ)) (q :=
      (127771397037108601 / 320000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_668_15 :
    Uω (aρ 15) (bρ 15) (40985227487781 / 51200000000000 : ℝ) ≤
      (-(5233528120475439557461 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (112349592456445801 / 320000000000000000 : ℝ) ≤
      (-(5233528120475439557461 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (112349592456445801 / 320000000000000000 : ℝ) =
            (112349592456445801 / 80000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (112349592456445801 / 80000000000000000 : ℝ) ≤
            (1697943682524560442539 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (649523954551409 / 2500000000000000 : ℝ)) (q :=
      (112349592456445801 / 320000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_668_16 :
    Uω (aρ 16) (bρ 16) (40985227487781 / 51200000000000 : ℝ) ≤
      (-(11476547035735173474157 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (101561679294659737 / 320000000000000000 : ℝ) ≤
      (-(11476547035735173474157 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (101561679294659737 / 320000000000000000 : ℝ) =
            (101561679294659737 / 80000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (101561679294659737 / 80000000000000000 : ℝ) ≤
            (2386396570264826525843 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2076222897104007 / 10000000000000000 : ℝ)) (q :=
      (101561679294659737 / 320000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_668 :
    Uρ (40985227487781 / 51200000000000 : ℝ) ≤
      (-(431209322955317224327 / 1000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (40985227487781 / 51200000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(28827527957205322453 / 125000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_668_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (40985227487781 / 51200000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) * (-(46726498663784903531 / 200000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_668_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (40985227487781 / 51200000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(2396801783767159707439 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_668_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (40985227487781 / 51200000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(312241245281524448941 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_668_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (40985227487781 / 51200000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) * (-(663396520318592504421 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_668_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (40985227487781 / 51200000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(115213863744958042733 / 400000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_668_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (40985227487781 / 51200000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(3196506870553017259521 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_668_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (40985227487781 / 51200000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(3621029128780322054959 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_668_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (40985227487781 / 51200000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(2086192537048560607821 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_668_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (40985227487781 / 51200000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(4867177017714833062951 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_668_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (40985227487781 / 51200000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(571822785259138887833 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_668_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (40985227487781 / 51200000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) * (-(420707167491835697151 / 625000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_668_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (40985227487781 / 51200000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(1579666510826825980323 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_668_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (40985227487781 / 51200000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(1836156577461968690781 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_668_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (40985227487781 / 51200000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(5233528120475439557461 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_668_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (40985227487781 / 51200000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(11476547035735173474157 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_668_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_669_1 :
    Uω (aρ 1) (bρ 1) (51544875035809 / 64000000000000 : ℝ) ≤
      (-(2244732758859609584141 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (63914954167080633 / 80000000000000000 : ℝ) ≤
      (-(2244732758859609584141 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (63914954167080633 / 80000000000000000 : ℝ) =
            (63914954167080633 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (63914954167080633 / 40000000000000000 : ℝ) ≤
            (4686739044140390415859 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3994674517755001 / 5000000000000000 : ℝ)) (q :=
      (63914954167080633 / 80000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_669_2 :
    Uω (aρ 2) (bρ 2) (51544875035809 / 64000000000000 : ℝ) ≤
      (-(227466970668141009613 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (63723898426264653 / 80000000000000000 : ℝ) ≤
      (-(227466970668141009613 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (63723898426264653 / 80000000000000000 : ℝ) =
            (63723898426264653 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (63723898426264653 / 40000000000000000 : ℝ) ≤
            (465680209631858990387 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7965354112816007 / 10000000000000000 : ℝ)) (q :=
      (63723898426264653 / 80000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_669_3 :
    Uω (aρ 3) (bρ 3) (51544875035809 / 64000000000000 : ℝ) ≤
      (-(2334771082517334658739 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (63342057636596289 / 80000000000000000 : ℝ) ≤
      (-(2334771082517334658739 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (63342057636596289 / 80000000000000000 : ℝ) =
            (63342057636596289 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (63342057636596289 / 40000000000000000 : ℝ) ≤
            (4596700720482665341261 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1979322505437229 / 2500000000000000 : ℝ)) (q :=
      (63342057636596289 / 80000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_669_4 :
    Uω (aρ 4) (bρ 4) (51544875035809 / 64000000000000 : ℝ) ≤
      (-(304407961166478728341 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (62708704482840553 / 80000000000000000 : ℝ) ≤
      (-(304407961166478728341 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (62708704482840553 / 80000000000000000 : ℝ) =
            (62708704482840553 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (62708704482840553 / 40000000000000000 : ℝ) ≤
            (562026014208521271659 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3918622957187491 / 5000000000000000 : ℝ)) (q :=
      (62708704482840553 / 80000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_669_5 :
    Uω (aρ 5) (bρ 5) (51544875035809 / 64000000000000 : ℝ) ≤
      (-(647480560805871238739 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2469852877802989 / 3200000000000000 : ℝ) ≤
      (-(647480560805871238739 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (2469852877802989 / 3200000000000000 : ℝ) =
            (2469852877802989 / 1600000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2469852877802989 / 1600000000000000 : ℝ) ≤
            (1085387389944128761261 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (308593607970741 / 400000000000000 : ℝ)) (q :=
      (2469852877802989 / 3200000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_669_6 :
    Uω (aρ 6) (bρ 6) (51544875035809 / 64000000000000 : ℝ) ≤
      (-(87974566296101048461 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12074189918970493 / 16000000000000000 : ℝ) ≤
      (-(87974566296101048461 / 312500000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (12074189918970493 / 16000000000000000 : ℝ) =
            (12074189918970493 / 8000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (12074189918970493 / 8000000000000000 : ℝ) ≤
            (128633927547648951539 / 312500000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (47113984292831 / 62500000000000 : ℝ)) (q :=
      (12074189918970493 / 16000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_669_7 :
    Uω (aρ 7) (bρ 7) (51544875035809 / 64000000000000 : ℝ) ≤
      (-(391146157008232414821 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (58504853043606353 / 80000000000000000 : ℝ) ≤
      (-(391146157008232414821 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (58504853043606353 / 80000000000000000 : ℝ) =
            (58504853043606353 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (58504853043606353 / 40000000000000000 : ℝ) ≤
            (475287818366767585179 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (911921841225179 / 1250000000000000 : ℝ)) (q :=
      (58504853043606353 / 80000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_669_8 :
    Uω (aρ 8) (bρ 8) (51544875035809 / 64000000000000 : ℝ) ≤
      (-(355058973366974848083 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (56090567494944313 / 80000000000000000 : ℝ) ≤
      (-(355058973366974848083 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (56090567494944313 / 80000000000000000 : ℝ) =
            (56090567494944313 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (56090567494944313 / 40000000000000000 : ℝ) ≤
            (338088206933025151917 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3487672496987961 / 5000000000000000 : ℝ)) (q :=
      (56090567494944313 / 80000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_669_9 :
    Uω (aρ 9) (bρ 9) (51544875035809 / 64000000000000 : ℝ) ≤
      (-(1024394782019966389091 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (53104874451030497 / 80000000000000000 : ℝ) ≤
      (-(1024394782019966389091 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (53104874451030497 / 80000000000000000 : ℝ) =
            (53104874451030497 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (53104874451030497 / 40000000000000000 : ℝ) ≤
            (708473168730033610909 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1642471840339367 / 2500000000000000 : ℝ)) (q :=
      (53104874451030497 / 80000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_669_10 :
    Uω (aρ 10) (bρ 10) (51544875035809 / 64000000000000 : ℝ) ≤
      (-(11965611613780661111 / 25000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (49570810864276341 / 80000000000000000 : ℝ) ≤
      (-(11965611613780661111 / 25000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (49570810864276341 / 80000000000000000 : ℝ) =
            (49570810864276341 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (49570810864276341 / 40000000000000000 : ℝ) ≤
            (5363067893719338889 / 25000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6074930498163929 / 10000000000000000 : ℝ)) (q :=
      (49570810864276341 / 80000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_669_11 :
    Uω (aρ 11) (bρ 11) (51544875035809 / 64000000000000 : ℝ) ≤
      (-(5628654436701494422077 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (45565971127884609 / 80000000000000000 : ℝ) ≤
      (-(5628654436701494422077 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (45565971127884609 / 80000000000000000 : ℝ) =
            (45565971127884609 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (45565971127884609 / 40000000000000000 : ℝ) ≤
            (1302817366298505577923 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1373049297567749 / 2500000000000000 : ℝ)) (q :=
      (45565971127884609 / 80000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_669_12 :
    Uω (aρ 12) (bρ 12) (51544875035809 / 64000000000000 : ℝ) ≤
      (-(6629385355911510922651 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1649071288432777 / 3200000000000000 : ℝ) ≤
      (-(6629385355911510922651 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (1649071288432777 / 3200000000000000 : ℝ) =
            (1649071288432777 / 1600000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1649071288432777 / 1600000000000000 : ℝ) ≤
            (302086447088489077349 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (48311000576897 / 100000000000000 : ℝ)) (q :=
      (1649071288432777 / 3200000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_669_13 :
    Uω (aρ 13) (bρ 13) (51544875035809 / 64000000000000 : ℝ) ≤
      (-(972296894257070220027 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (36751870368632741 / 80000000000000000 : ℝ) ≤
      (-(972296894257070220027 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (36751870368632741 / 80000000000000000 : ℝ) =
            (36751870368632741 / 20000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (36751870368632741 / 20000000000000000 : ℝ) ≤
            (760571056492929779973 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4111753838738029 / 10000000000000000 : ℝ)) (q :=
      (36751870368632741 / 80000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_669_14 :
    Uω (aρ 14) (bρ 14) (51544875035809 / 64000000000000 : ℝ) ≤
      (-(9034059768671761378607 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6482995971853097 / 16000000000000000 : ℝ) ≤
      (-(9034059768671761378607 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (6482995971853097 / 16000000000000000 : ℝ) =
            (6482995971853097 / 4000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (6482995971853097 / 4000000000000000 : ℝ) ≤
            (4828883837328238621393 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (674291699288243 / 2000000000000000 : ℝ)) (q :=
      (6482995971853097 / 16000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_669_15 :
    Uω (aρ 15) (bρ 15) (51544875035809 / 64000000000000 : ℝ) ≤
      (-(10281552864863602885801 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28613291501051061 / 80000000000000000 : ℝ) ≤
      (-(10281552864863602885801 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (28613291501051061 / 80000000000000000 : ℝ) =
            (28613291501051061 / 20000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (28613291501051061 / 20000000000000000 : ℝ) ≤
            (3581390741136397114199 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2680609684302609 / 10000000000000000 : ℝ)) (q :=
      (28613291501051061 / 80000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_669_16 :
    Uω (aρ 16) (bρ 16) (51544875035809 / 64000000000000 : ℝ) ≤
      (-(5623107287608835128659 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25982030816194973 / 80000000000000000 : ℝ) ≤
      (-(5623107287608835128659 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (25982030816194973 / 80000000000000000 : ℝ) =
            (25982030816194973 / 20000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (25982030816194973 / 20000000000000000 : ℝ) ≤
            (1308364515391164871341 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2175166164598587 / 10000000000000000 : ℝ)) (q :=
      (25982030816194973 / 80000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_669 :
    Uρ (51544875035809 / 64000000000000 : ℝ) ≤
      (-(4233482968561500353719 / 10000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (51544875035809 / 64000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(2244732758859609584141 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_669_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (51544875035809 / 64000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(227466970668141009613 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_669_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (51544875035809 / 64000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(2334771082517334658739 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_669_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (51544875035809 / 64000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(304407961166478728341 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_669_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (51544875035809 / 64000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) * (-(647480560805871238739 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_669_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (51544875035809 / 64000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) * (-(87974566296101048461 / 312500000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_669_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (51544875035809 / 64000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(391146157008232414821 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_669_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (51544875035809 / 64000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(355058973366974848083 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_669_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (51544875035809 / 64000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(1024394782019966389091 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_669_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (51544875035809 / 64000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) * (-(11965611613780661111 / 25000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_669_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (51544875035809 / 64000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(5628654436701494422077 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_669_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (51544875035809 / 64000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(6629385355911510922651 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_669_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (51544875035809 / 64000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(972296894257070220027 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_669_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (51544875035809 / 64000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(9034059768671761378607 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_669_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (51544875035809 / 64000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(10281552864863602885801 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_669_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (51544875035809 / 64000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(5623107287608835128659 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_669_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_670_1 :
    Uω (aρ 1) (bρ 1) (104343112775949 / 128000000000000 : ℝ) ≤
      (-(2122915875407152198241 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (129396615634666397 / 160000000000000000 : ℝ) ≤
      (-(2122915875407152198241 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (129396615634666397 / 160000000000000000 : ℝ) =
            (129396615634666397 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (129396615634666397 / 80000000000000000 : ℝ) ≤
            (4808555927592847801759 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2021817121699321 / 2500000000000000 : ℝ)) (q :=
      (129396615634666397 / 160000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1])
      (by norm_num [bρ_1]) (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_670_2 :
    Uω (aρ 2) (bρ 2) (104343112775949 / 128000000000000 : ℝ) ≤
      (-(2152488114323455304571 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (129014526112001253 / 160000000000000000 : ℝ) ≤
      (-(2152488114323455304571 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (129014526112001253 / 160000000000000000 : ℝ) =
            (129014526112001253 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (129014526112001253 / 80000000000000000 : ℝ) ≤
            (4778983688676544695429 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (8063276308974141 / 10000000000000000 : ℝ)) (q :=
      (129014526112001253 / 160000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2])
      (by norm_num [bρ_2]) (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_670_3 :
    Uω (aρ 3) (bρ 3) (104343112775949 / 128000000000000 : ℝ) ≤
      (-(2211852356495572801771 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (128250909972047621 / 160000000000000000 : ℝ) ≤
      (-(2211852356495572801771 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (128250909972047621 / 160000000000000000 : ℝ) =
            (128250909972047621 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (128250909972047621 / 80000000000000000 : ℝ) ≤
            (4719619446504427198229 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (8015220397829937 / 10000000000000000 : ℝ)) (q :=
      (128250909972047621 / 160000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3])
      (by norm_num [bρ_3]) (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_670_4 :
    Uω (aρ 4) (bρ 4) (104343112775949 / 128000000000000 : ℝ) ≤
      (-(23110974918272984411 / 100000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (126984377336210149 / 160000000000000000 : ℝ) ≤
      (-(23110974918272984411 / 100000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (126984377336210149 / 160000000000000000 : ℝ) =
            (126984377336210149 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (126984377336210149 / 80000000000000000 : ℝ) ≤
            (46203743111727015589 / 100000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7935197999415253 / 10000000000000000 : ℝ)) (q :=
      (126984377336210149 / 160000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4])
      (by norm_num [bρ_4]) (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_670_5 :
    Uω (aρ 5) (bρ 5) (104343112775949 / 128000000000000 : ℝ) ≤
      (-(2463798801145355917777 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (125060039108793597 / 160000000000000000 : ℝ) ≤
      (-(2463798801145355917777 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (125060039108793597 / 160000000000000000 : ℝ) =
            (125060039108793597 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (125060039108793597 / 80000000000000000 : ℝ) ≤
            (4467673001854644082223 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (488302852520199 / 625000000000000 : ℝ)) (q :=
      (125060039108793597 / 160000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5])
      (by norm_num [bρ_5]) (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_670_6 :
    Uω (aρ 6) (bρ 6) (104343112775949 / 128000000000000 : ℝ) ≤
      (-(671531988149197401087 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (122310270820928029 / 160000000000000000 : ℝ) ≤
      (-(671531988149197401087 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (122310270820928029 / 160000000000000000 : ℝ) =
            (122310270820928029 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (122310270820928029 / 80000000000000000 : ℝ) ≤
            (1061335962600802598913 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1909091244869997 / 2500000000000000 : ℝ)) (q :=
      (122310270820928029 / 160000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6])
      (by norm_num [bρ_6]) (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_670_7 :
    Uω (aρ 7) (bρ 7) (104343112775949 / 128000000000000 : ℝ) ≤
      (-(1497922846347504928719 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (118580166892592797 / 160000000000000000 : ℝ) ≤
      (-(1497922846347504928719 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (118580166892592797 / 160000000000000000 : ℝ) =
            (118580166892592797 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (118580166892592797 / 80000000000000000 : ℝ) ≤
            (1967813055152495071281 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1848440842299521 / 2500000000000000 : ℝ)) (q :=
      (118580166892592797 / 160000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7])
      (by norm_num [bρ_7]) (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_670_8 :
    Uω (aρ 8) (bρ 8) (104343112775949 / 128000000000000 : ℝ) ≤
      (-(426399641951322608969 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (113755806355612957 / 160000000000000000 : ℝ) ≤
      (-(426399641951322608969 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (113755806355612957 / 160000000000000000 : ℝ) =
            (113755806355612957 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (113755806355612957 / 80000000000000000 : ℝ) ≤
            (440034333423677391031 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1768564988353901 / 2500000000000000 : ℝ)) (q :=
      (113755806355612957 / 160000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8])
      (by norm_num [bρ_8]) (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_670_9 :
    Uω (aρ 9) (bρ 9) (104343112775949 / 128000000000000 : ℝ) ≤
      (-(3949659208324676186013 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (107792479667179109 / 160000000000000000 : ℝ) ≤
      (-(3949659208324676186013 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (107792479667179109 / 160000000000000000 : ℝ) =
            (107792479667179109 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (107792479667179109 / 80000000000000000 : ℝ) ≤
            (2981812594675323813987 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6669809745721373 / 10000000000000000 : ℝ)) (q :=
      (107792479667179109 / 160000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9])
      (by norm_num [bρ_9]) (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_670_10 :
    Uω (aρ 10) (bρ 10) (104343112775949 / 128000000000000 : ℝ) ≤
      (-(4626394831317498006823 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (100739132785923661 / 160000000000000000 : ℝ) ≤
      (-(4626394831317498006823 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (100739132785923661 / 160000000000000000 : ℝ) =
            (100739132785923661 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (100739132785923661 / 80000000000000000 : ℝ) ≤
            (2305076971682501993177 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3088350209529721 / 5000000000000000 : ℝ)) (q :=
      (100739132785923661 / 160000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_670_11 :
    Uω (aρ 11) (bρ 11) (104343112775949 / 128000000000000 : ℝ) ≤
      (-(2726025637081969480721 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (92755656630473309 / 160000000000000000 : ℝ) ≤
      (-(2726025637081969480721 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (92755656630473309 / 160000000000000000 : ℝ) =
            (92755656630473309 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (92755656630473309 / 80000000000000000 : ℝ) ≤
            (739710264418030519279 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1399310631458287 / 2500000000000000 : ℝ)) (q :=
      (92755656630473309 / 160000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_670_12 :
    Uω (aρ 12) (bρ 12) (104343112775949 / 128000000000000 : ℝ) ≤
      (-(1607247505027276502399 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (84122562513276669 / 160000000000000000 : ℝ) ≤
      (-(1607247505027276502399 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (84122562513276669 / 160000000000000000 : ℝ) =
            (84122562513276669 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (84122562513276669 / 80000000000000000 : ℝ) ≤
            (125620445722723497601 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (617725732233571 / 1250000000000000 : ℝ)) (q :=
      (84122562513276669 / 160000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_670_13 :
    Uω (aρ 13) (bρ 13) (104343112775949 / 128000000000000 : ℝ) ≤
      (-(7543653695001394939451 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (75249438756350077 / 160000000000000000 : ℝ) ≤
      (-(7543653695001394939451 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (75249438756350077 / 160000000000000000 : ℝ) =
            (75249438756350077 / 40000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (75249438756350077 / 40000000000000000 : ℝ) ≤
            (6319289910998605060549 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (66125736403871 / 156250000000000 : ℝ)) (q :=
      (75249438756350077 / 160000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_670_14 :
    Uω (aρ 14) (bρ 14) (104343112775949 / 128000000000000 : ℝ) ≤
      (-(8749352398163579758549 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2668089704939989 / 6400000000000000 : ℝ) ≤
      (-(8749352398163579758549 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (2668089704939989 / 6400000000000000 : ℝ) =
            (2668089704939989 / 1600000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2668089704939989 / 1600000000000000 : ℝ) ≤
            (5113591207836420241451 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (70151497965729 / 200000000000000 : ℝ)) (q :=
      (2668089704939989 / 6400000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_670_15 :
    Uω (aρ 15) (bρ 15) (104343112775949 / 128000000000000 : ℝ) ≤
      (-(2481709788466278231419 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (59292919606829613 / 160000000000000000 : ℝ) ≤
      (-(2481709788466278231419 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (59292919606829613 / 160000000000000000 : ℝ) =
            (59292919606829613 / 40000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (59292919606829613 / 40000000000000000 : ℝ) ≤
            (984026113033721768581 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1420491399308843 / 5000000000000000 : ℝ)) (q :=
      (59292919606829613 / 160000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_670_16 :
    Uω (aρ 16) (bρ 16) (104343112775949 / 128000000000000 : ℝ) ≤
      (-(1081467769326687780553 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (54255590911517429 / 160000000000000000 : ℝ) ≤
      (-(1081467769326687780553 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (54255590911517429 / 160000000000000000 : ℝ) =
            (54255590911517429 / 40000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (54255590911517429 / 40000000000000000 : ℝ) ≤
            (304826591273312219447 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2363688363213663 / 10000000000000000 : ℝ)) (q :=
      (54255590911517429 / 160000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_670 :
    Uρ (104343112775949 / 128000000000000 : ℝ) ≤
      (-(32631863470159351417 / 80000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (104343112775949 / 128000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(2122915875407152198241 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_670_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (104343112775949 / 128000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(2152488114323455304571 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_670_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (104343112775949 / 128000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(2211852356495572801771 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_670_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (104343112775949 / 128000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) * (-(23110974918272984411 / 100000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_670_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (104343112775949 / 128000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(2463798801145355917777 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_670_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (104343112775949 / 128000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(671531988149197401087 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_670_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (104343112775949 / 128000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(1497922846347504928719 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_670_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (104343112775949 / 128000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(426399641951322608969 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_670_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (104343112775949 / 128000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(3949659208324676186013 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_670_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) *
        Uω (aρ 10) (bρ 10) (104343112775949 / 128000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(4626394831317498006823 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_670_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) *
        Uω (aρ 11) (bρ 11) (104343112775949 / 128000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(2726025637081969480721 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_670_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) *
        Uω (aρ 12) (bρ 12) (104343112775949 / 128000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(1607247505027276502399 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_670_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) *
        Uω (aρ 13) (bρ 13) (104343112775949 / 128000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(7543653695001394939451 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_670_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) *
        Uω (aρ 14) (bρ 14) (104343112775949 / 128000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(8749352398163579758549 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_670_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) *
        Uω (aρ 15) (bρ 15) (104343112775949 / 128000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(2481709788466278231419 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_670_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) *
        Uω (aρ 16) (bρ 16) (104343112775949 / 128000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(1081467769326687780553 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_670_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_671_1 :
    Uω (aρ 1) (bρ 1) (2639911887007 / 3200000000000 : ℝ) ≤
      (-(500641273210134050889 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (16370415355172451 / 20000000000000000 : ℝ) ≤
      (-(500641273210134050889 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (16370415355172451 / 20000000000000000 : ℝ) =
            (16370415355172451 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (16370415355172451 / 10000000000000000 : ℝ) ≤
            (1232226677539865949111 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (15986695168673 / 19531250000000 : ℝ)) (q :=
      (16370415355172451 / 20000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_671_2 :
    Uω (aρ 2) (bρ 2) (2639911887007 / 3200000000000 : ℝ) ≤
      (-(1015890701030451598891 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8161328421903959 / 10000000000000000 : ℝ) ≤
      (-(1015890701030451598891 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (8161328421903959 / 10000000000000000 : ℝ) =
            (8161328421903959 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (8161328421903959 / 5000000000000000 : ℝ) ≤
            (2449845200469548401109 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (8161198427506043 / 10000000000000000 : ℝ)) (q :=
      (8161328421903959 / 10000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_671_3 :
    Uω (aρ 3) (bρ 3) (2639911887007 / 3200000000000 : ℝ) ≤
      (-(1045213186822443644979 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8113606404156209 / 10000000000000000 : ℝ) ≤
      (-(1045213186822443644979 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (8113606404156209 / 10000000000000000 : ℝ) =
            (8113606404156209 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (8113606404156209 / 5000000000000000 : ℝ) ≤
            (2420522714677556355021 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (8113150498360543 / 10000000000000000 : ℝ)) (q :=
      (8113606404156209 / 10000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_671_4 :
    Uω (aρ 4) (bρ 4) (2639911887007 / 3200000000000 : ℝ) ≤
      (-(2188454632258100397817 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8034458702845387 / 10000000000000000 : ℝ) ≤
      (-(2188454632258100397817 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (8034458702845387 / 10000000000000000 : ℝ) =
            (8034458702845387 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (8034458702845387 / 5000000000000000 : ℝ) ≤
            (4743017170741899602183 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (8033149276803899 / 10000000000000000 : ℝ)) (q :=
      (8034458702845387 / 10000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_671_5 :
    Uω (aρ 5) (bρ 5) (2639911887007 / 3200000000000 : ℝ) ≤
      (-(2339247632052252958919 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (15457448387817 / 19531250000000 : ℝ) ≤
      (-(2339247632052252958919 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show (15457448387817 / 19531250000000 : ℝ) = (15457448387817 / 9765625000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (15457448387817 / 9765625000000 : ℝ) ≤
            (4592224170947747041081 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7910848939572733 / 10000000000000000 : ℝ)) (q :=
      (15457448387817 / 19531250000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_671_6 :
    Uω (aρ 6) (bρ 6) (2639911887007 / 3200000000000 : ℝ) ≤
      (-(127935879922268966083 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7742412510432781 / 10000000000000000 : ℝ) ≤
      (-(127935879922268966083 / 500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (7742412510432781 / 10000000000000000 : ℝ) =
            (7742412510432781 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7742412510432781 / 5000000000000000 : ℝ) ≤
            (218637710227731033917 / 500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7734487186453687 / 10000000000000000 : ℝ)) (q :=
      (7742412510432781 / 10000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_671_7 :
    Uω (aρ 7) (bρ 7) (2639911887007 / 3200000000000 : ℝ) ≤
      (-(143214223958901012311 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (15018816155841109 / 20000000000000000 : ℝ) ≤
      (-(143214223958901012311 / 500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (15018816155841109 / 20000000000000000 : ℝ) =
            (15018816155841109 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (15018816155841109 / 10000000000000000 : ℝ) ≤
            (203359366191098987689 / 500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3746069851094617 / 5000000000000000 : ℝ)) (q :=
      (15018816155841109 / 20000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_671_8 :
    Uω (aρ 8) (bρ 8) (2639911887007 / 3200000000000 : ℝ) ≤
      (-(3273739843396933459351 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1802035298080953 / 2500000000000000 : ℝ) ≤
      (-(3273739843396933459351 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (1802035298080953 / 2500000000000000 : ℝ) =
            (1802035298080953 / 1250000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1802035298080953 / 1250000000000000 : ℝ) ≤
            (3657731959603066540649 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7173147582335749 / 10000000000000000 : ℝ)) (q :=
      (1802035298080953 / 2500000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_671_9 :
    Uω (aρ 9) (bρ 9) (2639911887007 / 3200000000000 : ℝ) ≤
      (-(3803938287939391401999 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13671842754950423 / 20000000000000000 : ℝ) ≤
      (-(3803938287939391401999 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (13671842754950423 / 20000000000000000 : ℝ) =
            (13671842754950423 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (13671842754950423 / 10000000000000000 : ℝ) ≤
            (3127533515060608598001 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1692418395249637 / 2500000000000000 : ℝ)) (q :=
      (13671842754950423 / 20000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_671_10 :
    Uω (aρ 10) (bρ 10) (2639911887007 / 3200000000000 : ℝ) ≤
      (-(4469155812153975488917 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3197989499534529 / 5000000000000000 : ℝ) ≤
      (-(4469155812153975488917 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (3197989499534529 / 5000000000000000 : ℝ) =
            (3197989499534529 / 2500000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3197989499534529 / 2500000000000000 : ℝ) ≤
            (2462315990846024511083 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6278347857681241 / 10000000000000000 : ℝ)) (q :=
      (3197989499534529 / 5000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_671_11 :
    Uω (aρ 11) (bρ 11) (2639911887007 / 3200000000000 : ℝ) ≤
      (-(5278727945726234280523 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (11797167717509879 / 20000000000000000 : ℝ) ≤
      (-(5278727945726234280523 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (11797167717509879 / 20000000000000000 : ℝ) =
            (11797167717509879 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (11797167717509879 / 10000000000000000 : ℝ) ≤
            (1652743857273765719477 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1425508550814501 / 2500000000000000 : ℝ)) (q :=
      (11797167717509879 / 20000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_671_12 :
    Uω (aρ 12) (bρ 12) (2639911887007 / 3200000000000 : ℝ) ≤
      (-(1558256031449427925669 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10723417062856459 / 20000000000000000 : ℝ) ≤
      (-(1558256031449427925669 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (10723417062856459 / 20000000000000000 : ℝ) =
            (10723417062856459 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (10723417062856459 / 10000000000000000 : ℝ) ≤
            (174611919300572074331 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (315748977830599 / 625000000000000 : ℝ)) (q :=
      (10723417062856459 / 20000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_671_13 :
    Uω (aρ 13) (bρ 13) (2639911887007 / 3200000000000 : ℝ) ≤
      (-(7315481309970044122373 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (96232701758961 / 200000000000000 : ℝ) ≤
      (-(7315481309970044122373 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (96232701758961 / 200000000000000 : ℝ) = (96232701758961 / 50000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (96232701758961 / 50000000000000 : ℝ) ≤
            (6547462296029955877627 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (174048739996969 / 400000000000000 : ℝ)) (q :=
      (96232701758961 / 200000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13]) (by norm_num [bρ_13])
      (by norm_num) (by norm_num [aρ_13, bρ_13]) (by norm_num [aρ_13, bρ_13]) hlg

lemma U_671_14 :
    Uω (aρ 14) (bρ 14) (2639911887007 / 3200000000000 : ℝ) ≤
      (-(132427977383954035777 / 156250000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8569361431673801 / 20000000000000000 : ℝ) ≤
      (-(132427977383954035777 / 156250000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (8569361431673801 / 20000000000000000 : ℝ) =
            (8569361431673801 / 5000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (8569361431673801 / 5000000000000000 : ℝ) ≤
            (84180516459795964223 / 156250000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1820618520373463 / 5000000000000000 : ℝ)) (q :=
      (8569361431673801 / 20000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_671_15 :
    Uω (aρ 15) (bρ 15) (2639911887007 / 3200000000000 : ℝ) ≤
      (-(4795647034182452320199 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1532905499401413 / 4000000000000000 : ℝ) ≤
      (-(4795647034182452320199 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (1532905499401413 / 4000000000000000 : ℝ) =
            (1532905499401413 / 1000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1532905499401413 / 1000000000000000 : ℝ) ≤
            (2135824768817547679801 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (299597638349519 / 1000000000000000 : ℝ)) (q :=
      (1532905499401413 / 4000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_671_16 :
    Uω (aρ 16) (bρ 16) (2639911887007 / 3200000000000 : ℝ) ≤
      (-(10415420626330915702817 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1764550262759391 / 5000000000000000 : ℝ) ≤
      (-(10415420626330915702817 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (1764550262759391 / 5000000000000000 : ℝ) =
            (1764550262759391 / 1250000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1764550262759391 / 1250000000000000 : ℝ) ≤
            (3447522979669084297183 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2542021589035689 / 10000000000000000 : ℝ)) (q :=
      (1764550262759391 / 5000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_671 :
    Uρ (2639911887007 / 3200000000000 : ℝ) ≤
      (-(122746261948983473009 / 312500000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (2639911887007 / 3200000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(500641273210134050889 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_671_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (2639911887007 / 3200000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(1015890701030451598891 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_671_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (2639911887007 / 3200000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(1045213186822443644979 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_671_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (2639911887007 / 3200000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(2188454632258100397817 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_671_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (2639911887007 / 3200000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(2339247632052252958919 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_671_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (2639911887007 / 3200000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(127935879922268966083 / 500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_671_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (2639911887007 / 3200000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(143214223958901012311 / 500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_671_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (2639911887007 / 3200000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(3273739843396933459351 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_671_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (2639911887007 / 3200000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(3803938287939391401999 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_671_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (2639911887007 / 3200000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(4469155812153975488917 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_671_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (2639911887007 / 3200000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(5278727945726234280523 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_671_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (2639911887007 / 3200000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(1558256031449427925669 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_671_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (2639911887007 / 3200000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(7315481309970044122373 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_671_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (2639911887007 / 3200000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) * (-(132427977383954035777 / 156250000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_671_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (2639911887007 / 3200000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(4795647034182452320199 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_671_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (2639911887007 / 3200000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(10415420626330915702817 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_671_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_672_1 :
    Uω (aρ 1) (bρ 1) (106849838184611 / 128000000000000 : ℝ) ≤
      (-(235455692546499870873 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (132530029957627211 / 160000000000000000 : ℝ) ≤
      (-(235455692546499870873 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (132530029957627211 / 160000000000000000 : ℝ) =
            (132530029957627211 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (132530029957627211 / 80000000000000000 : ℝ) ≤
            (630978282828500129127 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (8283107354615667 / 10000000000000000 : ℝ)) (q :=
      (132530029957627211 / 160000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1])
      (by norm_num [bρ_1]) (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_672_2 :
    Uω (aρ 2) (bρ 2) (106849838184611 / 128000000000000 : ℝ) ≤
      (-(191251438587919057173 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (132147982790004099 / 160000000000000000 : ℝ) ≤
      (-(191251438587919057173 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (132147982790004099 / 160000000000000000 : ℝ) =
            (132147982790004099 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (132147982790004099 / 80000000000000000 : ℝ) ≤
            (501895741712080942827 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4129560235586389 / 5000000000000000 : ℝ)) (q :=
      (132147982790004099 / 160000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2])
      (by norm_num [bρ_2]) (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_672_3 :
    Uω (aρ 3) (bρ 3) (106849838184611 / 128000000000000 : ℝ) ≤
      (-(123153581774262376029 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (131384492835420723 / 160000000000000000 : ℝ) ≤
      (-(123153581774262376029 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (131384492835420723 / 160000000000000000 : ℝ) =
            (131384492835420723 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (131384492835420723 / 80000000000000000 : ℝ) ≤
            (310063405913237623971 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (513192520824991 / 625000000000000 : ℝ)) (q :=
      (131384492835420723 / 160000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3])
      (by norm_num [bρ_3]) (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_672_4 :
    Uω (aρ 4) (bρ 4) (106849838184611 / 128000000000000 : ℝ) ≤
      (-(413459634607695491819 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (130118294927134203 / 160000000000000000 : ℝ) ≤
      (-(413459634607695491819 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (130118294927134203 / 160000000000000000 : ℝ) =
            (130118294927134203 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (130118294927134203 / 80000000000000000 : ℝ) ≤
            (972834725992304508181 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (8131099775729041 / 10000000000000000 : ℝ)) (q :=
      (130118294927134203 / 160000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4])
      (by norm_num [bρ_4]) (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_672_5 :
    Uω (aρ 5) (bρ 5) (106849838184611 / 128000000000000 : ℝ) ≤
      (-(2216229985259282885979 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (128194778771775299 / 160000000000000000 : ℝ) ≤
      (-(2216229985259282885979 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (128194778771775299 / 160000000000000000 : ℝ) =
            (128194778771775299 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (128194778771775299 / 80000000000000000 : ℝ) ≤
            (4715241817740717114021 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4004425087822089 / 5000000000000000 : ℝ)) (q :=
      (128194778771775299 / 160000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5])
      (by norm_num [bρ_5]) (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_672_6 :
    Uω (aρ 6) (bρ 6) (106849838184611 / 128000000000000 : ℝ) ≤
      (-(486582685306763027307 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (125446888816866827 / 160000000000000000 : ℝ) ≤
      (-(486582685306763027307 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (125446888816866827 / 160000000000000000 : ℝ) =
            (125446888816866827 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (125446888816866827 / 80000000000000000 : ℝ) ≤
            (899711675293236972693 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7832604306420619 / 10000000000000000 : ℝ)) (q :=
      (125446888816866827 / 160000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6])
      (by norm_num [bρ_6]) (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_672_7 :
    Uω (aρ 7) (bρ 7) (106849838184611 / 128000000000000 : ℝ) ≤
      (-(341804927920539353553 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (121720796977537651 / 160000000000000000 : ℝ) ≤
      (-(341804927920539353553 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (121720796977537651 / 160000000000000000 : ℝ) =
            (121720796977537651 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (121720796977537651 / 80000000000000000 : ℝ) ≤
            (524629047454460646447 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (948813025908059 / 1250000000000000 : ℝ)) (q :=
      (121720796977537651 / 160000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7])
      (by norm_num [bρ_7]) (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_672_8 :
    Uω (aρ 8) (bρ 8) (106849838184611 / 128000000000000 : ℝ) ≤
      (-(3138164350541981558903 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (116904502074220267 / 160000000000000000 : ℝ) ≤
      (-(3138164350541981558903 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (116904502074220267 / 160000000000000000 : ℝ) =
            (116904502074220267 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (116904502074220267 / 80000000000000000 : ℝ) ≤
            (3793307452458018441097 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7272008995689799 / 10000000000000000 : ℝ)) (q :=
      (116904502074220267 / 160000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8])
      (by norm_num [bρ_8]) (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_672_9 :
    Uω (aρ 9) (bρ 9) (106849838184611 / 128000000000000 : ℝ) ≤
      (-(915087684084109970181 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (22191311289371623 / 32000000000000000 : ℝ) ≤
      (-(915087684084109970181 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (22191311289371623 / 32000000000000000 : ℝ) =
            (22191311289371623 / 16000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (22191311289371623 / 16000000000000000 : ℝ) ≤
            (817780266665890029819 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (686948142062953 / 1000000000000000 : ℝ)) (q :=
      (22191311289371623 / 32000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_672_10 :
    Uω (aρ 10) (bρ 10) (106849838184611 / 128000000000000 : ℝ) ≤
      (-(2157220375553611875821 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (103931262160899803 / 160000000000000000 : ℝ) ≤
      (-(2157220375553611875821 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (103931262160899803 / 160000000000000000 : ℝ) =
            (103931262160899803 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (103931262160899803 / 80000000000000000 : ℝ) ≤
            (1308515525946388124179 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6379878668379741 / 10000000000000000 : ℝ)) (q :=
      (103931262160899803 / 160000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_672_11 :
    Uω (aρ 11) (bρ 11) (106849838184611 / 128000000000000 : ℝ) ≤
      (-(2554278773373393057629 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (95997107451389363 / 160000000000000000 : ℝ) ≤
      (-(2554278773373393057629 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (95997107451389363 / 160000000000000000 : ℝ) =
            (95997107451389363 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (95997107451389363 / 80000000000000000 : ℝ) ≤
            (911457128126606942371 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (45363952780437 / 78125000000000 : ℝ)) (q :=
      (95997107451389363 / 160000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_672_12 :
    Uω (aρ 12) (bρ 12) (106849838184611 / 128000000000000 : ℝ) ≤
      (-(188789903102745975883 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (87448156886536459 / 160000000000000000 : ℝ) ≤
      (-(188789903102745975883 / 312500000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (87448156886536459 / 160000000000000000 : ℝ) =
            (87448156886536459 / 80000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (87448156886536459 / 80000000000000000 : ℝ) ≤
            (27818590741004024117 / 312500000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (5161667231974323 / 10000000000000000 : ℝ)) (q :=
      (87448156886536459 / 160000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_672_13 :
    Uω (aρ 13) (bρ 13) (106849838184611 / 128000000000000 : ℝ) ≤
      (-(1773362058072074792879 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (15742925331419543 / 32000000000000000 : ℝ) ≤
      (-(1773362058072074792879 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (15742925331419543 / 32000000000000000 : ℝ) =
            (15742925331419543 / 8000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (15742925331419543 / 8000000000000000 : ℝ) ≤
            (1692373843427925207121 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (111733942372237 / 250000000000000 : ℝ)) (q :=
      (15742925331419543 / 32000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_672_14 :
    Uω (aρ 14) (bρ 14) (106849838184611 / 128000000000000 : ℝ) ≤
      (-(8211227049645739158739 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (70389993110883323 / 160000000000000000 : ℝ) ≤
      (-(8211227049645739158739 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (70389993110883323 / 160000000000000000 : ℝ) =
            (70389993110883323 / 40000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (70389993110883323 / 40000000000000000 : ℝ) ≤
            (5651716556354260841261 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3772705786657681 / 10000000000000000 : ℝ)) (q :=
      (70389993110883323 / 160000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_672_15 :
    Uω (aρ 15) (bρ 15) (106849838184611 / 128000000000000 : ℝ) ≤
      (-(1854487086372971585059 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (63302844916412531 / 160000000000000000 : ℝ) ≤
      (-(1854487086372971585059 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (63302844916412531 / 160000000000000000 : ℝ) =
            (63302844916412531 / 40000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (63302844916412531 / 40000000000000000 : ℝ) ≤
            (918101634827028414941 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (393298192470479 / 1250000000000000 : ℝ)) (q :=
      (63302844916412531 / 160000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_672_16 :
    Uω (aρ 16) (bρ 16) (106849838184611 / 128000000000000 : ℝ) ≤
      (-(10042650893961810327003 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (58610198971289891 / 160000000000000000 : ℝ) ≤
      (-(10042650893961810327003 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (58610198971289891 / 160000000000000000 : ℝ) =
            (58610198971289891 / 40000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (58610198971289891 / 40000000000000000 : ℝ) ≤
            (3820292712038189672997 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1356088224066751 / 5000000000000000 : ℝ)) (q :=
      (58610198971289891 / 160000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_672 :
    Uρ (106849838184611 / 128000000000000 : ℝ) ≤
      (-(3779941234837194175711 / 10000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (106849838184611 / 128000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(235455692546499870873 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_672_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (106849838184611 / 128000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(191251438587919057173 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_672_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (106849838184611 / 128000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(123153581774262376029 / 625000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_672_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (106849838184611 / 128000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(413459634607695491819 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_672_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (106849838184611 / 128000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(2216229985259282885979 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_672_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (106849838184611 / 128000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(486582685306763027307 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_672_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (106849838184611 / 128000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(341804927920539353553 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_672_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (106849838184611 / 128000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(3138164350541981558903 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_672_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (106849838184611 / 128000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(915087684084109970181 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_672_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) *
        Uω (aρ 10) (bρ 10) (106849838184611 / 128000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(2157220375553611875821 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_672_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) *
        Uω (aρ 11) (bρ 11) (106849838184611 / 128000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(2554278773373393057629 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_672_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) *
        Uω (aρ 12) (bρ 12) (106849838184611 / 128000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) * (-(188789903102745975883 / 312500000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_672_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) *
        Uω (aρ 13) (bρ 13) (106849838184611 / 128000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(1773362058072074792879 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_672_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) *
        Uω (aρ 14) (bρ 14) (106849838184611 / 128000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(8211227049645739158739 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_672_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) *
        Uω (aρ 15) (bρ 15) (106849838184611 / 128000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(1854487086372971585059 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_672_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) *
        Uω (aρ 16) (bρ 16) (106849838184611 / 128000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(10042650893961810327003 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_672_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_673_1 :
    Uω (aρ 1) (bρ 1) (54051600444471 / 64000000000000 : ℝ) ≤
      (-(441530894174971766827 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (67048368493290031 / 80000000000000000 : ℝ) ≤
      (-(441530894174971766827 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (67048368493290031 / 80000000000000000 : ℝ) =
            (67048368493290031 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (67048368493290031 / 40000000000000000 : ℝ) ≤
            (1291337056575028233173 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4190513385979457 / 5000000000000000 : ℝ)) (q :=
      (67048368493290031 / 80000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_673_2 :
    Uω (aρ 2) (bρ 2) (54051600444471 / 64000000000000 : ℝ) ≤
      (-(358930625195043976947 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (66857355125838379 / 80000000000000000 : ℝ) ≤
      (-(358930625195043976947 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (66857355125838379 / 80000000000000000 : ℝ) =
            (66857355125838379 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (66857355125838379 / 40000000000000000 : ℝ) ≤
            (1027363735404956023053 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (8357042442606001 / 10000000000000000 : ℝ)) (q :=
      (66857355125838379 / 80000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_673_3 :
    Uω (aρ 3) (bρ 3) (54051600444471 / 64000000000000 : ℝ) ≤
      (-(1851910609720033326851 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (66475640576983063 / 80000000000000000 : ℝ) ≤
      (-(1851910609720033326851 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (66475640576983063 / 80000000000000000 : ℝ) =
            (66475640576983063 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (66475640576983063 / 40000000000000000 : ℝ) ≤
            (5079561193279966673149 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2077252477935543 / 2500000000000000 : ℝ)) (q :=
      (66475640576983063 / 80000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_673_4 :
    Uω (aρ 4) (bρ 4) (54051600444471 / 64000000000000 : ℝ) ≤
      (-(973796252202356616109 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (65842622301709847 / 80000000000000000 : ℝ) ≤
      (-(973796252202356616109 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (65842622301709847 / 80000000000000000 : ℝ) =
            (65842622301709847 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (65842622301709847 / 40000000000000000 : ℝ) ≤
            (2491939649297643383891 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2057262380997217 / 2500000000000000 : ℝ)) (q :=
      (65842622301709847 / 80000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_673_5 :
    Uω (aρ 5) (bρ 5) (54051600444471 / 64000000000000 : ℝ) ≤
      (-(1047354263203227591767 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12976212444371607 / 16000000000000000 : ℝ) ≤
      (-(1047354263203227591767 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (12976212444371607 / 16000000000000000 : ℝ) =
            (12976212444371607 / 8000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (12976212444371607 / 8000000000000000 : ℝ) ≤
            (2418381638296772408233 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1621369884672183 / 2000000000000000 : ℝ)) (q :=
      (12976212444371607 / 16000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_673_6 :
    Uω (aρ 6) (bρ 6) (54051600444471 / 64000000000000 : ℝ) ≤
      (-(2308675365543395899577 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (63507569140601767 / 80000000000000000 : ℝ) ≤
      (-(2308675365543395899577 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (63507569140601767 / 80000000000000000 : ℝ) =
            (63507569140601767 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (63507569140601767 / 40000000000000000 : ℝ) ≤
            (4622796437456604100423 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (247834891505839 / 312500000000000 : ℝ)) (q :=
      (63507569140601767 / 80000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_673_7 :
    Uω (aρ 7) (bρ 7) (54051600444471 / 64000000000000 : ℝ) ≤
      (-(2606266133502291094023 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12329097371660311 / 16000000000000000 : ℝ) ≤
      (-(2606266133502291094023 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (12329097371660311 / 16000000000000000 : ℝ) =
            (12329097371660311 / 8000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (12329097371660311 / 8000000000000000 : ℝ) ≤
            (4325205669497708905977 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1537771467674359 / 2000000000000000 : ℝ)) (q :=
      (12329097371660311 / 16000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_673_8 :
    Uω (aρ 8) (bρ 8) (54051600444471 / 64000000000000 : ℝ) ≤
      (-(375552419867593022027 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (59239271892758979 / 80000000000000000 : ℝ) ≤
      (-(375552419867593022027 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (59239271892758979 / 80000000000000000 : ℝ) =
            (59239271892758979 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (59239271892758979 / 40000000000000000 : ℝ) ≤
            (490881555507406977973 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7370845248326151 / 10000000000000000 : ℝ)) (q :=
      (59239271892758979 / 80000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_673_9 :
    Uω (aρ 9) (bρ 9) (54051600444471 / 64000000000000 : ℝ) ≤
      (-(3518833867664006306331 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (56268971067573579 / 80000000000000000 : ℝ) ≤
      (-(3518833867664006306331 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (56268971067573579 / 80000000000000000 : ℝ) =
            (56268971067573579 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (56268971067573579 / 40000000000000000 : ℝ) ≤
            (3412637935335993693669 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6969235670389801 / 10000000000000000 : ℝ)) (q :=
      (56268971067573579 / 80000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_673_10 :
    Uω (aρ 10) (bρ 10) (54051600444471 / 64000000000000 : ℝ) ≤
      (-(4162167202080293224863 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2110519423226207 / 3200000000000000 : ℝ) ≤
      (-(4162167202080293224863 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (2110519423226207 / 3200000000000000 : ℝ) =
            (2110519423226207 / 1600000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2110519423226207 / 1600000000000000 : ℝ) ≤
            (2769304600919706775137 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4050811457597 / 6250000000000 : ℝ)) (q :=
      (2110519423226207 / 3200000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_673_11 :
    Uω (aρ 11) (bρ 11) (54051600444471 / 64000000000000 : ℝ) ≤
      (-(4941420751005724572059 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (48807527807521887 / 80000000000000000 : ℝ) ≤
      (-(4941420751005724572059 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (48807527807521887 / 80000000000000000 : ℝ) =
            (48807527807521887 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (48807527807521887 / 40000000000000000 : ℝ) ≤
            (1990051051994275427941 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2955455257538439 / 5000000000000000 : ℝ)) (q :=
      (48807527807521887 / 80000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_673_12 :
    Uω (aρ 12) (bρ 12) (54051600444471 / 64000000000000 : ℝ) ≤
      (-(1463388324566729199727 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (44552635240304839 / 80000000000000000 : ℝ) ≤
      (-(1463388324566729199727 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (44552635240304839 / 80000000000000000 : ℝ) =
            (44552635240304839 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (44552635240304839 / 40000000000000000 : ℝ) ≤
            (269479626183270800273 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (329430466872351 / 625000000000000 : ℝ)) (q :=
      (44552635240304839 / 80000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_673_13 :
    Uω (aρ 13) (bρ 13) (54051600444471 / 64000000000000 : ℝ) ≤
      (-(687718534739097609481 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (40217736294292543 / 80000000000000000 : ℝ) ≤
      (-(687718534739097609481 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (40217736294292543 / 80000000000000000 : ℝ) =
            (40217736294292543 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 3
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (40217736294292543 / 40000000000000000 : ℝ) ≤
            (5428645560902390519 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2293272237524771 / 5000000000000000 : ℝ)) (q :=
      (40217736294292543 / 80000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_673_14 :
    Uω (aρ 14) (bρ 14) (54051600444471 / 64000000000000 : ℝ) ≤
      (-(994505843548616338199 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (288837284746911 / 640000000000000 : ℝ) ≤
      (-(994505843548616338199 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (288837284746911 / 640000000000000 : ℝ) =
            (288837284746911 / 160000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (288837284746911 / 160000000000000 : ℝ) ≤
            (738362107201383661801 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (31217622678899 / 80000000000000 : ℝ)) (q :=
      (288837284746911 / 640000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14]) (by norm_num [bρ_14])
      (by norm_num) (by norm_num [aρ_14, bρ_14]) (by norm_num [aρ_14, bρ_14]) hlg

lemma U_673_15 :
    Uω (aρ 15) (bρ 15) (54051600444471 / 64000000000000 : ℝ) ≤
      (-(8968279189791174831113 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (32628910325302671 / 80000000000000000 : ℝ) ≤
      (-(8968279189791174831113 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (32628910325302671 / 80000000000000000 : ℝ) =
            (32628910325302671 / 20000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (32628910325302671 / 20000000000000000 : ℝ) ≤
            (4894664416208825168887 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1646419272631037 / 5000000000000000 : ℝ)) (q :=
      (32628910325302671 / 80000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_673_16 :
    Uω (aρ 16) (bρ 16) (54051600444471 / 64000000000000 : ℝ) ≤
      (-(387685589835395029451 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6070097983094999 / 16000000000000000 : ℝ) ≤
      (-(387685589835395029451 / 400000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (6070097983094999 / 16000000000000000 : ℝ) =
            (6070097983094999 / 4000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (6070097983094999 / 4000000000000000 : ℝ) ≤
            (166832154404604970549 / 400000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (575121018863031 / 2000000000000000 : ℝ)) (q :=
      (6070097983094999 / 16000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_673 :
    Uρ (54051600444471 / 64000000000000 : ℝ) ≤
      (-(363496725301935166593 / 1000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (54051600444471 / 64000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(441530894174971766827 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_673_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (54051600444471 / 64000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(358930625195043976947 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_673_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (54051600444471 / 64000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(1851910609720033326851 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_673_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (54051600444471 / 64000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(973796252202356616109 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_673_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (54051600444471 / 64000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(1047354263203227591767 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_673_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (54051600444471 / 64000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(2308675365543395899577 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_673_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (54051600444471 / 64000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(2606266133502291094023 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_673_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (54051600444471 / 64000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(375552419867593022027 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_673_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (54051600444471 / 64000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(3518833867664006306331 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_673_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (54051600444471 / 64000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(4162167202080293224863 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_673_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (54051600444471 / 64000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(4941420751005724572059 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_673_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (54051600444471 / 64000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(1463388324566729199727 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_673_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (54051600444471 / 64000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(687718534739097609481 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_673_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (54051600444471 / 64000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(994505843548616338199 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_673_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (54051600444471 / 64000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(8968279189791174831113 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_673_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (54051600444471 / 64000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(387685589835395029451 / 400000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_673_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_674_1 :
    Uω (aρ 1) (bρ 1) (27652481574401 / 32000000000000 : ℝ) ≤
      (-(383785914618737645777 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (34307537698640223 / 40000000000000000 : ℝ) ≤
      (-(383785914618737645777 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (34307537698640223 / 40000000000000000 : ℝ) =
            (34307537698640223 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (34307537698640223 / 20000000000000000 : ℝ) ≤
            (1349082036131262354223 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (8576865575404799 / 10000000000000000 : ℝ)) (q :=
      (34307537698640223 / 40000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_674_2 :
    Uω (aρ 2) (bρ 2) (27652481574401 / 32000000000000 : ℝ) ≤
      (-(48844312258711844961 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (34212040880202477 / 40000000000000000 : ℝ) ≤
      (-(48844312258711844961 / 312500000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (34212040880202477 / 40000000000000000 : ℝ) =
            (34212040880202477 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (34212040880202477 / 20000000000000000 : ℝ) ≤
            (167764181585038155039 / 312500000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4276443089347963 / 5000000000000000 : ℝ)) (q :=
      (34212040880202477 / 40000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_674_3 :
    Uω (aρ 3) (bρ 3) (27652481574401 / 32000000000000 : ℝ) ≤
      (-(404738031473057972023 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (34021212980809573 / 40000000000000000 : ℝ) ≤
      (-(404738031473057972023 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (34021212980809573 / 40000000000000000 : ℝ) =
            (34021212980809573 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (34021212980809573 / 20000000000000000 : ℝ) ≤
            (1328129919276942027977 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4252434167674737 / 5000000000000000 : ℝ)) (q :=
      (34021212980809573 / 40000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_674_4 :
    Uω (aρ 4) (bρ 4) (27652481574401 / 32000000000000 : ℝ) ≤
      (-(342479473035474896289 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1348191267778473 / 1600000000000000 : ℝ) ≤
      (-(342479473035474896289 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (1348191267778473 / 1600000000000000 : ℝ) =
            (1348191267778473 / 800000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1348191267778473 / 800000000000000 : ℝ) ≤
            (1043814887564525103711 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (42124734366203 / 50000000000000 : ℝ)) (q :=
      (1348191267778473 / 1600000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_674_5 :
    Uω (aρ 5) (bρ 5) (27652481574401 / 32000000000000 : ℝ) ≤
      (-(185601151129559812207 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (33224192580018133 / 40000000000000000 : ℝ) ≤
      (-(185601151129559812207 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (33224192580018133 / 40000000000000000 : ℝ) =
            (33224192580018133 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (33224192580018133 / 20000000000000000 : ℝ) ≤
            (507546029170440187793 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4151421117676877 / 5000000000000000 : ℝ)) (q :=
      (33224192580018133 / 40000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_674_6 :
    Uω (aρ 6) (bρ 6) (27652481574401 / 32000000000000 : ℝ) ≤
      (-(1032372319093198975119 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (32537881332450541 / 40000000000000000 : ℝ) ≤
      (-(1032372319093198975119 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (32537881332450541 / 40000000000000000 : ℝ) =
            (32537881332450541 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (32537881332450541 / 20000000000000000 : ℝ) ≤
            (2433363582406801024881 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4063463493354979 / 5000000000000000 : ℝ)) (q :=
      (32537881332450541 / 40000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_674_7 :
    Uω (aρ 7) (bρ 7) (27652481574401 / 32000000000000 : ℝ) ≤
      (-(1177382868026010592239 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (31607766959490703 / 40000000000000000 : ℝ) ≤
      (-(1177382868026010592239 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (31607766959490703 / 40000000000000000 : ℝ) =
            (31607766959490703 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (31607766959490703 / 20000000000000000 : ℝ) ≤
            (2288353033473989407761 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7885531180990039 / 10000000000000000 : ℝ)) (q :=
      (31607766959490703 / 40000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_674_8 :
    Uω (aρ 8) (bρ 8) (27652481574401 / 32000000000000 : ℝ) ≤
      (-(2742226011902361903109 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (30406513722986933 / 40000000000000000 : ℝ) ≤
      (-(2742226011902361903109 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (30406513722986933 / 40000000000000000 : ℝ) =
            (30406513722986933 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (30406513722986933 / 20000000000000000 : ℝ) ≤
            (4189245791097638096891 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3784223107039077 / 5000000000000000 : ℝ)) (q :=
      (30406513722986933 / 40000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_674_9 :
    Uω (aρ 9) (bρ 9) (27652481574401 / 32000000000000 : ℝ) ≤
      (-(129671004603477111227 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28924874733777511 / 40000000000000000 : ℝ) ≤
      (-(129671004603477111227 / 400000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (28924874733777511 / 40000000000000000 : ℝ) =
            (28924874733777511 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (28924874733777511 / 20000000000000000 : ℝ) ≤
            (147587867516522888773 / 400000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7168592347833443 / 10000000000000000 : ℝ)) (q :=
      (28924874733777511 / 40000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_674_10 :
    Uω (aρ 10) (bρ 10) (27652481574401 / 32000000000000 : ℝ) ≤
      (-(483079380526028675361 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5435644174946641 / 8000000000000000 : ℝ) ≤
      (-(483079380526028675361 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (5435644174946641 / 8000000000000000 : ℝ) =
            (5435644174946641 / 4000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5435644174946641 / 4000000000000000 : ℝ) ≤
            (383354594848971324639 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (668382445180629 / 1000000000000000 : ℝ)) (q :=
      (5435644174946641 / 8000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_674_11 :
    Uω (aρ 11) (bρ 11) (27652481574401 / 32000000000000 : ℝ) ≤
      (-(576975617282524960421 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25211467739382093 / 40000000000000000 : ℝ) ≤
      (-(576975617282524960421 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (25211467739382093 / 40000000000000000 : ℝ) =
            (25211467739382093 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (25211467739382093 / 20000000000000000 : ℝ) ≤
            (289458358092475039579 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3059462255167867 / 5000000000000000 : ℝ)) (q :=
      (25211467739382093 / 40000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_674_12 :
    Uω (aρ 12) (bρ 12) (27652481574401 / 32000000000000 : ℝ) ≤
      (-(2744733037009107092033 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (23102315404187439 / 40000000000000000 : ℝ) ≤
      (-(2744733037009107092033 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (23102315404187439 / 40000000000000000 : ℝ) =
            (23102315404187439 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (23102315404187439 / 20000000000000000 : ℝ) ≤
            (721002864490892907967 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (5488048439423407 / 10000000000000000 : ℝ)) (q :=
      (23102315404187439 / 40000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_674_13 :
    Uω (aρ 13) (bρ 13) (27652481574401 / 32000000000000 : ℝ) ≤
      (-(3230332515999585509361 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (20964131438699567 / 40000000000000000 : ℝ) ≤
      (-(3230332515999585509361 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (20964131438699567 / 40000000000000000 : ℝ) =
            (20964131438699567 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (20964131438699567 / 20000000000000000 : ℝ) ≤
            (235403385500414490639 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4818338198274471 / 10000000000000000 : ℝ)) (q :=
      (20964131438699567 / 40000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_674_14 :
    Uω (aρ 14) (bρ 14) (27652481574401 / 32000000000000 : ℝ) ≤
      (-(298795737915287152287 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3790326625954983 / 8000000000000000 : ℝ) ≤
      (-(298795737915287152287 / 400000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (3790326625954983 / 8000000000000000 : ℝ) =
            (3790326625954983 / 2000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3790326625954983 / 2000000000000000 : ℝ) ≤
            (255722006324712847713 / 400000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (831203265771429 / 2000000000000000 : ℝ)) (q :=
      (3790326625954983 / 8000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_674_15 :
    Uω (aρ 15) (bρ 15) (27652481574401 / 32000000000000 : ℝ) ≤
      (-(2099471820989259101859 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (17272069640599751 / 40000000000000000 : ℝ) ≤
      (-(2099471820989259101859 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (17272069640599751 / 40000000000000000 : ℝ) =
            (17272069640599751 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (17272069640599751 / 10000000000000000 : ℝ) ≤
            (1366264080510740898141 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3575807861684563 / 10000000000000000 : ℝ)) (q :=
      (17272069640599751 / 40000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_674_16 :
    Uω (aρ 16) (bρ 16) (27652481574401 / 32000000000000 : ℝ) ≤
      (-(9045797086010213353117 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (16188477844103073 / 40000000000000000 : ℝ) ≤
      (-(9045797086010213353117 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (16188477844103073 / 40000000000000000 : ℝ) =
            (16188477844103073 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (16188477844103073 / 10000000000000000 : ℝ) ≤
            (4817146519989786646883 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (199148975934139 / 625000000000000 : ℝ)) (q :=
      (16188477844103073 / 40000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_674 :
    Uρ (27652481574401 / 32000000000000 : ℝ) ≤
      (-(104789093514343343243 / 312500000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (27652481574401 / 32000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(383785914618737645777 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_674_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (27652481574401 / 32000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) * (-(48844312258711844961 / 312500000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_674_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (27652481574401 / 32000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(404738031473057972023 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_674_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (27652481574401 / 32000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(342479473035474896289 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_674_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (27652481574401 / 32000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) * (-(185601151129559812207 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_674_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (27652481574401 / 32000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(1032372319093198975119 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_674_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (27652481574401 / 32000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(1177382868026010592239 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_674_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (27652481574401 / 32000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(2742226011902361903109 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_674_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (27652481574401 / 32000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(129671004603477111227 / 400000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_674_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (27652481574401 / 32000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(483079380526028675361 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_674_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (27652481574401 / 32000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(576975617282524960421 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_674_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (27652481574401 / 32000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(2744733037009107092033 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_674_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (27652481574401 / 32000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(3230332515999585509361 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_674_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (27652481574401 / 32000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) * (-(298795737915287152287 / 400000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_674_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (27652481574401 / 32000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(2099471820989259101859 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_674_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (27652481574401 / 32000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(9045797086010213353117 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_674_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_675_1 :
    Uω (aρ 1) (bρ 1) (56558325853133 / 64000000000000 : ℝ) ≤
      (-(1309378706805599354279 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (70181782143953017 / 80000000000000000 : ℝ) ≤
      (-(1309378706805599354279 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (70181782143953017 / 80000000000000000 : ℝ) =
            (70181782143953017 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (70181782143953017 / 40000000000000000 : ℝ) ≤
            (5622093096194400645721 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (8772704339521223 / 10000000000000000 : ℝ)) (q :=
      (70181782143953017 / 80000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_675_2 :
    Uω (aρ 2) (bρ 2) (56558325853133 / 64000000000000 : ℝ) ≤
      (-(1336627245042598542631 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (69990807353880377 / 80000000000000000 : ℝ) ≤
      (-(1336627245042598542631 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (69990807353880377 / 80000000000000000 : ℝ) =
            (69990807353880377 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (69990807353880377 / 40000000000000000 : ℝ) ≤
            (5594844557957401457369 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (8748729654513063 / 10000000000000000 : ℝ)) (q :=
      (69990807353880377 / 80000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_675_3 :
    Uω (aρ 3) (bρ 3) (56558325853133 / 64000000000000 : ℝ) ≤
      (-(1391297819368064538101 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (69609207654522701 / 80000000000000000 : ℝ) ≤
      (-(1391297819368064538101 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (69609207654522701 / 80000000000000000 : ℝ) =
            (69609207654522701 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (69609207654522701 / 40000000000000000 : ℝ) ≤
            (5540173983631935461899 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2175181459005911 / 2500000000000000 : ℝ)) (q :=
      (69609207654522701 / 80000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_675_4 :
    Uω (aρ 4) (bρ 4) (56558325853133 / 64000000000000 : ℝ) ≤
      (-(741304296202974127503 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (68976493674625433 / 80000000000000000 : ℝ) ≤
      (-(741304296202974127503 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (68976493674625433 / 80000000000000000 : ℝ) =
            (68976493674625433 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (68976493674625433 / 40000000000000000 : ℝ) ≤
            (2724431605297025872497 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (8620841522114327 / 10000000000000000 : ℝ)) (q :=
      (68976493674625433 / 80000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_675_5 :
    Uω (aρ 5) (bρ 5) (56558325853133 / 64000000000000 : ℝ) ≤
      (-(1622883744341165361017 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13603135906815797 / 16000000000000000 : ℝ) ≤
      (-(1622883744341165361017 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (13603135906815797 / 16000000000000000 : ℝ) =
            (13603135906815797 / 8000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (13603135906815797 / 8000000000000000 : ℝ) ≤
            (5308588058658834638983 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1699765581262543 / 2000000000000000 : ℝ)) (q :=
      (13603135906815797 / 16000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_675_6 :
    Uω (aρ 6) (bρ 6) (56558325853133 / 64000000000000 : ℝ) ≤
      (-(913316624783847168869 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (66643885998227629 / 80000000000000000 : ℝ) ≤
      (-(913316624783847168869 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (66643885998227629 / 80000000000000000 : ℝ) =
            (66643885998227629 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (66643885998227629 / 40000000000000000 : ℝ) ≤
            (2552419276716152831131 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2080779974372469 / 2500000000000000 : ℝ)) (q :=
      (66643885998227629 / 80000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_675_7 :
    Uω (aρ 7) (bρ 7) (56558325853133 / 64000000000000 : ℝ) ≤
      (-(527365195200048172033 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (64785418593637181 / 80000000000000000 : ℝ) ≤
      (-(527365195200048172033 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (64785418593637181 / 80000000000000000 : ℝ) =
            (64785418593637181 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (64785418593637181 / 40000000000000000 : ℝ) ≤
            (1205502755549951827967 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1010270553387783 / 1250000000000000 : ℝ)) (q :=
      (64785418593637181 / 80000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_675_8 :
    Uω (aρ 8) (bρ 8) (56558325853133 / 64000000000000 : ℝ) ≤
      (-(1243394595876810300753 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (62386425724127397 / 80000000000000000 : ℝ) ≤
      (-(1243394595876810300753 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (62386425724127397 / 80000000000000000 : ℝ) =
            (62386425724127397 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 11
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (62386425724127397 / 40000000000000000 : ℝ) ≤
            (2222341305623189699247 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3882978930532409 / 5000000000000000 : ℝ)) (q :=
      (62386425724127397 / 80000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_675_9 :
    Uω (aρ 9) (bρ 9) (56558325853133 / 64000000000000 : ℝ) ≤
      (-(2972313060724690363641 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (59429772916198877 / 80000000000000000 : ℝ) ≤
      (-(2972313060724690363641 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (59429772916198877 / 80000000000000000 : ℝ) =
            (59429772916198877 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (59429772916198877 / 40000000000000000 : ℝ) ≤
            (3959158742275309636359 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (28780313622823 / 39062500000000 : ℝ)) (q :=
      (59429772916198877 / 80000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_675_10 :
    Uω (aρ 10) (bρ 10) (56558325853133 / 64000000000000 : ℝ) ≤
      (-(893994214702231111179 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (55948350270039657 / 80000000000000000 : ℝ) ≤
      (-(893994214702231111179 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (55948350270039657 / 80000000000000000 : ℝ) =
            (55948350270039657 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (55948350270039657 / 40000000000000000 : ℝ) ≤
            (838873736047768888821 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6885963659397883 / 10000000000000000 : ℝ)) (q :=
      (55948350270039657 / 80000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_675_11 :
    Uω (aρ 11) (bρ 11) (56558325853133 / 64000000000000 : ℝ) ≤
      (-(215052782857109338981 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10407046827545529 / 16000000000000000 : ℝ) ≤
      (-(215052782857109338981 / 500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (10407046827545529 / 16000000000000000 : ℝ) =
            (10407046827545529 / 8000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (10407046827545529 / 8000000000000000 : ℝ) ≤
            (131520807292890661019 / 500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (79077015656561 / 125000000000000 : ℝ)) (q :=
      (10407046827545529 / 16000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_675_12 :
    Uω (aρ 12) (bρ 12) (56558325853133 / 64000000000000 : ℝ) ≤
      (-(1027892171772619989907 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9570090251541869 / 16000000000000000 : ℝ) ≤
      (-(1027892171772619989907 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (9570090251541869 / 16000000000000000 : ℝ) =
            (9570090251541869 / 8000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9570090251541869 / 8000000000000000 : ℝ) ≤
            (358402188827380010093 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1140733125841061 / 2000000000000000 : ℝ)) (q :=
      (9570090251541869 / 16000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_675_13 :
    Uω (aρ 13) (bρ 13) (56558325853133 / 64000000000000 : ℝ) ≤
      (-(1212718825538876018277 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (43626607223548973 / 80000000000000000 : ℝ) ≤
      (-(1212718825538876018277 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (43626607223548973 / 80000000000000000 : ℝ) =
            (43626607223548973 / 40000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (43626607223548973 / 40000000000000000 : ℝ) ≤
            (173575535061123981723 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1261771590565053 / 2500000000000000 : ℝ)) (q :=
      (43626607223548973 / 80000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_675_14 :
    Uω (aρ 14) (bρ 14) (56558325853133 / 64000000000000 : ℝ) ≤
      (-(280489785711701105503 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7935641994942533 / 16000000000000000 : ℝ) ≤
      (-(280489785711701105503 / 400000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (7935641994942533 / 16000000000000000 : ℝ) =
            (7935641994942533 / 4000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7935641994942533 / 4000000000000000 : ℝ) ≤
            (274027958528298894497 / 400000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (880782867019227 / 2000000000000000 : ℝ)) (q :=
      (7935641994942533 / 16000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_675_15 :
    Uω (aρ 15) (bρ 15) (56558325853133 / 64000000000000 : ℝ) ≤
      (-(7870167065046628959241 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (36416061511973109 / 80000000000000000 : ℝ) ≤
      (-(7870167065046628959241 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (36416061511973109 / 80000000000000000 : ℝ) =
            (36416061511973109 / 20000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (36416061511973109 / 20000000000000000 : ℝ) ≤
            (5992776540953371040759 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1923975248413123 / 5000000000000000 : ℝ)) (q :=
      (36416061511973109 / 80000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_675_16 :
    Uω (aρ 16) (bρ 16) (56558325853133 / 64000000000000 : ℝ) ≤
      (-(4229065425846391883387 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (34336658657888021 / 80000000000000000 : ℝ) ≤
      (-(4229065425846391883387 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (34336658657888021 / 80000000000000000 : ℝ) =
            (34336658657888021 / 20000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (34336658657888021 / 20000000000000000 : ℝ) ≤
            (2702406377153608116613 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1740235717407487 / 5000000000000000 : ℝ)) (q :=
      (34336658657888021 / 80000000000000000 : ℝ)) (by norm_num [aρ_16, bρ_16])
      (by norm_num [bρ_16]) (by norm_num) (by norm_num [aρ_16, bρ_16])
      (by norm_num [aρ_16, bρ_16]) hlg

lemma U_675 :
    Uρ (56558325853133 / 64000000000000 : ℝ) ≤
      (-(1540795269486682136973 / 5000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (56558325853133 / 64000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(1309378706805599354279 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_675_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (56558325853133 / 64000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(1336627245042598542631 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_675_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (56558325853133 / 64000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(1391297819368064538101 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_675_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (56558325853133 / 64000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(741304296202974127503 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_675_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (56558325853133 / 64000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(1622883744341165361017 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_675_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (56558325853133 / 64000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(913316624783847168869 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_675_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (56558325853133 / 64000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(527365195200048172033 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_675_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (56558325853133 / 64000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(1243394595876810300753 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_675_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (56558325853133 / 64000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(2972313060724690363641 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_675_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (56558325853133 / 64000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(893994214702231111179 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_675_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (56558325853133 / 64000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) * (-(215052782857109338981 / 500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_675_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (56558325853133 / 64000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(1027892171772619989907 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_675_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (56558325853133 / 64000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(1212718825538876018277 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_675_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (56558325853133 / 64000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) * (-(280489785711701105503 / 400000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_675_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (56558325853133 / 64000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(7870167065046628959241 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_675_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (56558325853133 / 64000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) *
        (-(4229065425846391883387 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_675_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

end Zeta5Irrational
