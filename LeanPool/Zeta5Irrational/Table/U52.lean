/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Table.UpperCertificate

/-! # Certified arcsine potential bounds (U52) -/

public section

open Finset

namespace Zeta5Irrational

lemma U_628_1 :
    Uω (aρ 1) (bρ 1) (11671906263691 / 16000000000000 : ℝ) ≤
      (-(3242877128542114788709 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3615210918661643 / 5000000000000000 : ℝ) ≤
      (-(3242877128542114788709 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (3615210918661643 / 5000000000000000 : ℝ) =
            (3615210918661643 / 2500000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3615210918661643 / 2500000000000000 : ℝ) ≤
            (3688594674457885211291 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7230399477924697 / 10000000000000000 : ℝ)) (q :=
      (3615210918661643 / 5000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_628_2 :
    Uω (aρ 2) (bρ 2) (11671906263691 / 16000000000000 : ℝ) ≤
      (-(1637989077187245085489 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14413055933439441 / 20000000000000000 : ℝ) ≤
      (-(1637989077187245085489 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (14413055933439441 / 20000000000000000 : ℝ) =
            (14413055933439441 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14413055933439441 / 10000000000000000 : ℝ) ≤
            (1827746824312754914511 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3603190374613783 / 5000000000000000 : ℝ)) (q :=
      (14413055933439441 / 20000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_628_3 :
    Uω (aρ 3) (bρ 3) (11671906263691 / 16000000000000 : ℝ) ≤
      (-(3342479810571222740781 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14317524725642981 / 20000000000000000 : ℝ) ≤
      (-(3342479810571222740781 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (14317524725642981 / 20000000000000000 : ℝ) =
            (14317524725642981 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14317524725642981 / 10000000000000000 : ℝ) ≤
            (3588991992428777259219 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3579122823890553 / 5000000000000000 : ℝ)) (q :=
      (14317524725642981 / 20000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_628_4 :
    Uω (aρ 4) (bρ 4) (11671906263691 / 16000000000000 : ℝ) ≤
      (-(3453819726866507349207 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14158997682236471 / 20000000000000000 : ℝ) ≤
      (-(3453819726866507349207 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (14158997682236471 / 20000000000000000 : ℝ) =
            (14158997682236471 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14158997682236471 / 10000000000000000 : ℝ) ≤
            (3477652076133492650793 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1769503196359899 / 2500000000000000 : ℝ)) (q :=
      (14158997682236471 / 20000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_628_5 :
    Uω (aρ 5) (bρ 5) (11671906263691 / 16000000000000 : ℝ) ≤
      (-(3625538355383480504909 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6958968485077981 / 10000000000000000 : ℝ) ≤
      (-(3625538355383480504909 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (6958968485077981 / 10000000000000000 : ℝ) =
            (6958968485077981 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (6958968485077981 / 5000000000000000 : ℝ) ≤
            (3305933447616519495091 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6955141992694087 / 10000000000000000 : ℝ)) (q :=
      (6958968485077981 / 10000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_628_6 :
    Uω (aρ 6) (bρ 6) (11671906263691 / 16000000000000 : ℝ) ≤
      (-(193823918117542028053 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2714605189622871 / 4000000000000000 : ℝ) ≤
      (-(193823918117542028053 / 500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (2714605189622871 / 4000000000000000 : ℝ) =
            (2714605189622871 / 2000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2714605189622871 / 2000000000000000 : ℝ) ≤
            (152749672032457971947 / 500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (42359195911203 / 62500000000000 : ℝ)) (q :=
      (2714605189622871 / 4000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_628_7 :
    Uω (aρ 7) (bρ 7) (11671906263691 / 16000000000000 : ℝ) ≤
      (-(132124751893165640127 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6552101819691467 / 10000000000000000 : ℝ) ≤
      (-(132124751893165640127 / 312500000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (6552101819691467 / 10000000000000000 : ℝ) =
            (6552101819691467 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (6552101819691467 / 5000000000000000 : ℝ) ≤
            (84483741950584359873 / 312500000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6532310417821059 / 10000000000000000 : ℝ)) (q :=
      (6552101819691467 / 10000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_628_8 :
    Uω (aρ 8) (bρ 8) (11671906263691 / 16000000000000 : ℝ) ≤
      (-(4703268327102192686097 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1561995075781669 / 2500000000000000 : ℝ) ≤
      (-(4703268327102192686097 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (1561995075781669 / 2500000000000000 : ℝ) =
            (1561995075781669 / 1250000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1561995075781669 / 1250000000000000 : ℝ) ≤
            (2228203475897807313903 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6207609036031477 / 10000000000000000 : ℝ)) (q :=
      (1561995075781669 / 2500000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_628_9 :
    Uω (aρ 9) (bρ 9) (11671906263691 / 16000000000000 : ℝ) ≤
      (-(5326895601779464101117 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (23480960321493 / 40000000000000 : ℝ) ≤
      (-(5326895601779464101117 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (23480960321493 / 40000000000000 : ℝ) = (23480960321493 / 20000000000000 : ℝ) / 2 ^ 1 by
          norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (23480960321493 / 20000000000000 : ℝ) ≤
            (1604576201220535898883 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (46344753751077 / 80000000000000 : ℝ)) (q :=
      (23480960321493 / 40000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_628_10 :
    Uω (aρ 10) (bρ 10) (11671906263691 / 16000000000000 : ℝ) ≤
      (-(3062433192379457887933 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1084002860470187 / 2000000000000000 : ℝ) ≤
      (-(3062433192379457887933 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (1084002860470187 / 2000000000000000 : ℝ) =
            (1084002860470187 / 1000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1084002860470187 / 1000000000000000 : ℝ) ≤
            (403302709120542112067 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1056240339266999 / 2000000000000000 : ℝ)) (q :=
      (1084002860470187 / 2000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_628_11 :
    Uω (aρ 11) (bρ 11) (11671906263691 / 16000000000000 : ℝ) ≤
      (-(7125471243255631514223 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4903935118129209 / 10000000000000000 : ℝ) ≤
      (-(7125471243255631514223 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (4903935118129209 / 10000000000000000 : ℝ) =
            (4903935118129209 / 2500000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4903935118129209 / 2500000000000000 : ℝ) ≤
            (6737472362744368485777 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4667519954096543 / 10000000000000000 : ℝ)) (q :=
      (4903935118129209 / 10000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_628_12 :
    Uω (aρ 12) (bρ 12) (11671906263691 / 16000000000000 : ℝ) ≤
      (-(8362255243951402653027 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8666861662668721 / 20000000000000000 : ℝ) ≤
      (-(8362255243951402653027 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (8666861662668721 / 20000000000000000 : ℝ) =
            (8666861662668721 / 5000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (8666861662668721 / 5000000000000000 : ℝ) ≤
            (5500688362048597346973 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1975105738595923 / 5000000000000000 : ℝ)) (q :=
      (8666861662668721 / 20000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_628_13 :
    Uω (aρ 13) (bρ 13) (11671906263691 / 16000000000000 : ℝ) ≤
      (-(9883039534702144509293 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1488829747688233 / 4000000000000000 : ℝ) ≤
      (-(9883039534702144509293 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (1488829747688233 / 4000000000000000 : ℝ) =
            (1488829747688233 / 1000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1488829747688233 / 1000000000000000 : ℝ) ≤
            (3979904071297855490707 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (312688029455929 / 1000000000000000 : ℝ)) (q :=
      (1488829747688233 / 4000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_628_14 :
    Uω (aρ 14) (bρ 14) (11671906263691 / 16000000000000 : ℝ) ≤
      (-(589233722447172838279 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6155000421638059 / 20000000000000000 : ℝ) ≤
      (-(589233722447172838279 / 500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (6155000421638059 / 20000000000000000 : ℝ) =
            (6155000421638059 / 5000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (6155000421638059 / 5000000000000000 : ℝ) ≤
            (103913457852827161721 / 500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (68176851962537 / 312500000000000 : ℝ)) (q :=
      (6155000421638059 / 20000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_628_15 :
    Uω (aρ 15) (bρ 15) (11671906263691 / 16000000000000 : ℝ) ≤
      (-(7240890309318723000821 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2349980500237737 / 10000000000000000 : ℝ) ≤
      (-(7240890309318723000821 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (2349980500237737 / 10000000000000000 : ℝ) =
            (2349980500237737 / 1250000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2349980500237737 / 1250000000000000 : ℝ) ≤
            (3156317395181276999179 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (986193119053599 / 10000000000000000 : ℝ)) (q :=
      (2349980500237737 / 10000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_628_16 :
    Uω (aρ 16) (bρ 16) (11671906263691 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_628 :
    Uρ (11671906263691 / 16000000000000 : ℝ) ≤
      (-(1399085531536063093099 / 2500000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (11671906263691 / 16000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(3242877128542114788709 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_628_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (11671906263691 / 16000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(1637989077187245085489 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_628_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (11671906263691 / 16000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(3342479810571222740781 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_628_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (11671906263691 / 16000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(3453819726866507349207 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_628_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (11671906263691 / 16000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(3625538355383480504909 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_628_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (11671906263691 / 16000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(193823918117542028053 / 500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_628_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (11671906263691 / 16000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(132124751893165640127 / 312500000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_628_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (11671906263691 / 16000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(4703268327102192686097 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_628_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (11671906263691 / 16000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(5326895601779464101117 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_628_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (11671906263691 / 16000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(3062433192379457887933 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_628_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (11671906263691 / 16000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(7125471243255631514223 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_628_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (11671906263691 / 16000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(8362255243951402653027 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_628_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (11671906263691 / 16000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(9883039534702144509293 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_628_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (11671906263691 / 16000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) * (-(589233722447172838279 / 500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_628_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (11671906263691 / 16000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(7240890309318723000821 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_628_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (11671906263691 / 16000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_628_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_629_1 :
    Uω (aρ 1) (bρ 1) (23374289245939 / 32000000000000 : ℝ) ≤
      (-(645942733699712492987 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28959783365142761 / 40000000000000000 : ℝ) ≤
      (-(645942733699712492987 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (28959783365142761 / 40000000000000000 : ℝ) =
            (28959783365142761 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (28959783365142761 / 20000000000000000 : ℝ) ≤
            (740351626900287507013 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7239923511300443 / 10000000000000000 : ℝ)) (q :=
      (28959783365142761 / 40000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_629_2 :
    Uω (aρ 2) (bρ 2) (23374289245939 / 32000000000000 : ℝ) ≤
      (-(815692712508334048631 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28864208542300257 / 40000000000000000 : ℝ) ≤
      (-(815692712508334048631 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (28864208542300257 / 40000000000000000 : ℝ) =
            (28864208542300257 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (28864208542300257 / 20000000000000000 : ℝ) ≤
            (917175238241665951369 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7215905112389191 / 10000000000000000 : ℝ)) (q :=
      (28864208542300257 / 40000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_629_3 :
    Uω (aρ 3) (bρ 3) (23374289245939 / 32000000000000 : ℝ) ≤
      (-(832295938651579155123 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28673148095764909 / 40000000000000000 : ℝ) ≤
      (-(832295938651579155123 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (28673148095764909 / 40000000000000000 : ℝ) =
            (28673148095764909 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (28673148095764909 / 20000000000000000 : ℝ) ≤
            (900572012098420844877 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7167770995471517 / 10000000000000000 : ℝ)) (q :=
      (28673148095764909 / 40000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_629_4 :
    Uω (aρ 4) (bρ 4) (23374289245939 / 32000000000000 : ℝ) ≤
      (-(3440373057157870478887 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28356099250297589 / 40000000000000000 : ℝ) ≤
      (-(3440373057157870478887 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (28356099250297589 / 40000000000000000 : ℝ) =
            (28356099250297589 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (28356099250297589 / 20000000000000000 : ℝ) ≤
            (3491098745842129521113 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7087540753802857 / 10000000000000000 : ℝ)) (q :=
      (28356099250297589 / 40000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_629_5 :
    Uω (aρ 5) (bρ 5) (23374289245939 / 32000000000000 : ℝ) ≤
      (-(722370860654510914959 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27873990768952717 / 40000000000000000 : ℝ) ≤
      (-(722370860654510914959 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (27873990768952717 / 40000000000000000 : ℝ) =
            (27873990768952717 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (27873990768952717 / 20000000000000000 : ℝ) ≤
            (663923499945489085041 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6964676432465421 / 10000000000000000 : ℝ)) (q :=
      (27873990768952717 / 40000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_629_6 :
    Uω (aρ 6) (bρ 6) (23374289245939 / 32000000000000 : ℝ) ≤
      (-(965608962956098136493 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1087367941825877 / 1600000000000000 : ℝ) ≤
      (-(965608962956098136493 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (1087367941825877 / 1600000000000000 : ℝ) =
            (1087367941825877 / 800000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1087367941825877 / 800000000000000 : ℝ) ≤
            (767258987793901863507 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (271480827838101 / 400000000000000 : ℝ)) (q :=
      (1087367941825877 / 1600000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_629_7 :
    Uω (aρ 7) (bρ 7) (23374289245939 / 32000000000000 : ℝ) ≤
      (-(105335573704855377237 / 250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (26246618430248087 / 40000000000000000 : ℝ) ≤
      (-(105335573704855377237 / 250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (26246618430248087 / 40000000000000000 : ℝ) =
            (26246618430248087 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (26246618430248087 / 20000000000000000 : ℝ) ≤
            (67951221370144622763 / 250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3270946009506553 / 5000000000000000 : ℝ)) (q :=
      (26246618430248087 / 40000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_629_8 :
    Uω (aρ 8) (bρ 8) (23374289245939 / 32000000000000 : ℝ) ≤
      (-(4687937817110196890423 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25030264485880559 / 40000000000000000 : ℝ) ≤
      (-(4687937817110196890423 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (25030264485880559 / 40000000000000000 : ℝ) =
            (25030264485880559 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (25030264485880559 / 20000000000000000 : ℝ) ≤
            (2243533985889803109577 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3108628349084671 / 5000000000000000 : ℝ)) (q :=
      (25030264485880559 / 40000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_629_9 :
    Uω (aρ 9) (bρ 9) (23374289245939 / 32000000000000 : ℝ) ≤
      (-(5310469239407437719787 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4703912538789881 / 8000000000000000 : ℝ) ≤
      (-(5310469239407437719787 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (4703912538789881 / 8000000000000000 : ℝ) =
            (4703912538789881 / 4000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 6
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4703912538789881 / 4000000000000000 : ℝ) ≤
            (1621002563592562280213 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1160574286112753 / 2000000000000000 : ℝ)) (q :=
      (4703912538789881 / 8000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_629_10 :
    Uω (aρ 10) (bρ 10) (23374289245939 / 32000000000000 : ℝ) ≤
      (-(3053424875716178132791 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (21719152581301551 / 40000000000000000 : ℝ) ≤
      (-(3053424875716178132791 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (21719152581301551 / 40000000000000000 : ℝ) =
            (21719152581301551 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (21719152581301551 / 20000000000000000 : ℝ) ≤
            (412311025783821867209 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2645612703867419 / 5000000000000000 : ℝ)) (q :=
      (21719152581301551 / 40000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_629_11 :
    Uω (aρ 11) (bρ 11) (23374289245939 / 32000000000000 : ℝ) ≤
      (-(1421017869337593465473 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (19655761843575217 / 40000000000000000 : ℝ) ≤
      (-(1421017869337593465473 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (19655761843575217 / 40000000000000000 : ℝ) =
            (19655761843575217 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (19655761843575217 / 10000000000000000 : ℝ) ≤
            (1351570851862406534527 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4678006665076671 / 10000000000000000 : ℝ)) (q :=
      (19655761843575217 / 40000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_629_12 :
    Uω (aρ 12) (bρ 12) (23374289245939 / 32000000000000 : ℝ) ≤
      (-(833817983441931326163 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3475101049956067 / 8000000000000000 : ℝ) ≤
      (-(833817983441931326163 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (3475101049956067 / 8000000000000000 : ℝ) =
            (3475101049956067 / 2000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3475101049956067 / 2000000000000000 : ℝ) ≤
            (552476377158068673837 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (396157846486423 / 1000000000000000 : ℝ)) (q :=
      (3475101049956067 / 8000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_629_13 :
    Uω (aρ 13) (bρ 13) (23374289245939 / 32000000000000 : ℝ) ≤
      (-(12315806207499133563 / 12500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2986723731185781 / 8000000000000000 : ℝ) ≤
      (-(12315806207499133563 / 12500000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (2986723731185781 / 8000000000000000 : ℝ) =
            (2986723731185781 / 2000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2986723731185781 / 2000000000000000 : ℝ) ≤
            (5012873300000866437 / 12500000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (628003381906703 / 2000000000000000 : ℝ)) (q :=
      (2986723731185781 / 8000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_629_14 :
    Uω (aρ 14) (bρ 14) (23374289245939 / 32000000000000 : ℝ) ≤
      (-(469647681200431082067 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2472728849475393 / 8000000000000000 : ℝ) ≤
      (-(469647681200431082067 / 400000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (2472728849475393 / 8000000000000000 : ℝ) =
            (2472728849475393 / 2000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2472728849475393 / 2000000000000000 : ℝ) ≤
            (84870063039568917933 / 400000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (439791398060509 / 2000000000000000 : ℝ)) (q :=
      (2472728849475393 / 8000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_629_15 :
    Uω (aρ 15) (bρ 15) (23374289245939 / 32000000000000 : ℝ) ≤
      (-(14386903830489276582459 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9489529854871201 / 40000000000000000 : ℝ) ≤
      (-(14386903830489276582459 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (9489529854871201 / 40000000000000000 : ℝ) =
            (9489529854871201 / 5000000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9489529854871201 / 5000000000000000 : ℝ) ≤
            (6407511578510723417541 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1021473071464663 / 10000000000000000 : ℝ)) (q :=
      (9489529854871201 / 40000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_629_16 :
    Uω (aρ 16) (bρ 16) (23374289245939 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_629 :
    Uρ (23374289245939 / 32000000000000 : ℝ) ≤
      (-(5576914744225668371273 / 10000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (23374289245939 / 32000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(645942733699712492987 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_629_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (23374289245939 / 32000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(815692712508334048631 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_629_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (23374289245939 / 32000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(832295938651579155123 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_629_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (23374289245939 / 32000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(3440373057157870478887 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_629_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (23374289245939 / 32000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) * (-(722370860654510914959 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_629_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (23374289245939 / 32000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(965608962956098136493 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_629_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (23374289245939 / 32000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(105335573704855377237 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_629_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (23374289245939 / 32000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(4687937817110196890423 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_629_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (23374289245939 / 32000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(5310469239407437719787 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_629_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (23374289245939 / 32000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(3053424875716178132791 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_629_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (23374289245939 / 32000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(1421017869337593465473 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_629_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (23374289245939 / 32000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(833817983441931326163 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_629_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (23374289245939 / 32000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) * (-(12315806207499133563 / 12500000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_629_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (23374289245939 / 32000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) * (-(469647681200431082067 / 400000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_629_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (23374289245939 / 32000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(14386903830489276582459 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_629_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (23374289245939 / 32000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_629_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_630_1 :
    Uω (aρ 1) (bρ 1) (1462797872781 / 2000000000000 : ℝ) ≤
      (-(3216567513452919317099 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14498939690341621 / 20000000000000000 : ℝ) ≤
      (-(3216567513452919317099 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (14498939690341621 / 20000000000000000 : ℝ) =
            (14498939690341621 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14498939690341621 / 10000000000000000 : ℝ) ≤
            (3714904289547080682901 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7249447544521621 / 10000000000000000 : ℝ)) (q :=
      (14498939690341621 / 20000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_630_2 :
    Uω (aρ 2) (bρ 2) (1462797872781 / 2000000000000 : ℝ) ≤
      (-(1624790483342472992419 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14451152607836319 / 20000000000000000 : ℝ) ≤
      (-(1624790483342472992419 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (14451152607836319 / 20000000000000000 : ℝ) =
            (14451152607836319 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14451152607836319 / 10000000000000000 : ℝ) ≤
            (1840945418157527007581 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7225429474526319 / 10000000000000000 : ℝ)) (q :=
      (14451152607836319 / 20000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_630_3 :
    Uω (aρ 3) (bρ 3) (1462797872781 / 2000000000000 : ℝ) ≤
      (-(1657952678109447268993 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7177811683238731 / 10000000000000000 : ℝ) ≤
      (-(1657952678109447268993 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (7177811683238731 / 10000000000000000 : ℝ) =
            (7177811683238731 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7177811683238731 / 5000000000000000 : ℝ) ≤
            (1807783223390552731007 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3588648169758731 / 5000000000000000 : ℝ)) (q :=
      (7177811683238731 / 10000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_630_4 :
    Uω (aρ 4) (bρ 4) (1462797872781 / 2000000000000 : ℝ) ≤
      (-(3426944452015668801577 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7098550778669901 / 10000000000000000 : ℝ) ≤
      (-(3426944452015668801577 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (7098550778669901 / 10000000000000000 : ℝ) =
            (7098550778669901 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7098550778669901 / 5000000000000000 : ℝ) ≤
            (3504527350984331198423 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3548534355722401 / 5000000000000000 : ℝ)) (q :=
      (7098550778669901 / 10000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_630_5 :
    Uω (aρ 5) (bρ 5) (1462797872781 / 2000000000000 : ℝ) ≤
      (-(1799094485697806630207 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13956053770198459 / 20000000000000000 : ℝ) ≤
      (-(1799094485697806630207 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (13956053770198459 / 20000000000000000 : ℝ) =
            (13956053770198459 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (13956053770198459 / 10000000000000000 : ℝ) ≤
            (1666641415802193369793 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6974210843638459 / 10000000000000000 : ℝ)) (q :=
      (13956053770198459 / 20000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_630_6 :
    Uω (aρ 6) (bρ 6) (1462797872781 / 2000000000000 : ℝ) ≤
      (-(38484130851782445057 / 100000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13611172526320581 / 20000000000000000 : ℝ) ≤
      (-(38484130851782445057 / 100000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (13611172526320581 / 20000000000000000 : ℝ) =
            (13611172526320581 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (13611172526320581 / 10000000000000000 : ℝ) ≤
            (30830587178217554943 / 100000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6796569974900581 / 10000000000000000 : ℝ)) (q :=
      (13611172526320581 / 20000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_630_7 :
    Uω (aρ 7) (bρ 7) (1462797872781 / 2000000000000 : ℝ) ≤
      (-(524859394838169808527 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13142414622812853 / 20000000000000000 : ℝ) ≤
      (-(524859394838169808527 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (13142414622812853 / 20000000000000000 : ℝ) =
            (13142414622812853 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (13142414622812853 / 10000000000000000 : ℝ) ≤
            (341574580536830191473 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6551473452152853 / 10000000000000000 : ℝ)) (q :=
      (13142414622812853 / 20000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_630_8 :
    Uω (aρ 8) (bρ 8) (1462797872781 / 2000000000000 : ℝ) ≤
      (-(4672631077418728873253 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1253430349881301 / 2000000000000000 : ℝ) ≤
      (-(4672631077418728873253 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (1253430349881301 / 2000000000000000 : ℝ) =
            (1253430349881301 / 1000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1253430349881301 / 1000000000000000 : ℝ) ≤
            (2258840725581271126747 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (622690397949301 / 1000000000000000 : ℝ)) (q :=
      (1253430349881301 / 2000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_630_9 :
    Uω (aρ 9) (bρ 9) (1462797872781 / 2000000000000 : ℝ) ≤
      (-(529407052921083357707 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (11779081692316477 / 20000000000000000 : ℝ) ≤
      (-(529407052921083357707 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (11779081692316477 / 20000000000000000 : ℝ) =
            (11779081692316477 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (11779081692316477 / 10000000000000000 : ℝ) ≤
            (163740127378916642293 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (5812647801356477 / 10000000000000000 : ℝ)) (q :=
      (11779081692316477 / 20000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_630_10 :
    Uω (aρ 10) (bρ 10) (1462797872781 / 2000000000000 : ℝ) ≤
      (-(3044433606727779236829 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10879122133882899 / 20000000000000000 : ℝ) ≤
      (-(3044433606727779236829 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (10879122133882899 / 20000000000000000 : ℝ) =
            (10879122133882899 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (10879122133882899 / 10000000000000000 : ℝ) ≤
            (421302294772220763171 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (5301247276417899 / 10000000000000000 : ℝ)) (q :=
      (10879122133882899 / 20000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_630_11 :
    Uω (aρ 11) (bρ 11) (1462797872781 / 2000000000000 : ℝ) ≤
      (-(7084753080275469726601 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1969577499663141 / 4000000000000000 : ℝ) ≤
      (-(7084753080275469726601 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (1969577499663141 / 4000000000000000 : ℝ) =
            (1969577499663141 / 1000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1969577499663141 / 1000000000000000 : ℝ) ≤
            (6778190525724530273399 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (937697853411141 / 2000000000000000 : ℝ)) (q :=
      (1969577499663141 / 4000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_630_12 :
    Uω (aρ 12) (bρ 12) (1462797872781 / 2000000000000 : ℝ) ≤
      (-(1662834675285439792897 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2177158473993287 / 5000000000000000 : ℝ) ≤
      (-(1662834675285439792897 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (2177158473993287 / 5000000000000000 : ℝ) =
            (2177158473993287 / 1250000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2177158473993287 / 1250000000000000 : ℝ) ≤
            (1109754045914560207103 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (993233940349537 / 2500000000000000 : ℝ)) (q :=
      (2177158473993287 / 5000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_630_13 :
    Uω (aρ 13) (bρ 13) (1462797872781 / 2000000000000 : ℝ) ≤
      (-(9822377166288816452343 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7489443954622891 / 20000000000000000 : ℝ) ≤
      (-(9822377166288816452343 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (7489443954622891 / 20000000000000000 : ℝ) =
            (7489443954622891 / 5000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7489443954622891 / 5000000000000000 : ℝ) ≤
            (4040566439711183547657 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3153127561642891 / 10000000000000000 : ℝ)) (q :=
      (7489443954622891 / 20000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_630_14 :
    Uω (aρ 14) (bρ 14) (1462797872781 / 2000000000000 : ℝ) ≤
      (-(5849024699973716311919 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (310427487186159 / 1000000000000000 : ℝ) ≤
      (-(5849024699973716311919 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (310427487186159 / 1000000000000000 : ℝ) =
            (310427487186159 / 250000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (310427487186159 / 250000000000000 : ℝ) ≤
            (1082447103026283688081 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (110808031789409 / 500000000000000 : ℝ)) (q :=
      (310427487186159 / 1000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14]) (by norm_num [bρ_14])
      (by norm_num) (by norm_num [aρ_14, bρ_14]) (by norm_num [aρ_14, bρ_14]) hlg

lemma U_630_15 :
    Uω (aρ 15) (bρ 15) (1462797872781 / 2000000000000 : ℝ) ≤
      (-(7147600066389320593217 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4788476294669653 / 20000000000000000 : ℝ) ≤
      (-(7147600066389320593217 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (4788476294669653 / 20000000000000000 : ℝ) =
            (4788476294669653 / 2500000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4788476294669653 / 2500000000000000 : ℝ) ≤
            (3249607638110679406783 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1055660464149653 / 10000000000000000 : ℝ)) (q :=
      (4788476294669653 / 20000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_630_16 :
    Uω (aρ 16) (bρ 16) (1462797872781 / 2000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_630 :
    Uρ (1462797872781 / 2000000000000 : ℝ) ≤
      (-(5557629648906738505043 / 10000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (1462797872781 / 2000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(3216567513452919317099 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_630_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (1462797872781 / 2000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(1624790483342472992419 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_630_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (1462797872781 / 2000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(1657952678109447268993 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_630_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (1462797872781 / 2000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(3426944452015668801577 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_630_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (1462797872781 / 2000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(1799094485697806630207 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_630_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (1462797872781 / 2000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) * (-(38484130851782445057 / 100000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_630_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (1462797872781 / 2000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(524859394838169808527 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_630_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (1462797872781 / 2000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(4672631077418728873253 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_630_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (1462797872781 / 2000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(529407052921083357707 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_630_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (1462797872781 / 2000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(3044433606727779236829 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_630_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (1462797872781 / 2000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(7084753080275469726601 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_630_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (1462797872781 / 2000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(1662834675285439792897 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_630_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (1462797872781 / 2000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(9822377166288816452343 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_630_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (1462797872781 / 2000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(5849024699973716311919 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_630_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (1462797872781 / 2000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(7147600066389320593217 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_630_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (1462797872781 / 2000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_630_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_631_1 :
    Uω (aρ 1) (bρ 1) (23435242683053 / 32000000000000 : ℝ) ≤
      (-(3203438617965511292341 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (29035975395915803 / 40000000000000000 : ℝ) ≤
      (-(3203438617965511292341 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (29035975395915803 / 40000000000000000 : ℝ) =
            (29035975395915803 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (29035975395915803 / 20000000000000000 : ℝ) ≤
            (3728033185034488707659 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7258971577588839 / 10000000000000000 : ℝ)) (q :=
      (29035975395915803 / 40000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_631_2 :
    Uω (aρ 2) (bρ 2) (23435242683053 / 32000000000000 : ℝ) ≤
      (-(3236408458429937679207 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28940401887004121 / 40000000000000000 : ℝ) ≤
      (-(3236408458429937679207 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (28940401887004121 / 40000000000000000 : ℝ) =
            (28940401887004121 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (28940401887004121 / 20000000000000000 : ℝ) ≤
            (3695063344570062320793 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3617476917821499 / 5000000000000000 : ℝ)) (q :=
      (28940401887004121 / 40000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_631_3 :
    Uω (aρ 3) (bρ 3) (23435242683053 / 32000000000000 : ℝ) ≤
      (-(132105782742592253447 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28749345362884991 / 40000000000000000 : ℝ) ≤
      (-(132105782742592253447 / 400000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (28749345362884991 / 40000000000000000 : ℝ) =
            (28749345362884991 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (28749345362884991 / 20000000000000000 : ℝ) ≤
            (145153089377407746553 / 400000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7186821679933433 / 10000000000000000 : ℝ)) (q :=
      (28749345362884991 / 40000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_631_4 :
    Uω (aρ 4) (bρ 4) (23435242683053 / 32000000000000 : ℝ) ≤
      (-(3413533862948097198867 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28432306957705233 / 40000000000000000 : ℝ) ≤
      (-(3413533862948097198867 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (28432306957705233 / 40000000000000000 : ℝ) =
            (28432306957705233 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (28432306957705233 / 20000000000000000 : ℝ) ≤
            (3517937940051902801133 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3553298329204277 / 5000000000000000 : ℝ)) (q :=
      (28432306957705233 / 40000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_631_5 :
    Uω (aρ 5) (bρ 5) (23435242683053 / 32000000000000 : ℝ) ≤
      (-(3584542308547022505337 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27950224254878789 / 40000000000000000 : ℝ) ≤
      (-(3584542308547022505337 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (27950224254878789 / 40000000000000000 : ℝ) =
            (27950224254878789 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (27950224254878789 / 20000000000000000 : ℝ) ≤
            (3346929494452977494663 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1745936306582583 / 2500000000000000 : ℝ)) (q :=
      (27950224254878789 / 40000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_631_6 :
    Uω (aρ 6) (bρ 6) (23435242683053 / 32000000000000 : ℝ) ≤
      (-(3834410006823929320503 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27260491417810903 / 40000000000000000 : ℝ) ≤
      (-(3834410006823929320503 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (27260491417810903 / 40000000000000000 : ℝ) =
            (27260491417810903 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (27260491417810903 / 20000000000000000 : ℝ) ≤
            (3097061796176070679497 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6806119182936389 / 10000000000000000 : ℝ)) (q :=
      (27260491417810903 / 40000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_631_7 :
    Uω (aρ 7) (bρ 7) (23435242683053 / 32000000000000 : ℝ) ≤
      (-(836869725883868706071 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (26323039726371219 / 40000000000000000 : ℝ) ≤
      (-(836869725883868706071 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (26323039726371219 / 40000000000000000 : ℝ) =
            (26323039726371219 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (26323039726371219 / 20000000000000000 : ℝ) ≤
            (549424634716131293929 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6561054717976547 / 10000000000000000 : ℝ)) (q :=
      (26323039726371219 / 40000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_631_8 :
    Uω (aρ 8) (bρ 8) (23435242683053 / 32000000000000 : ℝ) ≤
      (-(931469606699471203557 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25106948751277561 / 40000000000000000 : ℝ) ≤
      (-(931469606699471203557 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (25106948751277561 / 40000000000000000 : ℝ) =
            (25106948751277561 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (25106948751277561 / 20000000000000000 : ℝ) ≤
            (454824753900528796443 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3118275440884859 / 5000000000000000 : ℝ)) (q :=
      (25106948751277561 / 40000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_631_9 :
    Uω (aρ 9) (bρ 9) (23435242683053 / 32000000000000 : ℝ) ≤
      (-(5277699375886241265793 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4719352480403037 / 8000000000000000 : ℝ) ≤
      (-(5277699375886241265793 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (4719352480403037 / 8000000000000000 : ℝ) =
            (4719352480403037 / 4000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4719352480403037 / 4000000000000000 : ℝ) ≤
            (1653772427113758734207 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (582242333549853 / 1000000000000000 : ℝ)) (q :=
      (4719352480403037 / 8000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_631_10 :
    Uω (aρ 10) (bρ 10) (23435242683053 / 32000000000000 : ℝ) ≤
      (-(758864829476275798249 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (21797332289658697 / 40000000000000000 : ℝ) ≤
      (-(758864829476275798249 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (21797332289658697 / 40000000000000000 : ℝ) =
            (21797332289658697 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (21797332289658697 / 20000000000000000 : ℝ) ≤
            (107569145898724201751 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2655633656407643 / 5000000000000000 : ℝ)) (q :=
      (21797332289658697 / 40000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_631_11 :
    Uω (aρ 11) (bρ 11) (23435242683053 / 32000000000000 : ℝ) ≤
      (-(7064462222460948975133 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (19735779986684331 / 40000000000000000 : ℝ) ≤
      (-(7064462222460948975133 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (19735779986684331 / 40000000000000000 : ℝ) =
            (19735779986684331 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (19735779986684331 / 10000000000000000 : ℝ) ≤
            (6798481383539051024867 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4698967787533103 / 10000000000000000 : ℝ)) (q :=
      (19735779986684331 / 40000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_631_12 :
    Uω (aρ 12) (bρ 12) (23435242683053 / 32000000000000 : ℝ) ≤
      (-(8290235418091904679413 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (17459011117584283 / 40000000000000000 : ℝ) ≤
      (-(8290235418091904679413 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (17459011117584283 / 40000000000000000 : ℝ) =
            (17459011117584283 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (17459011117584283 / 10000000000000000 : ℝ) ≤
            (5572708187908095320587 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3984283449668079 / 10000000000000000 : ℝ)) (q :=
      (17459011117584283 / 40000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_631_13 :
    Uω (aρ 13) (bρ 13) (23435242683053 / 32000000000000 : ℝ) ≤
      (-(9792234836373217187103 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (15024105881875133 / 40000000000000000 : ℝ) ≤
      (-(9792234836373217187103 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (15024105881875133 / 40000000000000000 : ℝ) =
            (15024105881875133 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (15024105881875133 / 10000000000000000 : ℝ) ≤
            (4070708769626782812897 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (395776571676063 / 1250000000000000 : ℝ)) (q :=
      (15024105881875133 / 40000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_631_14 :
    Uω (aρ 14) (bρ 14) (23435242683053 / 32000000000000 : ℝ) ≤
      (-(2913809875003440331781 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12470370911958191 / 40000000000000000 : ℝ) ≤
      (-(2913809875003440331781 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (12470370911958191 / 40000000000000000 : ℝ) =
            (12470370911958191 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (12470370911958191 / 10000000000000000 : ℝ) ≤
            (551926026496559668219 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2233272373495033 / 10000000000000000 : ℝ)) (q :=
      (12470370911958191 / 40000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_631_15 :
    Uω (aρ 15) (bρ 15) (23435242683053 / 32000000000000 : ℝ) ≤
      (-(221974656099820521723 / 156250000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9662396035747569 / 40000000000000000 : ℝ) ≤
      (-(221974656099820521723 / 156250000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (9662396035747569 / 40000000000000000 : ℝ) =
            (9662396035747569 / 5000000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9662396035747569 / 5000000000000000 : ℝ) ≤
            (102938084665804478277 / 156250000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (544429106402361 / 5000000000000000 : ℝ)) (q :=
      (9662396035747569 / 40000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_631_16 :
    Uω (aρ 16) (bρ 16) (23435242683053 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_631 :
    Uρ (23435242683053 / 32000000000000 : ℝ) ≤
      (-(86538710522970460249 / 156250000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (23435242683053 / 32000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(3203438617965511292341 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_631_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (23435242683053 / 32000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(3236408458429937679207 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_631_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (23435242683053 / 32000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(132105782742592253447 / 400000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_631_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (23435242683053 / 32000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(3413533862948097198867 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_631_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (23435242683053 / 32000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(3584542308547022505337 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_631_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (23435242683053 / 32000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(3834410006823929320503 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_631_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (23435242683053 / 32000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(836869725883868706071 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_631_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (23435242683053 / 32000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(931469606699471203557 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_631_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (23435242683053 / 32000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(5277699375886241265793 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_631_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (23435242683053 / 32000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(758864829476275798249 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_631_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (23435242683053 / 32000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(7064462222460948975133 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_631_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (23435242683053 / 32000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(8290235418091904679413 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_631_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (23435242683053 / 32000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(9792234836373217187103 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_631_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (23435242683053 / 32000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(2913809875003440331781 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_631_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (23435242683053 / 32000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(221974656099820521723 / 156250000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_631_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (23435242683053 / 32000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_631_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_632_1 :
    Uω (aρ 1) (bρ 1) (2346571940161 / 3200000000000 : ℝ) ≤
      (-(1595163468387701664069 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14537035705420829 / 20000000000000000 : ℝ) ≤
      (-(1595163468387701664069 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (14537035705420829 / 20000000000000000 : ℝ) =
            (14537035705420829 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14537035705420829 / 10000000000000000 : ℝ) ≤
            (1870572433112298335931 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (454280975656419 / 625000000000000 : ℝ)) (q :=
      (14537035705420829 / 20000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_632_2 :
    Uω (aρ 2) (bρ 2) (2346571940161 / 3200000000000 : ℝ) ≤
      (-(3223253279550098399567 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (905578079884461 / 1250000000000000 : ℝ) ≤
      (-(3223253279550098399567 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (905578079884461 / 1250000000000000 : ℝ) =
            (905578079884461 / 625000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (905578079884461 / 625000000000000 : ℝ) ≤
            (3708218523449901600433 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7244478195743251 / 10000000000000000 : ℝ)) (q :=
      (905578079884461 / 1250000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_632_3 :
    Uω (aρ 3) (bρ 3) (2346571940161 / 3200000000000 : ℝ) ≤
      (-(3289401344986094540583 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14393721992791967 / 20000000000000000 : ℝ) ≤
      (-(3289401344986094540583 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (14393721992791967 / 20000000000000000 : ℝ) =
            (14393721992791967 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14393721992791967 / 10000000000000000 : ℝ) ≤
            (3642070458013905459417 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3598173508366921 / 5000000000000000 : ℝ)) (q :=
      (14393721992791967 / 20000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_632_4 :
    Uω (aρ 4) (bρ 4) (2346571940161 / 3200000000000 : ℝ) ≤
      (-(680028248331685089271 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (889700336858133 / 1250000000000000 : ℝ) ≤
      (-(680028248331685089271 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (889700336858133 / 1250000000000000 : ℝ) =
            (889700336858133 / 625000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (889700336858133 / 625000000000000 : ℝ) ≤
            (706266112268314910729 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7116124594737003 / 10000000000000000 : ℝ)) (q :=
      (889700336858133 / 1250000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_632_5 :
    Uω (aρ 5) (bρ 5) (2346571940161 / 3200000000000 : ℝ) ≤
      (-(1785457131865592913579 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6997085228157827 / 10000000000000000 : ℝ) ≤
      (-(1785457131865592913579 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (6997085228157827 / 10000000000000000 : ℝ) =
            (6997085228157827 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (6997085228157827 / 5000000000000000 : ℝ) ≤
            (1680278769634407086421 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6993279580657529 / 10000000000000000 : ℝ)) (q :=
      (6997085228157827 / 10000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_632_6 :
    Uω (aρ 6) (bρ 6) (2346571940161 / 3200000000000 : ℝ) ≤
      (-(1910213280704012408157 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3412329705219033 / 5000000000000000 : ℝ) ≤
      (-(1910213280704012408157 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (3412329705219033 / 5000000000000000 : ℝ) =
            (3412329705219033 / 2500000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3412329705219033 / 2500000000000000 : ℝ) ≤
            (1555522620795987591843 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6815668320358007 / 10000000000000000 : ℝ)) (q :=
      (3412329705219033 / 5000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_632_7 :
    Uω (aρ 7) (bρ 7) (2346571940161 / 3200000000000 : ℝ) ≤
      (-(4169843297918505665339 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13180624936974249 / 20000000000000000 : ℝ) ≤
      (-(4169843297918505665339 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (13180624936974249 / 20000000000000000 : ℝ) =
            (13180624936974249 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (13180624936974249 / 10000000000000000 : ℝ) ≤
            (2761628505081494334661 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1642658954304031 / 2500000000000000 : ℝ)) (q :=
      (13180624936974249 / 20000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_632_8 :
    Uω (aρ 8) (bρ 8) (2346571940161 / 3200000000000 : ℝ) ≤
      (-(2321044305584939681371 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (157158060939673 / 250000000000000 : ℝ) ≤
      (-(2321044305584939681371 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (157158060939673 / 250000000000000 : ℝ) =
            (157158060939673 / 125000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (157158060939673 / 125000000000000 : ℝ) ≤
            (1144691595915060318629 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1249239481351143 / 2000000000000000 : ℝ)) (q :=
      (157158060939673 / 250000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_632_9 :
    Uω (aρ 9) (bρ 9) (2346571940161 / 3200000000000 : ℝ) ≤
      (-(5261355684633632966319 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (11817679877255061 / 20000000000000000 : ℝ) ≤
      (-(5261355684633632966319 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (11817679877255061 / 20000000000000000 : ℝ) =
            (11817679877255061 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (11817679877255061 / 10000000000000000 : ℝ) ≤
            (1670116118366367033681 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (729024754649617 / 1250000000000000 : ℝ)) (q :=
      (11817679877255061 / 20000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_632_10 :
    Uω (aρ 10) (bρ 10) (2346571940161 / 3200000000000 : ℝ) ≤
      (-(6053003884311726330449 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10918208333840763 / 20000000000000000 : ℝ) ≤
      (-(6053003884311726330449 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (10918208333840763 / 20000000000000000 : ℝ) =
            (10918208333840763 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (10918208333840763 / 10000000000000000 : ℝ) ≤
            (878467918688273669551 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2660642763638819 / 5000000000000000 : ℝ)) (q :=
      (10918208333840763 / 20000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_632_11 :
    Uω (aρ 11) (bρ 11) (2346571940161 / 3200000000000 : ℝ) ≤
      (-(7044216553404438458349 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1977577686822209 / 4000000000000000 : ℝ) ≤
      (-(7044216553404438458349 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (1977577686822209 / 4000000000000000 : ℝ) =
            (1977577686822209 / 1000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1977577686822209 / 1000000000000000 : ℝ) ≤
            (6818727052595561541651 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (117736056343823 / 250000000000000 : ℝ)) (q :=
      (1977577686822209 / 4000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_632_12 :
    Uω (aρ 12) (bρ 12) (2346571940161 / 3200000000000 : ℝ) ≤
      (-(4133182756188624599249 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8750367695210443 / 20000000000000000 : ℝ) ≤
      (-(4133182756188624599249 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (8750367695210443 / 20000000000000000 : ℝ) =
            (8750367695210443 / 5000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (8750367695210443 / 5000000000000000 : ℝ) ≤
            (2798289046811375400751 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1997810805768659 / 5000000000000000 : ℝ)) (q :=
      (8750367695210443 / 20000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_632_13 :
    Uω (aρ 13) (bρ 13) (2346571940161 / 3200000000000 : ℝ) ≤
      (-(9762216699229738464429 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7534636603494341 / 20000000000000000 : ℝ) ≤
      (-(9762216699229738464429 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (7534636603494341 / 20000000000000000 : ℝ) =
            (7534636603494341 / 5000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7534636603494341 / 5000000000000000 : ℝ) ≤
            (4100726906770261535571 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (397409032677027 / 1250000000000000 : ℝ)) (q :=
      (7534636603494341 / 20000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_632_14 :
    Uω (aρ 14) (bρ 14) (2346571940161 / 3200000000000 : ℝ) ≤
      (-(11612755515422022468479 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (6261731357118699 / 20000000000000000 : ℝ) ≤
      (-(11612755515422022468479 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (6261731357118699 / 20000000000000000 : ℝ) =
            (6261731357118699 / 5000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (6261731357118699 / 5000000000000000 : ℝ) ≤
            (2250188090577977531521 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1125147150042787 / 5000000000000000 : ℝ)) (q :=
      (6261731357118699 / 20000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_632_15 :
    Uω (aρ 15) (bρ 15) (2346571940161 / 3200000000000 : ℝ) ≤
      (-(2824037625449027245121 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2436509005779369 / 10000000000000000 : ℝ) ≤
      (-(2824037625449027245121 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (2436509005779369 / 10000000000000000 : ℝ) =
            (2436509005779369 / 1250000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2436509005779369 / 1250000000000000 : ℝ) ≤
            (1334845456350972754879 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1121154231940613 / 10000000000000000 : ℝ)) (q :=
      (2436509005779369 / 10000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_632_16 :
    Uω (aρ 16) (bρ 16) (2346571940161 / 3200000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_632 :
    Uρ (2346571940161 / 3200000000000 : ℝ) ≤
      (-(5519450151378080841463 / 10000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (2346571940161 / 3200000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(1595163468387701664069 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_632_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (2346571940161 / 3200000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(3223253279550098399567 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_632_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (2346571940161 / 3200000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(3289401344986094540583 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_632_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (2346571940161 / 3200000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(680028248331685089271 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_632_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (2346571940161 / 3200000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(1785457131865592913579 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_632_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (2346571940161 / 3200000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(1910213280704012408157 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_632_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (2346571940161 / 3200000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(4169843297918505665339 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_632_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (2346571940161 / 3200000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(2321044305584939681371 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_632_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (2346571940161 / 3200000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(5261355684633632966319 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_632_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (2346571940161 / 3200000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(6053003884311726330449 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_632_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (2346571940161 / 3200000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(7044216553404438458349 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_632_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (2346571940161 / 3200000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(4133182756188624599249 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_632_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (2346571940161 / 3200000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(9762216699229738464429 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_632_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (2346571940161 / 3200000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(11612755515422022468479 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_632_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (2346571940161 / 3200000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(2824037625449027245121 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_632_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (2346571940161 / 3200000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_632_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_633_1 :
    Uω (aρ 1) (bρ 1) (23496196120167 / 32000000000000 : ℝ) ≤
      (-(1588616212399733649147 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (29112167425462007 / 40000000000000000 : ℝ) ≤
      (-(1588616212399733649147 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (29112167425462007 / 40000000000000000 : ℝ) =
            (29112167425462007 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (29112167425462007 / 20000000000000000 : ℝ) ≤
            (1877119689100266350853 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (909752455407977 / 1250000000000000 : ℝ)) (q :=
      (29112167425462007 / 40000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_633_2 :
    Uω (aρ 2) (bρ 2) (23496196120167 / 32000000000000 : ℝ) ≤
      (-(3210115384507427481169 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (29016595223576541 / 40000000000000000 : ℝ) ≤
      (-(3210115384507427481169 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (29016595223576541 / 40000000000000000 : ℝ) =
            (29016595223576541 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (29016595223576541 / 20000000000000000 : ℝ) ≤
            (3721356418492572518831 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7254002554831083 / 10000000000000000 : ℝ)) (q :=
      (29016595223576541 / 40000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_633_3 :
    Uω (aρ 3) (bρ 3) (23496196120167 / 32000000000000 : ℝ) ≤
      (-(131047025560400143257 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28825542601080433 / 40000000000000000 : ℝ) ≤
      (-(131047025560400143257 / 400000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (28825542601080433 / 40000000000000000 : ℝ) =
            (28825542601080433 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (28825542601080433 / 20000000000000000 : ℝ) ≤
            (146211846559599856743 / 400000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7205872349933029 / 10000000000000000 : ℝ)) (q :=
      (28825542601080433 / 40000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_633_4 :
    Uω (aρ 4) (bρ 4) (23496196120167 / 32000000000000 : ℝ) ≤
      (-(846691635010987255199 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28508514580030001 / 40000000000000000 : ℝ) ≤
      (-(846691635010987255199 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (28508514580030001 / 40000000000000000 : ℝ) =
            (28508514580030001 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (28508514580030001 / 20000000000000000 : ℝ) ≤
            (886176315739012744801 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7125652520472813 / 10000000000000000 : ℝ)) (q :=
      (28508514580030001 / 40000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_633_5 :
    Uω (aρ 5) (bρ 5) (23496196120167 / 32000000000000 : ℝ) ≤
      (-(3557304786161391909607 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28026457513886189 / 40000000000000000 : ℝ) ≤
      (-(3557304786161391909607 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (28026457513886189 / 40000000000000000 : ℝ) =
            (28026457513886189 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (28026457513886189 / 20000000000000000 : ℝ) ≤
            (3374167016838608090393 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7002813906735907 / 10000000000000000 : ℝ)) (q :=
      (28026457513886189 / 40000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_633_6 :
    Uω (aρ 6) (bρ 6) (23496196120167 / 32000000000000 : ℝ) ≤
      (-(3806462693810826226399 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27336783725058021 / 40000000000000000 : ℝ) ≤
      (-(3806462693810826226399 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (27336783725058021 / 40000000000000000 : ℝ) =
            (27336783725058021 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (27336783725058021 / 20000000000000000 : ℝ) ≤
            (3125009109189173773601 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6825217387461823 / 10000000000000000 : ℝ)) (q :=
      (27336783725058021 / 40000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_633_7 :
    Uω (aρ 7) (bρ 7) (23496196120167 / 32000000000000 : ℝ) ≤
      (-(2077679551030624965963 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (26399459689812871 / 40000000000000000 : ℝ) ≤
      (-(2077679551030624965963 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (26399459689812871 / 40000000000000000 : ℝ) =
            (26399459689812871 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (26399459689812871 / 20000000000000000 : ℝ) ≤
            (1388056350469375034037 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (411263546912453 / 625000000000000 : ℝ)) (q :=
      (26399459689812871 / 40000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_633_8 :
    Uω (aρ 8) (bρ 8) (23496196120167 / 32000000000000 : ℝ) ≤
      (-(4626852736612063300721 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25183629998327079 / 40000000000000000 : ℝ) ≤
      (-(4626852736612063300721 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (25183629998327079 / 40000000000000000 : ℝ) =
            (25183629998327079 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (25183629998327079 / 20000000000000000 : ℝ) ≤
            (2304619066387936699279 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (95456597232 / 152587890625 : ℝ)) (q :=
      (25183629998327079 / 40000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_633_9 :
    Uω (aρ 9) (bρ 9) (23496196120167 / 32000000000000 : ℝ) ≤
      (-(5245039361152753413503 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (23673955450474761 / 40000000000000000 : ℝ) ≤
      (-(5245039361152753413503 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (23673955450474761 / 40000000000000000 : ℝ) =
            (23673955450474761 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (23673955450474761 / 20000000000000000 : ℝ) ≤
            (1686432441847246586497 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (5841971910630193 / 10000000000000000 : ℝ)) (q :=
      (23673955450474761 / 40000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_633_10 :
    Uω (aρ 10) (bρ 10) (23496196120167 / 32000000000000 : ℝ) ≤
      (-(1508780706400550594719 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (21875497422376211 / 40000000000000000 : ℝ) ≤
      (-(1508780706400550594719 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (21875497422376211 / 40000000000000000 : ℝ) =
            (21875497422376211 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (21875497422376211 / 20000000000000000 : ℝ) ≤
            (224087244349449405281 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2665650965037959 / 5000000000000000 : ℝ)) (q :=
      (21875497422376211 / 40000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_633_11 :
    Uω (aρ 11) (bρ 11) (23496196120167 / 32000000000000 : ℝ) ≤
      (-(219500495467645514591 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (19815765695228119 / 40000000000000000 : ℝ) ≤
      (-(219500495467645514591 / 312500000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (19815765695228119 / 40000000000000000 : ℝ) =
            (19815765695228119 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (19815765695228119 / 10000000000000000 : ℝ) ≤
            (213716492219854485409 / 312500000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (589989086588359 / 1250000000000000 : ℝ)) (q :=
      (19815765695228119 / 40000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_633_12 :
    Uω (aρ 12) (bρ 12) (23496196120167 / 32000000000000 : ℝ) ≤
      (-(1030320402127628943133 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3508488154438577 / 8000000000000000 : ℝ) ≤
      (-(1030320402127628943133 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (3508488154438577 / 8000000000000000 : ℝ) =
            (3508488154438577 / 2000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3508488154438577 / 2000000000000000 : ℝ) ≤
            (702547548622371056867 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (801390065574851 / 2000000000000000 : ℝ)) (q :=
      (3508488154438577 / 8000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_633_13 :
    Uω (aρ 13) (bρ 13) (23496196120167 / 32000000000000 : ℝ) ≤
      (-(304135046858737321201 / 312500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3022878101236307 / 8000000000000000 : ℝ) ≤
      (-(304135046858737321201 / 312500000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (3022878101236307 / 8000000000000000 : ℝ) =
            (3022878101236307 / 2000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3022878101236307 / 2000000000000000 : ℝ) ≤
            (129081940828762678799 / 312500000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (159615346823179 / 500000000000000 : ℝ)) (q :=
      (3022878101236307 / 8000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_633_14 :
    Uω (aρ 14) (bρ 14) (23496196120167 / 32000000000000 : ℝ) ≤
      (-(11570590863640125216681 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12576378939996057 / 40000000000000000 : ℝ) ≤
      (-(11570590863640125216681 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (12576378939996057 / 40000000000000000 : ℝ) =
            (12576378939996057 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (12576378939996057 / 10000000000000000 : ℝ) ≤
            (2292352742359874783319 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2267228438415841 / 10000000000000000 : ℝ)) (q :=
      (12576378939996057 / 40000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_633_15 :
    Uω (aρ 15) (bρ 15) (23496196120167 / 32000000000000 : ℝ) ≤
      (-(7018207705648636198711 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9828024152786267 / 40000000000000000 : ℝ) ≤
      (-(7018207705648636198711 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (9828024152786267 / 40000000000000000 : ℝ) =
            (9828024152786267 / 5000000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9828024152786267 / 5000000000000000 : ℝ) ≤
            (3378999998851363801289 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (576312161112973 / 5000000000000000 : ℝ)) (q :=
      (9828024152786267 / 40000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_633_16 :
    Uω (aρ 16) (bρ 16) (23496196120167 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_633 :
    Uρ (23496196120167 / 32000000000000 : ℝ) ≤
      (-(5500540668506838355503 / 10000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (23496196120167 / 32000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(1588616212399733649147 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_633_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (23496196120167 / 32000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(3210115384507427481169 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_633_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (23496196120167 / 32000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(131047025560400143257 / 400000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_633_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (23496196120167 / 32000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(846691635010987255199 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_633_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (23496196120167 / 32000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(3557304786161391909607 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_633_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (23496196120167 / 32000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(3806462693810826226399 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_633_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (23496196120167 / 32000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(2077679551030624965963 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_633_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (23496196120167 / 32000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(4626852736612063300721 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_633_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (23496196120167 / 32000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(5245039361152753413503 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_633_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (23496196120167 / 32000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(1508780706400550594719 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_633_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (23496196120167 / 32000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) * (-(219500495467645514591 / 312500000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_633_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (23496196120167 / 32000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(1030320402127628943133 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_633_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (23496196120167 / 32000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) * (-(304135046858737321201 / 312500000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_633_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (23496196120167 / 32000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(11570590863640125216681 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_633_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (23496196120167 / 32000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(7018207705648636198711 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_633_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (23496196120167 / 32000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_633_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_634_1 :
    Uω (aρ 1) (bρ 1) (5881668209681 / 8000000000000 : ℝ) ≤
      (-(3164155037131447097627 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (583005268795561 / 800000000000000 : ℝ) ≤
      (-(3164155037131447097627 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (583005268795561 / 800000000000000 : ℝ) =
            (583005268795561 / 400000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (583005268795561 / 400000000000000 : ℝ) ≤
            (3767316765868552902373 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (291501747034911 / 400000000000000 : ℝ)) (q :=
      (583005268795561 / 800000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_634_2 :
    Uω (aρ 2) (bρ 2) (5881668209681 / 8000000000000 : ℝ) ≤
      (-(3196994727943193935909 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7263672972208363 / 10000000000000000 : ℝ) ≤
      (-(3196994727943193935909 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (7263672972208363 / 10000000000000000 : ℝ) =
            (7263672972208363 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7263672972208363 / 5000000000000000 : ℝ) ≤
            (3734477075056806064091 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1815881728227619 / 2500000000000000 : ℝ)) (q :=
      (7263672972208363 / 10000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_634_3 :
    Uω (aρ 3) (bρ 3) (5881668209681 / 8000000000000 : ℝ) ≤
      (-(163148370217400263421 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7215910302350753 / 10000000000000000 : ℝ) ≤
      (-(163148370217400263421 / 500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (7215910302350753 / 10000000000000000 : ℝ) =
            (7215910302350753 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7215910302350753 / 5000000000000000 : ℝ) ≤
            (183425219932599736579 / 500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (901924709943157 / 1250000000000000 : ℝ)) (q :=
      (7215910302350753 / 10000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_634_4 :
    Uω (aρ 4) (bρ 4) (5881668209681 / 8000000000000 : ℝ) ≤
      (-(3373409710194953931207 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14273309179749669 / 20000000000000000 : ℝ) ≤
      (-(3373409710194953931207 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (14273309179749669 / 20000000000000000 : ℝ) =
            (14273309179749669 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14273309179749669 / 10000000000000000 : ℝ) ≤
            (3558062092805046068793 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7135180435658419 / 10000000000000000 : ℝ)) (q :=
      (14273309179749669 / 20000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_634_5 :
    Uω (aρ 5) (bρ 5) (5881668209681 / 8000000000000 : ℝ) ≤
      (-(3543713825258676462001 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7016143514718471 / 10000000000000000 : ℝ) ≤
      (-(3543713825258676462001 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (7016143514718471 / 10000000000000000 : ℝ) =
            (7016143514718471 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7016143514718471 / 5000000000000000 : ℝ) ≤
            (3387757977741323537999 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1753087051170173 / 2500000000000000 : ℝ)) (q :=
      (7016143514718471 / 10000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_634_6 :
    Uω (aρ 6) (bρ 6) (5881668209681 / 8000000000000 : ℝ) ≤
      (-(3792518349145028688873 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13687464834158817 / 20000000000000000 : ℝ) ≤
      (-(3792518349145028688873 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (13687464834158817 / 20000000000000000 : ℝ) =
            (13687464834158817 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (13687464834158817 / 10000000000000000 : ℝ) ≤
            (3138953453854971311127 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6834766384542567 / 10000000000000000 : ℝ)) (q :=
      (13687464834158817 / 20000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_634_7 :
    Uω (aρ 7) (bρ 7) (5881668209681 / 8000000000000 : ℝ) ≤
      (-(1035223994995105045411 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13218834587705587 / 20000000000000000 : ℝ) ≤
      (-(1035223994995105045411 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (13218834587705587 / 20000000000000000 : ℝ) =
            (13218834587705587 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (13218834587705587 / 10000000000000000 : ℝ) ≤
            (697643955754894954589 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6589797518849337 / 10000000000000000 : ℝ)) (q :=
      (13218834587705587 / 20000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_634_8 :
    Uω (aρ 8) (bρ 8) (5881668209681 / 8000000000000 : ℝ) ≤
      (-(4611640336349390814731 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3152746187335603 / 5000000000000000 : ℝ) ≤
      (-(4611640336349390814731 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (3152746187335603 / 5000000000000000 : ℝ) =
            (3152746187335603 / 2500000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3152746187335603 / 2500000000000000 : ℝ) ≤
            (2319831466650609185269 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3132744665913081 / 5000000000000000 : ℝ)) (q :=
      (3152746187335603 / 5000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_634_9 :
    Uω (aρ 9) (bρ 9) (5881668209681 / 8000000000000 : ℝ) ≤
      (-(5228750311639540664367 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5928137374552389 / 10000000000000000 : ℝ) ≤
      (-(5228750311639540664367 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (5928137374552389 / 10000000000000000 : ℝ) =
            (5928137374552389 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5928137374552389 / 5000000000000000 : ℝ) ≤
            (1702721491360459335633 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (365734059996783 / 625000000000000 : ℝ)) (q :=
      (5928137374552389 / 10000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_634_10 :
    Uω (aρ 10) (bρ 10) (5881668209681 / 8000000000000 : ℝ) ≤
      (-(6017275327143369276991 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5478643643531723 / 10000000000000000 : ℝ) ≤
      (-(6017275327143369276991 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (5478643643531723 / 10000000000000000 : ℝ) =
            (5478643643531723 / 5000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5478643643531723 / 5000000000000000 : ℝ) ≤
            (914196475856630723009 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1335329132850549 / 2500000000000000 : ℝ)) (q :=
      (5478643643531723 / 10000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_634_11 :
    Uω (aρ 11) (bρ 11) (5881668209681 / 8000000000000 : ℝ) ≤
      (-(437741244417544630727 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (620492078787101 / 1250000000000000 : ℝ) ≤
      (-(437741244417544630727 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (620492078787101 / 1250000000000000 : ℝ) =
            (620492078787101 / 312500000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (620492078787101 / 312500000000000 : ℝ) ≤
            (428692730957455369273 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2365189565568683 / 5000000000000000 : ℝ)) (q :=
      (620492078787101 / 1250000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11]) (by norm_num [bρ_11])
      (by norm_num) (by norm_num [aρ_11, bρ_11]) (by norm_num [aρ_11, bρ_11]) hlg

lemma U_634_12 :
    Uω (aρ 12) (bρ 12) (5881668209681 / 8000000000000 : ℝ) ≤
      (-(4109414047231730727419 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (8792063711339569 / 20000000000000000 : ℝ) ≤
      (-(4109414047231730727419 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (8792063711339569 / 20000000000000000 : ℝ) =
            (8792063711339569 / 5000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (8792063711339569 / 5000000000000000 : ℝ) ≤
            (2822057755768269272581 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4018269678568319 / 10000000000000000 : ℝ)) (q :=
      (8792063711339569 / 20000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_634_13 :
    Uω (aρ 13) (bρ 13) (5881668209681 / 8000000000000 : ℝ) ≤
      (-(1940509600574714462243 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1894932298719603 / 5000000000000000 : ℝ) ≤
      (-(1940509600574714462243 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (1894932298719603 / 5000000000000000 : ℝ) =
            (1894932298719603 / 1250000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1894932298719603 / 1250000000000000 : ℝ) ≤
            (832079120625285537757 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1602658451851081 / 5000000000000000 : ℝ)) (q :=
      (1894932298719603 / 5000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_634_14 :
    Uω (aρ 14) (bρ 14) (5881668209681 / 8000000000000 : ℝ) ≤
      (-(90068274870373059033 / 78125000000000000000 : ℝ)) := by
  have hlg :
    Real.log (157864043680091 / 500000000000000 : ℝ) ≤
      (-(90068274870373059033 / 78125000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (157864043680091 / 500000000000000 : ℝ) =
            (157864043680091 / 125000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (157864043680091 / 125000000000000 : ℝ) ≤
            (18235972051501940967 / 78125000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (228407674107239 / 1000000000000000 : ℝ)) (q :=
      (157864043680091 / 500000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14]) (by norm_num [bρ_14])
      (by norm_num) (by norm_num [aρ_14, bρ_14]) (by norm_num [aρ_14, bρ_14]) hlg

lemma U_634_15 :
    Uω (aρ 15) (bρ 15) (5881668209681 / 8000000000000 : ℝ) ≤
      (-(13954872639935423773157 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2477123054752717 / 10000000000000000 : ℝ) ≤
      (-(13954872639935423773157 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (2477123054752717 / 10000000000000000 : ℝ) =
            (2477123054752717 / 1250000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2477123054752717 / 1250000000000000 : ℝ) ≤
            (6839542769064576226843 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (18489599699831 / 156250000000000 : ℝ)) (q :=
      (2477123054752717 / 10000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_634_16 :
    Uω (aρ 16) (bρ 16) (5881668209681 / 8000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_634 :
    Uρ (5881668209681 / 8000000000000 : ℝ) ≤
      (-(2740871436653137694881 / 5000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (5881668209681 / 8000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(3164155037131447097627 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_634_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (5881668209681 / 8000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(3196994727943193935909 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_634_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (5881668209681 / 8000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(163148370217400263421 / 500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_634_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (5881668209681 / 8000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(3373409710194953931207 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_634_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (5881668209681 / 8000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(3543713825258676462001 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_634_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (5881668209681 / 8000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(3792518349145028688873 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_634_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (5881668209681 / 8000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(1035223994995105045411 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_634_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (5881668209681 / 8000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(4611640336349390814731 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_634_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (5881668209681 / 8000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(5228750311639540664367 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_634_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (5881668209681 / 8000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(6017275327143369276991 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_634_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (5881668209681 / 8000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) * (-(437741244417544630727 / 625000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_634_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (5881668209681 / 8000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(4109414047231730727419 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_634_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (5881668209681 / 8000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(1940509600574714462243 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_634_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (5881668209681 / 8000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) * (-(90068274870373059033 / 78125000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_634_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (5881668209681 / 8000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(13954872639935423773157 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_634_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (5881668209681 / 8000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_634_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_635_1 :
    Uω (aρ 1) (bρ 1) (23557149557281 / 32000000000000 : ℝ) ≤
      (-(630218945808207475073 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (29188359453790979 / 40000000000000000 : ℝ) ≤
      (-(630218945808207475073 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (29188359453790979 / 40000000000000000 : ℝ) =
            (29188359453790979 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (29188359453790979 / 20000000000000000 : ℝ) ≤
            (756075414791792524927 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7297067708330177 / 10000000000000000 : ℝ)) (q :=
      (29188359453790979 / 40000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_635_2 :
    Uω (aρ 2) (bρ 2) (23557149557281 / 32000000000000 : ℝ) ≤
      (-(636778252935398947851 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (29092788552081409 / 40000000000000000 : ℝ) ≤
      (-(636778252935398947851 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (29092788552081409 / 40000000000000000 : ℝ) =
            (29092788552081409 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (29092788552081409 / 20000000000000000 : ℝ) ≤
            (749516107664601052149 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (454565704374087 / 625000000000000 : ℝ)) (q :=
      (29092788552081409 / 40000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_635_3 :
    Uω (aρ 3) (bρ 3) (23557149557281 / 32000000000000 : ℝ) ≤
      (-(649955318978965030579 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28901739810580043 / 40000000000000000 : ℝ) ≤
      (-(649955318978965030579 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (28901739810580043 / 40000000000000000 : ℝ) =
            (28901739810580043 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (28901739810580043 / 20000000000000000 : ℝ) ≤
            (736339041621034969421 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7224923005584709 / 10000000000000000 : ℝ)) (q :=
      (28901739810580043 / 40000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_635_4 :
    Uω (aρ 4) (bρ 4) (23557149557281 / 32000000000000 : ℝ) ≤
      (-(672014140878737271299 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28584722117952679 / 40000000000000000 : ℝ) ≤
      (-(672014140878737271299 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (28584722117952679 / 40000000000000000 : ℝ) =
            (28584722117952679 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (28584722117952679 / 20000000000000000 : ℝ) ≤
            (714280219721262728701 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7144708340336027 / 10000000000000000 : ℝ)) (q :=
      (28584722117952679 / 40000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_635_5 :
    Uω (aρ 5) (bρ 5) (23557149557281 / 32000000000000 : ℝ) ≤
      (-(882535332662672776061 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28102690547823587 / 40000000000000000 : ℝ) ≤
      (-(882535332662672776061 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (28102690547823587 / 40000000000000000 : ℝ) =
            (28102690547823587 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (28102690547823587 / 20000000000000000 : ℝ) ≤
            (850332618087327223939 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7021882474606481 / 10000000000000000 : ℝ)) (q :=
      (28102690547823587 / 40000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_635_6 :
    Uω (aρ 6) (bρ 6) (23557149557281 / 32000000000000 : ℝ) ≤
      (-(1889296736377210212201 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27413075472117267 / 40000000000000000 : ℝ) ≤
      (-(1889296736377210212201 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (27413075472117267 / 40000000000000000 : ℝ) =
            (27413075472117267 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (27413075472117267 / 20000000000000000 : ℝ) ≤
            (1576439165122789787799 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6844315311893321 / 10000000000000000 : ℝ)) (q :=
      (27413075472117267 / 40000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_635_7 :
    Uω (aρ 7) (bρ 7) (23557149557281 / 32000000000000 : ℝ) ≤
      (-(82529077401633511151 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5295175666436363 / 8000000000000000 : ℝ) ≤
      (-(82529077401633511151 / 200000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (5295175666436363 / 8000000000000000 : ℝ) =
            (5295175666436363 / 4000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5295175666436363 / 4000000000000000 : ℝ) ≤
            (56100358658366488849 / 200000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1319875624537119 / 2000000000000000 : ℝ)) (q :=
      (5295175666436363 / 8000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_635_8 :
    Uω (aρ 8) (bρ 8) (23557149557281 / 32000000000000 : ℝ) ≤
      (-(1149112834313707893071 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25260308254868517 / 40000000000000000 : ℝ) ≤
      (-(1149112834313707893071 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (25260308254868517 / 40000000000000000 : ℝ) =
            (25260308254868517 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (25260308254868517 / 20000000000000000 : ℝ) ≤
            (583755116436292106929 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3137567367684473 / 5000000000000000 : ℝ)) (q :=
      (25260308254868517 / 40000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_635_9 :
    Uω (aρ 9) (bρ 9) (23557149557281 / 32000000000000 : ℝ) ≤
      (-(2606244221391287807851 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (23751141905958909 / 40000000000000000 : ℝ) ≤
      (-(2606244221391287807851 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (23751141905958909 / 40000000000000000 : ℝ) =
            (23751141905958909 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (23751141905958909 / 20000000000000000 : ℝ) ≤
            (859491680108712192149 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2930758594637071 / 5000000000000000 : ℝ)) (q :=
      (23751141905958909 / 40000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_635_10 :
    Uω (aρ 10) (bρ 10) (23557149557281 / 32000000000000 : ℝ) ≤
      (-(1499865314302420498799 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (21953648143161469 / 40000000000000000 : ℝ) ≤
      (-(1499865314302420498799 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (21953648143161469 / 40000000000000000 : ℝ) =
            (21953648143161469 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (21953648143161469 / 20000000000000000 : ℝ) ≤
            (233002636447579501201 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2675664670685211 / 5000000000000000 : ℝ)) (q :=
      (21953648143161469 / 40000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_635_11 :
    Uω (aρ 11) (bρ 11) (23557149557281 / 32000000000000 : ℝ) ≤
      (-(6983748505754081904723 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3979143879818317 / 8000000000000000 : ℝ) ≤
      (-(6983748505754081904723 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (3979143879818317 / 8000000000000000 : ℝ) =
            (3979143879818317 / 2000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3979143879818317 / 2000000000000000 : ℝ) ≤
            (6879195100245918095277 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (925945624129 / 1953125000000 : ℝ)) (q :=
      (3979143879818317 / 8000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_635_12 :
    Uω (aρ 12) (bρ 12) (23557149557281 / 32000000000000 : ℝ) ≤
      (-(1639031942355393550651 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (17625795499731837 / 40000000000000000 : ℝ) ≤
      (-(1639031942355393550651 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (17625795499731837 / 40000000000000000 : ℝ) =
            (17625795499731837 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 12
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (17625795499731837 / 10000000000000000 : ℝ) ≤
            (1133556778844606449349 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2014789871272803 / 5000000000000000 : ℝ)) (q :=
      (17625795499731837 / 40000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_635_13 :
    Uω (aρ 13) (bρ 13) (23557149557281 / 32000000000000 : ℝ) ≤
      (-(4836447497896644797437 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3040895491400307 / 8000000000000000 : ℝ) ≤
      (-(4836447497896644797437 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (3040895491400307 / 8000000000000000 : ℝ) =
            (3040895491400307 / 2000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3040895491400307 / 2000000000000000 : ℝ) ≤
            (2095024305103355202563 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (643660492555091 / 2000000000000000 : ℝ)) (q :=
      (3040895491400307 / 8000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_635_14 :
    Uω (aρ 14) (bρ 14) (23557149557281 / 32000000000000 : ℝ) ≤
      (-(11487194324412495821493 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12681700148751069 / 40000000000000000 : ℝ) ≤
      (-(11487194324412495821493 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (12681700148751069 / 40000000000000000 : ℝ) =
            (12681700148751069 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (12681700148751069 / 10000000000000000 : ℝ) ≤
            (2375749281587504178507 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1150420546847611 / 5000000000000000 : ℝ)) (q :=
      (12681700148751069 / 40000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_635_15 :
    Uω (aρ 15) (bρ 15) (23557149557281 / 32000000000000 : ℝ) ≤
      (-(346884892714684572593 / 250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9987555644342411 / 40000000000000000 : ℝ) ≤
      (-(346884892714684572593 / 250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 3
        (show
          (9987555644342411 / 40000000000000000 : ℝ) =
            (9987555644342411 / 5000000000000000 : ℝ) / 2 ^ 3
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 15
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9987555644342411 / 5000000000000000 : ℝ) ≤
            (172975492510315427407 / 250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1213342118905893 / 10000000000000000 : ℝ)) (q :=
      (9987555644342411 / 40000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_635_16 :
    Uω (aρ 16) (bρ 16) (23557149557281 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_635 :
    Uρ (23557149557281 / 32000000000000 : ℝ) ≤
      (-(109261026582514005137 / 200000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (23557149557281 / 32000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(630218945808207475073 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_635_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (23557149557281 / 32000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(636778252935398947851 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_635_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (23557149557281 / 32000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(649955318978965030579 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_635_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (23557149557281 / 32000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(672014140878737271299 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_635_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (23557149557281 / 32000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) * (-(882535332662672776061 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_635_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (23557149557281 / 32000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(1889296736377210212201 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_635_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (23557149557281 / 32000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) * (-(82529077401633511151 / 200000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_635_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (23557149557281 / 32000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(1149112834313707893071 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_635_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (23557149557281 / 32000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(2606244221391287807851 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_635_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (23557149557281 / 32000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(1499865314302420498799 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_635_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (23557149557281 / 32000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(6983748505754081904723 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_635_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (23557149557281 / 32000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(1639031942355393550651 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_635_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (23557149557281 / 32000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(4836447497896644797437 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_635_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (23557149557281 / 32000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(11487194324412495821493 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_635_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (23557149557281 / 32000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(346884892714684572593 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_635_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (23557149557281 / 32000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_635_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_636_1 :
    Uω (aρ 1) (bρ 1) (11793813137919 / 16000000000000 : ℝ) ≤
      (-(627610291194593107191 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14613227733750989 / 20000000000000000 : ℝ) ≤
      (-(627610291194593107191 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (14613227733750989 / 20000000000000000 : ℝ) =
            (14613227733750989 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14613227733750989 / 10000000000000000 : ℝ) ≤
            (758684069405406892809 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3653295870318307 / 5000000000000000 : ℝ)) (q :=
      (14613227733750989 / 20000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_636_2 :
    Uω (aρ 2) (bρ 2) (11793813137919 / 16000000000000 : ℝ) ≤
      (-(634160989941164399659 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14565442606664147 / 20000000000000000 : ℝ) ≤
      (-(634160989941164399659 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (14565442606664147 / 20000000000000000 : ℝ) =
            (14565442606664147 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14565442606664147 / 10000000000000000 : ℝ) ≤
            (752133370658835600341 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1820643906514943 / 2500000000000000 : ℝ)) (q :=
      (14565442606664147 / 20000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_636_3 :
    Uω (aρ 3) (bρ 3) (11793813137919 / 16000000000000 : ℝ) ≤
      (-(1618301582363736978203 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14469919202319877 / 20000000000000000 : ℝ) ≤
      (-(1618301582363736978203 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (14469919202319877 / 20000000000000000 : ℝ) =
            (14469919202319877 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14469919202319877 / 10000000000000000 : ℝ) ≤
            (1847434319136263021797 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3617224164032751 / 5000000000000000 : ℝ)) (q :=
      (14469919202319877 / 20000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_636_4 :
    Uω (aρ 4) (bρ 4) (11793813137919 / 16000000000000 : ℝ) ≤
      (-(1673374737556661780137 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14311412927736997 / 20000000000000000 : ℝ) ≤
      (-(1673374737556661780137 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (14311412927736997 / 20000000000000000 : ℝ) =
            (14311412927736997 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14311412927736997 / 10000000000000000 : ℝ) ≤
            (1792361163943338219863 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3577118117273811 / 5000000000000000 : ℝ)) (q :=
      (14311412927736997 / 20000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_636_5 :
    Uω (aρ 5) (bρ 5) (11793813137919 / 16000000000000 : ℝ) ≤
      (-(3516587252170573535409 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (3517600872620407 / 5000000000000000 : ℝ) ≤
      (-(3516587252170573535409 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (3517600872620407 / 5000000000000000 : ℝ) =
            (3517600872620407 / 2500000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (3517600872620407 / 2500000000000000 : ℝ) ≤
            (3414884550829426464591 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7031416716627253 / 10000000000000000 : ℝ)) (q :=
      (3517600872620407 / 5000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_636_6 :
    Uω (aρ 6) (bρ 6) (11793813137919 / 16000000000000 : ℝ) ≤
      (-(470586001276572675323 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13725610568519909 / 20000000000000000 : ℝ) ≤
      (-(470586001276572675323 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (13725610568519909 / 20000000000000000 : ℝ) =
            (13725610568519909 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (13725610568519909 / 10000000000000000 : ℝ) ≤
            (395847974098427324677 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3426932084902767 / 5000000000000000 : ℝ)) (q :=
      (13725610568519909 / 20000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_636_7 :
    Uω (aρ 7) (bρ 7) (11793813137919 / 16000000000000 : ℝ) ≤
      (-(822406542208375767147 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (13257043580777419 / 20000000000000000 : ℝ) ≤
      (-(822406542208375767147 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (13257043580777419 / 20000000000000000 : ℝ) =
            (13257043580777419 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (13257043580777419 / 10000000000000000 : ℝ) ≤
            (563887818391624232853 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1652239640705761 / 2500000000000000 : ℝ)) (q :=
      (13257043580777419 / 20000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_636_8 :
    Uω (aρ 8) (bρ 8) (11793813137919 / 16000000000000 : ℝ) ≤
      (-(4581285666546628779379 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1581165391894029 / 2500000000000000 : ℝ) ≤
      (-(4581285666546628779379 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (1581165391894029 / 2500000000000000 : ℝ) =
            (1581165391894029 / 1250000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1581165391894029 / 1250000000000000 : ℝ) ≤
            (2350186136453371220621 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6284779768537857 / 10000000000000000 : ℝ)) (q :=
      (1581165391894029 / 2500000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_636_9 :
    Uω (aρ 9) (bρ 9) (11793813137919 / 16000000000000 : ℝ) ≤
      (-(5196253661759570077241 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (594743317047791 / 1000000000000000 : ℝ) ≤
      (-(5196253661759570077241 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (594743317047791 / 1000000000000000 : ℝ) =
            (594743317047791 / 500000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (594743317047791 / 500000000000000 : ℝ) ≤
            (1735218141240429922759 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1174257720540289 / 2000000000000000 : ℝ)) (q :=
      (594743317047791 / 1000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_636_10 :
    Uω (aρ 10) (bρ 10) (11793813137919 / 16000000000000 : ℝ) ≤
      (-(5981680484881463733891 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10996359074776561 / 20000000000000000 : ℝ) ≤
      (-(5981680484881463733891 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (10996359074776561 / 20000000000000000 : ℝ) =
            (10996359074776561 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (10996359074776561 / 10000000000000000 : ℝ) ≤
            (949791318118536266109 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2680670185008593 / 5000000000000000 : ℝ)) (q :=
      (10996359074776561 / 20000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_636_11 :
    Uω (aρ 11) (bρ 11) (11793813137919 / 16000000000000 : ℝ) ≤
      (-(278547257081232514053 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (9967842190723267 / 20000000000000000 : ℝ) ≤
      (-(278547257081232514053 / 400000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (9967842190723267 / 20000000000000000 : ℝ) =
            (9967842190723267 / 5000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 14
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (9967842190723267 / 5000000000000000 : ℝ) ≤
            (275970487158767485947 / 400000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1187825028042223 / 2500000000000000 : ℝ)) (q :=
      (9967842190723267 / 20000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_636_12 :
    Uω (aρ 12) (bρ 12) (11793813137919 / 16000000000000 : ℝ) ≤
      (-(817155764059736202051 / 1000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1766744515930713 / 4000000000000000 : ℝ) ≤
      (-(817155764059736202051 / 1000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (1766744515930713 / 4000000000000000 : ℝ) =
            (1766744515930713 / 1000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1766744515930713 / 1000000000000000 : ℝ) ≤
            (569138596540263797949 / 1000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (404088059778419 / 1000000000000000 : ℝ)) (q :=
      (1766744515930713 / 4000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_636_13 :
    Uω (aρ 13) (bρ 13) (11793813137919 / 16000000000000 : ℝ) ≤
      (-(9643361284767544950333 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (7624724148226917 / 20000000000000000 : ℝ) ≤
      (-(9643361284767544950333 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (7624724148226917 / 20000000000000000 : ℝ) =
            (7624724148226917 / 5000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (7624724148226917 / 5000000000000000 : ℝ) ≤
            (4219582321232455049667 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1615631953976271 / 5000000000000000 : ℝ)) (q :=
      (7624724148226917 / 20000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_636_14 :
    Uω (aρ 14) (bρ 14) (11793813137919 / 16000000000000 : ℝ) ≤
      (-(457838013503125911517 / 400000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1273411254666331 / 4000000000000000 : ℝ) ≤
      (-(457838013503125911517 / 400000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (1273411254666331 / 4000000000000000 : ℝ) =
            (1273411254666331 / 1000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1273411254666331 / 1000000000000000 : ℝ) ≤
            (96679730736874088483 / 400000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (57938082952557 / 250000000000000 : ℝ)) (q :=
      (1273411254666331 / 4000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_636_15 :
    Uω (aρ 15) (bρ 15) (11793813137919 / 16000000000000 : ℝ) ≤
      (-(6898919903209831485569 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2516329046367611 / 10000000000000000 : ℝ) ≤
      (-(6898919903209831485569 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (2516329046367611 / 10000000000000000 : ℝ) =
            (2516329046367611 / 2500000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 3
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2516329046367611 / 2500000000000000 : ℝ) ≤
            (32551899790168514431 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1242698414920847 / 10000000000000000 : ℝ)) (q :=
      (2516329046367611 / 10000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_636_16 :
    Uω (aρ 16) (bρ 16) (11793813137919 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_636 :
    Uρ (11793813137919 / 16000000000000 : ℝ) ≤
      (-(5444461197856341892419 / 10000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (11793813137919 / 16000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(627610291194593107191 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_636_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (11793813137919 / 16000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(634160989941164399659 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_636_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (11793813137919 / 16000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(1618301582363736978203 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_636_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (11793813137919 / 16000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(1673374737556661780137 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_636_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (11793813137919 / 16000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(3516587252170573535409 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_636_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (11793813137919 / 16000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(470586001276572675323 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_636_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (11793813137919 / 16000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(822406542208375767147 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_636_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (11793813137919 / 16000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(4581285666546628779379 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_636_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (11793813137919 / 16000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(5196253661759570077241 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_636_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (11793813137919 / 16000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(5981680484881463733891 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_636_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (11793813137919 / 16000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) * (-(278547257081232514053 / 400000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_636_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (11793813137919 / 16000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(817155764059736202051 / 1000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_636_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (11793813137919 / 16000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(9643361284767544950333 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_636_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (11793813137919 / 16000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) * (-(457838013503125911517 / 400000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_636_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (11793813137919 / 16000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(6898919903209831485569 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_636_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (11793813137919 / 16000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_636_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_637_1 :
    Uω (aρ 1) (bρ 1) (4723620598879 / 6400000000000 : ℝ) ≤
      (-(195314073346629939723 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1170582059236489 / 1600000000000000 : ℝ) ≤
      (-(195314073346629939723 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (1170582059236489 / 1600000000000000 : ℝ) =
            (1170582059236489 / 800000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1170582059236489 / 800000000000000 : ℝ) ≤
            (237902914340870060277 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (292644630911707 / 400000000000000 : ℝ)) (q :=
      (1170582059236489 / 1600000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_637_2 :
    Uω (aρ 2) (bρ 2) (4723620598879 / 6400000000000 : ℝ) ≤
      (-(25261885905625078749 / 80000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (29168981872581949 / 40000000000000000 : ℝ) ≤
      (-(25261885905625078749 / 80000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (29168981872581949 / 40000000000000000 : ℝ) =
            (29168981872581949 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (29168981872581949 / 20000000000000000 : ℝ) ≤
            (30189888518374921251 / 80000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7292099981137537 / 10000000000000000 : ℝ)) (q :=
      (29168981872581949 / 40000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_637_3 :
    Uω (aρ 3) (bρ 3) (4723620598879 / 6400000000000 : ℝ) ≤
      (-(3223447068104290737667 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28977936991610221 / 40000000000000000 : ℝ) ≤
      (-(3223447068104290737667 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (28977936991610221 / 40000000000000000 : ℝ) =
            (28977936991610221 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (28977936991610221 / 20000000000000000 : ℝ) ≤
            (3708024734895709262333 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7243973647001673 / 10000000000000000 : ℝ)) (q :=
      (28977936991610221 / 40000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_637_4 :
    Uω (aρ 4) (bρ 4) (4723620598879 / 6400000000000 : ℝ) ≤
      (-(166672298750848071597 / 500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28660929572146799 / 40000000000000000 : ℝ) ≤
      (-(166672298750848071597 / 500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (28660929572146799 / 40000000000000000 : ℝ) =
            (28660929572146799 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (28660929572146799 / 20000000000000000 : ℝ) ≤
            (179901291399151928403 / 500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3581882059167481 / 5000000000000000 : ℝ)) (q :=
      (28660929572146799 / 40000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_637_5 :
    Uω (aρ 5) (bρ 5) (4723620598879 / 6400000000000 : ℝ) ≤
      (-(3503051539855834598479 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28178923358519609 / 40000000000000000 : ℝ) ≤
      (-(3503051539855834598479 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (28178923358519609 / 40000000000000000 : ℝ) =
            (28178923358519609 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (28178923358519609 / 20000000000000000 : ℝ) ≤
            (3428420263144165401521 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7040950930856367 / 10000000000000000 : ℝ)) (q :=
      (28178923358519609 / 40000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_637_6 :
    Uω (aρ 6) (bρ 6) (4723620598879 / 6400000000000 : ℝ) ≤
      (-(750160381464319673849 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27489366663664929 / 40000000000000000 : ℝ) ≤
      (-(750160381464319673849 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (27489366663664929 / 40000000000000000 : ℝ) =
            (27489366663664929 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (27489366663664929 / 20000000000000000 : ℝ) ≤
            (636133979135680326151 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6863412958569027 / 10000000000000000 : ℝ)) (q :=
      (27489366663664929 / 40000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_637_7 :
    Uω (aρ 7) (bρ 7) (4723620598879 / 6400000000000 : ℝ) ≤
      (-(1024408110451874314823 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5310459132990397 / 8000000000000000 : ℝ) ≤
      (-(1024408110451874314823 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (5310459132990397 / 8000000000000000 : ℝ) =
            (5310459132990397 / 4000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5310459132990397 / 4000000000000000 : ℝ) ≤
            (708459840298125685177 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1323707767994511 / 2000000000000000 : ℝ)) (q :=
      (5310459132990397 / 8000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_637_8 :
    Uω (aρ 8) (bρ 8) (4723620598879 / 6400000000000 : ℝ) ≤
      (-(2283071625893052422273 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25336983548397839 / 40000000000000000 : ℝ) ≤
      (-(2283071625893052422273 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (25336983548397839 / 40000000000000000 : ℝ) =
            (25336983548397839 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (25336983548397839 / 20000000000000000 : ℝ) ≤
            (1182664275606947577727 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3147212216517741 / 5000000000000000 : ℝ)) (q :=
      (25336983548397839 / 40000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_637_9 :
    Uω (aρ 9) (bρ 9) (4723620598879 / 6400000000000 : ℝ) ≤
      (-(647505734529234841183 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (23828321834201471 / 40000000000000000 : ℝ) ≤
      (-(647505734529234841183 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (23828321834201471 / 40000000000000000 : ℝ) =
            (23828321834201471 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (23828321834201471 / 20000000000000000 : ℝ) ≤
            (218928240845765158817 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2940529602148649 / 5000000000000000 : ℝ)) (q :=
      (23828321834201471 / 40000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_637_10 :
    Uω (aρ 10) (bρ 10) (4723620598879 / 6400000000000 : ℝ) ≤
      (-(2981966440019059832977 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (22031784613221831 / 40000000000000000 : ℝ) ≤
      (-(2981966440019059832977 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (22031784613221831 / 40000000000000000 : ℝ) =
            (22031784613221831 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (22031784613221831 / 20000000000000000 : ℝ) ≤
            (483769461480940167023 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2685674813651239 / 5000000000000000 : ℝ)) (q :=
      (22031784613221831 / 40000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_637_11 :
    Uω (aρ 11) (bρ 11) (4723620598879 / 6400000000000 : ℝ) ≤
      (-(1388731692596799573783 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (19975641520276431 / 40000000000000000 : ℝ) ≤
      (-(1388731692596799573783 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (19975641520276431 / 40000000000000000 : ℝ) =
            (19975641520276431 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 15
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (19975641520276431 / 10000000000000000 : ℝ) ≤
            (1383857028603200426217 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2380877353517389 / 5000000000000000 : ℝ)) (q :=
      (19975641520276431 / 40000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_637_12 :
    Uω (aρ 12) (bρ 12) (4723620598879 / 6400000000000 : ℝ) ≤
      (-(4074010728528158471861 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (17709076555495139 / 40000000000000000 : ℝ) ≤
      (-(4074010728528158471861 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (17709076555495139 / 40000000000000000 : ℝ) =
            (17709076555495139 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (17709076555495139 / 10000000000000000 : ℝ) ≤
            (2857461074471841528139 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1013043080332283 / 2500000000000000 : ℝ)) (q :=
      (17709076555495139 / 40000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_637_13 :
    Uω (aρ 13) (bρ 13) (4723620598879 / 6400000000000 : ℝ) ≤
      (-(2403486424000805781369 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (15294371486162191 / 40000000000000000 : ℝ) ≤
      (-(2403486424000805781369 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (15294371486162191 / 40000000000000000 : ℝ) =
            (15294371486162191 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (15294371486162191 / 10000000000000000 : ℝ) ≤
            (1062249477499194218631 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1622100764128829 / 5000000000000000 : ℝ)) (q :=
      (15294371486162191 / 40000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_637_14 :
    Uω (aρ 14) (bρ 14) (4723620598879 / 6400000000000 : ℝ) ≤
      (-(11405001465921323028451 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12786364210016413 / 40000000000000000 : ℝ) ≤
      (-(11405001465921323028451 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (12786364210016413 / 40000000000000000 : ℝ) =
            (12786364210016413 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (12786364210016413 / 10000000000000000 : ℝ) ≤
            (2457942140078676971549 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2334125175229769 / 10000000000000000 : ℝ)) (q :=
      (12786364210016413 / 40000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_637_15 :
    Uω (aρ 15) (bρ 15) (4723620598879 / 6400000000000 : ℝ) ≤
      (-(857629773117390833237 / 625000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10141864090335721 / 40000000000000000 : ℝ) ≤
      (-(857629773117390833237 / 625000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (10141864090335721 / 40000000000000000 : ℝ) =
            (10141864090335721 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 3
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (10141864090335721 / 10000000000000000 : ℝ) ≤
            (8804202257609166763 / 625000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1271448392804423 / 10000000000000000 : ℝ)) (q :=
      (10141864090335721 / 40000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_637_16 :
    Uω (aρ 16) (bρ 16) (4723620598879 / 6400000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_637 :
    Uρ (4723620598879 / 6400000000000 : ℝ) ≤
      (-(339123009167877599779 / 625000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (4723620598879 / 6400000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(195314073346629939723 / 625000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_637_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (4723620598879 / 6400000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) * (-(25261885905625078749 / 80000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_637_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (4723620598879 / 6400000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(3223447068104290737667 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_637_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (4723620598879 / 6400000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) * (-(166672298750848071597 / 500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_637_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (4723620598879 / 6400000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) *
        (-(3503051539855834598479 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_637_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (4723620598879 / 6400000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(750160381464319673849 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_637_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (4723620598879 / 6400000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(1024408110451874314823 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_637_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (4723620598879 / 6400000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(2283071625893052422273 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_637_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (4723620598879 / 6400000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(647505734529234841183 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_637_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (4723620598879 / 6400000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(2981966440019059832977 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_637_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (4723620598879 / 6400000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(1388731692596799573783 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_637_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (4723620598879 / 6400000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(4074010728528158471861 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_637_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (4723620598879 / 6400000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(2403486424000805781369 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_637_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (4723620598879 / 6400000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(11405001465921323028451 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_637_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (4723620598879 / 6400000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(857629773117390833237 / 625000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_637_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (4723620598879 / 6400000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_637_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_638_1 :
    Uω (aρ 1) (bρ 1) (2956072464119 / 4000000000000 : ℝ) ≤
      (-(622403167510487586771 / 2000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1831415468376431 / 2500000000000000 : ℝ) ≤
      (-(622403167510487586771 / 2000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (1831415468376431 / 2500000000000000 : ℝ) =
            (1831415468376431 / 1250000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1831415468376431 / 1250000000000000 : ℝ) ≤
            (763891193089512413229 / 2000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1831409951199737 / 2500000000000000 : ℝ)) (q :=
      (1831415468376431 / 2500000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_638_2 :
    Uω (aρ 2) (bρ 2) (2956072464119 / 4000000000000 : ℝ) ≤
      (-(1572341792758970059237 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2920707852985017 / 4000000000000000 : ℝ) ≤
      (-(1572341792758970059237 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (2920707852985017 / 4000000000000000 : ℝ) =
            (2920707852985017 / 2000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2920707852985017 / 2000000000000000 : ℝ) ≤
            (1893394108741029940763 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1460324867044517 / 2000000000000000 : ℝ)) (q :=
      (2920707852985017 / 4000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_638_3 :
    Uω (aρ 3) (bρ 3) (2956072464119 / 4000000000000 : ℝ) ≤
      (-(802577064865997302589 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (2901603557151937 / 4000000000000000 : ℝ) ≤
      (-(802577064865997302589 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (2901603557151937 / 4000000000000000 : ℝ) =
            (2901603557151937 / 2000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (2901603557151937 / 2000000000000000 : ℝ) ≤
            (930290885884002697411 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1450699792481437 / 2000000000000000 : ℝ)) (q :=
      (2901603557151937 / 4000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_638_4 :
    Uω (aρ 4) (bρ 4) (2956072464119 / 4000000000000 : ℝ) ≤
      (-(20751000980978739367 / 62500000000000000000 : ℝ)) := by
  have hlg :
    Real.log (14349516634027087 / 20000000000000000 : ℝ) ≤
      (-(20751000980978739367 / 62500000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (14349516634027087 / 20000000000000000 : ℝ) =
            (14349516634027087 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (14349516634027087 / 10000000000000000 : ℝ) ≤
            (22570697787771260633 / 62500000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7173291991739587 / 10000000000000000 : ℝ)) (q :=
      (14349516634027087 / 20000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_638_5 :
    Uω (aρ 5) (bρ 5) (2956072464119 / 4000000000000 : ℝ) ≤
      (-(872383535986811447349 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1410851984035907 / 2000000000000000 : ℝ) ≤
      (-(872383535986811447349 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (1410851984035907 / 2000000000000000 : ℝ) =
            (1410851984035907 / 1000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1410851984035907 / 1000000000000000 : ℝ) ≤
            (860484414763188552651 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (705048511740657 / 1000000000000000 : ℝ)) (q :=
      (1410851984035907 / 2000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_638_6 :
    Uω (aρ 6) (bρ 6) (2956072464119 / 4000000000000 : ℝ) ≤
      (-(3736935110110778650981 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (430117375821391 / 625000000000000 : ℝ) ≤
      (-(3736935110110778650981 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (430117375821391 / 625000000000000 : ℝ) =
            (430117375821391 / 312500000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (430117375821391 / 312500000000000 : ℝ) ≤
            (3194536692889221349019 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1718240419618003 / 2500000000000000 : ℝ)) (q :=
      (430117375821391 / 625000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_638_7 :
    Uω (aρ 7) (bρ 7) (2956072464119 / 4000000000000 : ℝ) ≤
      (-(81665060031860360223 / 200000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (106362015375147 / 160000000000000 : ℝ) ≤
      (-(81665060031860360223 / 200000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (106362015375147 / 160000000000000 : ℝ) = (106362015375147 / 80000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (106362015375147 / 80000000000000 : ℝ) ≤
            (56964376028139639777 / 200000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (53024951638727 / 80000000000000 : ℝ)) (q :=
      (106362015375147 / 160000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_638_8 :
    Uω (aρ 8) (bρ 8) (2956072464119 / 4000000000000 : ℝ) ≤
      (-(1137756005218871002723 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1585957505783303 / 2500000000000000 : ℝ) ≤
      (-(1137756005218871002723 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (1585957505783303 / 2500000000000000 : ℝ) =
            (1585957505783303 / 1250000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1585957505783303 / 1250000000000000 : ℝ) ≤
            (595111945531128997277 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1576017182638481 / 2500000000000000 : ℝ)) (q :=
      (1585957505783303 / 2500000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_638_9 :
    Uω (aρ 9) (bρ 9) (2956072464119 / 4000000000000 : ℝ) ≤
      (-(1290966248587763081941 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (11933454685453741 / 20000000000000000 : ℝ) ≤
      (-(1290966248587763081941 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (11933454685453741 / 20000000000000000 : ℝ) =
            (11933454685453741 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (11933454685453741 / 10000000000000000 : ℝ) ≤
            (441901702162236918059 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (5890828998101241 / 10000000000000000 : ℝ)) (q :=
      (11933454685453741 / 20000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_638_10 :
    Uω (aρ 10) (bρ 10) (2956072464119 / 4000000000000 : ℝ) ≤
      (-(2973109156675716891163 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (1379427972120991 / 2500000000000000 : ℝ) ≤
      (-(2973109156675716891163 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (1379427972120991 / 2500000000000000 : ℝ) =
            (1379427972120991 / 1250000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (1379427972120991 / 1250000000000000 : ℝ) ≤
            (492626744824283108837 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1345339280777607 / 2500000000000000 : ℝ)) (q :=
      (1379427972120991 / 2500000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_638_11 :
    Uω (aρ 11) (bρ 11) (2956072464119 / 4000000000000 : ℝ) ≤
      (-(6923679406295921670647 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10007795433565161 / 20000000000000000 : ℝ) ≤
      (-(6923679406295921670647 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (10007795433565161 / 20000000000000000 : ℝ) =
            (10007795433565161 / 10000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 2
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (10007795433565161 / 10000000000000000 : ℝ) ≤
            (7792396704078329353 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4772205405912661 / 10000000000000000 : ℝ)) (q :=
      (10007795433565161 / 20000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_638_12 :
    Uω (aρ 12) (bρ 12) (2956072464119 / 4000000000000 : ℝ) ≤
      (-(4062275370857562616801 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (4437672460137349 / 10000000000000000 : ℝ) ≤
      (-(4062275370857562616801 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (4437672460137349 / 10000000000000000 : ℝ) =
            (4437672460137349 / 2500000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (4437672460137349 / 2500000000000000 : ℝ) ≤
            (2869196432142437383199 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2031727494653599 / 5000000000000000 : ℝ)) (q :=
      (4437672460137349 / 10000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_638_13 :
    Uω (aρ 13) (bρ 13) (2956072464119 / 4000000000000 : ℝ) ≤
      (-(2396161768732546289149 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (958702974621041 / 2500000000000000 : ℝ) ≤
      (-(2396161768732546289149 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (958702974621041 / 2500000000000000 : ℝ) =
            (958702974621041 / 625000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (958702974621041 / 625000000000000 : ℝ) ≤
            (1069574132767453710851 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (814278901898957 / 2500000000000000 : ℝ)) (q :=
      (958702974621041 / 2500000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13]) (by norm_num [bρ_13])
      (by norm_num) (by norm_num [aρ_13, bρ_13]) (by norm_num [aρ_13, bρ_13]) hlg

lemma U_638_14 :
    Uω (aρ 14) (bρ 14) (2956072464119 / 4000000000000 : ℝ) ≤
      (-(11364342135936268109407 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (80240365902861 / 250000000000000 : ℝ) ≤
      (-(11364342135936268109407 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (80240365902861 / 250000000000000 : ℝ) = (80240365902861 / 62500000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (80240365902861 / 62500000000000 : ℝ) ≤
            (2498601470063731890593 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (117532418395069 / 500000000000000 : ℝ)) (q :=
      (80240365902861 / 250000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14]) (by norm_num [bρ_14])
      (by norm_num) (by norm_num [aρ_14, bρ_14]) (by norm_num [aρ_14, bρ_14]) hlg

lemma U_638_15 :
    Uω (aρ 15) (bρ 15) (2956072464119 / 4000000000000 : ℝ) ≤
      (-(13647990650442621606171 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5108639918318627 / 20000000000000000 : ℝ) ≤
      (-(13647990650442621606171 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (5108639918318627 / 20000000000000000 : ℝ) =
            (5108639918318627 / 5000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5108639918318627 / 5000000000000000 : ℝ) ≤
            (214952955557378393829 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1299632291406127 / 10000000000000000 : ℝ)) (q :=
      (5108639918318627 / 20000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_638_16 :
    Uω (aρ 16) (bρ 16) (2956072464119 / 4000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_638 :
    Uρ (2956072464119 / 4000000000000 : ℝ) ≤
      (-(675946034224267949889 / 1250000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (2956072464119 / 4000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(622403167510487586771 / 2000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_638_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (2956072464119 / 4000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(1572341792758970059237 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_638_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (2956072464119 / 4000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(802577064865997302589 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_638_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (2956072464119 / 4000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) * (-(20751000980978739367 / 62500000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_638_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (2956072464119 / 4000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) * (-(872383535986811447349 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_638_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (2956072464119 / 4000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(3736935110110778650981 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_638_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (2956072464119 / 4000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) * (-(81665060031860360223 / 200000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_638_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (2956072464119 / 4000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(1137756005218871002723 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_638_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (2956072464119 / 4000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(1290966248587763081941 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_638_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (2956072464119 / 4000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(2973109156675716891163 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_638_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (2956072464119 / 4000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(6923679406295921670647 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_638_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (2956072464119 / 4000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(4062275370857562616801 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_638_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (2956072464119 / 4000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(2396161768732546289149 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_638_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (2956072464119 / 4000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(11364342135936268109407 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_638_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (2956072464119 / 4000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(13647990650442621606171 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_638_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (2956072464119 / 4000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_638_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

lemma U_639_1 :
    Uω (aρ 1) (bρ 1) (23679056431509 / 32000000000000 : ℝ) ≤
      (-(3099023403956418114027 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (5868148701367031 / 8000000000000000 : ℝ) ≤
      (-(3099023403956418114027 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (5868148701367031 / 8000000000000000 : ℝ) =
            (5868148701367031 / 4000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (5868148701367031 / 4000000000000000 : ℝ) ≤
            (3832448399043581885973 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1467032767331203 / 2000000000000000 : ℝ)) (q :=
      (5868148701367031 / 8000000000000000 : ℝ)) (by norm_num [aρ_1, bρ_1]) (by norm_num [bρ_1])
      (by norm_num) (by norm_num [aρ_1, bρ_1]) (by norm_num [aρ_1, bρ_1]) hlg

lemma U_639_2 :
    Uω (aρ 2) (bρ 2) (23679056431509 / 32000000000000 : ℝ) ≤
      (-(3131648447173872218449 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (29245175185140721 / 40000000000000000 : ℝ) ≤
      (-(3131648447173872218449 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (29245175185140721 / 40000000000000000 : ℝ) =
            (29245175185140721 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (29245175185140721 / 20000000000000000 : ℝ) ≤
            (3799823355826127781551 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (3655574344159399 / 5000000000000000 : ℝ)) (q :=
      (29245175185140721 / 40000000000000000 : ℝ)) (by norm_num [aρ_2, bρ_2]) (by norm_num [bρ_2])
      (by norm_num) (by norm_num [aρ_2, bρ_2]) (by norm_num [aρ_2, bρ_2]) hlg

lemma U_639_3 :
    Uω (aρ 3) (bρ 3) (23679056431509 / 32000000000000 : ℝ) ≤
      (-(3197186693424707257857 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (29054134144394987 / 40000000000000000 : ℝ) ≤
      (-(3197186693424707257857 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (29054134144394987 / 40000000000000000 : ℝ) =
            (29054134144394987 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (29054134144394987 / 20000000000000000 : ℝ) ≤
            (3734285109575292742143 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7263024274295931 / 10000000000000000 : ℝ)) (q :=
      (29054134144394987 / 40000000000000000 : ℝ)) (by norm_num [aρ_3, bρ_3]) (by norm_num [bρ_3])
      (by norm_num) (by norm_num [aρ_3, bρ_3]) (by norm_num [aρ_3, bρ_3]) hlg

lemma U_639_4 :
    Uω (aρ 4) (bρ 4) (23679056431509 / 32000000000000 : ℝ) ≤
      (-(3306891973972135931103 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28737136943278751 / 40000000000000000 : ℝ) ≤
      (-(3306891973972135931103 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (28737136943278751 / 40000000000000000 : ℝ) =
            (28737136943278751 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (28737136943278751 / 20000000000000000 : ℝ) ≤
            (3624579829027864068897 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7182819854802813 / 10000000000000000 : ℝ)) (q :=
      (28737136943278751 / 40000000000000000 : ℝ)) (by norm_num [aρ_4, bρ_4]) (by norm_num [bρ_4])
      (by norm_num) (by norm_num [aρ_4, bρ_4]) (by norm_num [aρ_4, bρ_4]) hlg

lemma U_639_5 :
    Uω (aρ 5) (bρ 5) (23679056431509 / 32000000000000 : ℝ) ≤
      (-(54313047107620936833 / 156250000000000000000 : ℝ)) := by
  have hlg :
    Real.log (28255155947783119 / 40000000000000000 : ℝ) ≤
      (-(54313047107620936833 / 156250000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (28255155947783119 / 40000000000000000 : ℝ) =
            (28255155947783119 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (28255155947783119 / 20000000000000000 : ℝ) ≤
            (53991199814254063167 / 156250000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (7060019276389997 / 10000000000000000 : ℝ)) (q :=
      (28255155947783119 / 40000000000000000 : ℝ)) (by norm_num [aρ_5, bρ_5]) (by norm_num [bρ_5])
      (by norm_num) (by norm_num [aρ_5, bρ_5]) (by norm_num [aρ_5, bρ_5]) hlg

lemma U_639_6 :
    Uω (aρ 6) (bρ 6) (23679056431509 / 32000000000000 : ℝ) ≤
      (-(3723087564835383075901 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (27565657304325319 / 40000000000000000 : ℝ) ≤
      (-(3723087564835383075901 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (27565657304325319 / 40000000000000000 : ℝ) =
            (27565657304325319 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 9
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (27565657304325319 / 20000000000000000 : ℝ) ≤
            (3208384238164616924099 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6882510329801097 / 10000000000000000 : ℝ)) (q :=
      (27565657304325319 / 40000000000000000 : ℝ)) (by norm_num [aρ_6, bρ_6]) (by norm_num [bρ_6])
      (by norm_num) (by norm_num [aρ_6, bρ_6]) (by norm_num [aρ_6, bρ_6]) hlg

lemma U_639_7 :
    Uω (aρ 7) (bρ 7) (23679056431509 / 32000000000000 : ℝ) ≤
      (-(2034447164939685717283 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (26628711699464443 / 40000000000000000 : ℝ) ≤
      (-(2034447164939685717283 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (26628711699464443 / 40000000000000000 : ℝ) =
            (26628711699464443 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (26628711699464443 / 20000000000000000 : ℝ) ≤
            (1431288736560314282717 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6637698908130659 / 10000000000000000 : ℝ)) (q :=
      (26628711699464443 / 40000000000000000 : ℝ)) (by norm_num [aρ_7, bρ_7]) (by norm_num [bρ_7])
      (by norm_num) (by norm_num [aρ_7, bρ_7]) (by norm_num [aρ_7, bρ_7]) hlg

lemma U_639_8 :
    Uω (aρ 8) (bρ 8) (23679056431509 / 32000000000000 : ℝ) ≤
      (-(2267963951027866300151 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (25413655906072891 / 40000000000000000 : ℝ) ≤
      (-(2267963951027866300151 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (25413655906072891 / 40000000000000000 : ℝ) =
            (25413655906072891 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (25413655906072891 / 20000000000000000 : ℝ) ≤
            (1197771950472133699849 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (6313712662774883 / 10000000000000000 : ℝ)) (q :=
      (25413655906072891 / 40000000000000000 : ℝ)) (by norm_num [aρ_8, bρ_8]) (by norm_num [bρ_8])
      (by norm_num) (by norm_num [aρ_8, bρ_8]) (by norm_num [aρ_8, bρ_8]) hlg

lemma U_639_9 :
    Uω (aρ 9) (bρ 9) (23679056431509 / 32000000000000 : ℝ) ≤
      (-(5147710924735413315221 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (23905495300054583 / 40000000000000000 : ℝ) ≤
      (-(5147710924735413315221 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (23905495300054583 / 40000000000000000 : ℝ) =
            (23905495300054583 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 7
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (23905495300054583 / 20000000000000000 : ℝ) ≤
            (1783760878264586684779 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (5900597988125729 / 10000000000000000 : ℝ)) (q :=
      (23905495300054583 / 40000000000000000 : ℝ)) (by norm_num [aρ_9, bρ_9]) (by norm_num [bρ_9])
      (by norm_num) (by norm_num [aρ_9, bρ_9]) (by norm_num [aρ_9, bρ_9]) hlg

lemma U_639_10 :
    Uω (aρ 10) (bρ 10) (23679056431509 / 32000000000000 : ℝ) ≤
      (-(2964268328139464888913 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (22109906991313217 / 40000000000000000 : ℝ) ≤
      (-(2964268328139464888913 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (22109906991313217 / 40000000000000000 : ℝ) =
            (22109906991313217 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 5
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (22109906991313217 / 20000000000000000 : ℝ) ≤
            (501467573360535111087 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (2695681433625023 / 5000000000000000 : ℝ)) (q :=
      (22109906991313217 / 40000000000000000 : ℝ)) (by norm_num [aρ_10, bρ_10])
      (by norm_num [bρ_10]) (by norm_num) (by norm_num [aρ_10, bρ_10])
      (by norm_num [aρ_10, bρ_10]) hlg

lemma U_639_11 :
    Uω (aρ 11) (bρ 11) (23679056431509 / 32000000000000 : ℝ) ≤
      (-(6903744043443189821783 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (20055532473087563 / 40000000000000000 : ℝ) ≤
      (-(6903744043443189821783 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 1
        (show
          (20055532473087563 / 40000000000000000 : ℝ) =
            (20055532473087563 / 20000000000000000 : ℝ) / 2 ^ 1
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 3
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (20055532473087563 / 20000000000000000 : ℝ) ≤
            (27727759556810178217 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4782652234342219 / 10000000000000000 : ℝ)) (q :=
      (20055532473087563 / 40000000000000000 : ℝ)) (by norm_num [aρ_11, bρ_11])
      (by norm_num [bρ_11]) (by norm_num) (by norm_num [aρ_11, bρ_11])
      (by norm_num [aρ_11, bρ_11]) hlg

lemma U_639_12 :
    Uω (aρ 12) (bρ 12) (23679056431509 / 32000000000000 : ℝ) ≤
      (-(4050572539749861997181 / 5000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (17792285164915683 / 40000000000000000 : ℝ) ≤
      (-(4050572539749861997181 / 5000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (17792285164915683 / 40000000000000000 : ℝ) =
            (17792285164915683 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 13
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (17792285164915683 / 10000000000000000 : ℝ) ≤
            (2880899263250138002819 / 5000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (4074728676941279 / 10000000000000000 : ℝ)) (q :=
      (17792285164915683 / 40000000000000000 : ℝ)) (by norm_num [aρ_12, bρ_12])
      (by norm_num [bρ_12]) (by norm_num) (by norm_num [aρ_12, bρ_12])
      (by norm_num [aρ_12, bρ_12]) hlg

lemma U_639_13 :
    Uω (aρ 13) (bρ 13) (23679056431509 / 32000000000000 : ℝ) ≤
      (-(1194433035719959725449 / 1250000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (15384077177592513 / 40000000000000000 : ℝ) ≤
      (-(1194433035719959725449 / 1250000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (15384077177592513 / 40000000000000000 : ℝ) =
            (15384077177592513 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 10
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (15384077177592513 / 10000000000000000 : ℝ) ≤
            (538434915030040274551 / 1250000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1635003212437347 / 5000000000000000 : ℝ)) (q :=
      (15384077177592513 / 40000000000000000 : ℝ)) (by norm_num [aρ_13, bρ_13])
      (by norm_num [bρ_13]) (by norm_num) (by norm_num [aρ_13, bρ_13])
      (by norm_num [aρ_13, bρ_13]) hlg

lemma U_639_14 :
    Uω (aρ 14) (bρ 14) (23679056431509 / 32000000000000 : ℝ) ≤
      (-(11323966949471001526601 / 10000000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (12890398844629933 / 40000000000000000 : ℝ) ≤
      (-(11323966949471001526601 / 10000000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (12890398844629933 / 40000000000000000 : ℝ) =
            (12890398844629933 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 8
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (12890398844629933 / 10000000000000000 : ℝ) ≤
            (2538976656528998473399 / 10000000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (591773635859601 / 2500000000000000 : ℝ)) (q :=
      (12890398844629933 / 40000000000000000 : ℝ)) (by norm_num [aρ_14, bρ_14])
      (by norm_num [bρ_14]) (by norm_num) (by norm_num [aρ_14, bρ_14])
      (by norm_num [aρ_14, bρ_14]) hlg

lemma U_639_15 :
    Uω (aρ 15) (bρ 15) (23679056431509 / 32000000000000 : ℝ) ≤
      (-(3393869927754534575737 / 2500000000000000000000 : ℝ)) := by
  have hlg :
    Real.log (10291635546897611 / 40000000000000000 : ℝ) ≤
      (-(3393869927754534575737 / 2500000000000000000000 : ℝ)) := by
    have h :=
      log_le_of_split_neg 2
        (show
          (10291635546897611 / 40000000000000000 : ℝ) =
            (10291635546897611 / 10000000000000000 : ℝ) / 2 ^ 2
          by norm_num)
        (by norm_num)
        (log_le_of_ge_one (by norm_num) 4
            (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num) :
          Real.log (10291635546897611 / 10000000000000000 : ℝ) ≤
            (71865973745465424263 / 2500000000000000000000 : ℝ))
    linarith only [h, Real.log_two_gt_d9]
  exact
    Uω_le_right_certificate (s := (1327286171987243 / 10000000000000000 : ℝ)) (q :=
      (10291635546897611 / 40000000000000000 : ℝ)) (by norm_num [aρ_15, bρ_15])
      (by norm_num [bρ_15]) (by norm_num) (by norm_num [aρ_15, bρ_15])
      (by norm_num [aρ_15, bρ_15]) hlg

lemma U_639_16 :
    Uω (aρ 16) (bρ 16) (23679056431509 / 32000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

lemma U_639 :
    Uρ (23679056431509 / 32000000000000 : ℝ) ≤
      (-(2694629023050604486451 / 5000000000000000000000 : ℝ)) := by
  rw [Uρ_expand, cρ_1, cρ_2, cρ_3, cρ_4, cρ_5, cρ_6, cρ_7, cρ_8, cρ_9, cρ_10, cρ_11, cρ_12, cρ_13,
    cρ_14, cρ_15, cρ_16]
  have hm1 :
    (525779809 / 50000000000 : ℝ) * Uω (aρ 1) (bρ 1) (23679056431509 / 32000000000000 : ℝ) ≤
      (525779809 / 50000000000 : ℝ) * (-(3099023403956418114027 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_639_1 (by norm_num)
  have hm2 :
    (29471737793 / 1000000000000 : ℝ) * Uω (aρ 2) (bρ 2) (23679056431509 / 32000000000000 : ℝ) ≤
      (29471737793 / 1000000000000 : ℝ) *
        (-(3131648447173872218449 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_639_2 (by norm_num)
  have hm3 :
    (42934365099 / 1000000000000 : ℝ) * Uω (aρ 3) (bρ 3) (23679056431509 / 32000000000000 : ℝ) ≤
      (42934365099 / 1000000000000 : ℝ) *
        (-(3197186693424707257857 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_639_3 (by norm_num)
  have hm4 :
    (29102115983 / 500000000000 : ℝ) * Uω (aρ 4) (bρ 4) (23679056431509 / 32000000000000 : ℝ) ≤
      (29102115983 / 500000000000 : ℝ) *
        (-(3306891973972135931103 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_639_4 (by norm_num)
  have hm5 :
    (6903762131 / 100000000000 : ℝ) * Uω (aρ 5) (bρ 5) (23679056431509 / 32000000000000 : ℝ) ≤
      (6903762131 / 100000000000 : ℝ) * (-(54313047107620936833 / 156250000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_639_5 (by norm_num)
  have hm6 :
    (78873099189 / 1000000000000 : ℝ) * Uω (aρ 6) (bρ 6) (23679056431509 / 32000000000000 : ℝ) ≤
      (78873099189 / 1000000000000 : ℝ) *
        (-(3723087564835383075901 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_639_6 (by norm_num)
  have hm7 :
    (84856120711 / 1000000000000 : ℝ) * Uω (aρ 7) (bρ 7) (23679056431509 / 32000000000000 : ℝ) ≤
      (84856120711 / 1000000000000 : ℝ) *
        (-(2034447164939685717283 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_639_7 (by norm_num)
  have hm8 :
    (88396082127 / 1000000000000 : ℝ) * Uω (aρ 8) (bρ 8) (23679056431509 / 32000000000000 : ℝ) ≤
      (88396082127 / 1000000000000 : ℝ) *
        (-(2267963951027866300151 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_639_8 (by norm_num)
  have hm9 :
    (706427057 / 8000000000 : ℝ) * Uω (aρ 9) (bρ 9) (23679056431509 / 32000000000000 : ℝ) ≤
      (706427057 / 8000000000 : ℝ) * (-(5147710924735413315221 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_639_9 (by norm_num)
  have hm10 :
    (17094464251 / 200000000000 : ℝ) * Uω (aρ 10) (bρ 10) (23679056431509 / 32000000000000 : ℝ) ≤
      (17094464251 / 200000000000 : ℝ) *
        (-(2964268328139464888913 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_639_10 (by norm_num)
  have hm11 :
    (39449592119 / 500000000000 : ℝ) * Uω (aρ 11) (bρ 11) (23679056431509 / 32000000000000 : ℝ) ≤
      (39449592119 / 500000000000 : ℝ) *
        (-(6903744043443189821783 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_639_11 (by norm_num)
  have hm12 :
    (35176735959 / 500000000000 : ℝ) * Uω (aρ 12) (bρ 12) (23679056431509 / 32000000000000 : ℝ) ≤
      (35176735959 / 500000000000 : ℝ) *
        (-(4050572539749861997181 / 5000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_639_12 (by norm_num)
  have hm13 :
    (11767795323 / 200000000000 : ℝ) * Uω (aρ 13) (bρ 13) (23679056431509 / 32000000000000 : ℝ) ≤
      (11767795323 / 200000000000 : ℝ) *
        (-(1194433035719959725449 / 1250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_639_13 (by norm_num)
  have hm14 :
    (22210660553 / 500000000000 : ℝ) * Uω (aρ 14) (bρ 14) (23679056431509 / 32000000000000 : ℝ) ≤
      (22210660553 / 500000000000 : ℝ) *
        (-(11323966949471001526601 / 10000000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_639_14 (by norm_num)
  have hm15 :
    (30462865791 / 1000000000000 : ℝ) * Uω (aρ 15) (bρ 15) (23679056431509 / 32000000000000 : ℝ) ≤
      (30462865791 / 1000000000000 : ℝ) *
        (-(3393869927754534575737 / 2500000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_639_15 (by norm_num)
  have hm16 :
    (5959622577 / 1000000000000 : ℝ) * Uω (aρ 16) (bρ 16) (23679056431509 / 32000000000000 : ℝ) ≤
      (5959622577 / 1000000000000 : ℝ) * (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
    mul_le_mul_of_nonneg_left U_639_16 (by norm_num)
  linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15,
    hm16]

end Zeta5Irrational
