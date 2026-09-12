/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Certificates.EndpointIsolation

/-!
# The certified six-point endpoint

This file transfers the exact polynomial certificate to the natural radical endpoint and
identifies the constants defined from that endpoint.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

/-- The unique endpoint pair isolated by the exact polynomial certificate. -/
def certifiedEndpointPair : ℝ × ℝ :=
  Classical.choose existsUnique_isEndpointPolynomialPair.exists

/-- The certified pair satisfies the signed polynomial endpoint system. -/
theorem certifiedEndpointPair_isEndpointPolynomialPair :
    IsEndpointPolynomialPair certifiedEndpointPair.1 certifiedEndpointPair.2 :=
  Classical.choose_spec existsUnique_isEndpointPolynomialPair.exists

/-- The certified polynomial pair is a solution of the natural radical system. -/
theorem certifiedEndpointPair_isEndpointPair :
    IsEndpointPair certifiedEndpointPair.1 certifiedEndpointPair.2 :=
  isEndpointPair_of_isEndpointPolynomialPair certifiedEndpointPair_isEndpointPolynomialPair

/-- Every signed polynomial endpoint pair is the certified pair. -/
theorem IsEndpointPolynomialPair.eq_certifiedEndpointPair {c B : ℝ}
    (h : IsEndpointPolynomialPair c B) : (c, B) = certifiedEndpointPair := by
  apply existsUnique_isEndpointPolynomialPair.unique
  · exact h
  · exact certifiedEndpointPair_isEndpointPolynomialPair

/-- Every natural radical endpoint pair is the certified pair. -/
theorem IsEndpointPair.eq_certifiedEndpointPair {c B : ℝ} (h : IsEndpointPair c B) :
    (c, B) = certifiedEndpointPair :=
  h.isEndpointPolynomialPair.eq_certifiedEndpointPair

/-- A natural radical endpoint pair exists. -/
theorem exists_isEndpointPair : ∃ c B : ℝ, IsEndpointPair c B :=
  ⟨certifiedEndpointPair.1, certifiedEndpointPair.2, certifiedEndpointPair_isEndpointPair⟩

/-- The first coordinate of the certified pair is exactly `cStar`. -/
theorem cStar_eq_certifiedEndpointPair_fst : cStar = certifiedEndpointPair.1 := by
  apply cStar_eq_of_isEndpointPair_of_unique certifiedEndpointPair_isEndpointPair
  intro c B h
  exact congrArg Prod.fst h.eq_certifiedEndpointPair

/-- The certified endpoint radicands are strictly positive. -/
theorem certifiedEndpointPair_radicands_pos :
    0 < (certifiedEndpointPair.2 ^ 2 - 1) / 2 ∧
      0 < (certifiedEndpointPair.2 ^ 2 +
        (4 * certifiedEndpointPair.1 ^ 2 - 2 * certifiedEndpointPair.1 -
          certifiedEndpointPair.2) ^ 2) / 2 - certifiedEndpointPair.1 ^ 2 :=
  certifiedEndpointPair_isEndpointPair.radicands_pos

/-- The certified second coordinate lies in its strict rational isolation interval. -/
theorem certifiedEndpointPair_second_mem_isolation_box :
    2873744161801659 / 10 ^ 15 < certifiedEndpointPair.2 ∧
      certifiedEndpointPair.2 < 2873744161801662 / 10 ^ 15 :=
  certifiedEndpointPair_isEndpointPair.second_mem_isolation_box

/-- `cStar` lies strictly inside the certified rational isolation interval. -/
theorem cStar_mem_isolation_box :
    13866128436518096 / 10 ^ 16 < cStar ∧
      cStar < 13866128436518100 / 10 ^ 16 := by
  rw [cStar_eq_certifiedEndpointPair_fst]
  exact certifiedEndpointPair_isEndpointPair.c_mem_isolation_box

/-- `sStar` lies strictly inside the half-coordinate isolation interval. -/
theorem sStar_mem_isolation_box :
    6933064218259048 / 10 ^ 16 < sStar ∧
      sStar < 6933064218259050 / 10 ^ 16 := by
  apply sStar_mem_isolation_box_of_unique certifiedEndpointPair_isEndpointPair
  intro c B h
  exact congrArg Prod.fst h.eq_certifiedEndpointPair

/-- The exact isolation interval puts `sStar` below `0.6934`. -/
theorem sStar_le_6934_div_10000_certified : sStar ≤ 6934 / 10000 := by
  exact sStar_mem_isolation_box.2.le.trans (by norm_num)

/-- The certified endpoint lies in the elementary range needed by the six-point argument. -/
theorem half_lt_sStar_and_sStar_lt_one_certified : 1 / 2 < sStar ∧ sStar < 1 :=
  half_lt_sStar_and_sStar_lt_one exists_isEndpointPair

/-- The six-point endpoint is larger than one half. -/
theorem half_lt_sStar : 1 / 2 < sStar :=
  half_lt_sStar_and_sStar_lt_one_certified.1

/-- The six-point endpoint is smaller than one. -/
theorem sStar_lt_one : sStar < 1 :=
  half_lt_sStar_and_sStar_lt_one_certified.2

/-- Twice the endpoint lies strictly between one and two. -/
theorem one_lt_cStar_and_cStar_lt_two : 1 < cStar ∧ cStar < 2 := by
  rcases cStar_mem_isolation_box with ⟨hl, hu⟩
  constructor <;> norm_num at hl hu ⊢ <;> linarith

/-- The six-point endpoint is positive. -/
theorem sStar_pos : 0 < sStar :=
  (by norm_num : (0 : ℝ) < 1 / 2).trans half_lt_sStar

/-- Twice the six-point endpoint is positive. -/
theorem cStar_pos : 0 < cStar := zero_lt_one.trans one_lt_cStar_and_cStar_lt_two.1

end LeanPool.Besicovitch
