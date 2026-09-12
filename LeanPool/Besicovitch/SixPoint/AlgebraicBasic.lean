/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Statement

/-!
# Basic properties of the six-point endpoint

This file records the rational bounds built into `IsEndpointPair` and the
order-theoretic consequences of defining `cStar` as an infimum. The strict
lower bound for `sStar` requires uniqueness of the isolated first coordinate.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

/-- The polynomial residual obtained by squaring the endpoint balance equation. -/
def endpointBalanceResidual (c B : ℝ) : ℝ :=
  let D := 4 * c ^ 2 - 2 * c - B
  let b := (2 * B - 3 * c ^ 2 + 2 * c - 1) / (c + 1)
  let A2 := (B ^ 2 - 1) / 2
  let C2 := (B ^ 2 + D ^ 2) / 2 - c ^ 2
  let R := 3 * c * b + c ^ 2 - 1
  (R ^ 2 - A2 - C2) ^ 2 - 4 * A2 * C2

/-- The residual of the endpoint Gram equation. -/
def endpointGramResidual (c B : ℝ) : ℝ :=
  let D := 4 * c ^ 2 - 2 * c - B
  let b := (2 * B - 3 * c ^ 2 + 2 * c - 1) / (c + 1)
  let x := (5 - B ^ 2) / 4
  let z := (1 + 4 * b ^ 2 - D ^ 2) / 4
  let k := (1 + b ^ 2 - c ^ 2) / 2
  (k - x * z) ^ 2 - (1 - x ^ 2) * (b ^ 2 - z ^ 2)

/-- The signed polynomial system used to isolate the exact endpoint pair. -/
def IsEndpointPolynomialPair (c B : ℝ) : Prop :=
  let D := 4 * c ^ 2 - 2 * c - B
  let b := (2 * B - 3 * c ^ 2 + 2 * c - 1) / (c + 1)
  let A2 := (B ^ 2 - 1) / 2
  let C2 := (B ^ 2 + D ^ 2) / 2 - c ^ 2
  let R := 3 * c * b + c ^ 2 - 1
  let x := (5 - B ^ 2) / 4
  let z := (1 + 4 * b ^ 2 - D ^ 2) / 4
  let k := (1 + b ^ 2 - c ^ 2) / 2
  13866128436518096 / 10 ^ 16 < c ∧ c < 13866128436518100 / 10 ^ 16 ∧
    2873744161801659 / 10 ^ 15 < B ∧ B < 2873744161801662 / 10 ^ 15 ∧
    0 < A2 ∧ 0 < C2 ∧ 0 < R ∧ 0 < R ^ 2 - A2 - C2 ∧
    endpointBalanceResidual c B = 0 ∧ endpointGramResidual c B = 0 ∧
    x < 0 ∧ z < 0 ∧ k - x * z < 0

/-- The first coordinate of an endpoint pair lies in its rational isolation box. -/
theorem IsEndpointPair.c_mem_isolation_box {c B : ℝ} (h : IsEndpointPair c B) :
    13866128436518096 / 10 ^ 16 < c ∧ c < 13866128436518100 / 10 ^ 16 := by
  exact ⟨h.1, h.2.1⟩

/-- The second coordinate of an endpoint pair lies in its rational isolation box. -/
theorem IsEndpointPair.second_mem_isolation_box {c B : ℝ} (h : IsEndpointPair c B) :
    2873744161801659 / 10 ^ 15 < B ∧ B < 2873744161801662 / 10 ^ 15 := by
  exact ⟨h.2.2.1, h.2.2.2.1⟩

/-- Both radicands in an endpoint pair are strictly positive. -/
theorem IsEndpointPair.radicands_pos {c B : ℝ} (h : IsEndpointPair c B) :
    0 < (B ^ 2 - 1) / 2 ∧
      0 < (B ^ 2 + (4 * c ^ 2 - 2 * c - B) ^ 2) / 2 - c ^ 2 := by
  have hcl := h.c_mem_isolation_box.1
  have hcu := h.c_mem_isolation_box.2
  have hBl := h.second_mem_isolation_box.1
  have hc0 : 0 < c := by
    norm_num at hcl ⊢
    linarith
  have hc : c < 7 / 5 := by
    norm_num at hcu ⊢
    linarith
  have hB : 14 / 5 < B := by
    norm_num at hBl ⊢
    linarith
  have hc_sq : c ^ 2 < (7 / 5 : ℝ) ^ 2 := by
    nlinarith
  have hB_sq : (14 / 5 : ℝ) ^ 2 < B ^ 2 := by
    nlinarith
  constructor
  · nlinarith
  · nlinarith [sq_nonneg (4 * c ^ 2 - 2 * c - B)]

/-- The radical balance equation implies its exact polynomial equation. -/
theorem IsEndpointPair.endpointBalanceResidual_eq_zero {c B : ℝ}
    (h : IsEndpointPair c B) : endpointBalanceResidual c B = 0 := by
  let D := 4 * c ^ 2 - 2 * c - B
  let b := (2 * B - 3 * c ^ 2 + 2 * c - 1) / (c + 1)
  let A2 := (B ^ 2 - 1) / 2
  let C2 := (B ^ 2 + D ^ 2) / 2 - c ^ 2
  let A := Real.sqrt A2
  let C := Real.sqrt C2
  let R := 3 * c * b + c ^ 2 - 1
  have hA2 : 0 ≤ A2 := by
    dsimp [A2]
    exact h.radicands_pos.1.le
  have hC2 : 0 ≤ C2 := by
    dsimp [C2, D]
    exact h.radicands_pos.2.le
  have hA : A ^ 2 = A2 := by
    simpa [A] using Real.sq_sqrt hA2
  have hC : C ^ 2 = C2 := by
    simpa [C] using Real.sq_sqrt hC2
  have hR : A + C = R := by
    simpa only [IsEndpointPair, D, b, A2, C2, A, C, R] using h.2.2.2.2.1
  change (R ^ 2 - A2 - C2) ^ 2 - 4 * A2 * C2 = 0
  rw [← hA, ← hC, ← hR]
  ring

/-- The Gram equation says exactly that its residual vanishes. -/
theorem IsEndpointPair.endpointGramResidual_eq_zero {c B : ℝ}
    (h : IsEndpointPair c B) : endpointGramResidual c B = 0 := by
  have hg := h.2.2.2.2.2.1
  change endpointGramResidual c B = 0
  exact sub_eq_zero.mpr hg

/-- An endpoint pair satisfies the signed polynomial isolation system. -/
theorem IsEndpointPair.isEndpointPolynomialPair {c B : ℝ} (h : IsEndpointPair c B) :
    IsEndpointPolynomialPair c B := by
  let D := 4 * c ^ 2 - 2 * c - B
  let b := (2 * B - 3 * c ^ 2 + 2 * c - 1) / (c + 1)
  let A2 := (B ^ 2 - 1) / 2
  let C2 := (B ^ 2 + D ^ 2) / 2 - c ^ 2
  let A := Real.sqrt A2
  let C := Real.sqrt C2
  let R := 3 * c * b + c ^ 2 - 1
  have h_data := h
  simp only [IsEndpointPair] at h_data
  rcases h_data with ⟨hc_lo, hc_hi, hB_lo, hB_hi, hbalance, hgram, hx, hz, hk⟩
  have hA2 : 0 < A2 := by
    simpa [A2] using h.radicands_pos.1
  have hC2 : 0 < C2 := by
    simpa [C2, D] using h.radicands_pos.2
  have hA_sq : A ^ 2 = A2 := by
    simpa [A] using Real.sq_sqrt hA2.le
  have hC_sq : C ^ 2 = C2 := by
    simpa [C] using Real.sq_sqrt hC2.le
  have hA : 0 < A := by
    simpa [A] using Real.sqrt_pos.2 hA2
  have hC : 0 < C := by
    simpa [C] using Real.sqrt_pos.2 hC2
  have hR_eq : A + C = R := by
    simpa only [D, b, A2, C2, A, C, R] using hbalance
  have hR : 0 < R := by
    linarith
  have hQ : 0 < R ^ 2 - A2 - C2 := by
    rw [← hA_sq, ← hC_sq, ← hR_eq]
    nlinarith [mul_pos hA hC]
  dsimp only [IsEndpointPolynomialPair]
  exact ⟨hc_lo, hc_hi, hB_lo, hB_hi, hA2, hC2, hR, hQ,
    h.endpointBalanceResidual_eq_zero, h.endpointGramResidual_eq_zero, hx, hz, hk⟩

/-- The sign conditions in the polynomial system undo both squaring steps. -/
theorem isEndpointPair_of_isEndpointPolynomialPair {c B : ℝ}
    (h : IsEndpointPolynomialPair c B) : IsEndpointPair c B := by
  let D := 4 * c ^ 2 - 2 * c - B
  let b := (2 * B - 3 * c ^ 2 + 2 * c - 1) / (c + 1)
  let A2 := (B ^ 2 - 1) / 2
  let C2 := (B ^ 2 + D ^ 2) / 2 - c ^ 2
  let A := Real.sqrt A2
  let C := Real.sqrt C2
  let R := 3 * c * b + c ^ 2 - 1
  let x := (5 - B ^ 2) / 4
  let z := (1 + 4 * b ^ 2 - D ^ 2) / 4
  let k := (1 + b ^ 2 - c ^ 2) / 2
  simp only [IsEndpointPolynomialPair] at h
  rcases h with ⟨hc_lo, hc_hi, hB_lo, hB_hi, hA2, hC2, hR, hQ,
    hbalance, hgram, hx, hz, hk⟩
  change 0 < A2 at hA2
  change 0 < C2 at hC2
  change 0 < R at hR
  change 0 < R ^ 2 - A2 - C2 at hQ
  change x < 0 at hx
  change z < 0 at hz
  change k - x * z < 0 at hk
  have hA_sq : A ^ 2 = A2 := by
    simpa [A] using Real.sq_sqrt hA2.le
  have hC_sq : C ^ 2 = C2 := by
    simpa [C] using Real.sq_sqrt hC2.le
  have hA : 0 < A := by
    simpa [A] using Real.sqrt_pos.2 hA2
  have hC : 0 < C := by
    simpa [C] using Real.sqrt_pos.2 hC2
  have hbalance' : (R ^ 2 - A2 - C2) ^ 2 - 4 * A2 * C2 = 0 := by
    change endpointBalanceResidual c B = 0
    exact hbalance
  have hQ_eq : R ^ 2 - A2 - C2 = 2 * A * C := by
    rw [← hA_sq, ← hC_sq] at hbalance' hQ
    nlinarith [mul_pos hA hC]
  have hR_eq : A + C = R := by
    nlinarith [hQ_eq, hA_sq, hC_sq]
  have hgram' :
      (k - x * z) ^ 2 = (1 - x ^ 2) * (b ^ 2 - z ^ 2) := by
    apply sub_eq_zero.mp
    change endpointGramResidual c B = 0
    exact hgram
  dsimp only [IsEndpointPair]
  exact ⟨hc_lo, hc_hi, hB_lo, hB_hi, hR_eq, hgram', hx, hz, hk⟩

/-- The first coordinates of endpoint pairs have a uniform rational lower bound. -/
theorem endpoint_first_coordinates_bddBelow :
    BddBelow {c : ℝ | ∃ B : ℝ, IsEndpointPair c B} := by
  refine ⟨13866128436518096 / 10 ^ 16, ?_⟩
  rintro c ⟨B, h⟩
  exact h.c_mem_isolation_box.1.le

/-- The lower endpoint of the isolation box is a lower bound for `cStar`. -/
theorem c_lower_le_cStar (h : ∃ c B : ℝ, IsEndpointPair c B) :
    13866128436518096 / 10 ^ 16 ≤ cStar := by
  rw [cStar]
  apply le_csInf
  · rcases h with ⟨c, B, h⟩
    exact ⟨c, B, h⟩
  · rintro c ⟨B, h⟩
    exact h.c_mem_isolation_box.1.le

/-- If an endpoint pair exists, `cStar` lies below the upper edge of its box. -/
theorem cStar_lt_c_upper (h : ∃ c B : ℝ, IsEndpointPair c B) :
    cStar < 13866128436518100 / 10 ^ 16 := by
  rcases h with ⟨c, B, h⟩
  exact lt_of_le_of_lt
    (csInf_le endpoint_first_coordinates_bddBelow ⟨B, h⟩) h.c_mem_isolation_box.2

/-- Existence of an endpoint pair places `sStar` in a closed-open rational interval. -/
theorem sStar_mem_closedOpen_isolation_box (h : ∃ c B : ℝ, IsEndpointPair c B) :
    6933064218259048 / 10 ^ 16 ≤ sStar ∧
      sStar < 6933064218259050 / 10 ^ 16 := by
  constructor
  · rw [sStar]
    have hc := c_lower_le_cStar h
    norm_num at hc ⊢
    linarith
  · rw [sStar]
    have hc := cStar_lt_c_upper h
    norm_num at hc ⊢
    linarith

/-- Existence of an endpoint pair gives the elementary bounds used later. -/
theorem half_lt_sStar_and_sStar_lt_one (h : ∃ c B : ℝ, IsEndpointPair c B) :
    1 / 2 < sStar ∧ sStar < 1 := by
  rcases sStar_mem_closedOpen_isolation_box h with ⟨hl, hu⟩
  constructor <;> norm_num at hl hu ⊢ <;> linarith

/-- A unique first coordinate of an endpoint pair is the infimum `cStar`. -/
theorem cStar_eq_of_isEndpointPair_of_unique {c B : ℝ} (h : IsEndpointPair c B)
    (h_unique : ∀ ⦃c' B' : ℝ⦄, IsEndpointPair c' B' → c' = c) : cStar = c := by
  apply le_antisymm
  · exact csInf_le endpoint_first_coordinates_bddBelow ⟨B, h⟩
  · rw [cStar]
    apply le_csInf
    · exact ⟨c, B, h⟩
    · rintro c' ⟨B', h'⟩
      exact (h_unique h').ge

/-- A uniquely isolated endpoint pair identifies `sStar` exactly. -/
theorem sStar_eq_of_isEndpointPair_of_unique {c B : ℝ} (h : IsEndpointPair c B)
    (h_unique : ∀ ⦃c' B' : ℝ⦄, IsEndpointPair c' B' → c' = c) : sStar = c / 2 := by
  rw [sStar, cStar_eq_of_isEndpointPair_of_unique h h_unique]

/-- Uniqueness upgrades the lower endpoint bound from weak to strict. -/
theorem sStar_mem_isolation_box_of_unique {c B : ℝ} (h : IsEndpointPair c B)
    (h_unique : ∀ ⦃c' B' : ℝ⦄, IsEndpointPair c' B' → c' = c) :
    6933064218259048 / 10 ^ 16 < sStar ∧
      sStar < 6933064218259050 / 10 ^ 16 := by
  rw [sStar_eq_of_isEndpointPair_of_unique h h_unique]
  constructor
  · have hc := h.c_mem_isolation_box.1
    norm_num at hc ⊢
    linarith
  · have hc := h.c_mem_isolation_box.2
    norm_num at hc ⊢
    linarith

end LeanPool.Besicovitch
