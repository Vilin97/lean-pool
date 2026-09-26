/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage2Resume.Transport

/-!
The total local trial cost is bounded by the endpoint costs of the realized controller path.
-/

@[expose] public section

namespace V7
namespace Stage2Resume

open scoped BigOperators

/-- The two source-level sums, proved independently over the realized radius
prefix of each epoch and over the realized scale prefix. -/
theorem pathGeometricSumsR1 {eps G Ma R : ℝ}
    (heps : 0 < eps) (hG : 0 < G) (hMa : 0 < Ma) (hR : 0 ≤ R)
    (S : ℕ) (lastRadius : ℕ → ℕ) :
    let Ms : ℕ → ℝ := fun s => (2 : ℝ) ^ s * Ma
    let Dsj : ℕ → ℕ → ℝ := fun s j => (2 : ℝ) ^ j * G / Ms s
    let kappa : ℕ → ℕ → ℝ := fun s j => Ms s * Dsj s j / eps
    ∀ a : ℝ, 0 < a →
      (∀ s ≤ S,
        ∑ j ∈ Finset.range (lastRadius s + 1), (kappa s j) ^ a ≤
          (kappa s (lastRadius s)) ^ a / (1 - (2 : ℝ) ^ (-a))) ∧
      (∑ s ∈ Finset.range (S + 1), (Ms s * R / eps) ^ a ≤
        (Ms S * R / eps) ^ a / (1 - (2 : ℝ) ^ (-a))) := by
  dsimp
  intro a ha
  constructor
  · intro s hs
    have hMs : (2 : ℝ) ^ s * Ma ≠ 0 := (epochScale_pos hMa s).ne'
    have hkappa : ∀ j : ℕ,
        ((2 : ℝ) ^ s * Ma) * ((2 : ℝ) ^ j * G / ((2 : ℝ) ^ s * Ma)) / eps =
          (2 : ℝ) ^ j * (G / eps) := by
      intro j
      field_simp [hMs, heps.ne']
    simp_rw [hkappa]
    exact V7.Stage2.dyadic_geometric_sum_le_endpoint ha
      (div_nonneg hG.le heps.le) (lastRadius s)
  · have hrewrite : ∀ s : ℕ,
        (2 : ℝ) ^ s * Ma * R / eps = (2 : ℝ) ^ s * (Ma * R / eps) := by
      intro s
      ring
    simp_rw [hrewrite]
    exact V7.Stage2.dyadic_geometric_sum_le_endpoint ha
      (div_nonneg (mul_nonneg hMa.le hR) heps.le) S

private theorem currentRaggedMainBound {p eps G L R Ma : ℝ}
    (hp : 1 < p) (heps : 0 < eps) (hG : 0 < G) (hR : 0 < R)
    (hMa : 0 < Ma) (S : ℕ) (lastRadius : ℕ → ℕ)
    (hMsBound : ∀ s ≤ S, (2 : ℝ) ^ s * Ma < 2 * L)
    (hDBound : ∀ s ≤ S, ∀ j ≤ lastRadius s,
      (2 : ℝ) ^ j * G / ((2 : ℝ) ^ s * Ma) ≤ 2 * R)
    (hgeom : ∀ b : ℝ, 0 < b →
      (∀ s ≤ S,
        ∑ j ∈ Finset.range (lastRadius s + 1),
            ((((2 : ℝ) ^ s * Ma) *
              ((2 : ℝ) ^ j * G / ((2 : ℝ) ^ s * Ma)) / eps) ^ b) ≤
          ((((2 : ℝ) ^ s * Ma) *
              ((2 : ℝ) ^ (lastRadius s) * G / ((2 : ℝ) ^ s * Ma)) / eps) ^ b) /
            (1 - (2 : ℝ) ^ (-b))) ∧
      (∑ s ∈ Finset.range (S + 1),
          (((2 : ℝ) ^ s * Ma * R / eps) ^ b) ≤
        (((2 : ℝ) ^ S * Ma * R / eps) ^ b) /
          (1 - (2 : ℝ) ^ (-b)))) :
    let a := localCostExponent p
    (∑ s ∈ Finset.range (S + 1),
      ∑ j ∈ Finset.range (lastRadius s + 1),
        ((((2 : ℝ) ^ s * Ma) *
          ((2 : ℝ) ^ j * G / ((2 : ℝ) ^ s * Ma)) / eps) ^ a) ≤
      amortizationConstant a * (max 1 (L * R / eps)) ^ a) := by
  dsimp
  let a := localCostExponent p
  let den := 1 - (2 : ℝ) ^ (-a)
  let factor := (2 : ℝ) ^ a / den
  let Kbar := max 1 (L * R / eps)
  have ha : 0 < a := V7.Stage2.localCostExponent_pos (p := p)
  have hale : a ≤ 1 := localCostExponent_le_one hp
  have hden : 0 < den := V7.Stage2.one_sub_two_neg_rpow_pos ha
  have hfactor : 0 ≤ factor := div_nonneg (Real.rpow_nonneg (by norm_num) _) hden.le
  have hK : 0 < Kbar := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hinner := (hgeom a ha).1
  have houter := (hgeom a ha).2
  have hperEpoch : ∀ s ≤ S,
      ∑ j ∈ Finset.range (lastRadius s + 1),
          ((((2 : ℝ) ^ s * Ma) *
            ((2 : ℝ) ^ j * G / ((2 : ℝ) ^ s * Ma)) / eps) ^ a) ≤
        factor * (((2 : ℝ) ^ s * Ma * R / eps) ^ a) := by
    intro s hs
    have hM : 0 < (2 : ℝ) ^ s * Ma := epochScale_pos hMa s
    have hD : 0 < (2 : ℝ) ^ (lastRadius s) * G / ((2 : ℝ) ^ s * Ma) :=
      epochRadius_pos hG hMa s (lastRadius s)
    have hx : 0 < (2 : ℝ) ^ s * Ma * R / eps :=
      div_pos (mul_pos hM hR) heps
    have hkappaLe :
        ((2 : ℝ) ^ s * Ma) *
            ((2 : ℝ) ^ (lastRadius s) * G / ((2 : ℝ) ^ s * Ma)) / eps ≤
          2 * ((2 : ℝ) ^ s * Ma * R / eps) := by
      have hDle := hDBound s hs (lastRadius s) (le_refl _)
      calc
        ((2 : ℝ) ^ s * Ma) *
              ((2 : ℝ) ^ (lastRadius s) * G / ((2 : ℝ) ^ s * Ma)) / eps
            ≤ ((2 : ℝ) ^ s * Ma) * (2 * R) / eps :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hDle hM.le) heps.le
        _ = 2 * ((2 : ℝ) ^ s * Ma * R / eps) := by ring
    have hkappaPow :
        ((((2 : ℝ) ^ s * Ma) *
            ((2 : ℝ) ^ (lastRadius s) * G / ((2 : ℝ) ^ s * Ma)) / eps) ^ a) ≤
          (2 * ((2 : ℝ) ^ s * Ma * R / eps)) ^ a :=
      Real.rpow_le_rpow (div_nonneg (mul_nonneg hM.le hD.le) heps.le)
        hkappaLe ha.le
    have htwopow :
        (2 * ((2 : ℝ) ^ s * Ma * R / eps)) ^ a =
          (2 : ℝ) ^ a * (((2 : ℝ) ^ s * Ma * R / eps) ^ a) := by
      rw [Real.mul_rpow (by norm_num) hx.le]
    calc
      ∑ j ∈ Finset.range (lastRadius s + 1),
          ((((2 : ℝ) ^ s * Ma) *
            ((2 : ℝ) ^ j * G / ((2 : ℝ) ^ s * Ma)) / eps) ^ a)
          ≤ ((((2 : ℝ) ^ s * Ma) *
              ((2 : ℝ) ^ (lastRadius s) * G / ((2 : ℝ) ^ s * Ma)) / eps) ^ a) /
              den := by simpa [den] using hinner s hs
      _ ≤ (2 * ((2 : ℝ) ^ s * Ma * R / eps)) ^ a / den :=
        div_le_div_of_nonneg_right hkappaPow hden.le
      _ = factor * (((2 : ℝ) ^ s * Ma * R / eps) ^ a) := by
        rw [htwopow]
        dsimp [factor]
        ring
  have hsumEpoch :
      (∑ s ∈ Finset.range (S + 1),
        ∑ j ∈ Finset.range (lastRadius s + 1),
          ((((2 : ℝ) ^ s * Ma) *
            ((2 : ℝ) ^ j * G / ((2 : ℝ) ^ s * Ma)) / eps) ^ a) ≤
        factor * (∑ s ∈ Finset.range (S + 1),
          (((2 : ℝ) ^ s * Ma * R / eps) ^ a))) := by
    calc
      _ ≤ ∑ s ∈ Finset.range (S + 1),
          factor * (((2 : ℝ) ^ s * Ma * R / eps) ^ a) := by
        apply Finset.sum_le_sum
        intro s hs
        exact hperEpoch s (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs))
      _ = factor * (∑ s ∈ Finset.range (S + 1),
          (((2 : ℝ) ^ s * Ma * R / eps) ^ a)) := by
        rw [Finset.mul_sum]
  have hterminalBase : (2 : ℝ) ^ S * Ma * R / eps ≤ 2 * Kbar := by
    have hMS := hMsBound S (le_refl _)
    have hLR : L * R / eps ≤ Kbar := le_max_right _ _
    have h1 : (2 : ℝ) ^ S * Ma * R ≤ 2 * L * R := by nlinarith
    calc
      (2 : ℝ) ^ S * Ma * R / eps ≤ 2 * L * R / eps :=
        div_le_div_of_nonneg_right h1 heps.le
      _ = 2 * (L * R / eps) := by ring
      _ ≤ 2 * Kbar := mul_le_mul_of_nonneg_left hLR (by norm_num)
  have hterminalPos : 0 ≤ (2 : ℝ) ^ S * Ma * R / eps :=
    (div_pos (mul_pos (epochScale_pos hMa S) hR) heps).le
  have hterminalPow :
      (((2 : ℝ) ^ S * Ma * R / eps) ^ a) ≤ (2 * Kbar) ^ a :=
    Real.rpow_le_rpow hterminalPos hterminalBase ha.le
  have hKpow : 0 ≤ Kbar ^ a := Real.rpow_nonneg hK.le _
  calc
    ∑ s ∈ Finset.range (S + 1),
      ∑ j ∈ Finset.range (lastRadius s + 1),
        ((((2 : ℝ) ^ s * Ma) *
          ((2 : ℝ) ^ j * G / ((2 : ℝ) ^ s * Ma)) / eps) ^ a)
        ≤ factor * (∑ s ∈ Finset.range (S + 1),
          (((2 : ℝ) ^ s * Ma * R / eps) ^ a)) := hsumEpoch
    _ ≤ factor * ((((2 : ℝ) ^ S * Ma * R / eps) ^ a) / den) :=
      mul_le_mul_of_nonneg_left (by simpa [den] using houter) hfactor
    _ ≤ factor * ((2 * Kbar) ^ a / den) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hterminalPow hden.le) hfactor
    _ = factor ^ (2 : ℕ) * Kbar ^ a := by
      rw [Real.mul_rpow (by norm_num) hK.le]
      dsimp [factor]
      ring
    _ ≤ amortizationConstant a * Kbar ^ a :=
      mul_le_mul_of_nonneg_right (endpointCoefficient_le_constant ha hale) hKpow

theorem geometricTrialAmortization : GeometricTrialAmortizationStatement := by
  let C := amortizationConstant (1 / 2)
  refine ⟨C, amortizationConstant_pos (by norm_num), ?_⟩
  intro p hp
  let a := localCostExponent p
  let Cp := amortizationConstant a
  refine ⟨Cp, amortizationConstant_pos (V7.Stage2.localCostExponent_pos (p := p)), ?_⟩
  intro eps G L R Ma Da heps hepsG hL hR hMa hMaBound hDaEq hDaBound
    S lastRadius d visits reports
  dsimp only
  intro hpath hgrid hMsBound hDBound
  have hG : 0 < G := lt_trans heps hepsG
  have hDa : 0 < Da := acceptedRadius_pos hG hMa hDaEq
  have hgeom := pathGeometricSumsR1 heps hG hMa hR.le S lastRadius
  refine ⟨hgeom, ?_⟩
  have hmain := currentRaggedMainBound hp heps hG hR hMa S lastRadius
    hMsBound hDBound hgeom
  have hconst : (if p = 2 then C else Cp) = amortizationConstant a := by
    by_cases hp2 : p = 2
    · subst p
      simp [C, Cp, a, localCostExponent]
    · simp [hp2, Cp]
  rw [hconst]
  refine ⟨hmain, ?_⟩
  intro henvelope
  have hvisitSum := actualReportCallsLeVisitSum
    (C := amortizationConstant a) (a := a) (eps := eps)
    visits reports hpath.1 henvelope
  have hgridSum :
      (visits.map (fun visit => (visit.M * visit.D / eps) ^ a)).sum =
        (∑ s ∈ Finset.range (S + 1),
          ∑ j ∈ Finset.range (lastRadius s + 1),
            ((((2 : ℝ) ^ s * Ma) *
              ((2 : ℝ) ^ j * G / ((2 : ℝ) ^ s * Ma)) / eps) ^ a)) := by
    rw [hgrid]
    exact raggedVisitGridSum eps Ma G a S lastRadius
  rw [hgridSum] at hvisitSum
  calc
    (((reports.map (fun report => report.calls)).sum : ℕ) : ℝ)
        ≤ amortizationConstant a *
          (∑ s ∈ Finset.range (S + 1),
            ∑ j ∈ Finset.range (lastRadius s + 1),
              ((((2 : ℝ) ^ s * Ma) *
                ((2 : ℝ) ^ j * G / ((2 : ℝ) ^ s * Ma)) / eps) ^ a)) := hvisitSum
    _ ≤ amortizationConstant a *
        (amortizationConstant a * (max 1 (L * R / eps)) ^ a) :=
      mul_le_mul_of_nonneg_left hmain
        (amortizationConstant_pos (V7.Stage2.localCostExponent_pos (p := p))).le
    _ = amortizationConstant a ^ (2 : ℕ) *
        (max 1 (L * R / eps)) ^ a := by ring

end Stage2Resume

theorem geometricTrialAmortization : V7.GeometricTrialAmortizationStatement :=
  Stage2Resume.geometricTrialAmortization

end V7
