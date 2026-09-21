/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage8Main.History

/-!
Regime-specific local trial costs combine with geometric path amortization.
-/

namespace V7.Stage8Main

open scoped BigOperators

/-- A universal constant selected from the geometric trial amortization theorem. -/
noncomputable def amortUniversal : ℝ := Classical.choose V7.geometricTrialAmortization

theorem amortUniversal_pos : 0 < amortUniversal :=
  (Classical.choose_spec V7.geometricTrialAmortization).1

/-- The exponent-dependent constant selected from the geometric trial amortization theorem. -/
noncomputable def amortFor (p : ℝ) (hp : 1 < p) : ℝ :=
  Classical.choose ((Classical.choose_spec V7.geometricTrialAmortization).2 p hp)

theorem amortFor_pos (p : ℝ) (hp : 1 < p) : 0 < amortFor p hp :=
  (Classical.choose_spec
    ((Classical.choose_spec V7.geometricTrialAmortization).2 p hp)).1

/-- The universal amortization constant at exponent two and the regime constant otherwise. -/
noncomputable def selectedAmort (p : ℝ) (hp : 1 < p) : ℝ :=
  if p = 2 then amortUniversal else amortFor p hp

theorem selectedAmort_pos (p : ℝ) (hp : 1 < p) :
    0 < selectedAmort p hp := by
  by_cases h : p = 2
  · simp [selectedAmort, h, amortUniversal_pos]
  · simp [selectedAmort, h, amortFor_pos p hp]

theorem runtimeCoefficient_pos (data : RuntimeData d) :
    0 < runtimeCoefficient data := by
  by_cases hp2 : data.input.p < 2
  · have hsub : 0 < data.input.p - 1 := by linarith [data.hp]
    have hsqrt : 0 < Real.sqrt (data.input.p - 1) := Real.sqrt_pos.2 hsub
    simp only [runtimeCoefficient, hp2, ↓reduceDIte, gt_iff_lt]
    positivity
  · by_cases heq : data.input.p = 2
    · simpa [runtimeCoefficient, hp2, heq] using euclideanConstant_pos
    · have habove : 2 < data.input.p :=
        lt_of_le_of_ne (le_of_not_gt hp2) (Ne.symm heq)
      simpa [runtimeCoefficient, hp2, heq] using
        aboveConstant_pos data.input.p habove

private theorem indexedLedger (data : RuntimeData d)
    (inst : PositiveInstance data.input.p d data.input.x0)
    {finish : RuntimeFinish d} (hinv : FinishInvariant data inst finish) :
    ∀ i < finish.reports.length, ∃ visit report schedule,
      VisitAt finish.visits i visit ∧ ReportAt finish.reports i report ∧
      ((finish.reports.map TrialReport.checkedGuards).drop i).head? =
        some schedule ∧
      GuardLedgerComplete data.input.p report schedule ∧
      visit.D ≥ data.G / visit.M ∧
      TrialCertificate data.input.eps data.input.p visit.M visit.D
        inst.L inst.R data.cached inst.oracle report := by
  intro i hi
  have hlen := hinv.valid.length_eq
  have hiv : i < finish.visits.length := by simpa [hlen] using hi
  let visit := finish.visits[i]
  let report := finish.reports[i]
  have hv := hinv.valid.get hiv hi
  refine ⟨visit, report, report.checkedGuards, ?_, ?_, ?_, hv.1, hv.2.1, hv.2.2.1⟩
  · simp [VisitAt, List.head?_drop, visit]
  · simp [ReportAt, List.head?_drop, report]
  · rw [List.head?_drop]
    rw [List.getElem?_map]
    simp [List.getElem?_eq_getElem hi, report]

private theorem indexedCost (data : RuntimeData d)
    (inst : PositiveInstance data.input.p d data.input.x0)
    {finish : RuntimeFinish d} (hinv : FinishInvariant data inst finish) :
    ∀ i < finish.reports.length, ∃ visit report,
      VisitAt finish.visits i visit ∧ ReportAt finish.reports i report ∧
      (report.calls : ℝ) ≤ runtimeCoefficient data *
        (visit.M * visit.D / data.input.eps) ^ localCostExponent data.input.p := by
  intro i hi
  have hlen := hinv.valid.length_eq
  have hiv : i < finish.visits.length := by simpa [hlen] using hi
  let visit := finish.visits[i]
  let report := finish.reports[i]
  have hv := hinv.valid.get hiv hi
  refine ⟨visit, report, ?_, ?_, hv.2.2.2⟩
  · simp [VisitAt, List.head?_drop, visit]
  · simp [ReportAt, List.head?_drop, report]

theorem reportCalls_bound (data : RuntimeData d)
    (inst : PositiveInstance data.input.p d data.input.x0)
    (hcached : data.cached.observation = inst.oracle.observe data.input.x0)
    (hlarge : data.input.eps < lpNorm (conjugateExponent data.input.p)
      (inst.oracle.gradient data.input.x0))
    (hMaBound : data.Ma < 2 * inst.L)
    (hDaBound : data.G / data.Ma ≤ 2 * inst.R)
    {finish : RuntimeFinish d} (hinv : FinishInvariant data inst finish) :
    (((finish.reports.map (fun report => report.calls)).sum : ℕ) : ℝ) ≤
      runtimeCoefficient data * selectedAmort data.input.p data.hp *
        conditionBar inst data.input.eps ^ localCostExponent data.input.p := by
  have hGvalue : data.G = lpNorm (conjugateExponent data.input.p)
      (inst.oracle.gradient data.input.x0) := by
    rw [data.G_eq]
    rw [hcached]
    rfl
  have hepsG : data.input.eps < data.G := by simpa [hGvalue] using hlarge
  have hDaPos : 0 < data.G / data.Ma := div_pos data.hG data.Ma_pos
  have hR : 0 < inst.R := by linarith
  have hcert := V7.trialOutcomeCertification data.input.p data.hp d
    data.input.eps data.G data.Ma (data.G / data.Ma) inst.L inst.R
    data.heps data.hG data.Ma_pos hDaPos rfl hMaBound hDaBound
    data.cached inst.oracle finish.visits finish.reports
    (finish.reports.map TrialReport.checkedGuards)
    hinv.path (by simp) (indexedLedger data inst hinv)
  rcases hcert.2.2 with ⟨S, lastRadius, hgrid, hgeom⟩
  have hMsBound : ∀ s ≤ S, (2 : ℝ) ^ s * data.Ma < 2 * inst.L := by
    intro s hs
    have hmem :
        ({ M := (2 : ℝ) ^ s * data.Ma,
           D := (2 : ℝ) ^ 0 * data.G / ((2 : ℝ) ^ s * data.Ma) } :
          ControllerVisit) ∈ finish.visits := by
      rw [hgrid]
      apply List.mem_flatMap.mpr
      refine ⟨s, by simp [hs], ?_⟩
      apply List.mem_map.mpr
      exact ⟨0, by simp, rfl⟩
    exact hcert.1 _ hmem
  have hDBound : ∀ s ≤ S, ∀ j ≤ lastRadius s,
      (2 : ℝ) ^ j * data.G / ((2 : ℝ) ^ s * data.Ma) ≤ 2 * inst.R := by
    intro s hs j hj
    have hmem :
        ({ M := (2 : ℝ) ^ s * data.Ma,
           D := (2 : ℝ) ^ j * data.G / ((2 : ℝ) ^ s * data.Ma) } :
          ControllerVisit) ∈ finish.visits := by
      rw [hgrid]
      apply List.mem_flatMap.mpr
      refine ⟨s, by simp [hs], ?_⟩
      apply List.mem_map.mpr
      exact ⟨j, by simp [hj], rfl⟩
    exact hcert.2.1 _ hmem
  have hamort := (Classical.choose_spec
    ((Classical.choose_spec V7.geometricTrialAmortization).2
      data.input.p data.hp)).2 data.input.eps data.G
    inst.L inst.R data.Ma (data.G / data.Ma) data.heps hepsG inst.L_pos hR
    data.Ma_pos hMaBound rfl hDaBound S lastRadius d finish.visits finish.reports
    hinv.path hgrid hMsBound hDBound
  have hsum := hamort.2.1
  have hactual := V7.Stage2Resume.actualReportCallsLeVisitSum
    finish.visits finish.reports hinv.path.1 (indexedCost data inst hinv)
  have hvisitSum :
      (finish.visits.map (fun visit =>
        (visit.M * visit.D / data.input.eps) ^ localCostExponent data.input.p)).sum =
      ∑ s ∈ Finset.range (S + 1),
        ∑ j ∈ Finset.range (lastRadius s + 1),
          ((((2 : ℝ) ^ s * data.Ma) *
            ((2 : ℝ) ^ j * data.G / ((2 : ℝ) ^ s * data.Ma)) /
              data.input.eps) ^ localCostExponent data.input.p) := by
    rw [hgrid]
    exact V7.Stage2Resume.raggedVisitGridSum data.input.eps data.Ma data.G
      (localCostExponent data.input.p) S lastRadius
  rw [hvisitSum] at hactual
  have hcoeff := (runtimeCoefficient_pos data).le
  calc
    (((finish.reports.map (fun report => report.calls)).sum : ℕ) : ℝ)
        ≤ runtimeCoefficient data *
          (∑ s ∈ Finset.range (S + 1),
            ∑ j ∈ Finset.range (lastRadius s + 1),
              ((((2 : ℝ) ^ s * data.Ma) *
                ((2 : ℝ) ^ j * data.G / ((2 : ℝ) ^ s * data.Ma)) /
                  data.input.eps) ^ localCostExponent data.input.p)) := hactual
    _ ≤ runtimeCoefficient data *
        (selectedAmort data.input.p data.hp *
          conditionBar inst data.input.eps ^ localCostExponent data.input.p) := by
      apply mul_le_mul_of_nonneg_left _ hcoeff
      exact hsum
    _ = runtimeCoefficient data * selectedAmort data.input.p data.hp *
        conditionBar inst data.input.eps ^ localCostExponent data.input.p := by
      rw [mul_assoc]

end V7.Stage8Main
