/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage2.PathShape

/-!
Observable trial outcomes certify success or an insufficient scale or radius estimate.
-/

namespace V7
namespace Stage2

open scoped BigOperators

private theorem indexed_visit_bounds {p eps G Ma Da L R : ℝ}
      (hG : 0 < G) (hMa : 0 < Ma)
    (hDa : 0 < Da) (hMaBound : Ma < 2 * L)
    (hDaBound : Da ≤ 2 * R) (cached : CachedPair d) (oracle : PairOracle d)
    (visits : List ControllerVisit) (reports : List (TrialReport d))
    (schedules : List (List (ObservableGuardCheck d)))
    (hpath : ControllerPath G Ma Da visits reports)
    (hledger : ∀ i < reports.length, ∃ visit report schedule,
      VisitAt visits i visit ∧ ReportAt reports i report ∧
      (schedules.drop i).head? = some schedule ∧
      GuardLedgerComplete p report schedule ∧ visit.D ≥ G / visit.M ∧
      TrialCertificate eps p visit.M visit.D L R cached oracle report) :
    ∀ i (hi : i < visits.length),
      0 < visits[i].M ∧ 0 < visits[i].D ∧
      visits[i].M < 2 * L ∧ visits[i].D ≤ 2 * R := by
  intro i
  induction i with
  | zero =>
      intro hi
      have hhead := hpath.2.1
      rw [List.head?_eq_getElem?, List.getElem?_eq_some_iff] at hhead
      have hzero : visits[0] = (⟨Ma, Da⟩ : ControllerVisit) := hhead.2
      rw [hzero]
      exact ⟨hMa, hDa, hMaBound, hDaBound⟩
  | succ i ih =>
      intro hi
      have hiPrev : i < visits.length := by omega
      have hiReport : i < reports.length := by rw [← hpath.1]; exact hiPrev
      obtain ⟨visit, report, schedule, hvisitAt, hreportAt, hschedule,
        hcomplete, hlower, hcert⟩ := hledger i hiReport
      have hvisitEq : visit = visits[i] := by
        have hget := List.getElem?_eq_getElem hiPrev
        simp only [VisitAt, List.head?_drop] at hvisitAt
        exact Option.some.inj (hvisitAt.symm.trans hget)
      have hreportEq : report = reports[i] := by
        have hget := List.getElem?_eq_getElem hiReport
        simp only [ReportAt, List.head?_drop] at hreportAt
        exact Option.some.inj (hreportAt.symm.trans hget)
      subst visit
      subst report
      have hvisitNext : VisitAt visits (i + 1) visits[i + 1] := by
        simp [VisitAt, List.head?_drop]
      have hstep := hpath.2.2 i visits[i] visits[i + 1] reports[i]
        (by simpa using hi)
        (by simp [VisitAt, List.head?_drop]) hvisitNext
        (by simp [ReportAt, List.head?_drop])
      obtain ⟨hMpos, hDpos, hMbound, hDbound⟩ := ih hiPrev
      rcases hcert with ⟨htrace, hdata, hexhaustive, hsuccess, hscale, hradius⟩
      cases houtcome : reports[i].outcome with
      | success terminal => simp [houtcome] at hstep
      | radius terminal =>
          simp only [houtcome] at hstep
          have hrad := hradius terminal houtcome
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hstep.1]; exact hMpos
          · rw [hstep.2]; positivity
          · rw [hstep.1]; exact hMbound
          · rw [hstep.2]
            linarith [hrad.2.2.2.2]
      | scale failed =>
          simp only [houtcome] at hstep
          have hsc := hscale failed houtcome
          have hprevML : visits[i].M < L := hsc.2.2.2.2
          have hhalf : G / visits[i + 1].M = (G / visits[i].M) / 2 := by
            rw [hstep.1]
            field_simp [hMpos.ne']
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hstep.1]; positivity
          · rw [hstep.2]
            exact div_pos hG (by rw [hstep.1]; positivity)
          · rw [hstep.1]
            linarith
          · rw [hstep.2, hhalf]
            linarith

private theorem path_geometric_sums {eps G Ma R : ℝ}
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
    have hMs : (2 : ℝ) ^ s * Ma ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hMa.ne'
    have hkappa : ∀ j : ℕ,
        ((2 : ℝ) ^ s * Ma) * ((2 : ℝ) ^ j * G / ((2 : ℝ) ^ s * Ma)) / eps =
          (2 : ℝ) ^ j * (G / eps) := by
      intro j
      field_simp [hMs, heps.ne']
    simp_rw [hkappa]
    exact dyadic_geometric_sum_le_endpoint ha (div_nonneg hG.le heps.le)
      (lastRadius s)
  · have hrewrite : ∀ s : ℕ,
        (2 : ℝ) ^ s * Ma * R / eps = (2 : ℝ) ^ s * (Ma * R / eps) := by
      intro s
      ring
    simp_rw [hrewrite]
    exact dyadic_geometric_sum_le_endpoint ha
      (div_nonneg (mul_nonneg hMa.le hR) heps.le) S

theorem trialOutcomeCertification : TrialOutcomeCertificationStatement := by
  intro p hp d eps G Ma Da L R heps hG hMa hDa hDaEq hMaBound hDaBound
    cached oracle visits reports schedules hpath hschedules hledger
  have hb := indexed_visit_bounds hG hMa hDa hMaBound hDaBound
    cached oracle visits reports schedules hpath hledger
  have hR : 0 ≤ R := by linarith
  refine ⟨?_, ?_, ?_⟩
  · intro visit hmem
    rw [List.mem_iff_get] at hmem
    obtain ⟨i, rfl⟩ := hmem
    exact (hb i.val i.isLt).2.2.1
  · intro visit hmem
    rw [List.mem_iff_get] at hmem
    obtain ⟨i, rfl⟩ := hmem
    exact (hb i.val i.isLt).2.2.2
  · obtain ⟨S, lastRadius, hgrid⟩ := controllerPath_has_grid hMa hDaEq hpath
    refine ⟨S, lastRadius, ?_, ?_⟩
    · simpa [pathGrid, pathVisit, pathScale, pathRadius] using hgrid
    · exact path_geometric_sums heps hG hMa hR S lastRadius

end Stage2

theorem trialOutcomeCertification : V7.TrialOutcomeCertificationStatement :=
  Stage2.trialOutcomeCertification

end V7
