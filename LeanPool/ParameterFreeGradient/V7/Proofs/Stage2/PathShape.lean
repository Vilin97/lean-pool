/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage2.Geometric

/-!
The realized controller path has the prescribed geometric sequence of scales and radii.
-/

namespace V7
namespace Stage2

private theorem controllerVisit_ext {v w : ControllerVisit}
    (hM : v.M = w.M) (hD : v.D = w.D) : v = w := by
  cases v
  cases w
  simp_all

/-- The dyadic smoothness estimate at scale index `s`. -/
def pathScale (Ma : ℝ) (s : ℕ) : ℝ := (2 : ℝ) ^ s * Ma

/-- The dyadic radius at scale index `s` and radius index `j`. -/
noncomputable def pathRadius (G Ma : ℝ) (s j : ℕ) : ℝ :=
  (2 : ℝ) ^ j * G / pathScale Ma s

/-- The controller visit associated with the two geometric indices. -/
noncomputable def pathVisit (G Ma : ℝ) (s j : ℕ) : ControllerVisit :=
  ⟨pathScale Ma s, pathRadius G Ma s j⟩

/-- The chronological path through each scale's realized initial segment of radii. -/
noncomputable def pathGrid (G Ma : ℝ) (S : ℕ) (lastRadius : ℕ → ℕ) :
    List ControllerVisit :=
  (List.range (S + 1)).flatMap fun s =>
    (List.range (lastRadius s + 1)).map fun j => pathVisit G Ma s j

private theorem pathGrid_zero (G Ma : ℝ) (lastRadius : ℕ → ℕ)
    (hzero : lastRadius 0 = 0) :
    pathGrid G Ma 0 lastRadius = [pathVisit G Ma 0 0] := by
  simp [pathGrid, hzero]

private theorem pathGrid_extend_radius (G Ma : ℝ) (S : ℕ)
    (lastRadius : ℕ → ℕ) :
    pathGrid G Ma S (Function.update lastRadius S (lastRadius S + 1)) =
      pathGrid G Ma S lastRadius ++ [pathVisit G Ma S (lastRadius S + 1)] := by
  unfold pathGrid
  rw [List.range_succ]
  simp only [List.flatMap_append, List.flatMap_singleton]
  have hprefix :
      (List.range S).flatMap (fun s =>
        (List.range (Function.update lastRadius S (lastRadius S + 1) s + 1)).map
          (fun j => pathVisit G Ma s j)) =
      (List.range S).flatMap (fun s =>
        (List.range (lastRadius s + 1)).map (fun j => pathVisit G Ma s j)) := by
    apply List.flatMap_congr
    intro s hs
    have hlt : s < S := List.mem_range.mp hs
    simp [Function.update, Nat.ne_of_lt hlt]
  rw [hprefix]
  simp [List.range_succ]

private theorem pathGrid_extend_scale (G Ma : ℝ) (S : ℕ)
    (lastRadius : ℕ → ℕ) :
    pathGrid G Ma (S + 1) (Function.update lastRadius (S + 1) 0) =
      pathGrid G Ma S lastRadius ++ [pathVisit G Ma (S + 1) 0] := by
  unfold pathGrid
  rw [show S + 1 + 1 = (S + 1) + 1 by omega, List.range_succ]
  simp only [List.flatMap_append, List.flatMap_singleton]
  congr 1
  · apply List.flatMap_congr
    intro s hs
    have hlt : s < S + 1 := List.mem_range.mp hs
    simp [Function.update, Nat.ne_of_lt hlt]
  · simp

private noncomputable def advanceVisit (G : ℝ) (current : ControllerVisit)
    (report : TrialReport d) : ControllerVisit :=
  match report.outcome with
  | .success _ => current
  | .radius _ => ⟨current.M, 2 * current.D⟩
  | .scale _ => ⟨2 * current.M, G / (2 * current.M)⟩

private def TransitionReport (report : TrialReport d) : Prop :=
  match report.outcome with
  | .success _ => False
  | .radius _ => True
  | .scale _ => True

private theorem scan_path_has_grid {G Ma : ℝ} (hMa : Ma ≠ 0)
    (transitionReports : List (TrialReport d))
    (hall : ∀ report ∈ transitionReports, TransitionReport report) :
    ∃ S lastRadius,
      List.scanl (advanceVisit G) (pathVisit G Ma 0 0) transitionReports =
        pathGrid G Ma S lastRadius ∧
      List.foldl (advanceVisit G) (pathVisit G Ma 0 0) transitionReports =
        pathVisit G Ma S (lastRadius S) := by
  induction transitionReports using List.reverseRecOn with
  | nil =>
      refine ⟨0, fun _ => 0, ?_, ?_⟩
      · simp [pathGrid_zero]
      · simp
  | append_singleton reports report ih =>
      have hall' : ∀ r ∈ reports, TransitionReport r := by
        intro r hr
        exact hall r (List.mem_append_left [report] hr)
      obtain ⟨S, lastRadius, hscan, hfold⟩ := ih hall'
      have hreport := hall report (by simp)
      rw [List.scanl_append, List.foldl_append]
      simp only [List.scanl_cons, List.scanl_nil, List.tail_cons,
        List.foldl_cons, List.foldl_nil]
      rw [hscan, hfold]
      cases houtcome : report.outcome with
      | success terminal => simp [TransitionReport, houtcome] at hreport
      | radius terminal =>
          refine ⟨S, Function.update lastRadius S (lastRadius S + 1), ?_, ?_⟩
          · rw [pathGrid_extend_radius]
            simp [advanceVisit, houtcome, pathVisit, pathRadius, pathScale, pow_succ]
            field_simp
          · simp [advanceVisit, houtcome, pathVisit, pathRadius, pathScale, pow_succ]
            field_simp
      | scale failed =>
          refine ⟨S + 1, Function.update lastRadius (S + 1) 0, ?_, ?_⟩
          · rw [pathGrid_extend_scale]
            simp [advanceVisit, houtcome, pathVisit, pathRadius, pathScale, pow_succ]
            constructor
            · ring
            · congr 1
              ring
          · simp [advanceVisit, houtcome, pathVisit, pathRadius, pathScale, pow_succ]
            constructor
            · ring
            · congr 1
              ring

private theorem visit_eq_foldl_of_controllerPath {G Ma Da : ℝ}
    {visits : List ControllerVisit} {reports : List (TrialReport d)}
    (hpath : ControllerPath G Ma Da visits reports) :
    ∀ i (hi : i < visits.length),
      visits[i] = List.foldl (advanceVisit G) ⟨Ma, Da⟩ (reports.take i) := by
  intro i
  induction i with
  | zero =>
      intro hi
      have hhead := hpath.2.1
      rw [List.head?_eq_getElem?, List.getElem?_eq_some_iff] at hhead
      simpa using hhead.2
  | succ i ih =>
      intro hi
      have hiPrev : i < visits.length := by omega
      have hiReport : i < reports.length := by rw [← hpath.1]; exact hiPrev
      have hvisitCurrent : VisitAt visits i visits[i] := by
        simp [VisitAt, List.head?_drop]
      have hvisitNext : VisitAt visits (i + 1) visits[i + 1] := by
        simp [VisitAt, List.head?_drop]
      have hreportAt : ReportAt reports i reports[i] := by
        simp [ReportAt, List.head?_drop]
      have hstep := hpath.2.2 i visits[i] visits[i + 1] reports[i]
        (by simpa [Nat.succ_eq_add_one] using hi) hvisitCurrent hvisitNext hreportAt
      have hfold := ih hiPrev
      rw [← List.take_concat_get hiReport, List.concat_eq_append,
        List.foldl_concat]
      rw [← hfold]
      cases houtcome : reports[i].outcome with
      | success terminal => simp [houtcome] at hstep
      | radius terminal =>
          simp only [houtcome, advanceVisit] at hstep ⊢
          exact controllerVisit_ext hstep.1 hstep.2
      | scale failed =>
          simp only [houtcome, advanceVisit] at hstep ⊢
          apply controllerVisit_ext hstep.1
          rw [← hstep.1]
          exact hstep.2

private theorem controllerPath_eq_scan {G Ma Da : ℝ}
    {visits : List ControllerVisit} {reports : List (TrialReport d)}
    (hpath : ControllerPath G Ma Da visits reports) :
    visits = List.scanl (advanceVisit G) ⟨Ma, Da⟩ reports.dropLast := by
  have hnonempty : reports ≠ [] := by
    intro hnil
    have hvisitsNil : visits = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro visit hmem
      have : visits.length = 0 := by simp [hpath.1, hnil]
      simpa [this] using List.length_pos_of_mem hmem
    simpa [hvisitsNil] using hpath.2.1
  apply List.ext_getElem
  · rw [List.length_scanl, List.length_dropLast, hpath.1]
    have : 0 < reports.length := List.length_pos_iff.mpr hnonempty
    omega
  · intro i hiVisits hiScan
    rw [List.getElem_scanl hiScan]
    rw [List.dropLast_eq_take, List.take_take]
    have hiReports : i < reports.length := by simpa [hpath.1] using hiVisits
    have hmin : min i (reports.length - 1) = i := by omega
    rw [hmin]
    exact visit_eq_foldl_of_controllerPath hpath i hiVisits

private theorem controllerPath_transition_reports {G Ma Da : ℝ}
    {visits : List ControllerVisit} {reports : List (TrialReport d)}
    (hpath : ControllerPath G Ma Da visits reports) :
    ∀ report ∈ reports.dropLast, TransitionReport report := by
  intro report hmem
  rw [List.mem_iff_get] at hmem
  obtain ⟨i, hi⟩ := hmem
  have hiDrop : i.val < reports.dropLast.length := i.isLt
  have hiReports : i.val < reports.length := by
    have hlen := List.length_dropLast (xs := reports)
    omega
  have hiNext : i.val + 1 < visits.length := by
    have hlen := List.length_dropLast (xs := reports)
    have hpathlen := hpath.1
    omega
  have hgetDrop : reports.dropLast[i.val] = reports[i.val] :=
    List.getElem_dropLast hiDrop
  have hreportEq : report = reports[i.val] := by
    rw [← hi]
    exact hgetDrop
  subst report
  have hvisitCurrent : VisitAt visits i.val visits[i.val] := by
    simp [VisitAt, List.head?_drop]
  have hvisitNext : VisitAt visits (i.val + 1) visits[i.val + 1] := by
    simp [VisitAt, List.head?_drop]
  have hreportAt : ReportAt reports i.val reports[i.val] := by
    simp [ReportAt, List.head?_drop]
  have hstep := hpath.2.2 i.val visits[i.val] visits[i.val + 1]
    reports[i.val] hiNext hvisitCurrent hvisitNext hreportAt
  cases houtcome : reports[i.val].outcome with
  | success terminal => simp [houtcome] at hstep
  | radius terminal => simp [TransitionReport, houtcome]
  | scale failed => simp [TransitionReport, houtcome]

theorem controllerPath_has_grid {G Ma Da : ℝ}
    (hMa : 0 < Ma) (hDa : Da = G / Ma)
    {visits : List ControllerVisit} {reports : List (TrialReport d)}
    (hpath : ControllerPath G Ma Da visits reports) :
    ∃ S lastRadius, visits = pathGrid G Ma S lastRadius := by
  have hstart : (⟨Ma, Da⟩ : ControllerVisit) = pathVisit G Ma 0 0 := by
    apply controllerVisit_ext
    · simp [pathVisit, pathScale]
    · simp [pathVisit, pathRadius, pathScale, hDa]
  obtain ⟨S, lastRadius, hscan, hfold⟩ :=
    scan_path_has_grid (d := d) hMa.ne' reports.dropLast
      (controllerPath_transition_reports hpath)
  refine ⟨S, lastRadius, ?_⟩
  rw [controllerPath_eq_scan hpath, hstart, hscan]

end Stage2
end V7
