/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage2Resume.Positivity

namespace V7
namespace Stage2Resume

open scoped BigOperators

private theorem rangeListSumEqFinset (n : ℕ) (f : ℕ → ℝ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  have h := (List.sum_toFinset f (List.nodup_range (n := n))).symm
  rw [List.toFinset_range] at h
  exact h

private theorem sumFlatMap {α β : Type} [AddCommMonoid β]
    (xs : List α) (f : α → List β) :
    (xs.flatMap f).sum = (xs.map (fun x => (f x).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simpa using congrArg ((f x).sum + ·) ih

theorem raggedGridListSum (S : ℕ) (lastRadius : ℕ → ℕ)
    (f : ℕ → ℕ → ℝ) :
    (((List.range (S + 1)).flatMap (fun s =>
      (List.range (lastRadius s + 1)).map (fun j => f s j))).sum) =
      ∑ s ∈ Finset.range (S + 1),
        ∑ j ∈ Finset.range (lastRadius s + 1), f s j := by
  rw [sumFlatMap]
  rw [rangeListSumEqFinset]
  apply Finset.sum_congr rfl
  intro s hs
  exact rangeListSumEqFinset _ _

theorem raggedVisitGridSum (eps Ma G a : ℝ) (S : ℕ)
    (lastRadius : ℕ → ℕ) :
    (((List.range (S + 1)).flatMap (fun s =>
      (List.range (lastRadius s + 1)).map (fun j =>
        { M := (2 : ℝ) ^ s * Ma,
          D := (2 : ℝ) ^ j * G / ((2 : ℝ) ^ s * Ma) : ControllerVisit }))).map
        (fun visit => (visit.M * visit.D / eps) ^ a)).sum =
      ∑ s ∈ Finset.range (S + 1),
        ∑ j ∈ Finset.range (lastRadius s + 1),
          ((((2 : ℝ) ^ s * Ma) *
            ((2 : ℝ) ^ j * G / ((2 : ℝ) ^ s * Ma)) / eps) ^ a) := by
  rw [List.map_flatMap]
  rw [sumFlatMap]
  rw [rangeListSumEqFinset]
  apply Finset.sum_congr rfl
  intro s hs
  rw [List.map_map]
  rw [rangeListSumEqFinset]
  rfl

private theorem alignedListSumLe {α β : Type} (xs : List α) (ys : List β)
    (C : ℝ) (f : α → ℝ) (g : β → ℝ)
    (hlen : xs.length = ys.length)
    (hpoint : ∀ i (hi : i < ys.length), g ys[i] ≤ C * f xs[i]) :
    (ys.map g).sum ≤ C * (xs.map f).sum := by
  induction xs generalizing ys with
  | nil =>
      have : ys = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      subst ys
      simp
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have hlenTail : xs.length = ys.length := by simpa using hlen
          have hhead : g y ≤ C * f x := by
            have h := hpoint 0 (by simp)
            rw [List.getElem_cons_zero] at h
            exact h
          have htail : ∀ i (hi : i < ys.length), g ys[i] ≤ C * f xs[i] := by
            intro i hi
            have h := hpoint (i + 1) (by simp [hi])
            rw [List.getElem_cons_succ] at h
            exact h
          have hsum := ih ys hlenTail htail
          simp only [List.map_cons, List.sum_cons]
          rw [mul_add]
          linarith

theorem actualReportCallsLeVisitSum {d : ℕ} {eps C a : ℝ}
    (visits : List ControllerVisit) (reports : List (TrialReport d))
    (hlen : visits.length = reports.length)
    (henvelope : ∀ i < reports.length, ∃ visit report,
      VisitAt visits i visit ∧ ReportAt reports i report ∧
      (report.calls : ℝ) ≤ C * (visit.M * visit.D / eps) ^ a) :
    (((reports.map (fun report => report.calls)).sum : ℕ) : ℝ) ≤
      C * (visits.map (fun visit => (visit.M * visit.D / eps) ^ a)).sum := by
  have hpoint : ∀ i (hi : i < reports.length),
      (reports[i].calls : ℝ) ≤ C * (visits[i].M * visits[i].D / eps) ^ a := by
    intro i hi
    obtain ⟨visit, report, hvisit, hreport, hcost⟩ := henvelope i hi
    have hiVisit : i < visits.length := by simpa [hlen] using hi
    have hvisitEq : visit = visits[i] := by
      have hget := List.getElem?_eq_getElem hiVisit
      simp only [VisitAt, List.head?_drop] at hvisit
      exact Option.some.inj (hvisit.symm.trans hget)
    have hreportEq : report = reports[i] := by
      have hget := List.getElem?_eq_getElem hi
      simp only [ReportAt, List.head?_drop] at hreport
      exact Option.some.inj (hreport.symm.trans hget)
    simpa [hvisitEq, hreportEq] using hcost
  have hreal := alignedListSumLe visits reports C
    (fun visit => (visit.M * visit.D / eps) ^ a)
    (fun report => (report.calls : ℝ)) hlen hpoint
  have hcast : (((reports.map (fun report => report.calls)).sum : ℕ) : ℝ) =
      (reports.map (fun report => (report.calls : ℝ))).sum := by
    rw [Nat.cast_list_sum, List.map_map]
    rfl
  rw [hcast]
  exact hreal

end Stage2Resume
end V7
