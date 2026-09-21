/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage1E03.Machine

namespace V7
namespace Stage1E03

theorem checkHolds_exact_iff (p M : ℝ) (oracle : PairOracle d)
    (kind : ObservableGuardKind) (x y : Point d) :
    CheckHolds p M (exactGuardCheck kind oracle x y) ↔
      ¬ GuardFails p M oracle
        (exactGuardCheck kind oracle x y).failure := by
  cases kind <;>
    simp [CheckHolds, exactGuardCheck, ObservableGuardCheck.failure,
      GuardFails, UpperModelGuard, GradientGuard, CocoercivityGuard,
      BregmanRemainder, EuclideanInterpolationGuard, TerminalDescentGuard,
      O3.PairOracle.observe]

theorem upperCheck_exact (oracle : PairOracle d) (x y : Point d) :
    upperCheck (oracle.observe x) (oracle.observe y) =
      exactGuardCheck .upperModel oracle x y := rfl

theorem interpolationCheck_exact (oracle : PairOracle d) (x y : Point d) :
    interpolationCheck (oracle.observe x) (oracle.observe y) =
      exactGuardCheck .interpolation oracle x y := rfl

theorem terminalCheck_exact (oracle : PairOracle d) (x y : Point d) :
    terminalCheck (oracle.observe x) (oracle.observe y) =
      exactGuardCheck .terminalDescent oracle x y := rfl

theorem evaluateChecks_ok_iff (p M : ℝ) :
    ∀ (checks passed : List (ObservableGuardCheck d)),
      evaluateChecks p M checks = .ok passed ↔
        passed = checks ∧ ∀ check ∈ checks, CheckHolds p M check := by
  intro checks
  induction checks with
  | nil => intro passed; simp [evaluateChecks]
  | cons check checks ih =>
      intro passed
      simp only [evaluateChecks]
      by_cases hcheck : CheckHolds p M check
      · simp only [hcheck, ↓reduceIte]
        cases htail : evaluateChecks p M checks with
        | error err =>
            constructor
            · intro h; cases h
            · rintro ⟨rfl, hall⟩
              have hrest : ∀ g ∈ checks, CheckHolds p M g := by
                intro g hg
                exact hall g (by simp [hg])
              have hok := (ih checks).2 ⟨rfl, hrest⟩
              simp [htail] at hok
        | ok tail =>
            obtain ⟨rfl, hrest⟩ := (ih tail).1 htail
            constructor
            · intro h
              injection h with hp
              subst passed
              exact ⟨rfl, by
                intro g hg
                rcases List.mem_cons.mp hg with rfl | hg
                · exact hcheck
                · exact hrest g hg⟩
            · rintro ⟨rfl, _⟩
              rfl
      · simp [hcheck]

theorem evaluateChecks_error_characterization (p M : ℝ) :
    ∀ (checks prior : List (ObservableGuardCheck d)) failed,
      evaluateChecks p M checks = .error (prior, failed) →
      prior <+: checks ∧
      prior.getLast? = some failed ∧
      (∀ check ∈ prior.dropLast, CheckHolds p M check) ∧
      ¬ CheckHolds p M failed := by
  intro checks
  induction checks with
  | nil =>
      intro prior failed h
      simp [evaluateChecks] at h
  | cons check checks ih =>
      intro prior failed h
      simp only [evaluateChecks] at h
      by_cases hcheck : CheckHolds p M check
      · simp only [hcheck, ↓reduceIte] at h
        cases htail : evaluateChecks p M checks with
        | ok passed => simp [htail] at h
        | error err =>
            rcases err with ⟨tail, tailFailed⟩
            simp only [htail] at h
            injection h with hp
            injection hp with hprior hfailed
            subst prior
            subst failed
            obtain ⟨hprefix, hlast, hpassed, hbad⟩ :=
              ih tail tailFailed htail
            refine ⟨?_, ?_, ?_, hbad⟩
            · exact (List.cons_prefix_cons).2 ⟨rfl, hprefix⟩
            · have htailne : tail ≠ [] := by
                intro hnil
                subst tail
                simp at hlast
              cases tail with
              | nil => contradiction
              | cons first rest => simpa using hlast
            · intro g hg
              have htailne : tail ≠ [] := by
                intro hnil
                subst tail
                simp at hlast
              simp only [List.dropLast_cons_of_ne_nil htailne,
                List.mem_cons] at hg
              rcases hg with rfl | hg
              · exact hcheck
              · exact hpassed g hg
      · simp only [hcheck, ↓reduceIte] at h
        injection h with hp
        injection hp with hprior hfailed
        subst prior
        subst failed
        exact ⟨by simp, by simp, by simp, hcheck⟩

theorem evaluateChecks_error_prefix (p M : ℝ)
    {checks prior : List (ObservableGuardCheck d)} {failed} :
    evaluateChecks p M checks = .error (prior, failed) → prior <+: checks :=
  fun h => (evaluateChecks_error_characterization p M checks prior failed h).1

theorem evaluateChecks_error_last (p M : ℝ)
    {checks prior : List (ObservableGuardCheck d)} {failed} :
    evaluateChecks p M checks = .error (prior, failed) →
      prior.getLast? = some failed :=
  fun h => (evaluateChecks_error_characterization p M checks prior failed h).2.1

theorem evaluateChecks_error_prior_pass (p M : ℝ)
    {checks prior : List (ObservableGuardCheck d)} {failed} :
    evaluateChecks p M checks = .error (prior, failed) →
      ∀ check ∈ prior.dropLast, CheckHolds p M check :=
  fun h => (evaluateChecks_error_characterization p M checks prior failed h).2.2.1

theorem evaluateChecks_error_failed (p M : ℝ)
    {checks prior : List (ObservableGuardCheck d)} {failed} :
    evaluateChecks p M checks = .error (prior, failed) →
      ¬ CheckHolds p M failed :=
  fun h => (evaluateChecks_error_characterization p M checks prior failed h).2.2.2

end Stage1E03
end V7
