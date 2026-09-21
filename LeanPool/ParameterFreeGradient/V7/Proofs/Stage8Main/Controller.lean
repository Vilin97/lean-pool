/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage8Main.LocalSpec
import LeanPool.ParameterFreeGradient.O3.Controller
import LeanPool.ParameterFreeGradient.O3.Stage4AlgebraRadius

namespace V7.Stage8Main

noncomputable def controllerLocalSpec (data : RuntimeData d)
    (state : RuntimeControllerState d)
    (inst : PositiveInstance data.input.p d data.input.x0)
    (hcached : data.cached.observation = inst.oracle.observe data.input.x0)
    (hlarge : data.input.eps < lpNorm (conjugateExponent data.input.p)
      (inst.oracle.gradient data.input.x0)) : LocalRunSpec data state inst :=
  Classical.choice (runtimeTrial_spec data state inst hcached hlarge)

noncomputable def controllerReport (data : RuntimeData d)
    (inst : PositiveInstance data.input.p d data.input.x0)
    (hcached : data.cached.observation = inst.oracle.observe data.input.x0)
    (hlarge : data.input.eps < lpNorm (conjugateExponent data.input.p)
      (inst.oracle.gradient data.input.x0))
    (state : RuntimeControllerState d) : TrialReport d :=
  (controllerLocalSpec data state inst hcached hlarge).report

structure RuntimeFinish (d : ℕ) where
  returned : Point d
  visits : List ControllerVisit
  reports : List (TrialReport d)

inductive RuntimeControllerRunResult (d : ℕ) where
  | exhausted (state : RuntimeControllerState d)
  | success (finish : RuntimeFinish d)

noncomputable def controllerStep (data : RuntimeData d)
    (state : RuntimeControllerState d) (report : TrialReport d) :
    RuntimeControllerRunResult d :=
  match report.outcome with
  | .success terminal => .success
      { returned := terminal.point
        visits := state.visits ++ [⟨state.M data, state.D data⟩]
        reports := state.reports ++ [report] }
  | .scale _ => .exhausted (nextScale data state report)
  | .radius _ => .exhausted (nextRadius data state report)

noncomputable def runController (data : RuntimeData d)
    (inst : PositiveInstance data.input.p d data.input.x0)
    (hcached : data.cached.observation = inst.oracle.observe data.input.x0)
    (hlarge : data.input.eps < lpNorm (conjugateExponent data.input.p)
      (inst.oracle.gradient data.input.x0)) :
    ℕ → RuntimeControllerState d → RuntimeControllerRunResult d
  | 0, state => .exhausted state
  | fuel + 1, state =>
      let report := controllerReport data inst hcached hlarge state
      match controllerStep data state report with
      | .success finish => .success finish
      | .exhausted state' => runController data inst hcached hlarge fuel state'

noncomputable def controllerConfig (data : RuntimeData d) : O3.ControllerConfig :=
  { initialScale := data.Ma
    gradientSizeAtStart := data.G
    eps := data.input.eps
    prefixCalls := 1 + data.anchorTrace.length }

@[simp] theorem scale_eq_config (data : RuntimeData d)
    (state : RuntimeControllerState d) :
    state.M data = (controllerConfig data).scaleAt state.scaleEpoch := rfl

@[simp] theorem radius_eq_config (data : RuntimeData d)
    (state : RuntimeControllerState d) :
    state.D data = (controllerConfig data).radiusAt
      state.scaleEpoch state.radiusLevel := rfl

noncomputable def runtimeCaps (data : RuntimeData d)
    (inst : PositiveInstance data.input.p d data.input.x0) :
    O3.ControllerCaps (controllerConfig data) inst.L inst.R :=
  Classical.choice (O3.exists_controllerCaps (controllerConfig data) inst.L inst.R
    data.Ma_pos data.hG (by
      simpa [PositiveInstance.R, minimizerDistance] using
        O3.minimizerDistance_nonneg_of_nonempty (p := data.input.p)
          (x0 := data.input.x0) inst.minimizerNonempty))

def runtimeRank (caps : O3.ControllerCaps (controllerConfig data) L R)
    (state : RuntimeControllerState d) : ℕ :=
  (caps.scaleCap - state.scaleEpoch) * (caps.radiusCap + 1) +
    (caps.radiusCap - state.radiusLevel)

private theorem next_rank_lt (data : RuntimeData d)
    (inst : PositiveInstance data.input.p d data.input.x0)
    (hcached : data.cached.observation = inst.oracle.observe data.input.x0)
    (hlarge : data.input.eps < lpNorm (conjugateExponent data.input.p)
      (inst.oracle.gradient data.input.x0))
    (caps : O3.ControllerCaps (controllerConfig data) inst.L inst.R)
    (state state' : RuntimeControllerState d)
    (hs : state.scaleEpoch ≤ caps.scaleCap)
    (hj : state.radiusLevel ≤ caps.radiusCap)
    (hstep : controllerStep data state
      (controllerReport data inst hcached hlarge state) = .exhausted state') :
    runtimeRank caps state' < runtimeRank caps state := by
  let spec := controllerLocalSpec data state inst hcached hlarge
  have hreport : controllerReport data inst hcached hlarge state = spec.report := rfl
  rw [hreport] at hstep
  rcases spec.certificate with ⟨_, _, _, _, hscale, hradius⟩
  cases hout : spec.report.outcome with
  | success terminal => simp [controllerStep, hout] at hstep
  | scale failed =>
      have hML : state.M data < inst.L := (hscale failed hout).2.2.2.2
      have hslt : state.scaleEpoch < caps.scaleCap := by
        by_contra hnot
        have hdom := caps.scaleDominates state.scaleEpoch (Nat.le_of_not_gt hnot)
        exact (not_lt_of_ge (by simpa using hdom)) hML
      simp [controllerStep, hout] at hstep
      subst state'
      simp only [runtimeRank, nextScale]
      have hsub : caps.scaleCap - state.scaleEpoch =
          caps.scaleCap - (state.scaleEpoch + 1) + 1 := by omega
      rw [hsub, Nat.add_mul]
      omega
  | radius terminal =>
      have hDR : state.D data < inst.R := (hradius terminal hout).2.2.2.2
      have hjlt : state.radiusLevel < caps.radiusCap := by
        by_contra hnot
        have hdom := caps.radiusDominates state.scaleEpoch state.radiusLevel hs
          (Nat.le_of_not_gt hnot)
        exact (not_lt_of_ge (by simpa using hdom)) hDR
      simp [controllerStep, hout] at hstep
      subst state'
      simp only [runtimeRank, nextRadius]
      have hsub : caps.radiusCap - state.radiusLevel =
          caps.radiusCap - (state.radiusLevel + 1) + 1 := by omega
      rw [hsub]
      omega

theorem controller_terminates (data : RuntimeData d)
    (inst : PositiveInstance data.input.p d data.input.x0)
    (hcached : data.cached.observation = inst.oracle.observe data.input.x0)
    (hlarge : data.input.eps < lpNorm (conjugateExponent data.input.p)
      (inst.oracle.gradient data.input.x0)) :
    ∃ fuel finish,
      runController data inst hcached hlarge fuel initialRuntimeControllerState =
        .success finish := by
  let caps := runtimeCaps data inst
  let Rel := fun state' state : RuntimeControllerState d =>
    state.scaleEpoch ≤ caps.scaleCap ∧
    state.radiusLevel ≤ caps.radiusCap ∧
    controllerStep data state (controllerReport data inst hcached hlarge state) =
      .exhausted state'
  have hwf : WellFounded Rel := by
    apply Subrelation.wf ?_ (measure (runtimeRank caps)).wf
    intro state' state h
    exact next_rank_lt data inst hcached hlarge caps state state'
      h.1 h.2.1 h.2.2
  have hterm : ∀ state : RuntimeControllerState d,
      state.scaleEpoch ≤ caps.scaleCap → state.radiusLevel ≤ caps.radiusCap →
      ∃ fuel finish,
        runController data inst hcached hlarge fuel state = .success finish := by
    intro state
    induction state using hwf.induction with
    | h state ih =>
        intro hs hj
        let report := controllerReport data inst hcached hlarge state
        cases hstep : controllerStep data state report with
        | success finish =>
            refine ⟨1, finish, ?_⟩
            simp [runController, report, hstep]
        | exhausted state' =>
            have hrel : Rel state' state := ⟨hs, hj, by simpa [report] using hstep⟩
            have hrank := next_rank_lt data inst hcached hlarge caps state state'
              hs hj (by simpa [report] using hstep)
            have hs' : state'.scaleEpoch ≤ caps.scaleCap := by
              let spec := controllerLocalSpec data state inst hcached hlarge
              have hre : report = spec.report := rfl
              rw [hre] at hstep
              rcases spec.certificate with ⟨_, _, _, _, hscale, _⟩
              cases hout : spec.report.outcome with
              | success terminal => simp [controllerStep, hout] at hstep
              | scale failed =>
                  have hML := (hscale failed hout).2.2.2.2
                  have hslt : state.scaleEpoch < caps.scaleCap := by
                    by_contra hnot
                    have hdom := caps.scaleDominates state.scaleEpoch
                      (Nat.le_of_not_gt hnot)
                    have hdom' : inst.L ≤ state.M data := by simpa using hdom
                    exact (not_lt_of_ge hdom') hML
                  simp [controllerStep, hout] at hstep
                  subst state'
                  simpa [nextScale] using (Nat.succ_le_iff.mpr hslt)
              | radius terminal =>
                  simp [controllerStep, hout] at hstep
                  subst state'
                  exact hs
            have hj' : state'.radiusLevel ≤ caps.radiusCap := by
              let spec := controllerLocalSpec data state inst hcached hlarge
              have hre : report = spec.report := rfl
              rw [hre] at hstep
              rcases spec.certificate with ⟨_, _, _, _, _, hradius⟩
              cases hout : spec.report.outcome with
              | success terminal => simp [controllerStep, hout] at hstep
              | scale failed =>
                  simp [controllerStep, hout] at hstep
                  subst state'
                  exact Nat.zero_le _
              | radius terminal =>
                  have hDR := (hradius terminal hout).2.2.2.2
                  have hjlt : state.radiusLevel < caps.radiusCap := by
                    by_contra hnot
                    have hdom := caps.radiusDominates state.scaleEpoch
                      state.radiusLevel hs (Nat.le_of_not_gt hnot)
                    have hdom' : inst.R ≤ state.D data := by simpa using hdom
                    exact (not_lt_of_ge hdom') hDR
                  simp [controllerStep, hout] at hstep
                  subst state'
                  simpa [nextRadius] using (Nat.succ_le_iff.mpr hjlt)
            obtain ⟨fuel, finish, hrun⟩ := ih state' hrel hs' hj'
            refine ⟨fuel + 1, finish, ?_⟩
            simp [runController, report, hstep, hrun]
  exact hterm initialRuntimeControllerState (by simp [initialRuntimeControllerState])
    (by simp [initialRuntimeControllerState])

end V7.Stage8Main
