/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage8Main.LocalDispatch
public import LeanPool.ParameterFreeGradient.O3.Stage12AAnchorMachine
public import LeanPool.ParameterFreeGradient.O3.Stage11RConditionBar

/-!
# Stage 8: one current V7 runtime-p machine

This is a new V7 dispatcher.  It uses the current V7 local trials and only
the primitive `O3.FirstOrderMethod` execution interface from the historical
namespace.
-/

@[expose] public section

namespace V7.Stage8Main

/-- Classical proposition decisions used locally by the runtime construction. -/
noncomputable local instance runtimePropDecidable (q : Prop) : Decidable q :=
  Classical.propDecidable q

/-- The validated primitive input, cached gradient, and accepted anchor-search data. -/
structure RuntimeData (d : ℕ) where
  /-- The primitive numerical input of the method. -/
  input : MethodInput d
  hp : 1 < input.p
  heps : 0 < input.eps
  hM0 : 0 < input.M0
  /-- The initial observation reused by subsequent local trials. -/
  cached : CachedPair d
  /-- The dual norm of the cached initial gradient. -/
  G : ℝ
  G_eq : G = lpNorm (conjugateExponent input.p) cached.observation.gradient
  hG : 0 < G
  /-- The accepted dyadic epoch of the anchor search. -/
  anchorEpoch : ℕ
  /-- The observations made during the anchor search. -/
  anchorTrace : List (Observation d)

/-- The accepted anchor smoothness estimate. -/
noncomputable def RuntimeData.Ma (data : RuntimeData d) : ℝ :=
  (2 : ℝ) ^ data.anchorEpoch * data.input.M0

theorem RuntimeData.Ma_pos (data : RuntimeData d) : 0 < data.Ma := by
  exact mul_pos (pow_pos (by norm_num) _) data.hM0

/-- The geometric search indices and chronological history of the runtime controller. -/
structure RuntimeControllerState (d : ℕ) where
  /-- The number of smoothness doublings after the accepted anchor estimate. -/
  scaleEpoch : ℕ
  /-- The radius-doubling index at the current smoothness scale. -/
  radiusLevel : ℕ
  /-- The completed controller visits. -/
  visits : List ControllerVisit
  /-- The local trial reports associated with the completed visits. -/
  reports : List (TrialReport d)

/-- The controller state before its first local trial. -/
def initialRuntimeControllerState : RuntimeControllerState d :=
  ⟨0, 0, [], []⟩

/-- The current dyadic smoothness estimate. -/
noncomputable def RuntimeControllerState.M (data : RuntimeData d)
    (state : RuntimeControllerState d) : ℝ :=
  (2 : ℝ) ^ state.scaleEpoch * data.Ma

/-- The current dyadic radius estimate normalized by the initial gradient size. -/
noncomputable def RuntimeControllerState.D (data : RuntimeData d)
    (state : RuntimeControllerState d) : ℝ :=
  (2 : ℝ) ^ state.radiusLevel * data.G / state.M data

theorem RuntimeControllerState.M_pos (data : RuntimeData d)
    (state : RuntimeControllerState d) : 0 < state.M data := by
  exact mul_pos (pow_pos (by norm_num) _) data.Ma_pos

theorem RuntimeControllerState.D_pos (data : RuntimeData d)
    (state : RuntimeControllerState d) : 0 < state.D data := by
  exact div_pos (mul_pos (pow_pos (by norm_num) _) data.hG) (state.M_pos data)

/-- The certified local trial selected for the current exponent regime and controller estimates. -/
noncomputable def runtimeTrial (data : RuntimeData d)
    (state : RuntimeControllerState d) : LocalTrial d :=
  if hp2 : data.input.p < 2 then
    belowTrialFor data.input.p data.hp hp2 data.input.eps
      (state.M data) (state.D data) data.heps (state.M_pos data)
      (state.D_pos data) data.input.x0 data.cached
  else if hpEq : data.input.p = 2 then
    euclideanTrialFor data.input.eps (state.M data) (state.D data)
      data.heps (state.M_pos data) (state.D_pos data)
      data.input.x0 data.cached
  else
    aboveTrialFor data.input.p (lt_of_le_of_ne (le_of_not_gt hp2) (Ne.symm hpEq))
      data.input.eps (state.M data) (state.D data) data.heps
      (state.M_pos data) (state.D_pos data) data.input.x0 data.cached

/-- The next controller state after a scale failure, resetting the radius level. -/
noncomputable def nextScale (data : RuntimeData d) (state : RuntimeControllerState d)
    (report : TrialReport d) : RuntimeControllerState d :=
  { scaleEpoch := state.scaleEpoch + 1
    radiusLevel := 0
    visits := state.visits ++ [⟨state.M data, state.D data⟩]
    reports := state.reports ++ [report] }

/-- The next controller state after a radius failure, retaining the current smoothness scale. -/
noncomputable def nextRadius (data : RuntimeData d) (state : RuntimeControllerState d)
    (report : TrialReport d) : RuntimeControllerState d :=
  { scaleEpoch := state.scaleEpoch
    radiusLevel := state.radiusLevel + 1
    visits := state.visits ++ [⟨state.M data, state.D data⟩]
    reports := state.reports ++ [report] }

/-- The causal method's initialization, anchor-search, local-trial, and terminal states. -/
inductive CurrentMethodState (d : ℕ) where
  | needX0 (input : MethodInput d)
  | earlyDone (input : MethodInput d)
  | anchoring (input : MethodInput d) (hp : 1 < input.p)
      (heps : 0 < input.eps) (hM0 : 0 < input.M0)
      (cached : CachedPair d) (G : ℝ)
      (G_eq : G = lpNorm (conjugateExponent input.p) cached.observation.gradient)
      (hG : 0 < G)
      (epoch : ℕ) (observations : List (Observation d))
  | controllerReady (data : RuntimeData d) (state : RuntimeControllerState d)
  | localTrial (data : RuntimeData d) (state : RuntimeControllerState d)
      (machineState : (runtimeTrial data state).State)
      (observations : List (Observation d))

/-- The first action of the current local trial, embedded in the global method state. -/
noncomputable def startLocalAction (data : RuntimeData d)
    (state : RuntimeControllerState d) : O3.Action d (CurrentMethodState d) :=
  let trial := runtimeTrial data state
  match trial.action (trial.initial (state.M data) (state.D data) data.cached) with
  | .query x next =>
      .query x fun observation => .localTrial data state (next observation) [observation]
  | .finish _ _ => .done data.input.x0

/-- The next local query or controller transition after a local trial observation. -/
noncomputable def continueLocalAction (data : RuntimeData d)
    (state : RuntimeControllerState d)
    (machineState : (runtimeTrial data state).State)
    (observations : List (Observation d)) : O3.Action d (CurrentMethodState d) :=
  let trial := runtimeTrial data state
  match trial.action machineState with
  | .query x next =>
      .query x fun observation =>
        .localTrial data state (next observation) (observations ++ [observation])
  | .finish guards outcome =>
      let report : TrialReport d := ⟨observations, guards, outcome⟩
      match outcome with
      | .success terminal => .done terminal.point
      | .scale _ => startLocalAction data (nextScale data state report)
      | .radius _ => startLocalAction data (nextRadius data state report)

/-- The observable state transition of the complete parameter-free method. -/
noncomputable def currentMethodAction :
    CurrentMethodState d → O3.Action d (CurrentMethodState d)
  | .needX0 input =>
      .query input.x0 fun observation =>
        if hvalid : 1 < input.p ∧ 0 < input.eps ∧ 0 < input.M0 then
          let G := lpNorm (conjugateExponent input.p) observation.gradient
          if hsmall : G ≤ input.eps then .earlyDone input
          else .anchoring input hvalid.1 hvalid.2.1 hvalid.2.2
            ⟨observation⟩ G rfl
            (lt_trans hvalid.2.1 (lt_of_not_ge hsmall)) 0 []
        else .earlyDone input
  | .earlyDone input => .done input.x0
  | .anchoring input hp heps hM0 cached G G_eq hG epoch observations =>
      let cfg := O3.anchorPrefixConfig input.toO3 cached.observation.value
        cached.observation.gradient G
      let D := O3.anchorRadius cfg.G cfg.M₀ epoch
      let y := O3.anchorProbePoint cfg.q cfg.x₀ cfg.g₀ cfg.G cfg.M₀ epoch
      .query y fun observation =>
        let observations' := observations ++ [observation]
        if observation.value ≤ cfg.f₀ - cfg.G * D / 2 then
          let data : RuntimeData d :=
            { input := input
              hp := hp
              heps := heps
              hM0 := hM0
              cached := cached
              G := G
              G_eq := G_eq
              hG := hG
              anchorEpoch := epoch
              anchorTrace := observations' }
          .controllerReady data initialRuntimeControllerState
        else .anchoring input hp heps hM0 cached G G_eq hG
          (epoch + 1) observations'
  | .controllerReady data state => startLocalAction data state
  | .localTrial data state machineState observations =>
      continueLocalAction data state machineState observations

/-- The first-order method implementing initialization, anchor search, and the geometric
controller. -/
noncomputable def currentMethod (d : ℕ) : O3.FirstOrderMethod d where
  State := CurrentMethodState d
  initial := fun input => CurrentMethodState.needX0
    { p := input.p, eps := input.eps, x0 := input.x0,
      z0 := input.z0, M0 := input.M0 }
  action := currentMethodAction

/-- One family is fixed before runtime `p`, dimension-specific input, or oracle. -/
noncomputable def currentMethodFamily : RuntimeMethodFamily := fun d => currentMethod d

end V7.Stage8Main
