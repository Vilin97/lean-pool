/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.O3.Stage3Anchor

/-!
# Stage 12A: causal initial-query and anchor prefix

This module is executable plumbing only.  The machine is indexed by the
dimension and receives the exponent at runtime through `MethodInput`.  Its
transition function contains no oracle or admissible instance; objective data
enters only through the continuation of `Action.query`.
-/

namespace O3

/-- Runtime-only anchor configuration reconstructed after the counted query at
`x0`.  This definition has no proof-side problem parameters. -/
noncomputable def anchorPrefixConfig (input : MethodInput d)
    (f0 : ℝ) (g0 : Vec d) (G : ℝ) : AnchorConfig d :=
  { q := conjugateExponent input.p
    x₀ := input.x0
    f₀ := f0
    g₀ := g0
    G := G
    M₀ := input.M0 }

/-- Causal prefix states.  `earlyDone` and `accepted` are explicit handoff
states; Stage 12A terminates there, while a later controller may reuse the
unchanged preceding transitions and replace only their terminal actions. -/
inductive AnchorPrefixState (d : ℕ) where
  | needX0 (input : MethodInput d)
  | anchoring (input : MethodInput d) (f0 : ℝ) (g0 : Vec d)
      (G : ℝ) (epoch : ℕ)
  | earlyDone (input : MethodInput d)
  | accepted (input : MethodInput d) (f0 : ℝ) (g0 : Vec d)
      (G : ℝ) (epoch : ℕ)

/-- One observation-driven prefix transition.  The only objective values used
below are fields of observations delivered by query continuations. -/
noncomputable def anchorPrefixAction : AnchorPrefixState d →
    Action d (AnchorPrefixState d)
  | .needX0 input =>
      .query input.x0 fun observation =>
        let q := conjugateExponent input.p
        let G := lpNorm q observation.gradient
        if G ≤ input.eps then
          .earlyDone input
        else
          .anchoring input observation.value observation.gradient G 0
  | .anchoring input f0 g0 G epoch =>
      let cfg := anchorPrefixConfig input f0 g0 G
      let D := anchorRadius cfg.G cfg.M₀ epoch
      let y := anchorProbePoint cfg.q cfg.x₀ cfg.g₀ cfg.G cfg.M₀ epoch
      .query y fun observation =>
        if observation.value ≤ cfg.f₀ - cfg.G * D / 2 then
          .accepted input f0 g0 G epoch
        else
          .anchoring input f0 g0 G (epoch + 1)
  | .earlyDone input => .done input.x0
  | .accepted input f0 g0 G epoch =>
      let cfg := anchorPrefixConfig input f0 g0 G
      .done (anchorProbePoint cfg.q cfg.x₀ cfg.g₀ cfg.G cfg.M₀ epoch)

/-- The one dimension-indexed concrete first-order method for the causal
prefix.  The real exponent is read only from runtime input. -/
noncomputable def anchorPrefixMethod (d : ℕ) : FirstOrderMethod d where
  State := AnchorPrefixState d
  initial := AnchorPrefixState.needX0
  action := anchorPrefixAction

/-- The first executable action is definitionally the counted query at `x0`. -/
theorem anchorPrefixMethod_first_action (input : MethodInput d) :
    ∃ next : Observation d → AnchorPrefixState d,
      (anchorPrefixMethod d).action ((anchorPrefixMethod d).initial input) =
        .query input.x0 next := by
  simp [anchorPrefixMethod, anchorPrefixAction]

/-- The one-query early-success execution, before any anchor probe. -/
theorem anchorPrefixMethod_early_run (oracle : PairOracle d)
    (input : MethodInput d)
    (hsmall : lpNorm (conjugateExponent input.p)
      (oracle.gradient input.x0) ≤ input.eps) :
    (anchorPrefixMethod d).run oracle input 2 =
      some
        { returned := input.x0
          queries := [oracle.observe input.x0] } := by
  simp [FirstOrderMethod.run, FirstOrderMethod.runFuel, anchorPrefixMethod,
    anchorPrefixAction, PairOracle.observe, hsmall]

theorem anchorPrefixMethod_early_exact (oracle : PairOracle d)
    (input : MethodInput d)
    (hsmall : lpNorm (conjugateExponent input.p)
      (oracle.gradient input.x0) ≤ input.eps) :
    ∃ result,
      (anchorPrefixMethod d).run oracle input 2 = some result ∧
      result.returned = input.x0 ∧
      result.queries = [oracle.observe input.x0] ∧
      result.callCount = 1 ∧
      TraceExact oracle result.queries ∧
      result.returnedWasQueried := by
  refine ⟨{ returned := input.x0, queries := [oracle.observe input.x0] },
    anchorPrefixMethod_early_run oracle input hsmall,
    rfl, rfl, ?_, ?_, ?_⟩
  · rfl
  · intro o ho
    simp only [List.mem_singleton] at ho
    subst o
    rfl
  · simp [RunResult.returnedWasQueried, PairOracle.observe]

/-- The public one-query early branch specialized to any admissible instance;
the method itself remains the same dimension-indexed object. -/
theorem anchorPrefixMethod_admissible_early {p : ℝ}
    (P : AdmissibleInstance d p)
    (hsmall : lpNorm (conjugateExponent p) (P.grad P.x0) ≤ P.eps) :
    ∃ result,
      (anchorPrefixMethod d).run P.oracle P.methodInput 2 = some result ∧
      result.returned = P.x0 ∧
      result.queries = [P.oracle.observe P.x0] ∧
      result.callCount = 1 ∧
      TraceExact P.oracle result.queries ∧
      result.returnedWasQueried := by
  simpa [AdmissibleInstance.methodInput, AdmissibleInstance.oracle] using
    (anchorPrefixMethod_early_exact P.oracle P.methodInput hsmall)

/-- One executable anchoring query, exposed without unfolding the subsequent
recursive machine step. -/
theorem anchorPrefixMethod_runFuel_anchoring_succ (oracle : PairOracle d)
    (input : MethodInput d) (f0 : ℝ) (g0 : Vec d) (G : ℝ)
    (fuel epoch : ℕ) (history : OracleTrace d) :
    let cfg := anchorPrefixConfig input f0 g0 G
    let D := anchorRadius cfg.G cfg.M₀ epoch
    let y := anchorProbePoint cfg.q cfg.x₀ cfg.g₀ cfg.G cfg.M₀ epoch
    (anchorPrefixMethod d).runFuel oracle (fuel + 1)
        (.anchoring input f0 g0 G epoch) history =
      (anchorPrefixMethod d).runFuel oracle fuel
        (if oracle.value y ≤ cfg.f₀ - cfg.G * D / 2 then
          .accepted input f0 g0 G epoch
        else
          .anchoring input f0 g0 G (epoch + 1))
        (history ++ [oracle.observe y]) := by
  rfl

/-- An accepted handoff consumes exactly the final `done` action and makes no
additional query. -/
theorem anchorPrefixMethod_runFuel_accepted_succ (oracle : PairOracle d)
    (input : MethodInput d) (f0 : ℝ) (g0 : Vec d) (G : ℝ)
    (fuel epoch : ℕ) (history : OracleTrace d) :
    (anchorPrefixMethod d).runFuel oracle (fuel + 1)
        (.accepted input f0 g0 G epoch) history =
      some
        { returned := anchorProbePoint (anchorPrefixConfig input f0 g0 G).q
            (anchorPrefixConfig input f0 g0 G).x₀
            (anchorPrefixConfig input f0 g0 G).g₀
            (anchorPrefixConfig input f0 g0 G).G
            (anchorPrefixConfig input f0 g0 G).M₀ epoch
          queries := history } := by
  rfl

/-- Proof-level anchor success produces the identical causal suffix execution.
The extra unit of method fuel is the final `done` action. -/
theorem anchorPrefixMethod_anchorSuffix_of_runAnchor (oracle : PairOracle d)
    (input : MethodInput d) (f0 : ℝ) (g0 : Vec d) (G : ℝ) :
    ∀ {fuel epoch : ℕ} {history pre : OracleTrace d} {ar : AnchorResult d},
      runAnchor oracle (anchorPrefixConfig input f0 g0 G)
          fuel epoch history = some ar →
      (anchorPrefixMethod d).runFuel oracle (fuel + 1)
          (.anchoring input f0 g0 G epoch) (pre ++ history) =
        some
          { returned := ar.acceptedPoint
            queries := pre ++ ar.observations } := by
  intro fuel
  induction fuel with
  | zero =>
      intro epoch history pre ar hrun
      simp [runAnchor] at hrun
  | succ fuel ih =>
      intro epoch history pre ar hrun
      let cfg := anchorPrefixConfig input f0 g0 G
      let D := anchorRadius cfg.G cfg.M₀ epoch
      let y := anchorProbePoint cfg.q cfg.x₀ cfg.g₀ cfg.G cfg.M₀ epoch
      rw [runAnchor] at hrun
      by_cases hpass : oracle.value y ≤ cfg.f₀ - cfg.G * D / 2
      · dsimp only [cfg, D, y] at hpass
        simp only [hpass, ↓reduceIte] at hrun
        injection hrun with harEq
        subst ar
        rw [show fuel.succ + 1 = (fuel + 1) + 1 by omega,
          anchorPrefixMethod_runFuel_anchoring_succ]
        simp only [hpass, ↓reduceIte]
        rw [anchorPrefixMethod_runFuel_accepted_succ]
        simp [anchorPrefixConfig, List.append_assoc]
      · dsimp only [cfg, D, y] at hpass
        simp only [hpass, ↓reduceIte] at hrun
        have hrec := ih (pre := pre) hrun
        rw [show fuel.succ + 1 = (fuel + 1) + 1 by omega,
          anchorPrefixMethod_runFuel_anchoring_succ]
        simp only [hpass, ↓reduceIte]
        simpa [cfg, y, anchorPrefixConfig, List.append_assoc] using hrec

/-- Every causal suffix success reconstructs the identical proof-level anchor
result. -/
theorem anchorPrefixMethod_runAnchor_of_anchorSuffix (oracle : PairOracle d)
    (input : MethodInput d) (f0 : ℝ) (g0 : Vec d) (G : ℝ) :
    ∀ {fuel epoch : ℕ} {history pre : OracleTrace d} {result : RunResult d},
      (anchorPrefixMethod d).runFuel oracle (fuel + 1)
          (.anchoring input f0 g0 G epoch) (pre ++ history) = some result →
      ∃ ar : AnchorResult d,
        runAnchor oracle (anchorPrefixConfig input f0 g0 G)
            fuel epoch history = some ar ∧
        result =
          { returned := ar.acceptedPoint
            queries := pre ++ ar.observations } := by
  intro fuel
  induction fuel with
  | zero =>
      intro epoch history pre result hrun
      simp [FirstOrderMethod.runFuel, anchorPrefixMethod,
        anchorPrefixAction] at hrun
  | succ fuel ih =>
      intro epoch history pre result hrun
      let cfg := anchorPrefixConfig input f0 g0 G
      let D := anchorRadius cfg.G cfg.M₀ epoch
      let y := anchorProbePoint cfg.q cfg.x₀ cfg.g₀ cfg.G cfg.M₀ epoch
      by_cases hpass : oracle.value y ≤ cfg.f₀ - cfg.G * D / 2
      · dsimp only [cfg, D, y] at hpass
        rw [show fuel.succ + 1 = (fuel + 1) + 1 by omega,
          anchorPrefixMethod_runFuel_anchoring_succ] at hrun
        simp only [hpass, ↓reduceIte] at hrun
        rw [anchorPrefixMethod_runFuel_accepted_succ] at hrun
        injection hrun with hmethod
        let ar : AnchorResult d :=
          { epoch := epoch
            acceptedScale := anchorScale input.M0 epoch
            acceptedRadius := D
            acceptedPoint := y
            observations := history ++ [oracle.observe y] }
        refine ⟨ar, ?_, ?_⟩
        · rw [runAnchor]
          simp only [hpass, ↓reduceIte]
          rfl
        · rw [← hmethod]
          simp [ar, cfg, y, anchorPrefixConfig, List.append_assoc]
      · dsimp only [cfg, D, y] at hpass
        have htail :
            (anchorPrefixMethod d).runFuel oracle (fuel + 1)
                (.anchoring input f0 g0 G (epoch + 1))
                (pre ++ (history ++ [oracle.observe y])) = some result := by
          rw [show fuel.succ + 1 = (fuel + 1) + 1 by omega,
            anchorPrefixMethod_runFuel_anchoring_succ] at hrun
          simp only [hpass, ↓reduceIte] at hrun
          simpa [List.append_assoc] using hrun
        obtain ⟨ar, har, hresult⟩ := ih htail
        refine ⟨ar, ?_, hresult⟩
        rw [runAnchor]
        simp only [hpass, ↓reduceIte]
        simpa [cfg, y] using har

/-- Exact bidirectional suffix equivalence. -/
theorem anchorPrefixMethod_anchorSuffix_iff (oracle : PairOracle d)
    (input : MethodInput d) (f0 : ℝ) (g0 : Vec d) (G : ℝ)
    {fuel epoch : ℕ} {history pre : OracleTrace d} {result : RunResult d} :
    (anchorPrefixMethod d).runFuel oracle (fuel + 1)
        (.anchoring input f0 g0 G epoch) (pre ++ history) = some result ↔
      ∃ ar : AnchorResult d,
        runAnchor oracle (anchorPrefixConfig input f0 g0 G)
            fuel epoch history = some ar ∧
        result =
          { returned := ar.acceptedPoint
            queries := pre ++ ar.observations } := by
  constructor
  · exact anchorPrefixMethod_runAnchor_of_anchorSuffix oracle input f0 g0 G
  · rintro ⟨ar, har, rfl⟩
    exact anchorPrefixMethod_anchorSuffix_of_runAnchor oracle input f0 g0 G har

/-- Full nontrivial prefix equivalence in the proof-level-to-causal direction. -/
theorem anchorPrefixMethod_anchor_run_of_runAnchor (oracle : PairOracle d)
    (input : MethodInput d)
    (hlarge : input.eps < lpNorm (conjugateExponent input.p)
      (oracle.gradient input.x0))
    {anchorFuel : ℕ} {ar : AnchorResult d}
    (hrun : runAnchor oracle
      (anchorPrefixConfig input (oracle.value input.x0)
        (oracle.gradient input.x0)
        (lpNorm (conjugateExponent input.p) (oracle.gradient input.x0)))
      anchorFuel 0 [] = some ar) :
    (anchorPrefixMethod d).run oracle input (anchorFuel + 2) =
      some
        { returned := ar.acceptedPoint
          queries := [oracle.observe input.x0] ++ ar.observations } := by
  let G := lpNorm (conjugateExponent input.p) (oracle.gradient input.x0)
  have hnot : ¬G ≤ input.eps := not_le.mpr hlarge
  have hsuffix :=
    (anchorPrefixMethod_anchorSuffix_iff oracle input
      (oracle.value input.x0) (oracle.gradient input.x0) G
      (fuel := anchorFuel) (epoch := 0) (history := [])
      (pre := [oracle.observe input.x0])
      (result :=
        { returned := ar.acceptedPoint
          queries := [oracle.observe input.x0] ++ ar.observations })).2
      ⟨ar, by simpa only [G] using hrun, rfl⟩
  simpa [FirstOrderMethod.run, FirstOrderMethod.runFuel, anchorPrefixMethod,
    anchorPrefixAction, PairOracle.observe, G, hnot, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using hsuffix

/-- Converse reconstruction: every accepted causal run of the corresponding
fuel has one proof-level `runAnchor` result with identical accepted data and
trace. -/
theorem anchorPrefixMethod_runAnchor_of_anchor_run (oracle : PairOracle d)
    (input : MethodInput d)
    (hlarge : input.eps < lpNorm (conjugateExponent input.p)
      (oracle.gradient input.x0))
    (anchorFuel : ℕ) (result : RunResult d)
    (hrun : (anchorPrefixMethod d).run oracle input (anchorFuel + 2) =
      some result) :
    ∃ ar : AnchorResult d,
      runAnchor oracle
        (anchorPrefixConfig input (oracle.value input.x0)
          (oracle.gradient input.x0)
          (lpNorm (conjugateExponent input.p) (oracle.gradient input.x0)))
        anchorFuel 0 [] = some ar ∧
      result.returned = ar.acceptedPoint ∧
      result.queries = [oracle.observe input.x0] ++ ar.observations := by
  let G := lpNorm (conjugateExponent input.p) (oracle.gradient input.x0)
  have hnot : ¬G ≤ input.eps := not_le.mpr hlarge
  have hsuffix :
      (anchorPrefixMethod d).runFuel oracle (anchorFuel + 1)
          (.anchoring input (oracle.value input.x0)
            (oracle.gradient input.x0) G 0)
          ([oracle.observe input.x0] ++ []) = some result := by
    simpa [FirstOrderMethod.run, FirstOrderMethod.runFuel, anchorPrefixMethod,
      anchorPrefixAction, PairOracle.observe, G, hnot, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hrun
  obtain ⟨ar, har, hresult⟩ :=
    (anchorPrefixMethod_anchorSuffix_iff oracle input
      (oracle.value input.x0) (oracle.gradient input.x0) G
      (fuel := anchorFuel) (epoch := 0) (history := [])
      (pre := [oracle.observe input.x0]) (result := result)).1 hsuffix
  refine ⟨ar, by simpa only [G] using har, ?_, ?_⟩
  · rw [hresult]
  · rw [hresult]

/-- The accepted probe is the last observation of every successful proof-level
anchor execution. -/
theorem runAnchor_acceptedPoint_queried (oracle : PairOracle d)
    (cfg : AnchorConfig d) :
    ∀ {fuel epoch : ℕ} {history : OracleTrace d} {ar : AnchorResult d},
      runAnchor oracle cfg fuel epoch history = some ar →
      WasQueried ar.observations ar.acceptedPoint := by
  intro fuel
  induction fuel with
  | zero =>
      intro epoch history ar hrun
      simp [runAnchor] at hrun
  | succ fuel ih =>
      intro epoch history ar hrun
      rw [runAnchor] at hrun
      let D := anchorRadius cfg.G cfg.M₀ epoch
      let y := anchorProbePoint cfg.q cfg.x₀ cfg.g₀ cfg.G cfg.M₀ epoch
      by_cases hpass : oracle.value y ≤ cfg.f₀ - cfg.G * D / 2
      · dsimp only [D, y] at hpass
        simp only [hpass, ↓reduceIte, Option.some.injEq] at hrun
        subst ar
        refine ⟨oracle.observe y, ?_, rfl⟩
        simp [y]
      · dsimp only [D, y] at hpass
        simp only [hpass, ↓reduceIte] at hrun
        exact ih hrun

/-- Stage-3 termination transported to the concrete causal prefix. -/
theorem anchorPrefixMethod_admissible_anchor
    {p : ℝ} (P : AdmissibleInstance d p)
    (hlarge : P.eps < lpNorm (conjugateExponent p) (P.grad P.x0)) :
    let N := Nat.ceil (Real.logb 2 (P.L / P.M0))
    ∃ ar result,
      runAnchor P.oracle P.anchorConfig (1 + N) 0 [] = some ar ∧
      (anchorPrefixMethod d).run P.oracle P.methodInput ((1 + N) + 2) =
        some result ∧
      result.returned = ar.acceptedPoint ∧
      result.queries = [P.oracle.observe P.x0] ++ ar.observations ∧
      result.callCount = 1 + ar.observations.length ∧
      TraceExact P.oracle result.queries ∧
      result.returnedWasQueried ∧
      ar.acceptedScale < 2 * P.L ∧
      ar.acceptedRadius ≤ 2 * P.radius ∧
      ar.observations.length ≤ 1 + N := by
  dsimp only
  obtain ⟨ar, har, hscale, hradius, hpoint, htest, hscaleBound,
      hradiusBound, hcalls, htrace⟩ := anchor p d P hlarge
  let result : RunResult d :=
    { returned := ar.acceptedPoint
      queries := [P.oracle.observe P.x0] ++ ar.observations }
  have hcfg : anchorPrefixConfig P.methodInput
      (P.oracle.value P.methodInput.x0)
      (P.oracle.gradient P.methodInput.x0)
      (lpNorm (conjugateExponent P.methodInput.p)
        (P.oracle.gradient P.methodInput.x0)) =
      P.anchorConfig := by
    rfl
  have har' : runAnchor P.oracle
      (anchorPrefixConfig P.methodInput
        (P.oracle.value P.methodInput.x0)
        (P.oracle.gradient P.methodInput.x0)
        (lpNorm (conjugateExponent P.methodInput.p)
          (P.oracle.gradient P.methodInput.x0)))
      (1 + Nat.ceil (Real.logb 2 (P.L / P.M0))) 0 [] = some ar := by
    rw [hcfg]
    exact har
  have hmethod := anchorPrefixMethod_anchor_run_of_runAnchor P.oracle
    P.methodInput
    (by simpa [AdmissibleInstance.methodInput, AdmissibleInstance.oracle] using hlarge)
    (anchorFuel := 1 + Nat.ceil (Real.logb 2 (P.L / P.M0))) (ar := ar) har'
  refine ⟨ar, result, har, ?_, rfl, rfl, ?_, ?_, ?_, hscaleBound,
    hradiusBound, hcalls⟩
  · simpa [result, AdmissibleInstance.methodInput] using hmethod
  · simp [result, RunResult.callCount]
    omega
  · apply traceExact_append
    · intro o ho
      simp only [List.mem_singleton] at ho
      subst o
      rfl
    · exact htrace
  · obtain ⟨o, ho, hopoint⟩ :=
      runAnchor_acceptedPoint_queried P.oracle P.anchorConfig har
    unfold RunResult.returnedWasQueried
    change ar.acceptedPoint ∈
      (P.oracle.observe P.x0 :: ar.observations).map Observation.point
    simp only [List.map_cons, List.mem_cons]
    exact Or.inr (List.mem_map.mpr ⟨o, ho, hopoint⟩)

end O3
