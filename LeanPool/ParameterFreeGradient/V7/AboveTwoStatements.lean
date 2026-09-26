/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.BelowTwoStatements

/-!
The geometry, residual identities, phase bounds, and operational contracts for exponents above
two.
-/

@[expose] public section

namespace V7

/-- The power mirror potential `‖x‖ₚ^p / p` used for exponents above two. -/
noncomputable def aboveH (p : ℝ) (x : Point d) : ℝ :=
  (1 / p) * (lpNorm p x) ^ p

/-- The conjugate power potential with the Hölder-conjugate exponent. -/
noncomputable def aboveHstar (p : ℝ) (s : Point d) : ℝ :=
  (1 / conjugateExponent p) * (lpNorm (conjugateExponent p) s) ^ (conjugateExponent p)

/-- The power duality map at the Hölder-conjugate exponent. -/
noncomputable def aboveMirrorMap (p : ℝ) (s : Point d) : Point d :=
  O3.powerDualityMap (conjugateExponent p) s

/-- The conjugacy, gradient, uniform convexity, and Bregman identities for the above-two
geometry. -/
noncomputable def AboveGeometryStatement : Prop :=
  ∀ (p : ℝ), 2 < p → ∀ (d : ℕ),
    (∀ s : Point d, FenchelConjugate (aboveH p) s = aboveHstar p s) ∧
    O3.IsCoordinateGradient
      (fun s : Point d => aboveHstar p s)
      (fun s : Point d => aboveMirrorMap p s) ∧
    (∀ x y : Point d,
      FunctionBregman (aboveH p)
        (fun z => O3.powerDualityMap p z) x y ≥
          (2 ^ (2 - p) / p) * (lpNorm p (x - y)) ^ p) ∧
    ∀ s t : Point d,
      FunctionBregman (aboveHstar p) (aboveMirrorMap p) s t =
        FunctionBregman (aboveH p) (fun z => O3.powerDualityMap p z)
          (aboveMirrorMap p t) (aboveMirrorMap p s)

/-- The uniform convexity constant of the power mirror potential. -/
noncomputable def aboveUniformConstant (p : ℝ) : ℝ := 2 ^ (2 - p) / p
/-- The exponent in the accumulated above-two residual error. -/
noncomputable def aboveErrorPower (p : ℝ) : ℝ := p / (p - 2)
/-- The coefficient of the error bound obtained from the above-two mixed residual. -/
noncomputable def aboveErrorConstant (p : ℝ) : ℝ :=
  (p - 2) / (2 * p) * (p * aboveUniformConstant p) ^ (-2 / (p - 2))
/-- The error constant after bounding the squared weight increments by their growth rate. -/
noncomputable def aboveBudgetConstant (p : ℝ) : ℝ :=
  4 ^ (aboveErrorPower p) * aboveErrorConstant p
/-- The exponent relating an above-two error budget to the coefficient scale. -/
noncomputable def aboveBudgetExponent (p : ℝ) : ℝ := (p - 2) / p
/-- The coefficient of the terminal weight in terms of the error budget and horizon. -/
noncomputable def aboveGrowthConstant (p : ℝ) : ℝ :=
  (2 * aboveBudgetConstant p) ^ (-aboveBudgetExponent p)
/-- The exponent-dependent constant used to choose the primal trial horizon. -/
noncomputable def aboveHp (p : ℝ) : ℝ :=
  3 * p ^ (aboveBudgetExponent p) / (2 * p * aboveGrowthConstant p)
/-- The exponent-dependent constant used to choose the dual trial horizon. -/
noncomputable def aboveJp (p : ℝ) : ℝ :=
  2 * (conjugateExponent p) ^ (1 + aboveBudgetExponent p) /
    aboveGrowthConstant p
/-- The weight scale chosen from the error budget and iteration horizon. -/
noncomputable def aboveGamma (p eta : ℝ) (n : ℕ) : ℝ :=
  (eta / (2 * aboveBudgetConstant p * n)) ^ (aboveBudgetExponent p)

/-- The accumulated above-two residual error for a weight sequence and its increments. -/
noncomputable def aboveErrorSum (p : ℝ) (n : ℕ)
    (u dw : ScalarSeq) : ℝ :=
  aboveErrorConstant p *
    ∑ k ∈ Finset.range n, ((dw k) ^ (2 : ℕ) / u k) ^ (aboveErrorPower p)

/-- Quadratic trial weights meet the error budget and have the stated terminal growth. -/
noncomputable def AboveWeightErrorBalanceStatement : Prop :=
  ∀ (p : ℝ), 2 < p → ∀ (n : ℕ), 1 ≤ n → ∀ (eta : ℝ), 0 < eta →
    let gamma := aboveGamma p eta n
    let u : ScalarSeq := fun k =>
      if k < n then gamma * ((k : ℝ) + 1) ^ (2 : ℕ)
      else gamma * (n : ℝ) ^ (2 : ℕ)
    let dw : ScalarSeq := fun k => u k - (if k = 0 then 0 else u (k - 1))
    aboveErrorSum p n u dw ≤ eta / 2 ∧
    u n = aboveGrowthConstant p * eta ^ (aboveBudgetExponent p) *
      (n : ℝ) ^ ((p + 2) / p)

/-- The primal residual for above-two geometry, expressed through the common residual formula. -/
noncomputable def AbovePrimalResidual (p : ℝ) (n : ℕ)
    (u : ScalarSeq) (alpha : ScalarMatrix) (A B X : VectorSeq d)
    (Omega : Point d → ℝ) : ℝ :=
  BelowPrimalResidual p n u (fun _ => 0) alpha A B X Omega

/-- The dual residual for above-two geometry, expressed through the common residual formula. -/
noncomputable def AboveDualResidual (p : ℝ) (n : ℕ)
    (u : ScalarSeq) (alpha b : ScalarMatrix) (C D : VectorSeq d)
    (Omega : Point d → ℝ) : ℝ :=
  BelowDualResidual p n u alpha b C D Omega

/-- The weight, increment, matrix recurrence, row-sum, and support conditions for an above-two
phase. -/
def AboveCoefficientAssumptions (n : ℕ) (u dw : ScalarSeq)
    (alpha c b : ScalarMatrix) : Prop :=
  0 < u 0 ∧ u n = u (n - 1) ∧ dw n = 0 ∧ c 0 0 = 1 ∧ b 0 0 = -1 ∧
  (∀ k < n, 0 < u k ∧ u k ≤ u (k + 1) ∧
    dw k = u k - (if k = 0 then 0 else u (k - 1)) ∧
    ∀ i, alpha (k + 1) i = if i = k then dw k else 0) ∧
  (∀ k < n, ∀ i,
    c (k + 1) i =
      (u k / u (k + 1)) * c k i +
      ((dw (k + 1) + dw k) / u (k + 1)) * (if i = k + 1 then 1 else 0) -
      (dw k / u (k + 1)) * (if i = k then 1 else 0) ∧
    b (k + 1) i = c k i - c (k + 1) i) ∧
  (∀ k ≤ n, (∑ i ∈ Finset.range (k + 1), c k i) = 1) ∧
  (∀ k ≤ n, ∀ i, k < i → c k i = 0) ∧
  ∀ k < n, (∑ i ∈ Finset.range (k + 2), b (k + 1) i) = 0

/-- Source carrier for `lem:above-pointwise` (A05). -/
noncomputable def AbovePointwiseResidualIdentityStatement : Prop :=
  ∀ (p : ℝ), 2 < p → ∀ (d n : ℕ), 1 ≤ n → ∀ (u dw : ScalarSeq)
    (alpha c b : ScalarMatrix) (Omega : Point d → ℝ),
    AboveCoefficientAssumptions n u dw alpha c b → EvenIncrement Omega →
    (∀ A B : VectorSeq d, ∃ C D, BelowResidualMap n u A B C D) ∧
    (∀ C D : VectorSeq d, ∃ A B, BelowResidualMap n u A B C D) ∧
    (∀ A B C₁ D₁ C₂ D₂ : VectorSeq d,
      BelowResidualMap n u A B C₁ D₁ → BelowResidualMap n u A B C₂ D₂ →
      SameOnHorizon n C₁ C₂ ∧ SameOnHorizon n D₁ D₂) ∧
    (∀ A₁ B₁ A₂ B₂ C D : VectorSeq d,
      BelowResidualMap n u A₁ B₁ C D → BelowResidualMap n u A₂ B₂ C D →
      SameOnHorizon n A₁ A₂ ∧ SameOnHorizon n B₁ B₂) ∧
    ∀ A B C D X : VectorSeq d,
      A (n + 1) = 0 → BelowXRecurrence n b B X → BelowResidualMap n u A B C D →
      AbovePrimalResidual p n u alpha A B X Omega =
        AboveDualResidual p n u alpha b C D Omega

/-- Oracle, coefficients, iterates, and observations of an above-two primal phase. -/
structure AbovePrimalPhaseData (p : ℝ) (d n : ℕ) where
  /-- The value-gradient oracle used by the primal phase. -/
  oracle : PairOracle d
  /-- The proposed minimum value of the objective. -/
  fstar : ℝ
  /-- The cumulative weights of the primal phase. -/
  u : ScalarSeq
  /-- The successive weight increments, with zero terminal increment. -/
  dw : ScalarSeq
  /-- The matrix selecting the weighted gradient contribution at each step. -/
  alpha : ScalarMatrix
  /-- The coefficients expressing each primal iterate in the mirror iterates. -/
  c : ScalarMatrix
  /-- The successive differences of the primal coefficient rows. -/
  b : ScalarMatrix
  /-- The accumulated dual vectors updated by weighted gradients. -/
  s : VectorSeq d
  /-- The mirror-map images of the accumulated dual vectors. -/
  v : VectorSeq d
  /-- The primal query iterates. -/
  x : VectorSeq d
  /-- The chronological value-gradient observations of the phase. -/
  trace : List (Observation d)

/-- The above-two primal coefficient conditions, initial state, and step recurrences. -/
def AbovePrimalPhaseDynamics (data : AbovePrimalPhaseData p d n) : Prop :=
  1 ≤ n ∧ AboveCoefficientAssumptions n data.u data.dw data.alpha data.c data.b ∧
  data.s 0 = 0 ∧ data.v 0 = 0 ∧ data.x 0 = 0 ∧
  ∀ k < n,
    data.s (k + 1) = data.s k - data.dw k • data.oracle.gradient (data.x k) ∧
    data.v (k + 1) = aboveMirrorMap p (data.s (k + 1)) ∧
    data.x (k + 1) =
      (data.u k / data.u (k + 1)) • data.x k +
      (data.dw (k + 1) / data.u (k + 1)) • data.v (k + 1) +
      (data.dw k / data.u (k + 1)) • (data.v (k + 1) - data.v k)

/-- The primal dynamics, convex gradient oracle, attained minimum, guards, and exact query trace. -/
def AbovePrimalPhaseAssumptions (data : AbovePrimalPhaseData p d n) : Prop :=
  AbovePrimalPhaseDynamics data ∧ O3.IsConvexObjective data.oracle.value ∧
  O3.IsCoordinateGradient data.oracle.value data.oracle.gradient ∧
  data.fstar = sInf (Set.range data.oracle.value) ∧
  (∃ z, data.oracle.value z = data.fstar ∧
    ∀ x, data.oracle.value z ≤ data.oracle.value x) ∧
  AboveCoefficientAssumptions n data.u data.dw data.alpha data.c data.b ∧
  data.s 0 = 0 ∧ data.v 0 = 0 ∧ data.x 0 = 0 ∧
  (∀ k < n,
    data.s (k + 1) = data.s k - data.dw k • data.oracle.gradient (data.x k) ∧
    data.v (k + 1) = aboveMirrorMap p (data.s (k + 1)) ∧
    data.x (k + 1) =
      (data.u k / data.u (k + 1)) • data.x k +
      (data.dw (k + 1) / data.u (k + 1)) • data.v (k + 1) +
      (data.dw k / data.u (k + 1)) • (data.v (k + 1) - data.v k) ∧
    FunctionBregman data.oracle.value data.oracle.gradient
      (data.x k) (data.x (k + 1)) ≥
      (1 / 2) * (lpNorm (conjugateExponent p)
        (data.oracle.gradient (data.x k) -
          data.oracle.gradient (data.x (k + 1)))) ^ (2 : ℕ)) ∧
  TraceExact data.oracle data.trace ∧
  data.trace.length = n + 1 ∧
  ∀ k ≤ n, QueriedAt data.trace k (data.x k)

/-- Oracle, coefficients, iterates, and observations of an above-two dual phase. -/
structure AboveDualPhaseData (p : ℝ) (d n : ℕ) where
  /-- The value-gradient oracle used by the dual phase. -/
  oracle : PairOracle d
  /-- The cumulative weights underlying the reversed dual recurrence. -/
  u : ScalarSeq
  /-- The weight increments underlying the reversed dual recurrence. -/
  dw : ScalarSeq
  /-- The coefficient matrix used for the dual query updates. -/
  alpha : ScalarMatrix
  /-- The primal coefficient matrix associated with the dual phase. -/
  c : ScalarMatrix
  /-- The coefficient-row differences used to accumulate dual gradients. -/
  b : ScalarMatrix
  /-- The gradients observed at the dual query points. -/
  G : VectorSeq d
  /-- The accumulated vectors to which the dual mirror map is applied. -/
  r : VectorSeq d
  /-- The dual phase query points. -/
  q : VectorSeq d
  /-- The chronological value-gradient observations of the dual phase. -/
  trace : List (Observation d)

/-- The above-two coefficient conditions and reversed dual query and gradient recurrences. -/
def AboveDualPhaseDynamics (data : AboveDualPhaseData p d n) : Prop :=
  1 ≤ n ∧ AboveCoefficientAssumptions n data.u data.dw data.alpha data.c data.b ∧
  data.r 0 = -(data.b n n) • data.G 0 ∧
  ∀ k < n,
    data.q (k + 1) = data.q k -
      weightedSum (k + 1) (fun i => data.alpha (n - i) (n - 1 - k))
        (fun i => aboveMirrorMap p (data.r i)) ∧
    data.r (k + 1) = data.r k -
      weightedSum (k + 2) (fun i => data.b (n - i) (n - 1 - k)) data.G

/-- The dual dynamics, convex gradient oracle, lower bound, accepted guards, and exact trace. -/
def AboveDualPhaseAssumptions (data : AboveDualPhaseData p d n) : Prop :=
  AboveDualPhaseDynamics data ∧ O3.IsConvexObjective data.oracle.value ∧
  O3.IsCoordinateGradient data.oracle.value data.oracle.gradient ∧
  BddBelow (Set.range data.oracle.value) ∧
  TraceExact data.oracle data.trace ∧
  data.trace.length = n + 1 ∧
  (∀ k ≤ n, QueriedAt data.trace k (data.q k) ∧
    data.G k = data.oracle.gradient (data.q k)) ∧
  data.r 0 = -(data.b n n) • data.G 0 ∧
  ∀ k < n,
    data.q (k + 1) = data.q k -
      weightedSum (k + 1) (fun i => data.alpha (n - i) (n - 1 - k))
        (fun i => aboveMirrorMap p (data.r i)) ∧
    data.r (k + 1) = data.r k -
      weightedSum (k + 2) (fun i => data.b (n - i) (n - 1 - k)) data.G ∧
    FunctionBregman data.oracle.value data.oracle.gradient
      (data.q k) (data.q (k + 1)) ≥
      (1 / 2) * (lpNorm (conjugateExponent p)
        (data.G k - data.G (k + 1))) ^ (2 : ℕ)

/-- The two phase executions and numerical parameters witnessing an above-two trial. -/
structure AboveTrialWitness (p : ℝ) (d : ℕ) where
  /-- The planned number of primal phase iterations. -/
  nF : ℕ
  /-- The planned number of dual phase iterations. -/
  nD : ℕ
  /-- The number of primal iterations actually completed. -/
  completedF : ℕ
  /-- The number of dual iterations actually completed. -/
  completedD : ℕ
  /-- The primal phase error budget. -/
  etaF : ℝ
  /-- The dual phase error budget. -/
  etaD : ℝ
  /-- The scale of the primal phase weights. -/
  gammaF : ℝ
  /-- The scale of the dual phase weights. -/
  gammaD : ℝ
  /-- The recorded primal phase execution. -/
  phaseOne : AbovePrimalPhaseData p d nF
  /-- The recorded dual phase execution. -/
  phaseTwo : AboveDualPhaseData p d nD
  /-- The center used to translate the dual phase back to physical coordinates. -/
  phaseTwoCenter : Point d

/-- The horizon, normalization, phase execution, and report requirements of an above-two trial. -/
def AboveTrialOperationalContract (p eps M D : ℝ) (x0 : Point d)
    (cached : CachedPair d) (oracle : PairOracle d)
    (report : TrialReport d) (w : AboveTrialWitness p d) : Prop :=
  let delta := eps / (M * D)
  w.nF = Nat.ceil ((aboveHp p / delta) ^ (p / (p + 2))) ∧
  w.nD = Nat.ceil ((aboveJp p / delta) ^ (p / (p + 2))) ∧
  w.etaF = 1 / p ∧
  w.etaD = delta ^ (conjugateExponent p) / conjugateExponent p ∧
  w.gammaF = aboveGamma p w.etaF w.nF ∧
  w.gammaD = aboveGamma p w.etaD w.nD ∧
  (∀ k < w.nF,
    w.phaseOne.u k = w.gammaF * ((k : ℝ) + 1) ^ (2 : ℕ)) ∧
  w.phaseOne.u w.nF = w.gammaF * (w.nF : ℝ) ^ (2 : ℕ) ∧
  (∀ k < w.nD,
    w.phaseTwo.u k = w.gammaD * ((k : ℝ) + 1) ^ (2 : ℕ)) ∧
  w.phaseTwo.u w.nD = w.gammaD * (w.nD : ℝ) ^ (2 : ℕ) ∧
  w.phaseOne.oracle = normalizedPairOracle x0 M D oracle ∧
  AbovePrimalPhaseDynamics w.phaseOne ∧
  w.phaseTwoCenter = x0 + D • w.phaseOne.x w.nF ∧
  w.phaseTwo.oracle = normalizedPairOracle w.phaseTwoCenter M D oracle ∧
  w.phaseTwo.q 0 = 0 ∧ AboveDualPhaseDynamics w.phaseTwo ∧
  w.completedF ≤ w.nF ∧ w.completedD ≤ w.nD ∧
  (0 < w.completedD → w.completedF = w.nF) ∧
  (∀ k ≤ w.completedD,
    w.phaseTwo.G k = w.phaseTwo.oracle.gradient (w.phaseTwo.q k)) ∧
  report.trace =
    ((List.range w.completedF).map (fun k =>
      oracle.observe (x0 + D • w.phaseOne.x (k + 1)))) ++
    ((List.range w.completedD).map (fun k =>
      oracle.observe (w.phaseTwoCenter + D • w.phaseTwo.q (k + 1)))) ∧
  (∀ terminal, report.outcome = .success terminal →
    (0 < w.completedD ∧ terminal = oracle.observe
      (w.phaseTwoCenter + D • w.phaseTwo.q w.completedD)) ∨
    (w.completedD = 0 ∧ 0 < w.completedF ∧ terminal = oracle.observe
      (x0 + D • w.phaseOne.x w.completedF))) ∧
  (∀ terminal, report.outcome = .radius terminal →
    w.completedF = w.nF ∧ w.completedD = w.nD ∧
    terminal = oracle.observe
      (w.phaseTwoCenter + D • w.phaseTwo.q w.nD)) ∧
  CheckedGuardsHaveKinds report [.cocoercivity] ∧
  ConsecutiveGuardLedger cached report ∧
  report.consecutiveGuardAccounting ∧
  report.calls ≤ w.nF + w.nD

/-- Source carrier for `prop:abovetrial` (A01--A12), with the current
`p/(p+2)` exponent and endpoint reuse. -/
noncomputable def AboveTrialStatement : Prop :=
  ∀ (p : ℝ), 2 < p → ∃ Cp : ℝ,
    0 < Cp ∧ ∀ (d : ℕ)
    (eps M D : ℝ), 0 < eps → 0 < M → 0 < D → ∀ (x0 : Point d)
    (cached : CachedPair d), ∃ trial : LocalTrial d,
    ∀ inst : PositiveInstance p d x0,
    cached.observation = inst.oracle.observe x0 →
    eps < lpNorm (conjugateExponent p) (inst.oracle.gradient x0) →
    D ≥ lpNorm (conjugateExponent p) (inst.oracle.gradient x0) / M →
    ∃ (report : TrialReport d) (w : AboveTrialWitness p d),
      trial.Executes M D cached inst.oracle report ∧
      TrialCertificate eps p M D inst.L inst.R cached inst.oracle report ∧
      AboveTrialOperationalContract p eps M D x0 cached inst.oracle report w ∧
      (report.calls : ℝ) ≤
        Cp * (M * D / eps) ^ (p / (p + 2))

end V7
