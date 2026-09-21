/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.TrialInterfaces

/-!
The squared-norm geometry, residual identities, and two-phase trial contracts for exponents
below two.
-/

open scoped BigOperators

namespace V7

/-- The scaled squared norm mirror potential for exponents between one and two. -/
noncomputable def belowH (p : ℝ) (x : Point d) : ℝ :=
  (1 / (2 * (p - 1))) * (lpNorm p x) ^ (2 : ℕ)

/-- The conjugate scaled squared norm potential for the below-two geometry. -/
noncomputable def belowHstar (p : ℝ) (s : Point d) : ℝ :=
  ((p - 1) / 2) * (lpNorm (conjugateExponent p) s) ^ (2 : ℕ)

/-- The scaled duality map giving the gradient of the below-two conjugate potential. -/
noncomputable def belowMirrorMap (p : ℝ) (s : Point d) : Point d :=
  (p - 1) • O3.dualityMap (conjugateExponent p) s

/-- The Bregman difference of a function and its specified gradient, based at `y`. -/
noncomputable def FunctionBregman (F : Point d → ℝ) (grad : Point d → Point d)
    (x y : Point d) : ℝ :=
  F x - F y - pairing (grad y) (x - y)

/-- The real supremum of the affine dual pairings minus the objective. -/
noncomputable def FenchelConjugate (F : Point d → ℝ) (s : Point d) : ℝ :=
  sSup {r : ℝ | ∃ x : Point d, r = pairing s x - F x}

/-- Source carrier for `lem:belowgeometry` (B02). -/
noncomputable def BelowGeometryStatement : Prop :=
  ∀ (p : ℝ), 1 < p → p < 2 → ∀ (d : ℕ),
    (∀ x y : Point d,
      belowH p y ≥ belowH p x +
        pairing ((1 / (p - 1)) • O3.dualityMap p x) (y - x) +
        (1 / 2) * (lpNorm p (y - x)) ^ (2 : ℕ)) ∧
    (∀ x : Point d,
      lpNorm (conjugateExponent p) (O3.dualityMap p x) = lpNorm p x ∧
      pairing (O3.dualityMap p x) x = (lpNorm p x) ^ (2 : ℕ) ∧
      O3.dualityMap (conjugateExponent p) (O3.dualityMap p x) = x) ∧
    (∀ s : Point d, FenchelConjugate (belowH p) s = belowHstar p s) ∧
    O3.IsCoordinateGradient
      (fun s : Point d => belowHstar p s)
      (fun s : Point d => belowMirrorMap p s) ∧
    (∀ s t : Point d,
      FunctionBregman (belowHstar p) (belowMirrorMap p) s t =
        FunctionBregman (belowH p)
          (fun x => (1 / (p - 1)) • O3.dualityMap p x)
          (belowMirrorMap p t) (belowMirrorMap p s) ∧
      FunctionBregman (belowHstar p) (belowMirrorMap p) s t ≥
        (1 / 2) * (lpNorm p (belowMirrorMap p t - belowMirrorMap p s)) ^ (2 : ℕ))

/-- Oracle, minimizer, coefficients, iterates, and observations of a below-two primal phase. -/
structure BelowPrimalData (p : ℝ) (d n : ℕ) where
  /-- The value-gradient oracle of the primal phase. -/
  oracle : PairOracle d
  /-- The comparison minimizer used in the primal potential. -/
  z : Point d
  /-- The objective value at the comparison minimizer. -/
  fstar : ℝ
  /-- The quadratic cumulative weights of the below-two phase. -/
  u : ℕ → ℝ
  /-- The successive weight increments, with zero terminal increment. -/
  dw : ℕ → ℝ
  /-- The accumulated dual vectors updated by weighted gradients. -/
  s : ℕ → Point d
  /-- The mirror-map images of the accumulated dual vectors. -/
  v : ℕ → Point d
  /-- The primal query iterates. -/
  x : ℕ → Point d
  /-- The chronological oracle observations of the primal phase. -/
  trace : List (Observation d)

/-- The prescribed below-two weights, initial state, and primal update recurrences. -/
def BelowPrimalDynamics (data : BelowPrimalData p d n) : Prop :=
  1 ≤ n ∧ data.u 0 = 1 / 4 ∧ data.u n = data.u (n - 1) ∧
  data.dw n = 0 ∧
  (∀ k < n, data.u k = (((k : ℝ) + 1) ^ (2 : ℕ)) / 4 ∧
    data.dw k = data.u k - (if k = 0 then 0 else data.u (k - 1)) ∧
    data.dw k = ((2 : ℝ) * k + 1) / 4 ∧
    data.u k - (data.dw k) ^ (2 : ℕ) = ((4 : ℝ) * k + 3) / 16) ∧
  data.s 0 = 0 ∧ data.v 0 = 0 ∧ data.x 0 = 0 ∧
  ∀ k < n,
    data.s (k + 1) = data.s k - data.dw k • data.oracle.gradient (data.x k) ∧
    data.v (k + 1) = belowMirrorMap p (data.s (k + 1)) ∧
    data.x (k + 1) =
      (data.u k / data.u (k + 1)) • data.x k +
      (data.dw (k + 1) / data.u (k + 1)) • data.v (k + 1) +
      (data.dw k / data.u (k + 1)) • (data.v (k + 1) - data.v k)

/-- The below-two primal dynamics, convex gradient oracle, minimizer, guards, and exact trace. -/
def BelowPrimalAssumptions (data : BelowPrimalData p d n) : Prop :=
  BelowPrimalDynamics data ∧
  O3.IsConvexObjective data.oracle.value ∧
  O3.IsCoordinateGradient data.oracle.value data.oracle.gradient ∧
  data.fstar = data.oracle.value data.z ∧
  (∀ y, data.oracle.value data.z ≤ data.oracle.value y) ∧
  data.u 0 = 1 / 4 ∧ data.u n = data.u (n - 1) ∧ data.dw n = 0 ∧
  (∀ k < n, data.u k = (((k : ℝ) + 1) ^ (2 : ℕ)) / 4 ∧
    data.dw k = data.u k - (if k = 0 then 0 else data.u (k - 1)) ∧
    data.dw k = ((2 : ℝ) * k + 1) / 4 ∧
    data.u k - (data.dw k) ^ (2 : ℕ) = ((4 : ℝ) * k + 3) / 16) ∧
  data.s 0 = 0 ∧ data.v 0 = 0 ∧ data.x 0 = 0 ∧
  (∀ k < n,
    data.s (k + 1) = data.s k - data.dw k • data.oracle.gradient (data.x k) ∧
    data.v (k + 1) = belowMirrorMap p (data.s (k + 1)) ∧
    data.x (k + 1) =
      (data.u k / data.u (k + 1)) • data.x k +
      (data.dw (k + 1) / data.u (k + 1)) • data.v (k + 1) +
      (data.dw k / data.u (k + 1)) • (data.v (k + 1) - data.v k) ∧
    FunctionBregman data.oracle.value data.oracle.gradient (data.x k) (data.x (k + 1)) ≥
      (1 / 2) *
        (lpNorm (conjugateExponent p)
          (data.oracle.gradient (data.x k) - data.oracle.gradient (data.x (k + 1)))) ^ (2 : ℕ)) ∧
  TraceExact data.oracle data.trace ∧
  data.trace.length = n + 1 ∧
  ∀ k ≤ n, QueriedAt data.trace k (data.x k)

/-- Source carrier for `lem:below-primal` (B04--B05). -/
noncomputable def BelowPrimalStatement : Prop :=
  ∀ (p : ℝ), 1 < p → p < 2 → ∀ (d n : ℕ) (data : BelowPrimalData p d n),
    BelowPrimalAssumptions data →
    data.oracle.value (data.x n) - data.fstar ≤ belowH p data.z / data.u n

/-- A natural-number-indexed sequence of finite-dimensional real vectors. -/
abbrev VectorSeq (d : ℕ) := ℕ → Point d
/-- A natural-number-indexed sequence of real coefficients. -/
abbrev ScalarSeq := ℕ → ℝ
/-- A real coefficient array indexed by two natural numbers. -/
abbrev ScalarMatrix := ℕ → ℕ → ℝ

/-- The coordinatewise weighted sum of the first `n` vectors. -/
noncomputable def weightedSum (n : ℕ) (a : ScalarSeq) (X : VectorSeq d) : Point d :=
  fun j => ∑ i ∈ Finset.range n, a i * X i j

/-- The primal energy residual combining gradient differences, mirror increments, and mixed
pairings. -/
noncomputable def BelowPrimalResidual (p : ℝ) (n : ℕ)
    (u _dw : ScalarSeq) (alpha : ScalarMatrix) (A B X : VectorSeq d)
    (Omega : Point d → ℝ) : ℝ :=
  (∑ k ∈ Finset.range n,
      (u k / 2) * (lpNorm (conjugateExponent p) (A k - A (k + 1))) ^ (2 : ℕ)) +
  (∑ k ∈ Finset.range n, Omega (B k - B (k + 1))) +
  (∑ k ∈ Finset.range n,
      pairing (weightedSum (k + 1) (alpha (k + 1)) A) (B (k + 1))) -
  (∑ k ∈ Finset.range (n + 1),
      u k * pairing (A k - A (k + 1)) (X k))

/-- The reversed dual energy residual with reciprocal weights and mixed pairings. -/
noncomputable def BelowDualResidual (p : ℝ) (n : ℕ)
    (u : ScalarSeq) (alpha b : ScalarMatrix) (C D : VectorSeq d)
    (Omega : Point d → ℝ) : ℝ :=
  let w : ScalarSeq := fun i => 1 / u (n - i)
  (∑ k ∈ Finset.range n,
      (w (k + 1) / 2) *
        (lpNorm (conjugateExponent p) (C k - C (k + 1))) ^ (2 : ℕ)) +
  (∑ k ∈ Finset.range n, Omega (D k - D (k + 1))) +
  (∑ k ∈ Finset.range (n + 1),
      pairing (weightedSum (k + 1) (fun i => b (n - i) (n - k)) C) (D k)) +
  (∑ k ∈ Finset.range n,
      pairing
        (w (k + 1) • C (k + 1) -
          weightedSum (k + 1) (fun j => w (j + 1) - w j) C)
        (weightedSum (k + 1) (fun i => alpha (n - i) (n - 1 - k)) D))

/-- The increment potential is unchanged when its argument is negated. -/
def EvenIncrement (Omega : Point d → ℝ) : Prop := ∀ x, Omega (-x) = Omega x

/-- The reverse-indexed gradient and mirror correspondence used in the residual identity. -/
def BelowResidualMap (n : ℕ) (u : ScalarSeq) (A B C D : VectorSeq d) : Prop :=
  C 0 = u n • A n ∧
  (∀ i < n, C (n - i) - C (n - i - 1) = u i • (A i - A (i + 1))) ∧
  ∀ i ≤ n, D i = B (n - i)

/-- The primal iterate recurrence driven by coefficient-row differences. -/
def BelowXRecurrence (n : ℕ) (b : ScalarMatrix)
    (B X : VectorSeq d) : Prop :=
  X 0 = B 0 ∧ ∀ k < n,
    X (k + 1) = X k - weightedSum (k + 2) (b (k + 1)) B

/-- The explicit quadratic weights and coefficient recurrences for the below-two residual
identity. -/
def BelowCoefficientAssumptions (n : ℕ) (u dw : ScalarSeq)
    (alpha c b : ScalarMatrix) : Prop :=
  u 0 = 1 / 4 ∧ u n = u (n - 1) ∧ dw n = 0 ∧ c 0 0 = 1 ∧ b 0 0 = -1 ∧
  (∀ k < n, u k = (((k : ℝ) + 1) ^ (2 : ℕ)) / 4 ∧
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

/-- Two vector sequences agree through the inclusive horizon `n`. -/
def SameOnHorizon (n : ℕ) (A B : VectorSeq d) : Prop :=
  ∀ k ≤ n, A k = B k

/-- Source carrier for `lem:below-identity` (B06--B07). -/
noncomputable def BelowPointwiseResidualIdentityStatement : Prop :=
  ∀ (p : ℝ), 1 < p → p < 2 → ∀ (d n : ℕ), 1 ≤ n →
    ∀ (u dw : ScalarSeq) (alpha c b : ScalarMatrix)
    (Omega : Point d → ℝ), BelowCoefficientAssumptions n u dw alpha c b →
    EvenIncrement Omega →
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
      BelowPrimalResidual p n u dw alpha A B X Omega =
        BelowDualResidual p n u alpha b C D Omega

/-- Oracle, coefficients, gradients, iterates, and observations of a below-two dual phase. -/
structure BelowDualData (p : ℝ) (d n : ℕ) where
  /-- The value-gradient oracle of the below-two dual phase. -/
  oracle : PairOracle d
  /-- The cumulative weights underlying the reversed dual recurrence. -/
  u : ScalarSeq
  /-- The increments of the cumulative weight sequence. -/
  dw : ScalarSeq
  /-- The coefficient matrix used for the dual query updates. -/
  alpha : ScalarMatrix
  /-- The primal coefficient matrix associated with the dual phase. -/
  c : ScalarMatrix
  /-- The coefficient-row differences used to accumulate dual gradients. -/
  b : ScalarMatrix
  /-- The gradients observed at the dual query points. -/
  G : VectorSeq d
  /-- The dual phase query points. -/
  q : VectorSeq d
  /-- The accumulated vectors to which the dual mirror map is applied. -/
  r : VectorSeq d
  /-- The chronological oracle observations of the dual phase. -/
  trace : List (Observation d)

/-- The below-two coefficient conditions and reversed dual query and gradient recurrences. -/
def BelowDualDynamics (data : BelowDualData p d n) : Prop :=
  1 ≤ n ∧
  BelowCoefficientAssumptions n data.u data.dw data.alpha data.c data.b ∧
  data.r 0 = -(data.b n n) • data.G 0 ∧
  ∀ k < n,
    data.q (k + 1) = data.q k -
      weightedSum (k + 1) (fun i => data.alpha (n - i) (n - 1 - k))
        (fun i => belowMirrorMap p (data.r i)) ∧
    data.r (k + 1) = data.r k -
      weightedSum (k + 2) (fun i => data.b (n - i) (n - 1 - k)) data.G

/-- The below-two dual dynamics, convex gradient oracle, lower bound, guards, and exact trace. -/
def BelowDualAssumptions (data : BelowDualData p d n) : Prop :=
  BelowDualDynamics data ∧ O3.IsConvexObjective data.oracle.value ∧
  O3.IsCoordinateGradient data.oracle.value data.oracle.gradient ∧
  BddBelow (Set.range data.oracle.value) ∧
  BelowCoefficientAssumptions n data.u data.dw data.alpha data.c data.b ∧
  TraceExact data.oracle data.trace ∧
  data.trace.length = n + 1 ∧
  (∀ k ≤ n, QueriedAt data.trace k (data.q k)) ∧
  (∀ k ≤ n, data.G k = data.oracle.gradient (data.q k)) ∧
  data.r 0 = -(data.b n n) • data.G 0 ∧
  (∀ k < n,
    data.q (k + 1) = data.q k -
      weightedSum (k + 1) (fun i => data.alpha (n - i) (n - 1 - k))
        (fun i => belowMirrorMap p (data.r i)) ∧
    data.r (k + 1) = data.r k -
      weightedSum (k + 2) (fun i => data.b (n - i) (n - 1 - k)) data.G) ∧
  ∀ k < n,
    FunctionBregman data.oracle.value data.oracle.gradient (data.q k) (data.q (k + 1)) ≥
      (1 / 2) *
        (lpNorm (conjugateExponent p)
          (data.oracle.gradient (data.q k) - data.oracle.gradient (data.q (k + 1)))) ^ (2 : ℕ)

/-- Source carrier for `lem:below-dual` (B07--B08). -/
noncomputable def BelowTerminalGradientStatement : Prop :=
  ∀ (p : ℝ), 1 < p → p < 2 → ∀ (d n : ℕ) (data : BelowDualData p d n),
    BelowDualAssumptions data →
    data.r n = data.G n ∧
      belowHstar p (data.oracle.gradient (data.q n)) ≤
        (data.oracle.value (data.q 0) -
          sInf (Set.range data.oracle.value)) / data.u n

/-- Source carrier for `lem:below-guard-scaling` (B12), including the exact
argument orientation in both normalized and physical Bregman remainders. -/
noncomputable def BelowGuardScalingStatement : Prop :=
  ∀ (p M D : ℝ), 1 < p → 0 < M → 0 < D → ∀ (d : ℕ)
    (oracle : PairOracle d) (c x y : Point d),
    let X := c + D • x
    let Y := c + D • y
    let F : Point d → ℝ := fun z =>
      (oracle.value (c + D • z) - oracle.value c) / (M * D ^ (2 : ℕ))
    let gradF : Point d → Point d := fun z =>
      (1 / (M * D)) • oracle.gradient (c + D • z)
    (∀ z, gradF z = (1 / (M * D)) • oracle.gradient (c + D • z)) ∧
    FunctionBregman F gradF x y =
      BregmanRemainder oracle X Y / (M * D ^ (2 : ℕ)) ∧
    (FunctionBregman F gradF x y ≥
        (1 / 2) * (lpNorm (conjugateExponent p) (gradF x - gradF y)) ^ (2 : ℕ) ↔
      CocoercivityGuard p M oracle X Y)

/-- The oracle translated by `c` and rescaled by the distance and smoothness estimates. -/
noncomputable def normalizedPairOracle (c : Point d) (M D : ℝ)
    (oracle : PairOracle d) : PairOracle d :=
  { value := fun y =>
      (oracle.value (c + D • y) - oracle.value c) / (M * D ^ (2 : ℕ))
    gradient := fun y => (1 / (M * D)) • oracle.gradient (c + D • y) }

/-- The source's two finite phases, including their recurrences, the reused
endpoint, and the fact that every physical iterate is in the actual report. -/
structure BelowTrialWitness (p : ℝ) (d : ℕ) where
  /-- The shared planned horizon of the two below-two phases. -/
  n : ℕ
  /-- The number of primal iterations actually completed. -/
  completedOne : ℕ
  /-- The number of dual iterations actually completed. -/
  completedTwo : ℕ
  /-- The recorded normalized primal phase execution. -/
  phaseOne : BelowPrimalData p d n
  /-- The recorded normalized dual phase execution. -/
  phaseTwo : BelowDualData p d n
  /-- The physical center of the translated dual phase. -/
  phaseTwoCenter : Point d

/-- The horizon, normalization, phase execution, and report requirements of a below-two trial. -/
def BelowTrialOperationalContract (p eps M D : ℝ) (x0 : Point d)
    (cached : CachedPair d) (oracle : PairOracle d)
    (report : TrialReport d) (w : BelowTrialWitness p d) : Prop :=
  w.n = Nat.ceil (2 * Real.sqrt (M * D / ((p - 1) * eps))) ∧
  w.phaseOne.oracle = normalizedPairOracle x0 M D oracle ∧
  BelowPrimalDynamics w.phaseOne ∧
  w.phaseTwoCenter = x0 + D • w.phaseOne.x w.n ∧
  w.phaseTwo.oracle = normalizedPairOracle w.phaseTwoCenter M D oracle ∧
  w.phaseTwo.q 0 = 0 ∧ BelowDualDynamics w.phaseTwo ∧
  w.completedOne ≤ w.n ∧ w.completedTwo ≤ w.n ∧
  (0 < w.completedTwo → w.completedOne = w.n) ∧
  (∀ k ≤ w.completedTwo,
    w.phaseTwo.G k = w.phaseTwo.oracle.gradient (w.phaseTwo.q k)) ∧
  report.trace =
    ((List.range w.completedOne).map (fun k =>
      oracle.observe (x0 + D • w.phaseOne.x (k + 1)))) ++
    ((List.range w.completedTwo).map (fun k =>
      oracle.observe (w.phaseTwoCenter + D • w.phaseTwo.q (k + 1)))) ∧
  (∀ terminal, report.outcome = .success terminal →
    (0 < w.completedTwo ∧ terminal = oracle.observe
      (w.phaseTwoCenter + D • w.phaseTwo.q w.completedTwo)) ∨
    (w.completedTwo = 0 ∧ 0 < w.completedOne ∧ terminal = oracle.observe
      (x0 + D • w.phaseOne.x w.completedOne))) ∧
  (∀ terminal, report.outcome = .radius terminal →
    w.completedOne = w.n ∧ w.completedTwo = w.n ∧
    terminal = oracle.observe
      (w.phaseTwoCenter + D • w.phaseTwo.q w.n)) ∧
  CheckedGuardsHaveKinds report [.cocoercivity] ∧
  ConsecutiveGuardLedger cached report ∧
  report.consecutiveGuardAccounting ∧
  report.calls ≤ 2 * w.n

/-- Source carrier for `prop:belowtrial` (B01--B13), with the current no-log
local count. -/
noncomputable def BelowTrialStatement : Prop :=
  ∀ (p : ℝ), 1 < p → p < 2 → ∀ (d : ℕ) (eps M D : ℝ),
    0 < eps → 0 < M → 0 < D → ∀ (x0 : Point d)
    (cached : CachedPair d),
    ∃ trial : LocalTrial d, ∀ inst : PositiveInstance p d x0,
    cached.observation = inst.oracle.observe x0 →
    eps < lpNorm (conjugateExponent p) (inst.oracle.gradient x0) →
    D ≥ lpNorm (conjugateExponent p) (inst.oracle.gradient x0) / M →
    ∃ (report : TrialReport d) (w : BelowTrialWitness p d),
      trial.Executes M D cached inst.oracle report ∧
      TrialCertificate eps p M D inst.L inst.R cached inst.oracle report ∧
      BelowTrialOperationalContract p eps M D x0 cached inst.oracle report w ∧
      (report.calls : ℝ) ≤
        4 * Real.sqrt (M * D / ((p - 1) * eps)) + 2 ∧
      (report.calls : ℝ) ≤
        (4 / Real.sqrt (p - 1) + 2) * Real.sqrt (M * D / eps)

end V7
