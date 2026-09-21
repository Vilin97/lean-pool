/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import LeanPool.ParameterFreeGradient.V7.AboveTwoStatements
import LeanPool.ParameterFreeGradient.V7.StrictModel

/-!
Smoothing kernels, resisting oracle completions, and known-parameter lower-bound statements.
-/

open scoped BigOperators

namespace V7

/-- Causal deterministic exact-pair algorithm for the known-parameter lower
bound.  No inverse-gradient or unqueried-output channel is present. -/
structure DeterministicExactPairAlgorithm (d : ℕ) where
  /-- The next query determined by the initial point and observation history. -/
  nextQuery : Point d → List (Observation d) → Point d
  /-- The output determined by the initial point and observation history. -/
  output : Point d → List (Observation d) → Point d

/-- Each trace point is the deterministic algorithm's query for the preceding history. -/
def GeneratedBy (algorithm : DeterministicExactPairAlgorithm d) (x0 : Point d)
    (trace : List (Observation d)) : Prop :=
  ∀ (t : ℕ) (ht : t < trace.length),
    (trace.get ⟨t, ht⟩).point =
      if t = 0 then x0 else algorithm.nextQuery x0 (trace.take t)

/-- A smoothing potential, its derivatives, curvature bound, and induced oracle transformation. -/
structure SmoothingKernelData (p : ℝ) (d : ℕ) where
  /-- The convex potential used to regularize the nonsmooth objective. -/
  phi : Point d → ℝ
  /-- The coordinate gradient of the smoothing potential. -/
  gradPhi : Point d → Point d
  /-- The derivative of the kernel gradient, viewed as a continuous linear map. -/
  hessian : Point d → (Point d →L[ℝ] Point d)
  /-- The dimension- and exponent-dependent curvature bound for the kernel. -/
  Mpd : ℝ
  /-- The oracle obtained by smoothing an objective at a given scale. -/
  smooth : ℝ → (Point d → ℝ) → PairOracle d

/-- The infimal convolution of the objective with the rescaled smoothing potential. -/
noncomputable def localSmoothingValue (kernel : SmoothingKernelData p d)
    (chi : ℝ) (ell : Point d → ℝ) (x : Point d) : ℝ :=
  sInf {r : ℝ | ∃ v : Point d,
    r = ell (x + v) + chi * kernel.phi ((1 / chi) • v)}

/-- The objective is one-Lipschitz with respect to the `ℓp` norm. -/
def IsOneLipschitz (p : ℝ) (f : Point d → ℝ) : Prop :=
  ∀ x y, |f x - f y| ≤ lpNorm p (x - y)

/-- The primal and dual transformations preserve their norms and mutual pairing. -/
def SignedLpSymmetry (p : ℝ) (Q Qdual : Point d → Point d) : Prop :=
  (∀ x, lpNorm p (Q x) = lpNorm p x) ∧
  (∀ s, lpNorm (conjugateExponent p) (Qdual s) =
    lpNorm (conjugateExponent p) s) ∧
  (∀ s x, pairing (Qdual s) (Q x) = pairing s x)

/-- The regularity, curvature, normalization, and smoothing properties required of a kernel. -/
def SmoothingKernelAssumptions (kernel : SmoothingKernelData p d) : Prop :=
  0 < kernel.Mpd ∧
  O3.IsConvexObjective kernel.phi ∧
  ContDiff ℝ 2 kernel.phi ∧
  O3.IsCoordinateGradient kernel.phi kernel.gradPhi ∧
  (∀ x, HasFDerivAt kernel.gradPhi (kernel.hessian x) x) ∧
  (∀ x, kernel.phi x ≥ 0) ∧
  kernel.phi 0 = 0 ∧
  kernel.gradPhi 0 = 0 ∧
  (∀ x, lpNorm p x = 1 → kernel.phi x > lpNorm p x) ∧
  (∀ x e, lpNorm p x ≤ 1 →
    pairing e (kernel.hessian x e) ≤
      kernel.Mpd * (lpNorm p e) ^ (2 : ℕ)) ∧
  (∀ (Q Qdual : Point d → Point d), SignedLpSymmetry p Q Qdual →
    ∀ x, kernel.phi (Q x) = kernel.phi x) ∧
  (∀ (chi : ℝ), 0 < chi → ∀ (ell : Point d → ℝ),
    O3.IsConvexObjective ell → IsOneLipschitz p ell → ∀ x,
    (kernel.smooth chi ell).value x = localSmoothingValue kernel chi ell x) ∧
  (∀ (chi : ℝ), 0 < chi → ∀ ell : Point d → ℝ,
    O3.IsConvexObjective ell → IsOneLipschitz p ell →
    O3.IsCoordinateGradient (kernel.smooth chi ell).value
      (kernel.smooth chi ell).gradient ∧
    (∀ x, ell x - chi ≤ (kernel.smooth chi ell).value x ∧
      (kernel.smooth chi ell).value x ≤ ell x) ∧
    IsLpSmooth p (kernel.Mpd / chi) (kernel.smooth chi ell)) ∧
  (∀ (chi : ℝ), 0 < chi → ∀ ell₁ ell₂ : Point d → ℝ,
    O3.IsConvexObjective ell₁ → IsOneLipschitz p ell₁ →
    O3.IsConvexObjective ell₂ → IsOneLipschitz p ell₂ →
    ∀ x, (∀ v, lpNorm p v ≤ chi → ell₁ (x + v) = ell₂ (x + v)) →
      (kernel.smooth chi ell₁).observe x =
        (kernel.smooth chi ell₂).observe x) ∧
  ∀ (chi : ℝ), 0 < chi → ∀ (ell : Point d → ℝ)
    (Q Qdual : Point d → Point d),
    O3.IsConvexObjective ell → IsOneLipschitz p ell →
    SignedLpSymmetry p Q Qdual →
    ∀ x,
      (kernel.smooth chi (fun z => ell (Q z))).value x =
        (kernel.smooth chi ell).value (Q x)

/-- The signed-coordinate-invariant power kernel used in the lower-bound construction. -/
noncomputable def lowerKernelPhi (r0 theta : ℝ) (x : Point d) : ℝ :=
  2 * (∑ j, |x j| ^ r0) ^ (2 * theta / r0)

/-- A smoothing kernel exists with the prescribed power formula and dimension-dependent bounds. -/
noncomputable def SmoothingKernelConstructionStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (p : ℝ), 2 < p → ∀ (d : ℕ), 2 ≤ d →
    ∃ (r0 theta : ℝ) (kernel : SmoothingKernelData p d),
      r0 = min p (3 * Real.log d) ∧ 1 < theta ∧ 2 * theta < r0 ∧
      kernel.phi = lowerKernelPhi r0 theta ∧
      SmoothingKernelAssumptions kernel ∧
      (∀ x e,
        pairing e (kernel.hessian x e) ≤
          4 * theta * (r0 - 1) * (lpNorm r0 x) ^ (2 * theta - 2) *
            (lpNorm r0 e) ^ (2 : ℕ)) ∧
      kernel.Mpd ≤ (if p ≤ 3 * Real.log d then 5 * p
        else 15 * Real.exp (2 / 3) * Real.log d) ∧
      kernel.Mpd ≤ C * min p (Real.log d)

/-- The adaptive partial objectives, queries, and final oracle in the resisting construction. -/
structure LowerCompletionData (p : ℝ) (d T : ℕ) where
  /-- The deterministic algorithm against which the resisting oracle is constructed. -/
  algorithm : DeterministicExactPairAlgorithm d
  /-- The initial query point. -/
  x0 : Point d
  /-- The kernel used to smooth the resisting maxima. -/
  kernel : SmoothingKernelData p d
  /-- The main separation scale in the resisting construction. -/
  Delta : ℝ
  /-- The offset between successive affine pieces of the resisting maximum. -/
  delta : ℝ
  /-- The smoothing scale of the partial objectives. -/
  chi : ℝ
  /-- The coefficient of the added norm regularization. -/
  beta : ℝ
  /-- The successive maxima of signed coordinate affine functions. -/
  partialG : ℕ → Point d → ℝ
  /-- The successive regularized nonsmooth objectives. -/
  partialH : ℕ → Point d → ℝ
  /-- The smooth oracle for each partial objective. -/
  partialOracle : ℕ → PairOracle d
  /-- The final oracle that preserves the earlier observations. -/
  completedOracle : PairOracle d
  /-- The queries generated against the successive partial oracles. -/
  queries : ℕ → Point d
  /-- The coordinate selected at each resisting step. -/
  sigma : ℕ → Fin d
  /-- The sign selected for each resisting coordinate. -/
  xi : ℕ → ℝ

/-- The partial objective is exactly the maximum of the affine pieces selected through `t`. -/
def ResistingMaximumAt (data : LowerCompletionData p d T) (t : ℕ) : Prop :=
  ∀ x,
    (∀ i ≤ t,
      data.xi i * x (data.sigma i) - (i : ℝ) * data.delta ≤
        data.partialG t x) ∧
    ∃ i ≤ t,
      data.partialG t x =
        data.xi i * x (data.sigma i) - (i : ℝ) * data.delta

/-- The scales, fresh coordinates, oracle consistency, and adaptive queries of the resisting
construction. -/
def LowerCompletionAssumptions (data : LowerCompletionData p d T) : Prop :=
  2 < p ∧ 2 ≤ d ∧ 1 ≤ T ∧ T ≤ d ∧
  data.x0 = 0 ∧
  SmoothingKernelAssumptions data.kernel ∧
  data.Delta = (T : ℝ) ^ (-1 / p) ∧
  data.delta = data.Delta / (2 * T) ∧
  data.chi = data.delta / 2 ∧
  data.beta = data.chi / data.kernel.Mpd ∧
  (∀ t < T, data.queries t =
    if t = 0 then data.x0 else
      data.algorithm.nextQuery data.x0
        ((List.range t).map fun s => (data.partialOracle s).observe (data.queries s))) ∧
  (∀ t < T, (∀ s < t, data.sigma s ≠ data.sigma t) ∧
    (data.sigma t).val < T ∧
    (∀ j : Fin d, j.val < T → (∀ s < t, data.sigma s ≠ j) →
      |data.queries t j| ≤ |data.queries t (data.sigma t)|) ∧
    (data.xi t = 1 ∨ data.xi t = -1) ∧
    data.xi t * data.queries t (data.sigma t) =
      |data.queries t (data.sigma t)| ∧
    ResistingMaximumAt data t ∧
    (∀ x, data.partialH t x =
      max (data.partialG t x / 2) (lpNorm p x - 3 / 2)) ∧
    (∀ x, (data.partialOracle t).value x =
      data.beta * (data.kernel.smooth data.chi (data.partialH t)).value x) ∧
    (∀ x, (data.partialOracle t).gradient x =
      data.beta • (data.kernel.smooth data.chi (data.partialH t)).gradient x)) ∧
  (∀ x, data.completedOracle.value x =
    data.beta * (data.kernel.smooth data.chi (data.partialH (T - 1))).value x) ∧
  ∀ x, data.completedOracle.gradient x =
    data.beta • (data.kernel.smooth data.chi (data.partialH (T - 1))).gradient x

/-- Source carrier for `lem:above-lower-completion` (L01--L04): both value
and gradient agree at every chronological query. -/
def AboveLowerExactPairCompletionStatement : Prop :=
  ∀ (p : ℝ), 2 < p → ∀ (d T : ℕ) (data : LowerCompletionData p d T),
    LowerCompletionAssumptions data →
    ∀ t < T,
      data.completedOracle.observe (data.queries t) =
        (data.partialOracle t).observe (data.queries t)

/-- The completed resisting construction viewed as lower-bound objective data. -/
structure LowerObjectiveData (p : ℝ) (d T : ℕ)
    extends LowerCompletionData p d T

/-- The objective eventually exceeds every real bound outside a sufficiently large `ℓp` ball. -/
def IsCoerciveLp (p : ℝ) (f : Point d → ℝ) : Prop :=
  ∀ B : ℝ, ∃ radius : ℝ, 0 ≤ radius ∧
    ∀ x, radius ≤ lpNorm p x → B ≤ f x

/-- The completion conditions together with convexity and the exact coordinate gradient. -/
def LowerObjectiveAssumptions (data : LowerObjectiveData p d T) : Prop :=
  LowerCompletionAssumptions data.toLowerCompletionData ∧
  O3.IsConvexObjective data.completedOracle.value ∧
  O3.IsCoordinateGradient data.completedOracle.value data.completedOracle.gradient

/-- Source carrier for `lem:above-lower-gap` (L05). -/
noncomputable def AboveLowerQueryGapStatement : Prop :=
  ∀ (p : ℝ), 2 < p → ∀ (d T : ℕ) (data : LowerObjectiveData p d T),
    LowerObjectiveAssumptions data →
    IsCoerciveLp p data.completedOracle.value ∧
    ∃ minimizer : Point d,
      (∀ x, data.completedOracle.value minimizer ≤ data.completedOracle.value x) ∧
      ∀ t < T,
        data.completedOracle.value (data.queries t) -
          data.completedOracle.value minimizer ≥
        1 / (16 * data.kernel.Mpd * (T : ℝ) ^ (1 + 2 / p))

/-- Source carrier for `lem:above-lower-outside` (L06). -/
noncomputable def AboveLowerOutsideGradientStatement : Prop :=
  ∀ (p : ℝ), 2 < p → ∀ (d T : ℕ) (data : LowerObjectiveData p d T),
    LowerObjectiveAssumptions data →
    (∀ x, 4 ≤ lpNorm p x →
      lpNorm (conjugateExponent p)
        ((data.kernel.smooth data.chi
          (data.partialH (T - 1))).gradient x) = 1 ∧
      lpNorm (conjugateExponent p) (data.completedOracle.gradient x) = data.beta) ∧
    ∀ x, (∀ y, data.completedOracle.value x ≤ data.completedOracle.value y) →
      lpNorm p x < 4

/-- Source carrier for `prop:above-lower-base-gradient` (L07). -/
noncomputable def AboveLowerBaseGradientStatement : Prop :=
  ∀ (p : ℝ), 2 < p → ∀ (d T : ℕ) (data : LowerObjectiveData p d T),
    LowerObjectiveAssumptions data →
    ∀ t < T,
      lpNorm (conjugateExponent p)
        (data.completedOracle.gradient (data.queries t)) ≥
      1 / (128 * data.kernel.Mpd * (T : ℝ) ^ (1 + 2 / p))

/-- Source carrier for `lem:above-lower-radius` (L08). -/
noncomputable def AboveLowerOptimizerRadiusStatement : Prop :=
  ∀ (p : ℝ), 2 < p → ∀ (d T : ℕ), 2 ≤ d → 1 ≤ T → T ≤ d →
    ∀ kernel : SmoothingKernelData p d, SmoothingKernelAssumptions kernel →
    ∃ rT : ℝ, 1 / 4 < rT ∧ rT < 4 ∧
      ∀ data : LowerObjectiveData p d T,
        data.kernel = kernel → LowerObjectiveAssumptions data →
        rT = minimizerDistance p data.completedOracle data.x0

/-- An exact deterministic run with a nonempty trace charging its initial query. -/
def ChargedKnownParameterRun (algorithm : DeterministicExactPairAlgorithm d)
    (x0 : Point d) (oracle : PairOracle d) (trace : List (Observation d)) : Prop :=
  GeneratedBy algorithm x0 trace ∧ TraceExact oracle trace ∧
  trace ≠ [] ∧ (trace.head?.map O3.Observation.point) = some x0

/-- Upper half of the current known-parameter proposition.  `Cp` occurs
after `p` and before dimension and instance data. -/
noncomputable def KnownParameterAboveTwoUpperStatement : Prop :=
  ∀ (p : ℝ), 2 < p → ∃ Cp : ℝ, 0 < Cp ∧
    ∀ (d : ℕ) (eps L R : ℝ), 0 < eps → 0 < L → 0 < R →
    ∀ x0 : Point d,
      ∃ algorithm : DeterministicExactPairAlgorithm d,
        ∀ inst : PositiveInstance p d x0,
          inst.L = L → inst.R ≤ R →
          ∃ trace : List (Observation d),
            let xhat := algorithm.output x0 trace
            ChargedKnownParameterRun algorithm x0 inst.oracle trace ∧
            WasQueried trace xhat ∧
            lpNorm (conjugateExponent p) (inst.oracle.gradient xhat) ≤ eps ∧
            (trace.length : ℝ) ≤
              Cp * (1 + (L * R / eps) ^ (p / (p + 2)))

/-- Lower half of the current proposition: deterministic, exact-pair,
every first-`T` query, `T ≤ d`, and explicit `Mpd`. -/
noncomputable def KnownParameterAboveTwoLowerStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (p : ℝ), 2 < p → ∀ (d T : ℕ),
    2 ≤ d → 1 ≤ T → T ≤ d → ∀ (L R : ℝ), 0 < L → 0 < R →
    ∀ (x0 : Point d) (algorithm : DeterministicExactPairAlgorithm d),
      ∃ (inst : PositiveInstance p d x0) (trace : List (Observation d)) (Mpd : ℝ),
        inst.L = L ∧ inst.R = R ∧
        ChargedKnownParameterRun algorithm x0 inst.oracle trace ∧
        trace.length = T ∧ 0 < Mpd ∧
        Mpd ≤ (if p ≤ 3 * Real.log d then 5 * p
          else 15 * Real.exp (2 / 3) * Real.log d) ∧
        Mpd ≤ C * min p (Real.log d) ∧
        ∀ t < T, ∃ obs : Observation d,
          (trace.drop t).head? = some obs ∧
          lpNorm (conjugateExponent p) (inst.oracle.gradient obs.point) ≥
            L * R / (512 * Mpd * (T : ℝ) ^ (1 + 2 / p)) ∧
        (∀ eps : ℝ, 0 < eps →
          eps < L * R / (512 * Mpd * (T : ℝ) ^ (1 + 2 / p)) →
          ¬ ∃ t < T, ∃ obs : Observation d,
            (trace.drop t).head? = some obs ∧
            lpNorm (conjugateExponent p) (inst.oracle.gradient obs.point) ≤ eps) ∧
        (∀ eps : ℝ, 0 < eps →
          (T : ℝ) <
            (L * R / (512 * C * eps * min p (Real.log d))) ^
              (p / (p + 2)) →
          ¬ ∃ t < T, ∃ obs : Observation d,
            (trace.drop t).head? = some obs ∧
            lpNorm (conjugateExponent p) (inst.oracle.gradient obs.point) ≤ eps) ∧
        (p ≤ 3 * Real.log d → ∀ eps : ℝ, 0 < eps →
          (T : ℝ) < (L * R / (2560 * p * eps)) ^ (p / (p + 2)) →
          ¬ ∃ t < T, ∃ obs : Observation d,
            (trace.drop t).head? = some obs ∧
            lpNorm (conjugateExponent p) (inst.oracle.gradient obs.point) ≤ eps)

/-- Source carrier for `prop:pgtwo-optimality` (U11--U12, A01--A13,
L01--L09).  The upper and lower halves remain separately inspectable. -/
noncomputable def KnownParameterAboveTwoOptimalityStatement : Prop :=
  KnownParameterAboveTwoUpperStatement ∧ KnownParameterAboveTwoLowerStatement

end V7
