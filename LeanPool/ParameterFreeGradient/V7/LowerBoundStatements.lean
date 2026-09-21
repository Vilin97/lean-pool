/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.AboveTwoStatements
import LeanPool.ParameterFreeGradient.V7.StrictModel

open scoped BigOperators

namespace V7

/-- Causal deterministic exact-pair algorithm for the known-parameter lower
bound.  No inverse-gradient or unqueried-output channel is present. -/
structure DeterministicExactPairAlgorithm (d : ℕ) where
  nextQuery : Point d → List (Observation d) → Point d
  output : Point d → List (Observation d) → Point d

def GeneratedBy (algorithm : DeterministicExactPairAlgorithm d) (x0 : Point d)
    (trace : List (Observation d)) : Prop :=
  ∀ (t : ℕ) (ht : t < trace.length),
    (trace.get ⟨t, ht⟩).point =
      if t = 0 then x0 else algorithm.nextQuery x0 (trace.take t)

structure SmoothingKernelData (p : ℝ) (d : ℕ) where
  phi : Point d → ℝ
  gradPhi : Point d → Point d
  hessian : Point d → (Point d →L[ℝ] Point d)
  Mpd : ℝ
  smooth : ℝ → (Point d → ℝ) → PairOracle d

noncomputable def localSmoothingValue (kernel : SmoothingKernelData p d)
    (chi : ℝ) (ell : Point d → ℝ) (x : Point d) : ℝ :=
  sInf {r : ℝ | ∃ v : Point d,
    r = ell (x + v) + chi * kernel.phi ((1 / chi) • v)}

def IsOneLipschitz (p : ℝ) (f : Point d → ℝ) : Prop :=
  ∀ x y, |f x - f y| ≤ lpNorm p (x - y)

def SignedLpSymmetry (p : ℝ) (Q Qdual : Point d → Point d) : Prop :=
  (∀ x, lpNorm p (Q x) = lpNorm p x) ∧
  (∀ s, lpNorm (conjugateExponent p) (Qdual s) =
    lpNorm (conjugateExponent p) s) ∧
  (∀ s x, pairing (Qdual s) (Q x) = pairing s x)

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

noncomputable def lowerKernelPhi (r0 theta : ℝ) (x : Point d) : ℝ :=
  2 * (∑ j, |x j| ^ r0) ^ (2 * theta / r0)

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

structure LowerCompletionData (p : ℝ) (d T : ℕ) where
  algorithm : DeterministicExactPairAlgorithm d
  x0 : Point d
  kernel : SmoothingKernelData p d
  Delta : ℝ
  delta : ℝ
  chi : ℝ
  beta : ℝ
  partialG : ℕ → Point d → ℝ
  partialH : ℕ → Point d → ℝ
  partialOracle : ℕ → PairOracle d
  completedOracle : PairOracle d
  queries : ℕ → Point d
  sigma : ℕ → Fin d
  xi : ℕ → ℝ

def ResistingMaximumAt (data : LowerCompletionData p d T) (t : ℕ) : Prop :=
  ∀ x,
    (∀ i ≤ t,
      data.xi i * x (data.sigma i) - (i : ℝ) * data.delta ≤
        data.partialG t x) ∧
    ∃ i ≤ t,
      data.partialG t x =
        data.xi i * x (data.sigma i) - (i : ℝ) * data.delta

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

structure LowerObjectiveData (p : ℝ) (d T : ℕ)
    extends LowerCompletionData p d T

def IsCoerciveLp (p : ℝ) (f : Point d → ℝ) : Prop :=
  ∀ B : ℝ, ∃ radius : ℝ, 0 ≤ radius ∧
    ∀ x, radius ≤ lpNorm p x → B ≤ f x

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
