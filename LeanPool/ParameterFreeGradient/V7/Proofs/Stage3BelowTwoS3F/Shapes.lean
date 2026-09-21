/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage3BelowTwoS3F.Machine

/-!
Physical observations, guard schedules, and possible outcomes of the below-two trial.
-/

namespace V7.Stage3BelowTwoS3F

/-- The ceiling of the below-two iteration horizon determined by accuracy and trial estimates. -/
noncomputable def horizon (p eps M D : ℝ) : ℕ :=
  Nat.ceil (2 * Real.sqrt (M * D / ((p - 1) * eps)))

/-- The phase-one oracle normalized around the initial point. -/
noncomputable def phaseOneOracle (x0 : Point d) (M D : ℝ)
    (oracle : PairOracle d) : PairOracle d := normalizedPairOracle x0 M D oracle

/-- The normalized phase-one state at its prescribed accuracy-dependent horizon. -/
noncomputable def phaseOneState (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (k : ℕ) : PrimalState d :=
  primalState p (horizon p eps M D) (phaseOneOracle x0 M D oracle) k

/-- The physical oracle observation corresponding to a normalized primal iterate. -/
noncomputable def phaseOneObs (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (k : ℕ) : Observation d :=
  oracle.observe (x0 + D • (phaseOneState p eps M D x0 oracle k).x)

/-- The physical endpoint of phase one used as the center of phase two. -/
noncomputable def phaseTwoCenter (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) : Point d :=
  (phaseOneObs p eps M D x0 oracle (horizon p eps M D)).point

/-- The phase-two oracle normalized around the completed primal endpoint. -/
noncomputable def phaseTwoOracle (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) : PairOracle d :=
  normalizedPairOracle (phaseTwoCenter p eps M D x0 oracle) M D oracle

/-- The physical oracle observation corresponding to a normalized dual query. -/
noncomputable def phaseTwoObs (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (k : ℕ) : Observation d :=
  oracle.observe (phaseTwoCenter p eps M D x0 oracle +
    D • dualQ p (horizon p eps M D) (phaseTwoOracle p eps M D x0 oracle) k)

/-- The new primal observations after the reused initial query. -/
noncomputable def phaseOneNewTrace (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (m : ℕ) : List (Observation d) :=
  (List.range m).map fun k => phaseOneObs p eps M D x0 oracle (k + 1)

/-- The new dual observations after the reused phase-one endpoint. -/
noncomputable def phaseTwoNewTrace (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (m : ℕ) : List (Observation d) :=
  (List.range m).map fun k => phaseTwoObs p eps M D x0 oracle (k + 1)

/-- The consecutive cocoercivity checks in the completed primal prefix. -/
noncomputable def phaseOneChecks (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (m : ℕ) : List (ObservableGuardCheck d) :=
  (List.range m).map fun k => cocoCheck
    (phaseOneObs p eps M D x0 oracle k)
    (phaseOneObs p eps M D x0 oracle (k + 1))

/-- The consecutive cocoercivity checks in the completed dual prefix. -/
noncomputable def phaseTwoChecks (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (m : ℕ) : List (ObservableGuardCheck d) :=
  (List.range m).map fun k => cocoCheck
    (phaseTwoObs p eps M D x0 oracle k)
    (phaseTwoObs p eps M D x0 oracle (k + 1))

/-- The ordered guard checks from the completed prefixes of both phases. -/
noncomputable def allChecks (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (m₁ m₂ : ℕ) : List (ObservableGuardCheck d) :=
  phaseOneChecks p eps M D x0 oracle m₁ ++
    phaseTwoChecks p eps M D x0 oracle m₂

/-- The possible success, scale-failure, and radius outcomes of a below-two trial report. -/
inductive FullShape (p eps M D : ℝ) (x0 : Point d) (oracle : PairOracle d) :
    TrialReport d → ℕ → ℕ → Prop
  | primalSuccess (m : ℕ) (hm0 : 0 < m) (hmn : m ≤ horizon p eps M D)
      (hsmall : lpNorm (conjugateExponent p)
        (phaseOneObs p eps M D x0 oracle m).gradient ≤ eps)
      (hprior : ∀ k < m - 1, cocoPairHolds p M
        (phaseOneObs p eps M D x0 oracle k)
        (phaseOneObs p eps M D x0 oracle (k + 1))) :
      FullShape p eps M D x0 oracle
        ⟨phaseOneNewTrace p eps M D x0 oracle m,
          phaseOneChecks p eps M D x0 oracle (m - 1),
          .success (phaseOneObs p eps M D x0 oracle m)⟩ m 0
  | primalScale (m : ℕ) (hm0 : 0 < m) (hmn : m ≤ horizon p eps M D)
      (hprior : ∀ k < m - 1, cocoPairHolds p M
        (phaseOneObs p eps M D x0 oracle k)
        (phaseOneObs p eps M D x0 oracle (k + 1)))
      (hlarge : eps < lpNorm (conjugateExponent p)
        (phaseOneObs p eps M D x0 oracle m).gradient)
      (hfail : ¬ cocoPairHolds p M
        (phaseOneObs p eps M D x0 oracle (m - 1))
        (phaseOneObs p eps M D x0 oracle m)) :
      FullShape p eps M D x0 oracle
        ⟨phaseOneNewTrace p eps M D x0 oracle m,
          phaseOneChecks p eps M D x0 oracle m,
          .scale (cocoCheck
            (phaseOneObs p eps M D x0 oracle (m - 1))
            (phaseOneObs p eps M D x0 oracle m))⟩ m 0
  | dualSuccess (m : ℕ) (hm0 : 0 < m) (hmn : m ≤ horizon p eps M D)
      (hP : ∀ k < horizon p eps M D, cocoPairHolds p M
        (phaseOneObs p eps M D x0 oracle k)
        (phaseOneObs p eps M D x0 oracle (k + 1)))
      (hQ : ∀ k < m - 1, cocoPairHolds p M
        (phaseTwoObs p eps M D x0 oracle k)
        (phaseTwoObs p eps M D x0 oracle (k + 1)))
      (hsmall : lpNorm (conjugateExponent p)
        (phaseTwoObs p eps M D x0 oracle m).gradient ≤ eps) :
      FullShape p eps M D x0 oracle
        ⟨phaseOneNewTrace p eps M D x0 oracle (horizon p eps M D) ++
            phaseTwoNewTrace p eps M D x0 oracle m,
          allChecks p eps M D x0 oracle (horizon p eps M D) (m - 1),
          .success (phaseTwoObs p eps M D x0 oracle m)⟩
        (horizon p eps M D) m
  | dualScale (m : ℕ) (hm0 : 0 < m) (hmn : m ≤ horizon p eps M D)
      (hP : ∀ k < horizon p eps M D, cocoPairHolds p M
        (phaseOneObs p eps M D x0 oracle k)
        (phaseOneObs p eps M D x0 oracle (k + 1)))
      (hQ : ∀ k < m - 1, cocoPairHolds p M
        (phaseTwoObs p eps M D x0 oracle k)
        (phaseTwoObs p eps M D x0 oracle (k + 1)))
      (hlarge : eps < lpNorm (conjugateExponent p)
        (phaseTwoObs p eps M D x0 oracle m).gradient)
      (hfail : ¬ cocoPairHolds p M
        (phaseTwoObs p eps M D x0 oracle (m - 1))
        (phaseTwoObs p eps M D x0 oracle m)) :
      FullShape p eps M D x0 oracle
        ⟨phaseOneNewTrace p eps M D x0 oracle (horizon p eps M D) ++
            phaseTwoNewTrace p eps M D x0 oracle m,
          allChecks p eps M D x0 oracle (horizon p eps M D) m,
          .scale (cocoCheck
            (phaseTwoObs p eps M D x0 oracle (m - 1))
            (phaseTwoObs p eps M D x0 oracle m))⟩
        (horizon p eps M D) m
  | radius
      (hP : ∀ k < horizon p eps M D, cocoPairHolds p M
        (phaseOneObs p eps M D x0 oracle k)
        (phaseOneObs p eps M D x0 oracle (k + 1)))
      (hQ : ∀ k < horizon p eps M D, cocoPairHolds p M
        (phaseTwoObs p eps M D x0 oracle k)
        (phaseTwoObs p eps M D x0 oracle (k + 1)))
      (hlarge : eps < lpNorm (conjugateExponent p)
        (phaseTwoObs p eps M D x0 oracle (horizon p eps M D)).gradient) :
      FullShape p eps M D x0 oracle
        ⟨phaseOneNewTrace p eps M D x0 oracle (horizon p eps M D) ++
            phaseTwoNewTrace p eps M D x0 oracle (horizon p eps M D),
          allChecks p eps M D x0 oracle (horizon p eps M D)
            (horizon p eps M D),
          .radius (phaseTwoObs p eps M D x0 oracle (horizon p eps M D))⟩
        (horizon p eps M D) (horizon p eps M D)

end V7.Stage3BelowTwoS3F
