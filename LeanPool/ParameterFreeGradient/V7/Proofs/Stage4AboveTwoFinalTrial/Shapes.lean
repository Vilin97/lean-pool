/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage4AboveTwoFinalTrial.Machine

namespace V7.Stage4AboveTwoFinalTrial

open V7.Stage3BelowTwoS3F

noncomputable def phaseOneOracle (x0 : Point d) (M D : ℝ)
    (oracle : PairOracle d) : PairOracle d := normalizedPairOracle x0 M D oracle

noncomputable def phaseOneState (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (k : ℕ) : PrimalState d :=
  primalState p (etaF p) (nF p eps M D) (phaseOneOracle x0 M D oracle) k

noncomputable def phaseOneObs (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (k : ℕ) : Observation d :=
  oracle.observe (x0 + D • (phaseOneState p eps M D x0 oracle k).x)

noncomputable def phaseTwoCenter (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) : Point d :=
  (phaseOneObs p eps M D x0 oracle (nF p eps M D)).point

noncomputable def phaseTwoOracle (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) : PairOracle d :=
  normalizedPairOracle (phaseTwoCenter p eps M D x0 oracle) M D oracle

noncomputable def phaseTwoObs (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (k : ℕ) : Observation d :=
  oracle.observe (phaseTwoCenter p eps M D x0 oracle +
    D • dualQ p (etaD p eps M D) (nD p eps M D)
      (phaseTwoOracle p eps M D x0 oracle) k)

noncomputable def phaseOneNewTrace (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (m : ℕ) : List (Observation d) :=
  (List.range m).map fun k => phaseOneObs p eps M D x0 oracle (k + 1)

noncomputable def phaseTwoNewTrace (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (m : ℕ) : List (Observation d) :=
  (List.range m).map fun k => phaseTwoObs p eps M D x0 oracle (k + 1)

noncomputable def phaseOneChecks (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (m : ℕ) : List (ObservableGuardCheck d) :=
  (List.range m).map fun k => cocoCheck
    (phaseOneObs p eps M D x0 oracle k)
    (phaseOneObs p eps M D x0 oracle (k + 1))

noncomputable def phaseTwoChecks (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (m : ℕ) : List (ObservableGuardCheck d) :=
  (List.range m).map fun k => cocoCheck
    (phaseTwoObs p eps M D x0 oracle k)
    (phaseTwoObs p eps M D x0 oracle (k + 1))

noncomputable def allChecks (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (m₁ m₂ : ℕ) : List (ObservableGuardCheck d) :=
  phaseOneChecks p eps M D x0 oracle m₁ ++ phaseTwoChecks p eps M D x0 oracle m₂

inductive FullShape (p eps M D : ℝ) (x0 : Point d) (oracle : PairOracle d) :
    TrialReport d → ℕ → ℕ → Prop
  | primalSuccess (m : ℕ) (hm0 : 0 < m) (hmn : m ≤ nF p eps M D)
      (hsmall : lpNorm (conjugateExponent p)
        (phaseOneObs p eps M D x0 oracle m).gradient ≤ eps)
      (hprior : ∀ k < m - 1, cocoPairHolds p M
        (phaseOneObs p eps M D x0 oracle k)
        (phaseOneObs p eps M D x0 oracle (k + 1))) :
      FullShape p eps M D x0 oracle
        ⟨phaseOneNewTrace p eps M D x0 oracle m,
          phaseOneChecks p eps M D x0 oracle (m - 1),
          .success (phaseOneObs p eps M D x0 oracle m)⟩ m 0
  | primalScale (m : ℕ) (hm0 : 0 < m) (hmn : m ≤ nF p eps M D)
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
          .scale (cocoCheck (phaseOneObs p eps M D x0 oracle (m - 1))
            (phaseOneObs p eps M D x0 oracle m))⟩ m 0
  | dualSuccess (m : ℕ) (hm0 : 0 < m) (hmn : m ≤ nD p eps M D)
      (hP : ∀ k < nF p eps M D, cocoPairHolds p M
        (phaseOneObs p eps M D x0 oracle k)
        (phaseOneObs p eps M D x0 oracle (k + 1)))
      (hQ : ∀ k < m - 1, cocoPairHolds p M
        (phaseTwoObs p eps M D x0 oracle k)
        (phaseTwoObs p eps M D x0 oracle (k + 1)))
      (hsmall : lpNorm (conjugateExponent p)
        (phaseTwoObs p eps M D x0 oracle m).gradient ≤ eps) :
      FullShape p eps M D x0 oracle
        ⟨phaseOneNewTrace p eps M D x0 oracle (nF p eps M D) ++
            phaseTwoNewTrace p eps M D x0 oracle m,
          allChecks p eps M D x0 oracle (nF p eps M D) (m - 1),
          .success (phaseTwoObs p eps M D x0 oracle m)⟩ (nF p eps M D) m
  | dualScale (m : ℕ) (hm0 : 0 < m) (hmn : m ≤ nD p eps M D)
      (hP : ∀ k < nF p eps M D, cocoPairHolds p M
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
        ⟨phaseOneNewTrace p eps M D x0 oracle (nF p eps M D) ++
            phaseTwoNewTrace p eps M D x0 oracle m,
          allChecks p eps M D x0 oracle (nF p eps M D) m,
          .scale (cocoCheck (phaseTwoObs p eps M D x0 oracle (m - 1))
            (phaseTwoObs p eps M D x0 oracle m))⟩ (nF p eps M D) m
  | radius
      (hP : ∀ k < nF p eps M D, cocoPairHolds p M
        (phaseOneObs p eps M D x0 oracle k)
        (phaseOneObs p eps M D x0 oracle (k + 1)))
      (hQ : ∀ k < nD p eps M D, cocoPairHolds p M
        (phaseTwoObs p eps M D x0 oracle k)
        (phaseTwoObs p eps M D x0 oracle (k + 1)))
      (hlarge : eps < lpNorm (conjugateExponent p)
        (phaseTwoObs p eps M D x0 oracle (nD p eps M D)).gradient) :
      FullShape p eps M D x0 oracle
        ⟨phaseOneNewTrace p eps M D x0 oracle (nF p eps M D) ++
            phaseTwoNewTrace p eps M D x0 oracle (nD p eps M D),
          allChecks p eps M D x0 oracle (nF p eps M D) (nD p eps M D),
          .radius (phaseTwoObs p eps M D x0 oracle (nD p eps M D))⟩
        (nF p eps M D) (nD p eps M D)

end V7.Stage4AboveTwoFinalTrial
