/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.QuantumParallelRepetition.Part10

/-! # Quantum parallel repetition, part 11 -/

noncomputable section

namespace QuantumParallelRepetition

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

attribute [local instance] Classical.propDecidable

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem unconditionalActualC485GenericRetainedWinningBorn
    {X Y A B s t u v ι κ : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype s] [Fintype t] [Fintype u] [Fintype v]
    [Fintype ι] [Fintype κ]
    [DecidableEq s] [DecidableEq t] [DecidableEq u] [DecidableEq v]
    [DecidableEq ι] [DecidableEq κ]
    (G : Game X Y A B)
    (eA : ι ≃ s × t) (eB : κ ≃ u × v)
    (PA : POVM A s) (PB : POVM B u)
    (x : X) (y : Y)
    (z : EuclideanSpace ℂ (ι × κ)) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := ι × κ) (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM eA PA)
          (directDSVActualReindexedRetainedPOVM eB PB) x y)) z =
      quadraticExpectation
        (Matrix.toEuclideanCLM
          (n := (s × u) × (t × v)) (𝕜 := ℂ)
          (directDSVActualLocalPOVMWinningEffect
            G PA PB x y ⊗ₖ (1 : Matrix (t × v) (t × v) ℂ)))
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (directDSVActualBilateralRetainedIndexEquiv eA eB) z) := by
  rw [directDSVActualReindexedRetainedPOVMWinningEffect,
    directDSVActualReindexedWinningEffect_quadratic]

theorem unconditionalActualC485GenericSelectedWinningRegroupGauge
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {P N d m : ℕ} {ι κ R T : Type}
    [Fintype ι] [Fintype κ] [Fintype R] [Fintype T]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq R] [DecidableEq T]
    (G : Game X Y A B)
    (alice bob : Matrix.unitaryGroup (Fin d) ℂ)
    (PA : POVM A (Fin d)) (PB : POVM B (Fin d))
    (eA : ι ≃ UnconditionalSelectedCopyLocalIndex P d N m × R)
    (eB : κ ≃ UnconditionalSelectedCopyLocalIndex P d N m × R)
    (pair : R × R ≃ T)
    (x : X) (y : Y)
    (z : EuclideanSpace ℂ (ι × κ)) :
    let selected := UnconditionalSelectedCopyLocalIndex P d N m
    let stage := physical8SelectedGlobalTargetWorkEquiv P N d m
    let gaugedAlice := directDSVActualReindexedRetainedPOVM stage
      (unitaryConjugatePOVM alice PA)
    let gaugedBob := directDSVActualReindexedRetainedPOVM stage
      (unitaryConjugatePOVM bob PB)
    let plainAlice := directDSVActualReindexedRetainedPOVM stage PA
    let plainBob := directDSVActualReindexedRetainedPOVM stage PB
    let regrouped :=
      LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.prodCongr (Equiv.refl (selected × selected)) pair)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (directDSVActualBilateralRetainedIndexEquiv eA eB) z)
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := ι × κ) (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM eA gaugedAlice)
          (directDSVActualReindexedRetainedPOVM eB gaugedBob)
          x y)) z =
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (selected × selected) × T) (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          plainAlice plainBob x y ⊗ₖ (1 : Matrix T T ℂ)))
      (unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P alice)
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P bob)
        regrouped) := by
  dsimp only
  calc
    _ = quadraticExpectation
        (Matrix.toEuclideanCLM
          (n :=
            (UnconditionalSelectedCopyLocalIndex P d N m ×
             UnconditionalSelectedCopyLocalIndex P d N m) ×
              (R × R))
          (𝕜 := ℂ)
          (directDSVActualLocalPOVMWinningEffect G
            (directDSVActualReindexedRetainedPOVM
              (physical8SelectedGlobalTargetWorkEquiv P N d m)
              (unitaryConjugatePOVM alice PA))
            (directDSVActualReindexedRetainedPOVM
              (physical8SelectedGlobalTargetWorkEquiv P N d m)
              (unitaryConjugatePOVM bob PB)) x y ⊗ₖ
            (1 : Matrix (R × R) (R × R) ℂ)))
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (directDSVActualBilateralRetainedIndexEquiv eA eB) z) :=
      unconditionalActualC485GenericRetainedWinningBorn
        G eA eB
        (directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m)
          (unitaryConjugatePOVM alice PA))
        (directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m)
          (unitaryConjugatePOVM bob PB)) x y z
    _ = quadraticExpectation
        (Matrix.toEuclideanCLM
          (n :=
            (UnconditionalSelectedCopyLocalIndex P d N m ×
             UnconditionalSelectedCopyLocalIndex P d N m) × T)
          (𝕜 := ℂ)
          (directDSVActualLocalPOVMWinningEffect G
            (directDSVActualReindexedRetainedPOVM
              (physical8SelectedGlobalTargetWorkEquiv P N d m)
              (unitaryConjugatePOVM alice PA))
            (directDSVActualReindexedRetainedPOVM
              (physical8SelectedGlobalTargetWorkEquiv P N d m)
              (unitaryConjugatePOVM bob PB)) x y ⊗ₖ
            (1 : Matrix T T ℂ)))
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (Equiv.prodCongr
            (Equiv.refl
              (UnconditionalSelectedCopyLocalIndex P d N m ×
               UnconditionalSelectedCopyLocalIndex P d N m))
            pair)
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
            (directDSVActualBilateralRetainedIndexEquiv eA eB) z)) :=
      unconditionalActualC485RetainedPureWorkReindexBorn
        pair
        (directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM
            (physical8SelectedGlobalTargetWorkEquiv P N d m)
            (unitaryConjugatePOVM alice PA))
          (directDSVActualReindexedRetainedPOVM
            (physical8SelectedGlobalTargetWorkEquiv P N d m)
            (unitaryConjugatePOVM bob PB)) x y)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (directDSVActualBilateralRetainedIndexEquiv eA eB) z)
    _ = _ :=
      unconditionalActualFairSourceSelectedRetainedWinningBornGauge
        G alice bob PA PB x y
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (Equiv.prodCongr
            (Equiv.refl
              (UnconditionalSelectedCopyLocalIndex P d N m ×
               UnconditionalSelectedCopyLocalIndex P d N m))
            pair)
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
            (directDSVActualBilateralRetainedIndexEquiv eA eB) z))

theorem unconditionalActualC485GenericDecodedWinningBorn
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {P N d m : ℕ} {ι κ R T : Type}
    [Fintype ι] [Fintype κ] [Fintype R] [Fintype T]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq R] [DecidableEq T]
    (G : Game X Y A B)
    (alice bob : Matrix.unitaryGroup (Fin d) ℂ)
    (PA : POVM A (Fin d)) (PB : POVM B (Fin d))
    (eA : ι ≃ UnconditionalSelectedCopyLocalIndex P d N m × R)
    (eB : κ ≃ UnconditionalSelectedCopyLocalIndex P d N m × R)
    (pair : R × R ≃ T)
    (x : X) (y : Y)
    (z : EuclideanSpace ℂ (ι × κ))
    (actual : EuclideanSpace ℂ
      ((UnconditionalSelectedCopyLocalIndex P d N m ×
        UnconditionalSelectedCopyLocalIndex P d N m) × T))
    (decoded :
      unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P alice)
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P bob)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (Equiv.prodCongr
            (Equiv.refl
              (UnconditionalSelectedCopyLocalIndex P d N m ×
               UnconditionalSelectedCopyLocalIndex P d N m))
            pair)
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
            (directDSVActualBilateralRetainedIndexEquiv
              eA eB) z)) = actual) :
    let selected := UnconditionalSelectedCopyLocalIndex P d N m
    let stage := physical8SelectedGlobalTargetWorkEquiv P N d m
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (selected × selected) × T) (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM stage PA)
          (directDSVActualReindexedRetainedPOVM stage PB)
          x y ⊗ₖ (1 : Matrix T T ℂ))) actual =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := ι × κ) (𝕜 := ℂ)
          (directDSVActualLocalPOVMWinningEffect G
            (directDSVActualReindexedRetainedPOVM eA
              (directDSVActualReindexedRetainedPOVM stage
                (unitaryConjugatePOVM alice PA)))
            (directDSVActualReindexedRetainedPOVM eB
              (directDSVActualReindexedRetainedPOVM stage
                (unitaryConjugatePOVM bob PB))) x y)) z := by
  dsimp only
  have physical :=
    unconditionalActualC485GenericSelectedWinningRegroupGauge
      G alice bob PA PB eA eB pair x y z
  dsimp only at physical
  rw [decoded] at physical
  exact physical.symm

theorem unconditionalActualC485SourceSelectedDecodedWinningBorn
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {P N d m : ℕ} {ι κ R T : Type}
    [Fintype ι] [Fintype κ] [Fintype R] [Fintype T]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq R] [DecidableEq T]
    (G : Game X Y A B)
    (alice bob : Matrix.unitaryGroup (Fin d) ℂ)
    (PA : POVM A (Fin d)) (PB : POVM B (Fin d))
    (selectedA :
      POVM A (UnconditionalSelectedCopyLocalIndex P d N m))
    (selectedB :
      POVM B (UnconditionalSelectedCopyLocalIndex P d N m))
    (selectedA_eq :
      selectedA =
        directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m) PA)
    (selectedB_eq :
      selectedB =
        directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m) PB)
    (eA : ι ≃ UnconditionalSelectedCopyLocalIndex P d N m × R)
    (eB : κ ≃ UnconditionalSelectedCopyLocalIndex P d N m × R)
    (pair : R × R ≃ T)
    (x : X) (y : Y)
    (z : EuclideanSpace ℂ (ι × κ))
    (actual : EuclideanSpace ℂ
      ((UnconditionalSelectedCopyLocalIndex P d N m ×
        UnconditionalSelectedCopyLocalIndex P d N m) × T))
    (decoded :
      unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P alice)
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P bob)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (Equiv.prodCongr
            (Equiv.refl
              (UnconditionalSelectedCopyLocalIndex P d N m ×
               UnconditionalSelectedCopyLocalIndex P d N m))
            pair)
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
            (directDSVActualBilateralRetainedIndexEquiv
              eA eB) z)) = actual) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          (UnconditionalSelectedCopyLocalIndex P d N m ×
           UnconditionalSelectedCopyLocalIndex P d N m) × T)
        (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          selectedA selectedB x y ⊗ₖ (1 : Matrix T T ℂ))) actual =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := ι × κ) (𝕜 := ℂ)
          (directDSVActualLocalPOVMWinningEffect G
            (directDSVActualReindexedRetainedPOVM eA
              (directDSVActualReindexedRetainedPOVM
                (physical8SelectedGlobalTargetWorkEquiv P N d m)
                (unitaryConjugatePOVM alice PA)))
            (directDSVActualReindexedRetainedPOVM eB
              (directDSVActualReindexedRetainedPOVM
                (physical8SelectedGlobalTargetWorkEquiv P N d m)
                (unitaryConjugatePOVM bob PB))) x y)) z := by
  subst selectedA
  subst selectedB
  exact
    unconditionalActualC485GenericDecodedWinningBorn
      G alice bob PA PB eA eB pair x y z actual decoded

open QuantumParallelRepetition.ClassicalSampling

private def unconditionalActualFairSourceAliceTarget
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty) :
    ExactSourceSharedFlag X Y A B D denominator → X →
      BipartiteUnitVector
        (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) :=
  fun flag x =>
    exactGlobalHistoryFinGamma G n S D
      (exactSourceAlicePermutationHistory
        D denominator numerator nonempty flag x) x

private def unconditionalActualFairSourceBobTarget
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty) :
    ExactSourceSharedFlag X Y A B D denominator → Y →
      BipartiteUnitVector
        (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) :=
  fun flag y =>
    exactGlobalHistoryFinPhi G n S D
      (exactSourceBobPermutationHistory
        D denominator numerator nonempty flag y) y

theorem unconditionalActualC485CompleteDecodedPhysicalBorn
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {P N d m : ℕ} {ι κ R T : Type}
    [Fintype ι] [Fintype κ] [Fintype R] [Fintype T]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq R] [DecidableEq T]
    (G : Game X Y A B)
    (alice bob : Matrix.unitaryGroup (Fin d) ℂ)
    (PA : POVM A (Fin d)) (PB : POVM B (Fin d))
    (selectedA :
      POVM A (UnconditionalSelectedCopyLocalIndex P d N m))
    (selectedB :
      POVM B (UnconditionalSelectedCopyLocalIndex P d N m))
    (selectedA_eq :
      selectedA =
        directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m) PA)
    (selectedB_eq :
      selectedB =
        directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m) PB)
    (eA : ι ≃ UnconditionalSelectedCopyLocalIndex P d N m × R)
    (eB : κ ≃ UnconditionalSelectedCopyLocalIndex P d N m × R)
    (pair : R × R ≃ T)
    (rawA : POVM A ι) (rawB : POVM B κ)
    (rawA_eq :
      rawA =
        directDSVActualReindexedRetainedPOVM eA
          (directDSVActualReindexedRetainedPOVM
            (physical8SelectedGlobalTargetWorkEquiv P N d m)
            (unitaryConjugatePOVM alice PA)))
    (rawB_eq :
      rawB =
        directDSVActualReindexedRetainedPOVM eB
          (directDSVActualReindexedRetainedPOVM
            (physical8SelectedGlobalTargetWorkEquiv P N d m)
            (unitaryConjugatePOVM bob PB)))
    (x : X) (y : Y)
    (z : EuclideanSpace ℂ (ι × κ))
    (source cleaned : EuclideanSpace ℂ
      ((UnconditionalSelectedCopyLocalIndex P d N m ×
        UnconditionalSelectedCopyLocalIndex P d N m) × T))
    (source_eq : source = cleaned)
    (decoded :
      unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P alice)
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P bob)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (Equiv.prodCongr
            (Equiv.refl
              (UnconditionalSelectedCopyLocalIndex P d N m ×
               UnconditionalSelectedCopyLocalIndex P d N m))
            pair)
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
            (directDSVActualBilateralRetainedIndexEquiv
              eA eB) z)) = cleaned) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          (UnconditionalSelectedCopyLocalIndex P d N m ×
           UnconditionalSelectedCopyLocalIndex P d N m) × T)
        (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          selectedA selectedB x y ⊗ₖ (1 : Matrix T T ℂ))) source =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := ι × κ) (𝕜 := ℂ)
          (directDSVActualLocalPOVMWinningEffect G
            rawA rawB x y)) z := by
  subst rawA
  subst rawB
  calc
    _ = quadraticExpectation
        (Matrix.toEuclideanCLM
          (n :=
            (UnconditionalSelectedCopyLocalIndex P d N m ×
             UnconditionalSelectedCopyLocalIndex P d N m) × T)
          (𝕜 := ℂ)
          (directDSVActualLocalPOVMWinningEffect G
            selectedA selectedB x y ⊗ₖ (1 : Matrix T T ℂ))) cleaned :=
      congrArg
        (fun v : EuclideanSpace ℂ
            ((UnconditionalSelectedCopyLocalIndex P d N m ×
              UnconditionalSelectedCopyLocalIndex P d N m) × T) =>
          quadraticExpectation
            (Matrix.toEuclideanCLM
              (n :=
                (UnconditionalSelectedCopyLocalIndex P d N m ×
                 UnconditionalSelectedCopyLocalIndex P d N m) × T)
              (𝕜 := ℂ)
              (directDSVActualLocalPOVMWinningEffect G
                selectedA selectedB x y ⊗ₖ (1 : Matrix T T ℂ))) v)
        source_eq
    _ = _ :=
      unconditionalActualC485SourceSelectedDecodedWinningBorn
        G alice bob PA PB selectedA selectedB selectedA_eq selectedB_eq
        eA eB pair x y z cleaned decoded

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalSampling

/--
The positive operator-valued measurement implementing unconditional actual fair source alice
flag.
-/
def unconditionalActualFairSourceAliceFlagPOVM
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (a₀ : A) (P N L m : ℕ) :
    ExactSourceSharedFlag X Y A B D denominator →
      Fin (L + 1) → X →
        POVM A
          (UnconditionalSourcePhysicalStoppingPhaseFiber
            1 P N
            (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
            L m) := by
  classical
  intro flag
  exact
    physical8OneScaleOriginalFlagPOVM
      (N := N)
      (d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
      (m := m)
      (unconditionalActualOneScaleFixedSourcePhaseSplit P) a₀
      (fun x =>
        unitaryConjugatePOVM
          (conjugateUnitary
            (dSVDensityRationalCanonicalAliceBasis
              (unconditionalActualFairSourceAliceTarget
                G n S D denominator numerator nonempty flag x)))
          (integratorActualC485SourceAlicePOVM
            G n S D a₀ x))

/--
The positive operator-valued measurement implementing unconditional actual fair source bob flag.
-/
def unconditionalActualFairSourceBobFlagPOVM
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (b₀ : B) (P N L m : ℕ) :
    ExactSourceSharedFlag X Y A B D denominator →
      Fin (L + 1) → Y →
        POVM B
          (UnconditionalSourcePhysicalStoppingPhaseFiber
            1 P N
            (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
            L m) := by
  classical
  intro flag
  exact
    physical8OneScaleOriginalFlagPOVM
      (N := N)
      (d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
      (m := m)
      (unconditionalActualOneScaleFixedSourcePhaseSplit P) b₀
      (fun y =>
        unitaryConjugatePOVM
          (conjugateUnitary
            (dSVUniformDensityThresholdLeftBobBasis
              (unconditionalActualFairSourceBobTarget
                G n S D denominator numerator nonempty flag y)))
          (integratorActualC485SourceBobPOVM
            G n S D b₀ y))

/-- The unitary operator implementing unconditional actual fair source alice stopping. -/
def unconditionalActualFairSourceAliceStoppingUnitary
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    {P N L m : ℕ} (Q : ℕ)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (cleanup : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    ExactSourceSharedFlag X Y A B D denominator → X →
      Matrix.unitaryGroup
        (Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            1 P N
            (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
            L m) ℂ := by
  classical
  exact
    physical8OneScaleActualAliceStoppingUnitary
      (P := P) (N := N)
      (d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
      (L := L) (m := m)
      (unconditionalActualOneScaleFixedSourcePhaseSplit P)
      Q width schedule
      (unconditionalActualFairSourceAliceTarget
        G n S D denominator numerator nonempty)
      cleanup

/-- The unitary operator implementing unconditional actual fair source bob stopping. -/
def unconditionalActualFairSourceBobStoppingUnitary
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    {P N L m : ℕ} (Q : ℕ)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (cleanup : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    ExactSourceSharedFlag X Y A B D denominator → Y →
      Matrix.unitaryGroup
        (Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            1 P N
            (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
            L m) ℂ := by
  classical
  exact
    physical8OneScaleActualBobStoppingUnitary
      (P := P) (N := N)
      (d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
      (L := L) (m := m)
      (unconditionalActualOneScaleFixedSourcePhaseSplit P)
      Q width schedule
      (unconditionalActualFairSourceBobTarget
        G n S D denominator numerator nonempty)
      cleanup

theorem unconditionalActualFairSourceAliceFlagPOVM_succ_nested
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [decA : DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (a₀ : A) {P N L m : ℕ}
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (j : Fin L) (x : X) :
    unconditionalActualFairSourceAliceFlagPOVM
        G n S D denominator numerator nonempty a₀ P N L m
        flag j.succ x =
      directDSVActualReindexedRetainedPOVM
        (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
          (N := N)
          (d := Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D))
          (m := m)
          (unconditionalActualOneScaleFixedSourcePhaseSplit P) j)
        (directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv
            P N
            (Fintype.card
              (ExactGlobalHistoryLocalIndex G n S D)) m)
          (unitaryConjugatePOVM
            (conjugateUnitary
              (dSVDensityRationalCanonicalAliceBasis
                (unconditionalActualFairSourceAliceTarget
                  G n S D denominator numerator nonempty flag x)))
            (integratorActualC485SourceAlicePOVM
              G n S D a₀ x))) := by
  classical
  have same_instance : decA = Classical.decEq A :=
    Subsingleton.elim _ _
  cases same_instance
  change
    physical8OneScaleOriginalFlagPOVM
      (N := N)
      (d := Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D))
      (m := m)
      (unconditionalActualOneScaleFixedSourcePhaseSplit P)
      a₀
      (fun q =>
        unitaryConjugatePOVM
          (conjugateUnitary
            (dSVDensityRationalCanonicalAliceBasis
              (unconditionalActualFairSourceAliceTarget
                G n S D denominator numerator nonempty flag q)))
          (integratorActualC485SourceAlicePOVM
            G n S D a₀ q)) j.succ x = _
  exact
    unconditionalPhysicalOneScaleOriginalFlagPOVM_succ_nested
      (N := N)
      (d := Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D))
      (m := m)
      (unconditionalActualOneScaleFixedSourcePhaseSplit P)
      a₀
      (fun q =>
        unitaryConjugatePOVM
          (conjugateUnitary
            (dSVDensityRationalCanonicalAliceBasis
              (unconditionalActualFairSourceAliceTarget
                G n S D denominator numerator nonempty flag q)))
          (integratorActualC485SourceAlicePOVM
            G n S D a₀ q)) j x

theorem unconditionalActualFairSourceBobFlagPOVM_succ_nested
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [decB : DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (b₀ : B) {P N L m : ℕ}
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (j : Fin L) (y : Y) :
    unconditionalActualFairSourceBobFlagPOVM
        G n S D denominator numerator nonempty b₀ P N L m
        flag j.succ y =
      directDSVActualReindexedRetainedPOVM
        (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
          (N := N)
          (d := Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D))
          (m := m)
          (unconditionalActualOneScaleFixedSourcePhaseSplit P) j)
        (directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv
            P N
            (Fintype.card
              (ExactGlobalHistoryLocalIndex G n S D)) m)
          (unitaryConjugatePOVM
            (conjugateUnitary
              (dSVUniformDensityThresholdLeftBobBasis
                (unconditionalActualFairSourceBobTarget
                  G n S D denominator numerator nonempty flag y)))
            (integratorActualC485SourceBobPOVM
              G n S D b₀ y))) := by
  classical
  have same_instance : decB = Classical.decEq B :=
    Subsingleton.elim _ _
  cases same_instance
  change
    physical8OneScaleOriginalFlagPOVM
      (N := N)
      (d := Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D))
      (m := m)
      (unconditionalActualOneScaleFixedSourcePhaseSplit P)
      b₀
      (fun q =>
        unitaryConjugatePOVM
          (conjugateUnitary
            (dSVUniformDensityThresholdLeftBobBasis
              (unconditionalActualFairSourceBobTarget
                G n S D denominator numerator nonempty flag q)))
          (integratorActualC485SourceBobPOVM
            G n S D b₀ q)) j.succ y = _
  exact
    unconditionalPhysicalOneScaleOriginalFlagPOVM_succ_nested
      (N := N)
      (d := Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D))
      (m := m)
      (unconditionalActualOneScaleFixedSourcePhaseSplit P)
      b₀
      (fun q =>
        unitaryConjugatePOVM
          (conjugateUnitary
            (dSVUniformDensityThresholdLeftBobBasis
              (unconditionalActualFairSourceBobTarget
                G n S D denominator numerator nonempty flag q)))
          (integratorActualC485SourceBobPOVM
            G n S D b₀ q)) j y

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open Classical in
theorem unconditionalActualPairedDecodedMatchedCleanedVector
    {F X Y : Type} {P N d L m : ℕ}
    (Q : ℕ) (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (ξ : F → X → BipartiteUnitVector d)
    (ζ : F → Y → BipartiteUnitVector d)
    (A C : Fin P → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (grid : 0 < N)
    (flag : F) (x : X) (y : Y) (j : Fin L)
    (positive : 0 < width (schedule j)) :
    let phase := unconditionalActualOneScaleFixedSourcePhaseSplit P
    let outer := unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
      (N := N) (d := d) (m := m) phase j
    let pair := unconditionalActualC485RetainedHistoryPairEquiv
      (P := P) (N := N) (d := d) j
    let stopped := actualStoppingBranchVector
      (actualStoppingQuestionLocalAction
        (physical8OneScaleActualAliceStoppingUnitary
          (P := P) (N := N) (d := d) (L := L) (m := m)
          phase Q width schedule ξ A flag x)
        (physical8OneScaleActualBobStoppingUnitary
          (P := P) (N := N) (d := d) (L := L) (m := m)
          phase Q width schedule ζ C flag y)
        (unconditionalSourcePhysicalCleanedStoppingFixedSource
          1 P N d L m)) j.succ j.succ
    unconditionalMixedConjugateSelectedBranchLocalAction
      (unconditionalMixedConjugateSigmaAtomLift
        (m := N * m) P
        (conjugateUnitary
          (dSVDensityRationalCanonicalAliceBasis (ξ flag x))))
      (unconditionalMixedConjugateSigmaAtomLift
        (m := N * m) P
        (conjugateUnitary
          (dSVUniformDensityThresholdLeftBobBasis (ζ flag y))))
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.prodCongr
          (Equiv.refl
            (UnconditionalSelectedCopyLocalIndex P d N m ×
             UnconditionalSelectedCopyLocalIndex P d N m)) pair)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (directDSVActualBilateralRetainedIndexEquiv
            outer outer) stopped)) =
      integratorActualC485CleanedVector
        (S := 1) (B := P) (N := N) (d := d) (L := L) (m := m)
        Q width schedule (ξ flag x) (ζ flag y) A C j := by
  dsimp only
  rw [unconditionalActualC485FullBilateralWorkRegroup]
  exact unconditionalActualOneScaleDecodedMatchedCleanedVector
    Q width schedule ξ ζ A C grid flag x y j positive

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalSampling

private def unconditionalActualC485SelectedVerifierBorn
    {X Y A B ι T : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype ι] [DecidableEq ι] [Fintype T] [DecidableEq T]
    (G : Game X Y A B) (PA : POVM A ι) (PB : POVM B ι)
    (x : X) (y : Y)
    (z : EuclideanSpace ℂ ((ι × ι) × T)) : ℝ :=
  quadraticExpectation
    (Matrix.toEuclideanCLM (n := (ι × ι) × T) (𝕜 := ℂ)
      (directDSVActualLocalPOVMWinningEffect G PA PB x y ⊗ₖ
        (1 : Matrix T T ℂ))) z

private def unconditionalActualC485RawPhysicalVerifierBorn
    {X Y A B ι κ : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (G : Game X Y A B) (PA : POVM A ι) (PB : POVM B κ)
    (x : X) (y : Y) (z : EuclideanSpace ℂ (ι × κ)) : ℝ :=
  quadraticExpectation
    (Matrix.toEuclideanCLM (n := ι × κ) (𝕜 := ℂ)
      (directDSVActualLocalPOVMWinningEffect G PA PB x y)) z

theorem unconditionalActualC485CompleteDecodedScalarBorn
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {P N d m : ℕ} {ι κ R T : Type}
    [Fintype ι] [Fintype κ] [Fintype R] [Fintype T]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq R] [DecidableEq T]
    (G : Game X Y A B)
    (alice bob : Matrix.unitaryGroup (Fin d) ℂ)
    (PA : POVM A (Fin d)) (PB : POVM B (Fin d))
    (selectedA :
      POVM A (UnconditionalSelectedCopyLocalIndex P d N m))
    (selectedB :
      POVM B (UnconditionalSelectedCopyLocalIndex P d N m))
    (selectedA_eq :
      selectedA =
        directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m) PA)
    (selectedB_eq :
      selectedB =
        directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m) PB)
    (eA : ι ≃ UnconditionalSelectedCopyLocalIndex P d N m × R)
    (eB : κ ≃ UnconditionalSelectedCopyLocalIndex P d N m × R)
    (pair : R × R ≃ T)
    (rawA : POVM A ι) (rawB : POVM B κ)
    (rawA_eq :
      rawA =
        directDSVActualReindexedRetainedPOVM eA
          (directDSVActualReindexedRetainedPOVM
            (physical8SelectedGlobalTargetWorkEquiv P N d m)
            (unitaryConjugatePOVM alice PA)))
    (rawB_eq :
      rawB =
        directDSVActualReindexedRetainedPOVM eB
          (directDSVActualReindexedRetainedPOVM
            (physical8SelectedGlobalTargetWorkEquiv P N d m)
            (unitaryConjugatePOVM bob PB)))
    (x : X) (y : Y)
    (z : EuclideanSpace ℂ (ι × κ))
    (source cleaned : EuclideanSpace ℂ
      ((UnconditionalSelectedCopyLocalIndex P d N m ×
        UnconditionalSelectedCopyLocalIndex P d N m) × T))
    (source_eq : source = cleaned)
    (decoded :
      unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P alice)
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P bob)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (Equiv.prodCongr
            (Equiv.refl
              (UnconditionalSelectedCopyLocalIndex P d N m ×
               UnconditionalSelectedCopyLocalIndex P d N m))
            pair)
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
            (directDSVActualBilateralRetainedIndexEquiv
              eA eB) z)) = cleaned) :
    unconditionalActualC485SelectedVerifierBorn
        G selectedA selectedB x y source =
      unconditionalActualC485RawPhysicalVerifierBorn
        G rawA rawB x y z := by
  exact unconditionalActualC485CompleteDecodedPhysicalBorn
    G alice bob PA PB selectedA selectedB selectedA_eq selectedB_eq
    eA eB pair rawA rawB rawA_eq rawB_eq
    x y z source cleaned source_eq decoded

/-- The Born-rule weight for unconditional actual fair source history stop. -/
def unconditionalActualFairSourceHistoryStopBorn
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (Q : ℕ)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (UA UB : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (h : ExactLocallySampleableTuple X Y A B D)
    (j : Fin L) : ℝ :=
  quadraticExpectation
    (integratorActualC485WinningEffect
      (P := P) (N := N) (L := L) (m := m)
      G n S D a₀ b₀ j h.2.1 h.2.2.1)
    (integratorActualC485CleanedVector
      (S := 1) (B := P) (N := N)
      (d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
      (L := L) (m := m)
      Q width schedule
      (unconditionalExactFairGammaUnit G n S D h)
      (exactGlobalHistoryFinPhi G n S D h.2.2.2 h.2.2.1)
      UA UB j)

/-- The Born-rule weight for unconditional actual fair source physical stop. -/
def unconditionalActualFairSourcePhysicalStopBorn
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (Q : ℕ)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (UA UB : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) (y : Y) (j : Fin L) : ℝ := by
  let d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D)
  let PA := unconditionalActualFairSourceAliceFlagPOVM
    G n S D denominator numerator nonempty a₀ P N L m flag
  let PB := unconditionalActualFairSourceBobFlagPOVM
    G n S D denominator numerator nonempty b₀ P N L m flag
  let U := unconditionalActualFairSourceAliceStoppingUnitary
    (P := P) (N := N) (L := L) (m := m)
    G n S D denominator numerator nonempty Q width schedule UA flag x
  let V := unconditionalActualFairSourceBobStoppingUnitary
    (P := P) (N := N) (L := L) (m := m)
    G n S D denominator numerator nonempty Q width schedule UB flag y
  exact
    unconditionalActualC485RawPhysicalVerifierBorn
      G (PA j.succ x) (PB j.succ y) x y
      (actualStoppingBranchVector
        (actualStoppingQuestionLocalAction U V
          (unconditionalSourcePhysicalCleanedStoppingFixedSource
            1 P N d L m)) j.succ j.succ)

open Classical in
theorem unconditionalActualFairSourceHistoryStopBorn_eq_selected
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (Q : ℕ)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (UA UB : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (h : ExactLocallySampleableTuple X Y A B D)
    (j : Fin L) :
    unconditionalActualFairSourceHistoryStopBorn
        G n S D a₀ b₀ Q width schedule UA UB h j =
      unconditionalActualC485SelectedVerifierBorn G
        (integratorActualC485SelectedAlicePOVM
          G n S D a₀ P N m h.2.1)
        (integratorActualC485SelectedBobPOVM
          G n S D b₀ P N m h.2.2.1)
        h.2.1 h.2.2.1
        (integratorActualC485CleanedVector
          (S := 1) (B := P) (N := N)
          (d := Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D))
          (L := L) (m := m)
          Q width schedule
          (unconditionalExactFairGammaUnit G n S D h)
          (exactGlobalHistoryFinPhi
            G n S D h.2.2.2 h.2.2.1)
          UA UB j) := by
  classical
  unfold unconditionalActualFairSourceHistoryStopBorn
    unconditionalActualC485SelectedVerifierBorn
  unfold integratorActualC485WinningEffect
  rfl

theorem unconditionalActualFairSourcePhysicalStopBorn_eq_raw
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (Q : ℕ)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (UA UB : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) (y : Y) (j : Fin L) :
    let d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D)
    let PA := unconditionalActualFairSourceAliceFlagPOVM
      G n S D denominator numerator nonempty a₀ P N L m flag
    let PB := unconditionalActualFairSourceBobFlagPOVM
      G n S D denominator numerator nonempty b₀ P N L m flag
    let stopped := actualStoppingBranchVector
      (actualStoppingQuestionLocalAction
        (unconditionalActualFairSourceAliceStoppingUnitary
          (P := P) (N := N) (L := L) (m := m)
          G n S D denominator numerator nonempty
          Q width schedule UA flag x)
        (unconditionalActualFairSourceBobStoppingUnitary
          (P := P) (N := N) (L := L) (m := m)
          G n S D denominator numerator nonempty
          Q width schedule UB flag y)
        (unconditionalSourcePhysicalCleanedStoppingFixedSource
          1 P N d L m)) j.succ j.succ
    unconditionalActualFairSourcePhysicalStopBorn
        G n S D denominator numerator nonempty a₀ b₀
        Q width schedule UA UB flag x y j =
      unconditionalActualC485RawPhysicalVerifierBorn
        G (PA j.succ x) (PB j.succ y) x y stopped := by
  classical
  dsimp only
  rfl

theorem unconditionalActualFairSourceMatchedHistoryGamma
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) (y : Y) :
    unconditionalExactFairGammaUnit G n S D
        (exactSourceAliceSampleTuple
          D denominator numerator nonempty (flag, (x, y))) =
      unconditionalActualFairSourceAliceTarget
        G n S D denominator numerator nonempty flag x := by
  rw [unconditionalExactFairGammaUnit_eq_global]
  exact
    (unconditionalFairMatchedFlag_aliceTarget_eq_aliceSample
      G n S D denominator numerator nonempty flag x y).symm

theorem unconditionalActualFairSourceMatchedHistoryPhi
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) (y : Y)
    (matching :
      exactSourcePermutationMatched
        D denominator numerator nonempty (flag, (x, y)) = true) :
    exactGlobalHistoryFinPhi G n S D
        (exactSourceAliceSampleTuple
          D denominator numerator nonempty (flag, (x, y))).2.2.2 y =
      unconditionalActualFairSourceBobTarget
        G n S D denominator numerator nonempty flag y := by
  exact
    (unconditionalFairMatchedFlag_bobTarget_eq_aliceSample
      G n S D denominator numerator nonempty flag x y matching).symm

theorem unconditionalActualFairSourceMatchedHistoryCleanedVector
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    {P N L m : ℕ} (Q : ℕ)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (UA UB : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) (y : Y)
    (matching :
      exactSourcePermutationMatched
        D denominator numerator nonempty (flag, (x, y)) = true)
    (j : Fin L) :
    let h := exactSourceAliceSampleTuple
      D denominator numerator nonempty (flag, (x, y))
    integratorActualC485CleanedVector
        (S := 1) (B := P) (N := N)
        (d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
        (L := L) (m := m)
        Q width schedule
        (unconditionalExactFairGammaUnit G n S D h)
        (exactGlobalHistoryFinPhi G n S D h.2.2.2 h.2.2.1)
        UA UB j =
      integratorActualC485CleanedVector
        (S := 1) (B := P) (N := N)
        (d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
        (L := L) (m := m)
        Q width schedule
        (unconditionalActualFairSourceAliceTarget
          G n S D denominator numerator nonempty flag x)
        (unconditionalActualFairSourceBobTarget
          G n S D denominator numerator nonempty flag y)
        UA UB j := by
  dsimp only
  exact congrArg₂
    (fun (u v : BipartiteUnitVector
        (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))) =>
      integratorActualC485CleanedVector
        (S := 1) (B := P) (N := N)
        (d := Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
        (L := L) (m := m)
        Q width schedule u v UA UB j)
    (unconditionalActualFairSourceMatchedHistoryGamma
      G n S D denominator numerator nonempty flag x y)
    (unconditionalActualFairSourceMatchedHistoryPhi
      G n S D denominator numerator nonempty flag x y matching)

theorem unconditionalActualFairSourcePhysicalStopBornWitness
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (Q : ℕ)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (UA UB : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (grid : 0 < N)
    (width_positive : ∀ s : Fin 1, 0 < width s)
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) (y : Y)
    (matching :
      exactSourcePermutationMatched
        D denominator numerator nonempty (flag, (x, y)) = true)
    (j : Fin L) :
    unconditionalActualFairSourceHistoryStopBorn
        G n S D a₀ b₀ Q width schedule UA UB
        (exactSourceAliceSampleTuple
          D denominator numerator nonempty (flag, (x, y))) j =
      unconditionalActualFairSourcePhysicalStopBorn
        G n S D denominator numerator nonempty a₀ b₀
        Q width schedule UA UB flag x y j := by
  classical
  let d : ℕ :=
    Fintype.card (ExactGlobalHistoryLocalIndex G n S D)
  let h := exactSourceAliceSampleTuple
    D denominator numerator nonempty (flag, (x, y))
  let targetA := unconditionalActualFairSourceAliceTarget
    G n S D denominator numerator nonempty
  let targetB := unconditionalActualFairSourceBobTarget
    G n S D denominator numerator nonempty
  let phase := unconditionalActualOneScaleFixedSourcePhaseSplit P
  let sourceA := integratorActualC485SourceAlicePOVM
    G n S D a₀ x
  let sourceB := integratorActualC485SourceBobPOVM
    G n S D b₀ y
  let atomA : Matrix.unitaryGroup (Fin d) ℂ :=
    conjugateUnitary
      (dSVDensityRationalCanonicalAliceBasis (targetA flag x))
  let atomB : Matrix.unitaryGroup (Fin d) ℂ :=
    conjugateUnitary
      (dSVUniformDensityThresholdLeftBobBasis (targetB flag y))
  let outer := unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
    (N := N) (d := d) (m := m) phase j
  let pair := unconditionalActualC485RetainedHistoryPairEquiv
    (P := P) (N := N) (d := d) j
  let selectedA := integratorActualC485SelectedAlicePOVM
    G n S D a₀ P N m x
  let selectedB := integratorActualC485SelectedBobPOVM
    G n S D b₀ P N m y
  have selectedA_eq : selectedA =
      directDSVActualReindexedRetainedPOVM
        (physical8SelectedGlobalTargetWorkEquiv P N d m)
        sourceA := by
    rfl
  have selectedB_eq : selectedB =
      directDSVActualReindexedRetainedPOVM
        (physical8SelectedGlobalTargetWorkEquiv P N d m)
        sourceB := by
    rfl
  let rawA := unconditionalActualFairSourceAliceFlagPOVM
    G n S D denominator numerator nonempty a₀ P N L m flag j.succ x
  let rawB := unconditionalActualFairSourceBobFlagPOVM
    G n S D denominator numerator nonempty b₀ P N L m flag j.succ y
  have rawA_eq : rawA =
      directDSVActualReindexedRetainedPOVM outer
        (directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m)
          (unitaryConjugatePOVM atomA sourceA)) := by
    simpa only [rawA, outer, phase, atomA, sourceA, targetA, d] using
      (unconditionalActualFairSourceAliceFlagPOVM_succ_nested
        G n S D denominator numerator nonempty a₀
        (P := P) (N := N) (L := L) (m := m) flag j x)
  have rawB_eq : rawB =
      directDSVActualReindexedRetainedPOVM outer
        (directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m)
          (unitaryConjugatePOVM atomB sourceB)) := by
    simpa only [rawB, outer, phase, atomB, sourceB, targetB, d] using
      (unconditionalActualFairSourceBobFlagPOVM_succ_nested
        G n S D denominator numerator nonempty b₀
        (P := P) (N := N) (L := L) (m := m) flag j y)
  let source := integratorActualC485CleanedVector
    (S := 1) (B := P) (N := N) (d := d) (L := L) (m := m)
    Q width schedule
    (unconditionalExactFairGammaUnit G n S D h)
    (exactGlobalHistoryFinPhi G n S D h.2.2.2 h.2.2.1)
    UA UB j
  let cleaned := integratorActualC485CleanedVector
    (S := 1) (B := P) (N := N) (d := d) (L := L) (m := m)
    Q width schedule (targetA flag x) (targetB flag y) UA UB j
  have source_eq : source = cleaned := by
    exact unconditionalActualFairSourceMatchedHistoryCleanedVector
      G n S D denominator numerator nonempty
      Q width schedule UA UB flag x y matching j
  let stopped := actualStoppingBranchVector
    (actualStoppingQuestionLocalAction
      (unconditionalActualFairSourceAliceStoppingUnitary
        (P := P) (N := N) (L := L) (m := m)
        G n S D denominator numerator nonempty
        Q width schedule UA flag x)
      (unconditionalActualFairSourceBobStoppingUnitary
        (P := P) (N := N) (L := L) (m := m)
        G n S D denominator numerator nonempty
        Q width schedule UB flag y)
      (unconditionalSourcePhysicalCleanedStoppingFixedSource
        1 P N d L m)) j.succ j.succ
  have decoded :
      unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P atomA)
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P atomB)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (Equiv.prodCongr
            (Equiv.refl
              (UnconditionalSelectedCopyLocalIndex P d N m ×
               UnconditionalSelectedCopyLocalIndex P d N m))
            pair)
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
            (directDSVActualBilateralRetainedIndexEquiv
              outer outer) stopped)) = cleaned := by
    simpa only [phase, stopped, cleaned, atomA, atomB, targetA,
      targetB, unconditionalActualFairSourceAliceStoppingUnitary,
      unconditionalActualFairSourceBobStoppingUnitary] using
      (unconditionalActualPairedDecodedMatchedCleanedVector
        Q width schedule
        (unconditionalActualFairSourceAliceTarget
          G n S D denominator numerator nonempty)
        (unconditionalActualFairSourceBobTarget
          G n S D denominator numerator nonempty)
        UA UB grid flag x y j (width_positive (schedule j)))
  have source_born :
      unconditionalActualFairSourceHistoryStopBorn
          G n S D a₀ b₀ Q width schedule UA UB h j =
        unconditionalActualC485SelectedVerifierBorn
          G selectedA selectedB x y source := by
    exact unconditionalActualFairSourceHistoryStopBorn_eq_selected
      G n S D a₀ b₀ Q width schedule UA UB h j
  have raw_born :
      unconditionalActualFairSourcePhysicalStopBorn
          G n S D denominator numerator nonempty a₀ b₀
          Q width schedule UA UB flag x y j =
        unconditionalActualC485RawPhysicalVerifierBorn
          G rawA rawB x y stopped := by
    exact unconditionalActualFairSourcePhysicalStopBorn_eq_raw
      G n S D denominator numerator nonempty a₀ b₀
      Q width schedule UA UB flag x y j
  calc
    unconditionalActualFairSourceHistoryStopBorn
        G n S D a₀ b₀ Q width schedule UA UB h j =
      unconditionalActualC485SelectedVerifierBorn
        G selectedA selectedB x y source := source_born
    _ = unconditionalActualC485RawPhysicalVerifierBorn
        G rawA rawB x y stopped :=
      unconditionalActualC485CompleteDecodedScalarBorn
        G atomA atomB sourceA sourceB selectedA selectedB
        selectedA_eq selectedB_eq outer outer pair rawA rawB
        rawA_eq rawB_eq x y stopped source cleaned source_eq decoded
    _ = unconditionalActualFairSourcePhysicalStopBorn
        G n S D denominator numerator nonempty a₀ b₀
        Q width schedule UA UB flag x y j := raw_born.symm

theorem unconditionalActualFairSourcePhysicalBranchWitness
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (Q : ℕ)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (UA UB : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (grid : 0 < N)
    (width_positive : ∀ s : Fin 1, 0 < width s)
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) (y : Y)
    (matching :
      exactSourcePermutationMatched
        D denominator numerator nonempty (flag, (x, y)) = true) :
    (∑ j : Fin L,
      unconditionalActualFairSourceHistoryStopBorn
        G n S D a₀ b₀ Q width schedule UA UB
        (exactSourceAliceSampleTuple
          D denominator numerator nonempty (flag, (x, y))) j) =
      ∑ j : Fin L,
        unconditionalActualFairSourcePhysicalStopBorn
          G n S D denominator numerator nonempty a₀ b₀
          Q width schedule UA UB flag x y j := by
  apply Finset.sum_congr rfl
  intro j _
  exact unconditionalActualFairSourcePhysicalStopBornWitness
    G n S D denominator numerator nonempty a₀ b₀
    Q width schedule UA UB grid width_positive flag x y matching j

end

end QuantumParallelRepetition

end
