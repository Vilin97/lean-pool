/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage4AboveTwoFinalTrial.Ledger

namespace V7.Stage4AboveTwoFinalTrial

noncomputable def shapeWitness (p eps M D : ℝ) (x0 : Point d)
    (oracle : PairOracle d) (m₁ m₂ : ℕ) : AboveTrialWitness p d where
  nF := nF p eps M D
  nD := nD p eps M D
  completedF := m₁
  completedD := m₂
  etaF := etaF p
  etaD := etaD p eps M D
  gammaF := aboveGamma p (etaF p) (nF p eps M D)
  gammaD := aboveGamma p (etaD p eps M D) (nD p eps M D)
  phaseOne := primalData p (etaF p) (nF p eps M D)
    (phaseOneOracle x0 M D oracle) 0
  phaseTwo := dualData p (etaD p eps M D) (nD p eps M D)
    (phaseTwoOracle p eps M D x0 oracle)
  phaseTwoCenter := phaseTwoCenter p eps M D x0 oracle

theorem fullShape_operational_contract (hp : 2 < p) (heps : 0 < eps)
    (hM : 0 < M) (hD : 0 < D)
    (hcached : cached.observation = oracle.observe x0)
    (hshape : FullShape p eps M D x0 oracle report m₁ m₂) :
    AboveTrialOperationalContract p eps M D x0 cached oracle report
      (shapeWitness p eps M D x0 oracle m₁ m₂) := by
  have hnf := one_le_nF hp heps hM hD
  have hnd := one_le_nD hp heps hM hD
  have hef := etaF_pos hp
  have hed := etaD_pos hp heps hM hD
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl,
    primal_dynamics p (etaF p) (nF p eps M D) hp hef hnf _ 0,
    rfl, rfl, dualQ_zero _ _ _ _,
    dual_dynamics p (etaD p eps M D) (nD p eps M D) hp hed hnd _,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, fullShape_kinds hshape,
    fullShape_ledger hcached hshape, fullShape_accounting hshape,
    fullShape_calls_le hshape⟩
  · intro k hk
    exact weight_of_lt hk
  · exact weight_at
  · intro k hk
    exact weight_of_lt hk
  · exact weight_at
  · dsimp [shapeWitness]
    cases hshape <;> omega
  · dsimp [shapeWitness]
    cases hshape <;> omega
  · intro hm₂
    dsimp [shapeWitness] at hm₂ ⊢
    cases hshape <;> simp_all
  · intro k hk
    rfl
  · dsimp [shapeWitness]
    cases hshape <;>
      simp [phaseOneNewTrace, phaseTwoNewTrace, phaseOneObs, phaseOneState,
        phaseTwoObs, phaseTwoCenter, primalData, dualData]
  · intro terminal hout
    cases hshape with
    | primalSuccess m hm0 hmn hsmall hprior =>
        injection hout with heq
        subst terminal
        exact Or.inr ⟨rfl, hm0, rfl⟩
    | primalScale m hm0 hmn hprior hlarge hfail => cases hout
    | dualSuccess m hm0 hmn hP hQ hsmall =>
        injection hout with heq
        subst terminal
        exact Or.inl ⟨hm0, rfl⟩
    | dualScale m hm0 hmn hP hQ hlarge hfail => cases hout
    | radius hP hQ hlarge => cases hout
  · intro terminal hout
    cases hshape with
    | primalSuccess m hm0 hmn hsmall hprior => cases hout
    | primalScale m hm0 hmn hprior hlarge hfail => cases hout
    | dualSuccess m hm0 hmn hP hQ hsmall => cases hout
    | dualScale m hm0 hmn hP hQ hlarge hfail => cases hout
    | radius hP hQ hlarge =>
        injection hout with heq
        subst terminal
        exact ⟨rfl, rfl, rfl⟩

end V7.Stage4AboveTwoFinalTrial
