/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.InsertionAnalyticAssembly
import LeanPool.Feige.InsertionLastCoordinateLaw

/-!
# Realizing the genuine edges of an insertion chain

At every old chain level, the three numerical sequences `F`, `B`, and `A`
are respectively the nonnegative-tail probability of the old state law,
the positive shift by the new low-side scale, and the negative shift by the
new high-side scale.  This identifies every nonterminal edge with the
finite signed-exponential instance of the local transfer step.
-/

open MeasureTheory

namespace Feige

noncomputable section

theorem insertionOldK_eq_F_stateLaw {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) :
    insertionOldK γ β σ r.val =
      Lemma43.F
        (stateLaw (fun i : Fin n ↦ γ i.castSucc)
          (fun i : Fin n ↦ β i.castSucc) (chainState σ r)) := by
  unfold insertionOldK
  rw [booleanChainK_of_lt _ _ _ r.isLt]
  simpa only [Lemma43.F] using
    (twoPointKFinset_eq_stateLaw
      (fun i : Fin n ↦ γ i.castSucc)
      (fun i : Fin n ↦ β i.castSucc) (chainState σ r))

theorem insertionLowerK_eq_B_stateLaw {n : ℕ}
    (γ β : Fin (n + 1) → ℝ)
    (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (σ : Equiv.Perm (Fin n)) (r : Fin (n + 1)) :
    insertionLowerK γ β σ r.val =
      Lemma43.B
        (stateLaw (fun i : Fin n ↦ γ i.castSucc)
          (fun i : Fin n ↦ β i.castSucc) (chainState σ r))
        (γ (Fin.last n)) := by
  unfold insertionLowerK
  rw [dite_eq_left r.isLt]
  calc
    twoPointKFinset γ β (liftChainState (chainState σ r)) =
        Lemma43.F
          (stateLaw γ β (liftChainState (chainState σ r))) := by
      simpa only [Lemma43.F] using
        (twoPointKFinset_eq_stateLaw γ β
          (liftChainState (chainState σ r)))
    _ = Lemma43.F
        (TransferStein.zPlusLaw
          (stateLaw (fun i : Fin n ↦ γ i.castSucc)
            (fun i : Fin n ↦ β i.castSucc) (chainState σ r))
          (γ (Fin.last n))) := by
      rw [stateLaw_liftChainState_eq_zPlus_old γ β hγ hβ]
    _ = _ := Lemma43Endpoints.F_zPlusLaw_eq_B _
      (hγ (Fin.last n))

theorem insertionUpperK_eq_A_stateLaw {n : ℕ}
    (γ β : Fin (n + 1) → ℝ)
    (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (σ : Equiv.Perm (Fin n)) (r : Fin (n + 1)) :
    insertionUpperK γ β σ r.val =
      Lemma43.A
        (stateLaw (fun i : Fin n ↦ γ i.castSucc)
          (fun i : Fin n ↦ β i.castSucc) (chainState σ r))
        (β (Fin.last n)) := by
  unfold insertionUpperK
  rw [dite_eq_left r.isLt]
  calc
    twoPointKFinset γ β
        (insert (Fin.last n) (liftChainState (chainState σ r))) =
        Lemma43.F
          (stateLaw γ β
            (insert (Fin.last n) (liftChainState (chainState σ r)))) := by
      simpa only [Lemma43.F] using
        (twoPointKFinset_eq_stateLaw γ β
          (insert (Fin.last n) (liftChainState (chainState σ r))))
    _ = Lemma43.F
        (TransferStein.zMinusLaw
          (stateLaw (fun i : Fin n ↦ γ i.castSucc)
            (fun i : Fin n ↦ β i.castSucc) (chainState σ r))
          (β (Fin.last n))) := by
      rw [stateLaw_insert_last_eq_zMinus_old γ β hγ hβ]
    _ = _ := Lemma43Endpoints.F_zMinusLaw_eq_A _
      (hβ (Fin.last n))

theorem insertionWidth_eq_w_stateLaw {n : ℕ}
    (γ β : Fin (n + 1) → ℝ)
    (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (σ : Equiv.Perm (Fin n)) (r : Fin (n + 1)) :
    insertionWidth γ β σ r.val =
      Lemma43.w
        (stateLaw (fun i : Fin n ↦ γ i.castSucc)
          (fun i : Fin n ↦ β i.castSucc) (chainState σ r))
        (γ (Fin.last n)) (β (Fin.last n)) := by
  unfold insertionWidth
  rw [insertionLowerK_eq_B_stateLaw γ β hγ hβ σ r,
    insertionUpperK_eq_A_stateLaw γ β hγ hβ σ r,
    Lemma43.B_eq_A_add_w _ (hγ (Fin.last n)) (hβ (Fin.last n))]
  ring

theorem insertionTheta_eq_theta_stateLaw {n : ℕ}
    (γ β : Fin (n + 1) → ℝ)
    (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (σ : Equiv.Perm (Fin n)) (r : Fin (n + 1)) :
    insertionTheta γ β σ r.val =
      Lemma43.theta
        (stateLaw (fun i : Fin n ↦ γ i.castSucc)
          (fun i : Fin n ↦ β i.castSucc) (chainState σ r))
        (γ (Fin.last n)) (β (Fin.last n)) := by
  let ν :=
    stateLaw (fun i : Fin n ↦ γ i.castSucc)
      (fun i : Fin n ↦ β i.castSucc) (chainState σ r)
  have hFA :
      Lemma43.F ν =
        Lemma43.A ν (β (Fin.last n)) +
          Lemma43.u ν (β (Fin.last n)) := by
    calc
      Lemma43.F ν =
          Lemma43.B ν (γ (Fin.last n)) -
            Lemma43.v ν (γ (Fin.last n)) :=
        Lemma43.F_eq_B_sub_v ν (hγ (Fin.last n))
      _ = (Lemma43.A ν (β (Fin.last n)) +
            Lemma43.w ν (γ (Fin.last n)) (β (Fin.last n))) -
            Lemma43.v ν (γ (Fin.last n)) := by
        rw [Lemma43.B_eq_A_add_w ν
          (hγ (Fin.last n)) (hβ (Fin.last n))]
      _ = _ := by
        unfold Lemma43.w
        ring
  unfold insertionTheta
  rw [insertionOldK_eq_F_stateLaw γ β σ r,
    insertionUpperK_eq_A_stateLaw γ β hγ hβ σ r,
    insertionWidth_eq_w_stateLaw γ β hγ hβ σ r]
  change
    (Lemma43.F ν - Lemma43.A ν (β (Fin.last n))) /
        Lemma43.w ν (γ (Fin.last n)) (β (Fin.last n)) =
      Lemma43.theta ν (γ (Fin.last n)) (β (Fin.last n))
  rw [hFA]
  unfold Lemma43.theta
  ring

/-- Every genuine adjacent pair of old chain levels realizes exactly the
finite signed-exponential endpoint pair consumed by the local transfer
step. -/
theorem realizesInsertionEdge_interior {n : ℕ}
    (γ β : Fin (n + 1) → ℝ)
    (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    Lemma43.RealizesInsertionEdge
      (insertionUpperK γ β σ) (insertionOldK γ β σ)
      (insertionWidth γ β σ) (insertionTheta γ β σ) j.val
      (TransferStein.zPlusLaw
        (volume.withDensity
          (LikelihoodRatio.finiteSignedExpSumDensity
            (LikelihoodRatio.commonFactors
              (fun i : Fin n ↦ γ i.castSucc)
              (fun i : Fin n ↦ β i.castSucc)
              (fun i ↦ hγ i.castSucc) (fun i ↦ hβ i.castSucc)
              (chainState σ j.castSucc) (σ j))))
        (γ (σ j).castSucc))
      (TransferStein.zMinusLaw
        (volume.withDensity
          (LikelihoodRatio.finiteSignedExpSumDensity
            (LikelihoodRatio.commonFactors
              (fun i : Fin n ↦ γ i.castSucc)
              (fun i : Fin n ↦ β i.castSucc)
              (fun i ↦ hγ i.castSucc) (fun i ↦ hβ i.castSucc)
              (chainState σ j.castSucc) (σ j))))
        (β (σ j).castSucc))
      (γ (Fin.last n)) (β (Fin.last n)) := by
  let γold : Fin n → ℝ := fun i ↦ γ i.castSucc
  let βold : Fin n → ℝ := fun i ↦ β i.castSucc
  let hγold : ∀ i, 0 < γold i := fun i ↦ hγ i.castSucc
  let hβold : ∀ i, 0 < βold i := fun i ↦ hβ i.castSucc
  let S : Finset (Fin n) := chainState σ j.castSucc
  let changed : Fin n := σ j
  let common :=
    volume.withDensity
      (LikelihoodRatio.finiteSignedExpSumDensity
        (LikelihoodRatio.commonFactors
          γold βold hγold hβold S changed))
  let νP := TransferStein.zPlusLaw common (γold changed)
  let νM := TransferStein.zMinusLaw common (βold changed)
  change Lemma43.RealizesInsertionEdge
    (insertionUpperK γ β σ) (insertionOldK γ β σ)
    (insertionWidth γ β σ) (insertionTheta γ β σ) j.val
    νP νM (γ (Fin.last n)) (β (Fin.last n))
  have hchanged : changed ∉ S := by
    exact perm_not_mem_chainState_castSucc σ j
  have hνP : νP = stateLaw γold βold S := by
    calc
      νP = insertionLowEndpointLaw
          γold βold hγold hβold S changed := by
        unfold νP common insertionLowEndpointLaw
        rw [insertionCommonLaw_eq_withDensity]
      _ = stateLaw γold βold S :=
        insertionLowEndpointLaw_eq_stateLaw
          γold βold hγold hβold S changed hchanged
  have hνM :
      νM = stateLaw γold βold (chainState σ j.succ) := by
    calc
      νM = insertionHighEndpointLaw
          γold βold hγold hβold S changed := by
        unfold νM common insertionHighEndpointLaw
        rw [insertionCommonLaw_eq_withDensity]
      _ = stateLaw γold βold (insert changed S) :=
        insertionHighEndpointLaw_eq_stateLaw_insert
          γold βold hγold hβold S changed
      _ = stateLaw γold βold (chainState σ j.succ) := by
        rw [chainState_succ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hνP]
    simpa only [γold, βold, S, Fin.val_castSucc] using
      (insertionUpperK_eq_A_stateLaw γ β hγ hβ σ j.castSucc)
  · rw [show j.val + 1 = j.succ.val by rfl,
      insertionUpperK_eq_A_stateLaw γ β hγ hβ σ j.succ,
      ← hνM]
  · rw [hνP]
    simpa only [γold, βold, S, Fin.val_castSucc] using
      (insertionOldK_eq_F_stateLaw γ β σ j.castSucc)
  · rw [show j.val + 1 = j.succ.val by rfl,
      insertionOldK_eq_F_stateLaw γ β σ j.succ, ← hνM]
  · rw [hνP]
    simpa only [γold, βold, S, Fin.val_castSucc] using
      (insertionWidth_eq_w_stateLaw γ β hγ hβ σ j.castSucc)
  · rw [hνP]
    simpa only [γold, βold, S, Fin.val_castSucc] using
      (insertionTheta_eq_theta_stateLaw γ β hγ hβ σ j.castSucc)
  · rw [show j.val + 1 = j.succ.val by rfl,
      insertionTheta_eq_theta_stateLaw γ β hγ hβ σ j.succ,
      ← hνM]

end

end Feige
