/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.InsertionEdgeRealization

/-!
# The terminal law in the insertion argument

The common variable on the terminal edge is the sum of the negative old
coordinates, with the distinguished positive exponential removed.
-/

open MeasureTheory Set

namespace Feige

noncomputable section

/-- The all-negative signed exponential sum at the terminal chain state. -/
def terminalCommonSignedSum {n : ℕ} (β : Fin (n + 1) → ℝ)
    (e : Fin n → NNReal) : ℝ :=
  -∑ i, β i.castSucc * (e i : ℝ)

/-- The law of the terminal all-negative signed exponential sum. -/
noncomputable def terminalCommonLaw {n : ℕ}
    (β : Fin (n + 1) → ℝ) : Measure ℝ :=
  Measure.map (terminalCommonSignedSum β)
    (Measure.pi fun _ : Fin n ↦ nnexpMeasure)

theorem measurable_terminalCommonSignedSum {n : ℕ}
    (β : Fin (n + 1) → ℝ) :
    Measurable (terminalCommonSignedSum β) := by
  unfold terminalCommonSignedSum
  fun_prop

instance terminalCommonLaw_isProbability {n : ℕ}
    (β : Fin (n + 1) → ℝ) :
    IsProbabilityMeasure (terminalCommonLaw β) := by
  unfold terminalCommonLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_terminalCommonSignedSum β).aemeasurable

theorem terminalCommonLaw_Ioi_zero {n : ℕ}
    (β : Fin (n + 1) → ℝ) (hβ : ∀ i, 0 < β i) :
    terminalCommonLaw β (Ioi 0) = 0 := by
  rw [terminalCommonLaw,
    Measure.map_apply (measurable_terminalCommonSignedSum β) measurableSet_Ioi]
  have hpre :
      terminalCommonSignedSum β ⁻¹' Ioi 0 = (∅ : Set (Fin n → NNReal)) := by
    ext e
    simp only [mem_preimage, mem_Ioi, Set.mem_empty_iff_false]
    constructor
    · intro he
      exact (not_lt_of_ge (show terminalCommonSignedSum β e ≤ 0 by
        unfold terminalCommonSignedSum
        exact neg_nonpos.mpr <| Finset.sum_nonneg fun i _ ↦
          mul_nonneg (hβ i.castSucc).le (NNReal.coe_nonneg _))) he
    · intro he
      exact he.elim
  rw [hpre]
  exact measure_empty

theorem zPlus_terminalCommonLaw_eq_stateLaw_univ {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) :
    TransferStein.zPlusLaw (terminalCommonLaw β) 1 =
      stateLaw (fun i : Fin n ↦ γ i.castSucc)
        (fun i : Fin n ↦ β i.castSucc) Finset.univ := by
  let rest : Measure (Fin n → NNReal) :=
    Measure.pi fun _ : Fin n ↦ nnexpMeasure
  let split :
      (Option (Fin n) → NNReal) ≃ᵐ ((Fin n → NNReal) × NNReal) :=
    MeasurableEquiv.piOptionEquivProd
      (fun _ : Option (Fin n) ↦ NNReal)
  have hsplit :
      (rest.prod nnexpMeasure).map split.symm =
        expProductMeasure (Fin n) := by
    simpa [rest, split, expProductMeasure] using
      (Measure.pi_map_piOptionEquivProd
        (fun _ : Option (Fin n) ↦ nnexpMeasure))
  unfold TransferStein.zPlusLaw terminalCommonLaw stateLaw
  rw [show ProbabilityTheory.expMeasure 1 =
      Measure.map (fun x : NNReal ↦ (x : ℝ)) nnexpMeasure by
        exact map_nnexpMeasure_coe.symm]
  change Measure.map (fun p : ℝ × ℝ ↦ p.1 + 1 * p.2)
      ((Measure.map (terminalCommonSignedSum β) rest).prod
        (Measure.map (fun x : NNReal ↦ (x : ℝ)) nnexpMeasure)) =
    Measure.map
      (stateSignedSum (fun i : Fin n ↦ γ i.castSucc)
        (fun i : Fin n ↦ β i.castSucc) Finset.univ)
      (expProductMeasure (Fin n))
  rw [show
    (Measure.map (terminalCommonSignedSum β) rest).prod
        (Measure.map (fun x : NNReal ↦ (x : ℝ)) nnexpMeasure) =
      Measure.map
        (Prod.map (terminalCommonSignedSum β) (fun x : NNReal ↦ (x : ℝ)))
        (rest.prod nnexpMeasure) by
      exact Measure.map_prod_map rest nnexpMeasure
        (measurable_terminalCommonSignedSum β)
        NNReal.continuous_coe.measurable]
  rw [Measure.map_map]
  · rw [← hsplit, Measure.map_map]
    · congr 1
      funext p
      have hnone : split.symm p none = p.2 := by rfl
      have hsome : ∀ i, split.symm p (some i) = p.1 i := by
        intro i
        rfl
      simp only [Function.comp_apply, one_mul]
      dsimp only [Prod.map]
      unfold terminalCommonSignedSum stateSignedSum
      simp only [Finset.mem_univ, ite_true, hnone, hsome]
      rw [← Finset.sum_neg_distrib]
      ring
    · exact measurable_stateSignedSum _ _ Finset.univ
    · exact split.symm.measurable
  · fun_prop
  · exact (measurable_terminalCommonSignedSum β).prodMap
      NNReal.continuous_coe.measurable

theorem realizesInsertionEdge_terminal {n : ℕ}
    (γ β : Fin (n + 1) → ℝ)
    (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (σ : Equiv.Perm (Fin n)) :
    Lemma43.RealizesInsertionEdge
      (insertionUpperK γ β σ) (insertionOldK γ β σ)
      (insertionWidth γ β σ) (insertionTheta γ β σ) n
      (TransferStein.zPlusLaw (terminalCommonLaw β) 1)
      (TransferStein.zMinusLaw (terminalCommonLaw β) 1)
      (γ (Fin.last n)) (β (Fin.last n)) := by
  let νP := TransferStein.zPlusLaw (terminalCommonLaw β) 1
  let νM := TransferStein.zMinusLaw (terminalCommonLaw β) 1
  have hνP :
      νP = stateLaw (fun i : Fin n ↦ γ i.castSucc)
        (fun i : Fin n ↦ β i.castSucc) Finset.univ :=
    zPlus_terminalCommonLaw_eq_stateLaw_univ γ β
  obtain ⟨hFM, hθM⟩ :=
    Lemma43ArbitraryBase.terminal_zMinus
      (terminalCommonLaw β) (terminalCommonLaw_Ioi_zero β hβ)
      (b := (1 : ℝ)) (c := γ (Fin.last n)) (d := β (Fin.last n))
      one_pos
  have hAM : Lemma43.A νM (β (Fin.last n)) = 0 := by
    have hIci : νM (Ici 0) = 0 := by
      have htr : ENNReal.toReal (νM (Ici 0)) = 0 := by
        simpa only [Lemma43.F] using hFM
      rcases (ENNReal.toReal_eq_zero_iff _).mp htr with hzero | htop
      · exact hzero
      · exact (measure_ne_top νM (Ici 0) htop).elim
    have hae : ∀ᵐ y ∂νM, y ≤ 0 := by
      rw [ae_iff]
      have hs : {y : ℝ | ¬y ≤ 0} = Ioi 0 := by ext y; simp
      rw [hs]
      exact measure_mono_null Ioi_subset_Ici_self hIci
    unfold Lemma43.A
    apply integral_eq_zero_of_ae
    filter_upwards [hae] with y hy
    exact TransferTestFunctions.transferPhi_of_nonpos
      (hβ (Fin.last n)) hy
  change Lemma43.RealizesInsertionEdge
    (insertionUpperK γ β σ) (insertionOldK γ β σ)
    (insertionWidth γ β σ) (insertionTheta γ β σ) n
    νP νM (γ (Fin.last n)) (β (Fin.last n))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      insertionUpperK γ β σ n =
          Lemma43.A
            (stateLaw (fun i : Fin n ↦ γ i.castSucc)
              (fun i : Fin n ↦ β i.castSucc) Finset.univ)
            (β (Fin.last n)) := by
        simpa using
          insertionUpperK_eq_A_stateLaw γ β hγ hβ σ (Fin.last n)
      _ = _ := by rw [← hνP]
  · simp [insertionUpperK, hAM]
  · calc
      insertionOldK γ β σ n =
          Lemma43.F
            (stateLaw (fun i : Fin n ↦ γ i.castSucc)
              (fun i : Fin n ↦ β i.castSucc) Finset.univ) := by
        simpa using insertionOldK_eq_F_stateLaw γ β σ (Fin.last n)
      _ = _ := by rw [← hνP]
  · unfold insertionOldK
    rw [booleanChainK_sentinel, hFM]
  · calc
      insertionWidth γ β σ n =
          Lemma43.w
            (stateLaw (fun i : Fin n ↦ γ i.castSucc)
              (fun i : Fin n ↦ β i.castSucc) Finset.univ)
            (γ (Fin.last n)) (β (Fin.last n)) := by
        simpa using
          insertionWidth_eq_w_stateLaw γ β hγ hβ σ (Fin.last n)
      _ = _ := by rw [← hνP]
  · calc
      insertionTheta γ β σ n =
          Lemma43.theta
            (stateLaw (fun i : Fin n ↦ γ i.castSucc)
              (fun i : Fin n ↦ β i.castSucc) Finset.univ)
            (γ (Fin.last n)) (β (Fin.last n)) := by
        simpa using
          insertionTheta_eq_theta_stateLaw γ β hγ hβ σ (Fin.last n)
      _ = _ := by rw [← hνP]
  · rw [insertionTheta_sentinel]
    exact hθM.symm

end

end Feige
