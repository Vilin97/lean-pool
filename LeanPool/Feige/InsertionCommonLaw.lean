/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.TwoPoint
import LeanPool.Feige.SignedExpLaw
import LeanPool.Feige.TransferProbability23
import LeanPool.Feige.InsertionCommonDensity
import LeanPool.Feige.NNRealExponentialLaw
import Mathlib.Probability.Independence.Basic

/-!
# Signed-sum laws along a Boolean insertion edge

The event defining `twoPointKFinset` is rewritten as nonnegativity of the
corresponding signed exponential sum.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Feige

noncomputable section

local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The signed exponential statistic at Boolean state `S`. -/
def stateSignedSum (γ β : ι → ℝ) (S : Finset ι)
    (e : Option ι → NNReal) : ℝ :=
  (e none : ℝ) +
    ∑ i, if i ∈ S then -(β i * (e (some i) : ℝ))
      else γ i * (e (some i) : ℝ)

theorem measurable_stateSignedSum (γ β : ι → ℝ) (S : Finset ι) :
    Measurable (stateSignedSum γ β S) := by
  unfold stateSignedSum
  apply Measurable.add
  · exact (measurable_pi_apply none).coe_nnreal_real
  · apply Finset.measurable_fun_sum
    intro i hi
    by_cases hiS : i ∈ S
    · simp only [ite_eq_left hiS]
      fun_prop
    · simp only [ite_eq_right hiS]
      fun_prop

/-- Pushforward law of the signed sum at state `S`. -/
noncomputable def stateLaw (γ β : ι → ℝ) (S : Finset ι) : Measure ℝ :=
  Measure.map (stateSignedSum γ β S) (expProductMeasure ι)

instance stateLaw_isProbability (γ β : ι → ℝ) (S : Finset ι) :
    IsProbabilityMeasure (stateLaw γ β S) := by
  unfold stateLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_stateSignedSum γ β S).aemeasurable

/-- The original event in the definition of `K` is exactly nonnegativity
of the signed sum. -/
theorem kEvent_twoPointVector_eq_stateSignedSum
    (γ β : ι → ℝ) (S : Finset ι) :
    kEvent (twoPointVector γ β (S : Set ι)) =
      stateSignedSum γ β S ⁻¹' Ici 0 := by
  ext e
  simp only [kEvent, mem_ofPred_eq, mem_preimage, mem_Ici]
  have hsum :
      (∑ i, (twoPointVector γ β (S : Set ι) i - 1) *
          (e (some i) : ℝ)) =
        -(∑ i, if i ∈ S then -(β i * (e (some i) : ℝ))
          else γ i * (e (some i) : ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hiS : i ∈ S
    · simp [twoPointVector, hiS, highValue]
    · simp [twoPointVector, hiS, lowValue]
  rw [hsum]
  unfold stateSignedSum
  change
    -(∑ i, if i ∈ S then -(β i * (e (some i) : ℝ))
      else γ i * (e (some i) : ℝ)) ≤ (e none : ℝ) ↔
    0 ≤ (e none : ℝ) +
      ∑ i, if i ∈ S then -(β i * (e (some i) : ℝ))
        else γ i * (e (some i) : ℝ)
  constructor <;> intro h <;> linarith

/-- `twoPointKFinset` is the nonnegative-tail probability of the actual
signed exponential state law. -/
theorem twoPointKFinset_eq_stateLaw
    (γ β : ι → ℝ) (S : Finset ι) :
    twoPointKFinset γ β S =
      ENNReal.toReal (stateLaw γ β S (Ici 0)) := by
  rw [twoPointKFinset, twoPointK, dirichletK, stateLaw,
    Measure.map_apply (measurable_stateSignedSum γ β S) measurableSet_Ici,
    ← kEvent_twoPointVector_eq_stateSignedSum]
  rfl

/-- The common signed sum obtained by deleting the changed coordinate, on
the original product sample space. -/
def stateCommonSignedSum (γ β : ι → ℝ) (S : Finset ι) (changed : ι)
    (e : Option ι → NNReal) : ℝ :=
  (e none : ℝ) +
    ∑ i ∈ Finset.univ.erase changed,
      if i ∈ S then -(β i * (e (some i) : ℝ))
      else γ i * (e (some i) : ℝ)

theorem measurable_stateCommonSignedSum
    (γ β : ι → ℝ) (S : Finset ι) (changed : ι) :
    Measurable (stateCommonSignedSum γ β S changed) := by
  unfold stateCommonSignedSum
  apply Measurable.add
  · exact (measurable_pi_apply none).coe_nnreal_real
  · apply Finset.measurable_fun_sum
    intro i hi
    by_cases hiS : i ∈ S
    · simp only [ite_eq_left hiS]
      fun_prop
    · simp only [ite_eq_right hiS]
      fun_prop

/-- At the low endpoint, the state sum is the common sum plus the changed
positive exponential. -/
theorem stateSignedSum_eq_common_add
    (γ β : ι → ℝ) (S : Finset ι) (changed : ι)
    (hj : changed ∉ S) (e : Option ι → NNReal) :
    stateSignedSum γ β S e =
      stateCommonSignedSum γ β S changed e +
        γ changed * (e (some changed) : ℝ) := by
  unfold stateSignedSum stateCommonSignedSum
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ changed)]
  simp only [hj, ite_false]
  ring

/-- At the high endpoint, the changed coordinate contributes the
corresponding negative exponential to the same common sum. -/
theorem stateSignedSum_insert_eq_common_sub
    (γ β : ι → ℝ) (S : Finset ι) (changed : ι)
    (hj : changed ∉ S) (e : Option ι → NNReal) :
    stateSignedSum γ β (insert changed S) e =
      stateCommonSignedSum γ β S changed e -
        β changed * (e (some changed) : ℝ) := by
  unfold stateSignedSum stateCommonSignedSum
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ changed)]
  have herase :
      ∀ i ∈ Finset.univ.erase changed,
        (if i ∈ insert changed S
          then -(β i * (e (some i) : ℝ))
          else γ i * (e (some i) : ℝ)) =
        (if i ∈ S then -(β i * (e (some i) : ℝ))
          else γ i * (e (some i) : ℝ)) := by
    intro i hi
    have hine : i ≠ changed := (Finset.mem_erase.mp hi).1
    simp [hine]
  rw [Finset.sum_congr rfl herase]
  simp [hj]
  ring

/-- The common law on an insertion edge, constructed as the convolution of
the unchanged signed exponential factors together with the distinguished
rate-one exponential `E₀`. -/
noncomputable def insertionCommonLaw
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (changed : ι) : Measure ℝ :=
  LikelihoodRatio.finiteSignedExpSumMeasure
    (LikelihoodRatio.commonFactors γ β hγ hβ S changed)

instance insertionCommonLaw_isProbability
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (changed : ι) :
    IsProbabilityMeasure
      (insertionCommonLaw γ β hγ hβ S changed) := by
  unfold insertionCommonLaw
  infer_instance

/-- The common law has exactly the explicit finite signed-exponential
density used by the TP2 argument. -/
theorem insertionCommonLaw_eq_withDensity
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (changed : ι) :
    insertionCommonLaw γ β hγ hβ S changed =
      volume.withDensity
        (LikelihoodRatio.finiteSignedExpSumDensity
          (LikelihoodRatio.commonFactors γ β hγ hβ S changed)) := by
  exact LikelihoodRatio.finiteSignedExpSumMeasure_eq_withDensity _

/-- Law of the low endpoint obtained by adding the changed coordinate's
positive scaled exponential to the common part. -/
noncomputable def insertionLowEndpointLaw
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (changed : ι) : Measure ℝ :=
  TransferStein.zPlusLaw
    (insertionCommonLaw γ β hγ hβ S changed) (γ changed)

/-- Law of the high endpoint obtained by subtracting the changed
coordinate's scaled exponential from the common part. -/
noncomputable def insertionHighEndpointLaw
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (changed : ι) : Measure ℝ :=
  TransferStein.zMinusLaw
    (insertionCommonLaw γ β hγ hβ S changed) (β changed)

theorem insertionLowEndpointLaw_eq_zPlus
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (changed : ι) :
    insertionLowEndpointLaw γ β hγ hβ S changed =
      TransferStein.zPlusLaw
        (insertionCommonLaw γ β hγ hβ S changed) (γ changed) :=
  rfl

theorem insertionHighEndpointLaw_eq_zMinus
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (changed : ι) :
    insertionHighEndpointLaw γ β hγ hβ S changed =
      TransferStein.zMinusLaw
        (insertionCommonLaw γ β hγ hβ S changed) (β changed) :=
  rfl

/-- The real-valued signed contribution of one coordinate. -/
def signedCoordinate
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (i : ι) (x : NNReal) : ℝ :=
  match (LikelihoodRatio.stateFactor γ β hγ hβ S i).direction with
  | .positive =>
      (LikelihoodRatio.stateFactor γ β hγ hβ S i).scale * (x : ℝ)
  | .negative =>
      -((LikelihoodRatio.stateFactor γ β hγ hβ S i).scale * (x : ℝ))

omit [Fintype ι] in
theorem measurable_signedCoordinate
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (i : ι) :
    Measurable (signedCoordinate γ β hγ hβ S i) := by
  unfold signedCoordinate
  split <;> fun_prop

omit [Fintype ι] in
theorem map_signedCoordinate_nnexpMeasure
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (i : ι) :
    Measure.map (signedCoordinate γ β hγ hβ S i) nnexpMeasure =
      (LikelihoodRatio.stateFactor γ β hγ hβ S i).sourceLaw := by
  rw [LikelihoodRatio.SignedExpFactor.sourceLaw, ← map_nnexpMeasure_coe]
  rw [Measure.map_map]
  · rfl
  · cases h :
      (LikelihoodRatio.stateFactor γ β hγ hβ S i).direction <;> fun_prop
  · exact NNReal.continuous_coe.measurable

/-- The distinguished exponential and all transformed coordinates are
jointly independent on the canonical product space. -/
theorem iIndepFun_signedCoordinates
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) :
    iIndepFun
      (fun o (e : Option ι → NNReal) ↦
        match o with
        | none => (e none : ℝ)
        | some i => signedCoordinate γ β hγ hβ S i (e (some i)))
      (expProductMeasure ι) := by
  unfold expProductMeasure
  have h := iIndepFun_pi
    (μ := fun _ : Option ι ↦ nnexpMeasure)
    (X := fun o (x : NNReal) ↦
    match o with
    | none => (x : ℝ)
    | some i => signedCoordinate γ β hγ hβ S i x)
    (fun o ↦ by
      cases o with
      | none => exact NNReal.continuous_coe.measurable.aemeasurable
      | some i =>
          exact (measurable_signedCoordinate γ β hγ hβ S i).aemeasurable)
  convert h using 1
  funext o e
  cases o <;> rfl

/-- The distinguished exponential or a signed coordinate on the product space. -/
def transformedCoordinate
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (o : Option ι) (e : Option ι → NNReal) : ℝ :=
  match o with
  | none => (e none : ℝ)
  | some i => signedCoordinate γ β hγ hβ S i (e (some i))

omit [Fintype ι] in
theorem measurable_transformedCoordinate
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (o : Option ι) :
    Measurable (transformedCoordinate γ β hγ hβ S o) := by
  cases o with
  | none => exact (measurable_pi_apply none).coe_nnreal_real
  | some i =>
      exact (measurable_signedCoordinate γ β hγ hβ S i).comp
        (measurable_pi_apply (some i))

theorem map_transformedCoordinate_some
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (i : ι) :
    Measure.map (transformedCoordinate γ β hγ hβ S (some i))
        (expProductMeasure ι) =
      (LikelihoodRatio.stateFactor γ β hγ hβ S i).sourceLaw := by
  have heval :
      Measure.map (fun e : Option ι → NNReal ↦ e (some i))
          (expProductMeasure ι) = nnexpMeasure := by
    unfold expProductMeasure
    exact (measurePreserving_eval
      (fun _ : Option ι ↦ nnexpMeasure) (some i)).map_eq
  calc
    Measure.map (transformedCoordinate γ β hγ hβ S (some i))
        (expProductMeasure ι) =
      Measure.map (signedCoordinate γ β hγ hβ S i)
        (Measure.map (fun e : Option ι → NNReal ↦ e (some i))
          (expProductMeasure ι)) := by
            rw [Measure.map_map]
            · rfl
            · exact measurable_signedCoordinate γ β hγ hβ S i
            · exact measurable_pi_apply (some i)
    _ = Measure.map (signedCoordinate γ β hγ hβ S i) nnexpMeasure := by
      rw [heval]
    _ = _ := map_signedCoordinate_nnexpMeasure γ β hγ hβ S i

/-- The distinguished index together with the coordinate indices in `T`. -/
def commonIndexSet (T : Finset ι) : Finset (Option ι) :=
  insert none (T.image some)

omit [Fintype ι] in
theorem sum_commonIndexSet
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S T : Finset ι) (e : Option ι → NNReal) :
    (∑ o ∈ commonIndexSet T,
        transformedCoordinate γ β hγ hβ S o e) =
      (e none : ℝ) +
        ∑ i ∈ T, signedCoordinate γ β hγ hβ S i (e (some i)) := by
  unfold commonIndexSet
  rw [Finset.sum_insert (by simp)]
  simp only [transformedCoordinate]
  rw [Finset.sum_image (by
    intro i hi j hj hij
    exact Option.some.inj hij)]

theorem finiteSignedExpSumSourceMeasure_perm
    {Fs Gs : List LikelihoodRatio.SignedExpFactor}
    (h : Fs.Perm Gs) :
    LikelihoodRatio.finiteSignedExpSumSourceMeasure Fs =
      LikelihoodRatio.finiteSignedExpSumSourceMeasure Gs := by
  induction h with
  | nil => rfl
  | cons F h ih =>
      simp only [LikelihoodRatio.finiteSignedExpSumSourceMeasure]
      rw [ih]
  | swap F G Fs =>
      let : SFinite F.sourceLaw := by
        rw [F.sourceLaw_eq_withDensity]
        infer_instance
      let : SFinite G.sourceLaw := by
        rw [G.sourceLaw_eq_withDensity]
        infer_instance
      let : SFinite
          (LikelihoodRatio.finiteSignedExpSumSourceMeasure Fs) := by
        rw [LikelihoodRatio.finiteSignedExpSumSourceMeasure_eq]
        infer_instance
      simp only [LikelihoodRatio.finiteSignedExpSumSourceMeasure]
      calc
        G.sourceLaw ∗
            (F.sourceLaw ∗
              LikelihoodRatio.finiteSignedExpSumSourceMeasure Fs) =
          (G.sourceLaw ∗ F.sourceLaw) ∗
            LikelihoodRatio.finiteSignedExpSumSourceMeasure Fs := by
              rw [Measure.conv_assoc]
        _ = (F.sourceLaw ∗ G.sourceLaw) ∗
            LikelihoodRatio.finiteSignedExpSumSourceMeasure Fs := by
              rw [Measure.conv_comm G.sourceLaw F.sourceLaw]
        _ = F.sourceLaw ∗
            (G.sourceLaw ∗
              LikelihoodRatio.finiteSignedExpSumSourceMeasure Fs) := by
              rw [Measure.conv_assoc]
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem map_common_coordinate_sum
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S T : Finset ι) :
    Measure.map
        (fun e ↦ ∑ o ∈ commonIndexSet T,
          transformedCoordinate γ β hγ hβ S o e)
        (expProductMeasure ι) =
      LikelihoodRatio.finiteSignedExpSumSourceMeasure
        (T.toList.map (LikelihoodRatio.stateFactor γ β hγ hβ S)) := by
  induction T using Finset.induction_on with
  | empty =>
      simp only [commonIndexSet, Finset.image_empty, Finset.insert_empty,
        Finset.sum_singleton, transformedCoordinate, Finset.toList_empty,
        List.map_nil,
        LikelihoodRatio.finiteSignedExpSumSourceMeasure]
      have heval :
          Measure.map (fun e : Option ι → NNReal ↦ e none)
              (expProductMeasure ι) = nnexpMeasure := by
        unfold expProductMeasure
        exact (measurePreserving_eval
          (fun _ : Option ι ↦ nnexpMeasure) none).map_eq
      calc
        Measure.map (fun e : Option ι → NNReal ↦ (e none : ℝ))
            (expProductMeasure ι) =
            Measure.map (fun x : NNReal ↦ (x : ℝ))
              (Measure.map (fun e : Option ι → NNReal ↦ e none)
                (expProductMeasure ι)) := by
                  rw [Measure.map_map]
                  · rfl
                  · exact NNReal.continuous_coe.measurable
                  · exact (measurable_pi_apply none)
        _ = Measure.map (fun x : NNReal ↦ (x : ℝ)) nnexpMeasure := by
          rw [heval]
        _ = expMeasure 1 := map_nnexpMeasure_coe
        _ = Measure.map (fun x : ℝ ↦ x) (expMeasure 1) :=
          (Measure.map_id).symm
  | @insert i T hi ih =>
      have hind := iIndepFun_signedCoordinates γ β hγ hβ S
      have hnot : some i ∉ commonIndexSet T := by
        simp [commonIndexSet, hi]
      have hmeas : ∀ o : Option ι,
          Measurable (transformedCoordinate γ β hγ hβ S o) :=
        measurable_transformedCoordinate γ β hγ hβ S
      have hsep :=
        (hind.indepFun_finsetSum_of_notMem hmeas hnot).symm
      have hfi : Measurable (fun e : Option ι → NNReal ↦
          signedCoordinate γ β hγ hβ S i (e (some i))) :=
        (measurable_signedCoordinate γ β hγ hβ S i).comp
          (measurable_pi_apply (some i))
      have hsum : Measurable
          (∑ o ∈ commonIndexSet T, fun e : Option ι → NNReal ↦
            match o with
            | none => (e none : ℝ)
            | some j => signedCoordinate γ β hγ hβ S j (e (some j))) := by
        have hsum0 := Finset.measurable_fun_sum (commonIndexSet T)
          (fun o _ ↦ hmeas o)
        simp only [transformedCoordinate] at hsum0
        convert hsum0 using 1
        funext e
        simp only [Finset.sum_apply]
      have hadd := hsep.map_add_eq_map_conv_map
        hfi hsum
      have hsumfun :
          (∑ o ∈ commonIndexSet T, fun e : Option ι → NNReal ↦
            match o with
            | none => (e none : ℝ)
            | some j => signedCoordinate γ β hγ hβ S j (e (some j))) =
          (fun e ↦ ∑ o ∈ commonIndexSet T,
            match o with
            | none => (e none : ℝ)
            | some j => signedCoordinate γ β hγ hβ S j (e (some j))) := by
        funext e
        simp only [Finset.sum_apply]
      rw [hsumfun] at hadd
      have haddfun :
          (fun e : Option ι → NNReal ↦
              signedCoordinate γ β hγ hβ S i (e (some i))) +
              (fun e ↦ ∑ o ∈ commonIndexSet T,
                match o with
                | none => (e none : ℝ)
                | some j =>
                    signedCoordinate γ β hγ hβ S j (e (some j))) =
            (fun e ↦ signedCoordinate γ β hγ hβ S i (e (some i)) +
              ∑ o ∈ commonIndexSet T,
                match o with
                | none => (e none : ℝ)
                | some j =>
                    signedCoordinate γ β hγ hβ S j (e (some j))) := by
        funext e
        rfl
      rw [haddfun] at hadd
      have hadd2 :
          Measure.map
              (fun e ↦ transformedCoordinate γ β hγ hβ S (some i) e +
                ∑ o ∈ commonIndexSet T,
                  transformedCoordinate γ β hγ hβ S o e)
              (expProductMeasure ι) =
            Measure.map
                (transformedCoordinate γ β hγ hβ S (some i))
                (expProductMeasure ι) ∗
              Measure.map
                (fun e ↦ ∑ o ∈ commonIndexSet T,
                  transformedCoordinate γ β hγ hβ S o e)
                (expProductMeasure ι) := by
        change
          Measure.map
              (fun e ↦ signedCoordinate γ β hγ hβ S i (e (some i)) +
                ∑ o ∈ commonIndexSet T,
                  (match o with
                  | none => (e none : ℝ)
                  | some j =>
                      signedCoordinate γ β hγ hβ S j (e (some j))))
              (expProductMeasure ι) =
            Measure.map
                (fun e ↦ signedCoordinate γ β hγ hβ S i (e (some i)))
                (expProductMeasure ι) ∗
              Measure.map
                (fun e ↦ ∑ o ∈ commonIndexSet T,
                  (match o with
                  | none => (e none : ℝ)
                  | some j =>
                      signedCoordinate γ β hγ hβ S j (e (some j))))
                (expProductMeasure ι)
        exact hadd
      have hset :
          commonIndexSet (insert i T) =
            insert (some i) (commonIndexSet T) := by
        ext o
        cases o <;> simp [commonIndexSet]
      rw [hset]
      simp only [Finset.sum_insert hnot]
      rw [hadd2, map_transformedCoordinate_some γ β hγ hβ S i, ih]
      rw [show
        LikelihoodRatio.finiteSignedExpSumSourceMeasure
            (List.map (LikelihoodRatio.stateFactor γ β hγ hβ S)
              (insert i T).toList) =
          LikelihoodRatio.finiteSignedExpSumSourceMeasure
            (LikelihoodRatio.stateFactor γ β hγ hβ S i ::
              List.map (LikelihoodRatio.stateFactor γ β hγ hβ S)
                T.toList) by
          apply finiteSignedExpSumSourceMeasure_perm
          have hp : (insert i T).toList.Perm (i :: T.toList) :=
            Finset.toList_insert hi
          simpa only [List.map_cons] using
            hp.map (LikelihoodRatio.stateFactor γ β hγ hβ S)]
      rfl

theorem stateCommonLaw_eq_insertionCommonLaw
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (changed : ι) :
    Measure.map (stateCommonSignedSum γ β S changed)
        (expProductMeasure ι) =
      insertionCommonLaw γ β hγ hβ S changed := by
  rw [show Measure.map (stateCommonSignedSum γ β S changed)
        (expProductMeasure ι) =
      Measure.map
        (fun e ↦ ∑ o ∈ commonIndexSet (Finset.univ.erase changed),
          transformedCoordinate γ β hγ hβ S o e)
        (expProductMeasure ι) by
      congr 1
      funext e
      rw [sum_commonIndexSet]
      unfold stateCommonSignedSum
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      unfold signedCoordinate LikelihoodRatio.stateFactor
      by_cases hiS : i ∈ S <;> simp [hiS]]
  rw [map_common_coordinate_sum]
  unfold insertionCommonLaw LikelihoodRatio.commonFactors
  exact LikelihoodRatio.finiteSignedExpSumSourceMeasure_eq _

theorem zPlusLaw_eq_conv_map_mul
    (ν : Measure ℝ) [SFinite ν] (t : ℝ) :
    TransferStein.zPlusLaw ν t =
      ν ∗ Measure.map (fun x : ℝ ↦ t * x) (expMeasure 1) := by
  unfold TransferStein.zPlusLaw Measure.conv
  calc
    Measure.map (fun p : ℝ × ℝ ↦ p.1 + t * p.2)
        (ν.prod (expMeasure 1)) =
      Measure.map (fun p : ℝ × ℝ ↦ p.1 + p.2)
        (Measure.map (Prod.map id (fun x : ℝ ↦ t * x))
          (ν.prod (expMeasure 1))) := by
            rw [Measure.map_map]
            · rfl
            · fun_prop
            · fun_prop
    _ = Measure.map (fun p : ℝ × ℝ ↦ p.1 + p.2)
        ((Measure.map id ν).prod
          (Measure.map (fun x : ℝ ↦ t * x) (expMeasure 1))) := by
            rw [Measure.map_prod_map ν (expMeasure 1)
              measurable_id (by fun_prop)]
    _ = _ := by rw [Measure.map_id]

theorem zMinusLaw_eq_conv_map_neg_mul
    (ν : Measure ℝ) [SFinite ν] (t : ℝ) :
    TransferStein.zMinusLaw ν t =
      ν ∗ Measure.map (fun x : ℝ ↦ -(t * x)) (expMeasure 1) := by
  unfold TransferStein.zMinusLaw Measure.conv
  calc
    Measure.map (fun p : ℝ × ℝ ↦ p.1 - t * p.2)
        (ν.prod (expMeasure 1)) =
      Measure.map (fun p : ℝ × ℝ ↦ p.1 + p.2)
        (Measure.map (Prod.map id (fun x : ℝ ↦ -(t * x)))
          (ν.prod (expMeasure 1))) := by
            rw [Measure.map_map]
            · rfl
            · fun_prop
            · fun_prop
    _ = Measure.map (fun p : ℝ × ℝ ↦ p.1 + p.2)
        ((Measure.map id ν).prod
          (Measure.map (fun x : ℝ ↦ -(t * x)) (expMeasure 1))) := by
            rw [Measure.map_prod_map ν (expMeasure 1)
              measurable_id (by fun_prop)]
    _ = _ := by rw [Measure.map_id]

theorem stateLaw_eq_finiteSignedExpSumMeasure
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) :
    stateLaw γ β S =
      LikelihoodRatio.finiteSignedExpSumMeasure
        (Finset.univ.toList.map
          (LikelihoodRatio.stateFactor γ β hγ hβ S)) := by
  rw [stateLaw]
  rw [show Measure.map (stateSignedSum γ β S) (expProductMeasure ι) =
      Measure.map
        (fun e ↦ ∑ o ∈ commonIndexSet Finset.univ,
          transformedCoordinate γ β hγ hβ S o e)
        (expProductMeasure ι) by
      congr 1
      funext e
      rw [sum_commonIndexSet]
      unfold stateSignedSum
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      unfold signedCoordinate LikelihoodRatio.stateFactor
      by_cases hiS : i ∈ S <;> simp [hiS]]
  rw [map_common_coordinate_sum,
    LikelihoodRatio.finiteSignedExpSumSourceMeasure_eq]

theorem insertionLowEndpointLaw_eq_stateLaw
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (changed : ι) (hj : changed ∉ S) :
    insertionLowEndpointLaw γ β hγ hβ S changed =
      stateLaw γ β S := by
  rw [insertionLowEndpointLaw, zPlusLaw_eq_conv_map_mul,
    ]
  rw [show Measure.map (fun x : ℝ ↦ γ changed * x) (expMeasure 1) =
      (LikelihoodRatio.stateFactor γ β hγ hβ S changed).sourceLaw by
        rw [LikelihoodRatio.SignedExpFactor.sourceLaw]
        unfold LikelihoodRatio.stateFactor
        simp [hj]]
  let : SFinite
      (LikelihoodRatio.stateFactor γ β hγ hβ S changed).sourceLaw := by
    rw [LikelihoodRatio.SignedExpFactor.sourceLaw_eq_withDensity]
    infer_instance
  rw [Measure.conv_comm]
  rw [stateLaw_eq_finiteSignedExpSumMeasure γ β hγ hβ S]
  rw [← LikelihoodRatio.finiteSignedExpSumSourceMeasure_eq]
  unfold insertionCommonLaw LikelihoodRatio.commonFactors
  rw [← LikelihoodRatio.finiteSignedExpSumSourceMeasure_eq]
  change LikelihoodRatio.finiteSignedExpSumSourceMeasure
      (LikelihoodRatio.stateFactor γ β hγ hβ S changed ::
        (Finset.univ.erase changed).toList.map
          (LikelihoodRatio.stateFactor γ β hγ hβ S)) =
    LikelihoodRatio.finiteSignedExpSumSourceMeasure
      (Finset.univ.toList.map
        (LikelihoodRatio.stateFactor γ β hγ hβ S))
  apply finiteSignedExpSumSourceMeasure_perm
  have hp :
      Finset.univ.toList.Perm
        (changed :: (Finset.univ.erase changed).toList) := by
    have hjmem : changed ∈ (Finset.univ : Finset ι) := Finset.mem_univ _
    have herase : changed ∉ Finset.univ.erase changed := by simp
    have hins :
        insert changed (Finset.univ.erase changed) = (Finset.univ : Finset ι) :=
      Finset.insert_erase hjmem
    have hp0 := Finset.toList_insert herase
    rw [hins] at hp0
    exact hp0
  exact (hp.map (LikelihoodRatio.stateFactor γ β hγ hβ S)).symm

theorem insertionHighEndpointLaw_eq_stateLaw_insert
    (γ β : ι → ℝ) (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset ι) (changed : ι) (_hj : changed ∉ S) :
    insertionHighEndpointLaw γ β hγ hβ S changed =
      stateLaw γ β (insert changed S) := by
  rw [insertionHighEndpointLaw, zMinusLaw_eq_conv_map_neg_mul]
  rw [show Measure.map (fun x : ℝ ↦ -(β changed * x)) (expMeasure 1) =
      (LikelihoodRatio.stateFactor γ β hγ hβ
        (insert changed S) changed).sourceLaw by
        rw [LikelihoodRatio.SignedExpFactor.sourceLaw]
        unfold LikelihoodRatio.stateFactor
        simp]
  let : SFinite
      (LikelihoodRatio.stateFactor γ β hγ hβ
        (insert changed S) changed).sourceLaw := by
    rw [LikelihoodRatio.SignedExpFactor.sourceLaw_eq_withDensity]
    infer_instance
  rw [Measure.conv_comm]
  rw [stateLaw_eq_finiteSignedExpSumMeasure γ β hγ hβ
    (insert changed S)]
  rw [← LikelihoodRatio.finiteSignedExpSumSourceMeasure_eq]
  unfold insertionCommonLaw LikelihoodRatio.commonFactors
  rw [← LikelihoodRatio.finiteSignedExpSumSourceMeasure_eq]
  change LikelihoodRatio.finiteSignedExpSumSourceMeasure
      (LikelihoodRatio.stateFactor γ β hγ hβ
          (insert changed S) changed ::
        (Finset.univ.erase changed).toList.map
          (LikelihoodRatio.stateFactor γ β hγ hβ S)) =
    LikelihoodRatio.finiteSignedExpSumSourceMeasure
      (Finset.univ.toList.map
        (LikelihoodRatio.stateFactor γ β hγ hβ (insert changed S)))
  apply finiteSignedExpSumSourceMeasure_perm
  have hmap :
      (Finset.univ.erase changed).toList.map
          (LikelihoodRatio.stateFactor γ β hγ hβ S) =
        (Finset.univ.erase changed).toList.map
          (LikelihoodRatio.stateFactor γ β hγ hβ
            (insert changed S)) := by
    apply List.map_congr_left
    intro i hi
    have hiErase : i ∈ (Finset.univ.erase changed : Finset ι) := by
      simpa using hi
    have hine : i ≠ changed := (Finset.mem_erase.mp hiErase).1
    unfold LikelihoodRatio.stateFactor
    simp [hine]
  rw [hmap]
  have hp :
      Finset.univ.toList.Perm
        (changed :: (Finset.univ.erase changed).toList) := by
    have hjmem : changed ∈ (Finset.univ : Finset ι) := Finset.mem_univ _
    have herase : changed ∉ Finset.univ.erase changed := by simp
    have hins :
        insert changed (Finset.univ.erase changed) = (Finset.univ : Finset ι) :=
      Finset.insert_erase hjmem
    have hp0 := Finset.toList_insert herase
    rw [hins] at hp0
    exact hp0
  exact
    (hp.map
      (LikelihoodRatio.stateFactor γ β hγ hβ (insert changed S))).symm

end

end Feige
