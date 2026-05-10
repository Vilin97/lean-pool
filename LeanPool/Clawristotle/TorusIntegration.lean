/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.TorusDefs

/-!
# Torus Integration Lemmas

Box integral machinery, integration by parts on T³, curl integral vanishing,
and the energy method proof that harmonic functions on T³ are constant.
-/

open MeasureTheory Matrix Finset BigOperators Real Filter

noncomputable section

-- ============================================================================
-- Box integral machinery (proved by Aristotle)
-- ============================================================================

section AristotleLemmas
open intervalIntegral

/-- The half-open unit box `(0, 1]³ ⊆ ℝ³`, a fundamental domain for `T³ = (ℝ/ℤ)³`. -/
def box3 : Set (Fin 3 → ℝ) := Set.pi Set.univ (fun _ => Set.Ioc 0 1)

/-- The volume measure on T³ is the pushforward of the box measure. -/
lemma measure_torus_eq_map :
    (volume : Measure Torus3) =
    (volume.restrict box3).map torusMk := by
      have h_volume_eq : MeasureTheory.MeasureSpace.volume =
          MeasureTheory.Measure.map torusMk
            (MeasureTheory.Measure.pi
              (fun _ => MeasureTheory.MeasureSpace.volume.restrict (Set.Ioc 0 1))) := by
        have h_volume_eq : ∀ i : Fin 3,
            (MeasureTheory.MeasureSpace.volume.restrict (Set.Ioc 0 1)).map
              (fun x => QuotientAddGroup.mk x : ℝ → AddCircle (1 : ℝ)) =
            MeasureTheory.MeasureSpace.volume := by
          intro i
          symm
          convert (AddCircle.measurePreserving_mk 1 (0 : ℝ) |>
              MeasureTheory.MeasurePreserving.map_eq) using 1
          · ext s hs
            rw [ MeasureTheory.Measure.map_apply ]
            · rw [ MeasureTheory.Measure.restrict_apply' ]
              · exact AddCircle.add_projection_respects_measure 1 0 hs
              · norm_num
            · exact fun ⦃t⦄ a ↦ a
            · exact hs
          · convert (AddCircle.measurePreserving_mk 1 (0 : ℝ) |>
                MeasureTheory.MeasurePreserving.map_eq) using 1
            norm_num +zetaDelta at *
        convert MeasureTheory.Measure.pi_map_pi _ using 1
        any_goals tauto
        case convert_6 => exact fun _ => MeasureTheory.MeasureSpace.volume
        all_goals try infer_instance
        · exact Eq.symm Measure.map_id'
        · convert MeasureTheory.Measure.pi_map_pi (fun i => _) using 1
          · congr 1; funext i; simp only [Measure.map_id']; exact (h_volume_eq i).symm
          · exact fun i ↦ sigmaFinite_of_locallyFinite
          · exact Continuous.aemeasurable (by continuity)
        · exact fun i => measurable_id.aemeasurable
      suffices h_restrict : volume.restrict box3 =
          MeasureTheory.Measure.pi (fun _ => volume.restrict (Set.Ioc 0 1)) by
        rw [h_volume_eq, h_restrict]
      erw [ MeasureTheory.Measure.pi_eq ]
      intro s hs; erw [ MeasureTheory.Measure.restrict_apply ]
      · erw [ show (Set.univ.pi s ∩ box3 : Set (Fin 3 → ℝ) ) =
            Set.pi Set.univ fun i => s i ∩ Set.Ioc 0 1 from ?_,
          MeasureTheory.Measure.pi_pi ]
        · simp
        · unfold box3; exact Set.pi_inter_distrib.symm
      · exact MeasurableSet.univ_pi hs

/-- ∫ over T³ = ∫ over [0,1]³ of the periodic lift. -/
lemma integral_torus_eq_integral_box (g : Torus3 → ℝ) (hg : Continuous g) :
    ∫ x : Torus3, g x = ∫ y in box3, g (torusMk y) := by
      rw [ ← MeasureTheory.integral_map ]
      · convert MeasureTheory.integral_map _ _ using 3
        · rw [ ← MeasureTheory.integral_map ]
          · rw [ ← measure_torus_eq_map ]
          · refine Continuous.aemeasurable ?_
            exact continuous_pi_iff.mpr fun i =>
              QuotientAddGroup.continuous_mk.comp (continuous_apply i)
          · exact hg.aestronglyMeasurable
        · exact measurable_id.aemeasurable
        · exact hg.aestronglyMeasurable
      · exact measurable_id.aemeasurable
      · exact hg.aestronglyMeasurable

/-- Fubini decomposition of the unit-box integral along the `i`-th coordinate. -/
private lemma box3_fubini_slice (i : Fin 3) (g : (Fin 3 → ℝ) → ℝ) (hg : Continuous g) :
    (∫ y in (Set.pi Set.univ (fun _ => Set.Ioc 0 1)), g y) =
    (∫ y : ℝ in Set.Ioc 0 1,
      ∫ z : Fin 2 → ℝ in (Set.pi Set.univ (fun _ => Set.Ioc 0 1)),
        g (Fin.insertNth i y z)) := by
        have h_fubini :
            ∫ y : Fin 3 → ℝ in (Set.pi Set.univ (fun _ => Set.Ioc 0 1)), g y =
            ∫ y : ℝ × (Fin 2 → ℝ) in
              (Set.Ioc 0 1) ×ˢ (Set.pi Set.univ (fun _ => Set.Ioc 0 1)),
              g (Fin.insertNth i y.1 y.2) := by
          rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ]
          · have h_iso :
                (MeasureTheory.volume : MeasureTheory.Measure (Fin 3 → ℝ)) =
                MeasureTheory.Measure.map
                  (fun x : ℝ × (Fin 2 → ℝ) => Fin.insertNth i x.1 x.2)
                  (MeasureTheory.volume.prod
                    (MeasureTheory.volume : MeasureTheory.Measure (Fin 2 → ℝ))) := by
              simp only [volume, Nat.reduceAdd]
              erw [ MeasureTheory.Measure.pi_eq ]
              intro s hs; erw [ MeasureTheory.Measure.map_apply ]
              · rw [ show (fun x : ℝ × (Fin 2 → ℝ) => i.insertNth x.1 x.2) ⁻¹' Set.univ.pi s =
                    (s i) ×ˢ (Set.pi Set.univ fun j => s (Fin.succAbove i j)) from ?_ ]
                · simp only [Measure.prod_prod, Measure.pi_pi, Fin.prod_univ_two, Fin.isValue,
                    Fin.prod_univ_three]
                  fin_cases i <;> ring!
                · ext ⟨x, y⟩
                  simp only [Nat.reduceAdd, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
                    Fin.insertNth, Fin.succAbove_cases_eq_insertNth, forall_const, Set.mem_prod,
                    Fin.forall_fin_two, Fin.isValue]
                  fin_cases i <;> simp [ Fin.forall_fin_succ ]
                  · tauto
                  · tauto
              · refine measurable_pi_iff.mpr ?_
                intro a
                fin_cases a <;>
                  simp only [Fin.insertNth, Fin.succAbove_cases_eq_insertNth, Nat.reduceAdd,
                    Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
                · fin_cases i <;>
                    simp only [Fin.succAboveCases, Nat.reduceAdd, Fin.isValue, Fin.zero_eta,
                      ↓reduceDIte, Fin.mk_one, zero_ne_one, Fin.lt_one_iff, Fin.castPred_zero,
                      Fin.reduceFinMk, Fin.reduceEq, Fin.reduceLT]
                  · exact measurable_fst
                  · exact measurable_pi_apply 0 |> Measurable.comp <| measurable_snd
                  · exact measurable_pi_apply 0 |> Measurable.comp <| measurable_snd
                · fin_cases i <;> simp [ Fin.succAboveCases ] <;> measurability
                · fin_cases i <;>
                    simp only [Fin.succAboveCases, Nat.reduceAdd, Fin.isValue, Fin.zero_eta,
                      Fin.reduceEq, ↓reduceDIte, Fin.not_lt_zero, Fin.reducePred, Fin.mk_one,
                      Fin.lt_one_iff, Fin.reduceFinMk]
                  · exact measurable_pi_apply _ |> Measurable.comp <| measurable_snd
                  · exact measurable_pi_apply _ |> Measurable.comp <| measurable_snd
                  · exact measurable_fst
              · exact MeasurableSet.univ_pi hs
            rw [ h_iso, MeasureTheory.integral_map ]
            · simp only [Set.indicator, Nat.reduceAdd, Set.mem_pi, Set.mem_univ, Set.mem_Ioc,
                forall_const, Set.mem_prod, Fin.forall_fin_two, Fin.isValue]
              fin_cases i <;>
                simp only [Fin.zero_eta, Fin.isValue, Fin.insertNth_zero', Nat.reduceAdd,
                  Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.succ_zero_eq_one,
                  IsEmpty.forall_iff, and_true, Fin.mk_one, Fin.insertNth_apply_same,
                  Fin.succ_one_eq_two, Fin.reduceFinMk]
              · rfl
              · simp only [and_left_comm]
                rfl
              · simp only [Fin.insertNth, Fin.succAbove_cases_eq_insertNth, Nat.reduceAdd,
                  Fin.isValue]
                simp only [Fin.succAboveCases, Nat.reduceAdd, Fin.isValue, Fin.reduceEq,
                  ↓reduceDIte, Fin.reduceLT, Fin.castPred_zero, Fin.castPred_one]
                congr
                ext
                split_ifs <;> tauto
            · refine Measurable.aemeasurable ?_
              refine measurable_pi_iff.mpr ?_
              intro a
              fin_cases a <;>
                simp only [Fin.insertNth, Fin.succAbove_cases_eq_insertNth, Nat.reduceAdd,
                  Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
              · fin_cases i <;>
                  simp only [Fin.succAboveCases, Nat.reduceAdd, Fin.isValue, Fin.zero_eta,
                    ↓reduceDIte, Fin.mk_one, zero_ne_one, Fin.lt_one_iff, Fin.castPred_zero,
                    Fin.reduceFinMk, Fin.reduceEq, Fin.reduceLT]
                · exact measurable_fst
                · exact measurable_pi_apply 0 |> Measurable.comp <| measurable_snd
                · exact measurable_pi_apply 0 |> Measurable.comp <| measurable_snd
              · fin_cases i <;>
                  simp only [Fin.succAboveCases, Nat.reduceAdd, Fin.isValue, Fin.zero_eta,
                    one_ne_zero, ↓reduceDIte, Fin.not_lt_zero, Fin.pred_one, Fin.mk_one,
                    Fin.reduceFinMk, Fin.reduceEq, Fin.reduceLT, Fin.castPred_one]
                · exact measurable_pi_apply 0 |> Measurable.comp <| measurable_snd
                · exact measurable_fst
                · exact measurable_pi_apply _ |> Measurable.comp <| measurable_snd
              · fin_cases i <;>
                  simp only [Fin.succAboveCases, Nat.reduceAdd, Fin.isValue, Fin.zero_eta,
                    Fin.reduceEq, ↓reduceDIte, Fin.not_lt_zero, Fin.reducePred, Fin.mk_one,
                    Fin.lt_one_iff, Fin.reduceFinMk]
                · exact measurable_pi_apply _ |> Measurable.comp <| measurable_snd
                · exact measurable_pi_apply _ |> Measurable.comp <| measurable_snd
                · exact measurable_fst
            · refine Measurable.aestronglyMeasurable ?_
              exact Measurable.indicator (hg.measurable)
                (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)
          · exact measurableSet_Ioc.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)
          · exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc
        erw [ h_fubini, MeasureTheory.setIntegral_prod ]
        have h_integrable : ContinuousOn
            (fun y : ℝ × (Fin 2 → ℝ) => g (Fin.insertNth i y.1 y.2))
            (Set.Icc 0 1 ×ˢ Set.pi Set.univ (fun _ => Set.Icc 0 1)) := by
          refine hg.comp_continuousOn ?_
          refine Continuous.continuousOn ?_
          fin_cases i <;>
            simp only [Fin.zero_eta, Fin.isValue, Fin.insertNth_zero', Nat.reduceAdd, Fin.mk_one,
              Fin.reduceFinMk]
          · exact continuous_pi_iff.mpr fun i => by
              fin_cases i <;>
              [exact continuous_fst;
               exact continuous_apply 0 |> Continuous.comp <| continuous_snd;
               exact continuous_apply 1 |> Continuous.comp <| continuous_snd]
          · refine continuous_pi_iff.mpr ?_
            intro i
            fin_cases i <;>
              simp only [Fin.insertNth, Fin.succAbove_cases_eq_insertNth, Nat.reduceAdd,
                Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.insertNth_apply_same, Fin.reduceFinMk]
            · exact continuous_apply 0 |> Continuous.comp <| continuous_snd
            · exact continuous_fst
            · exact continuous_apply 1 |> Continuous.comp <| continuous_snd
          · exact continuous_pi_iff.mpr fun i => by
              fin_cases i <;>
              [exact continuous_pi_iff.mp continuous_snd 0;
               exact continuous_pi_iff.mp continuous_snd 1;
               exact continuous_fst]
        exact (h_integrable.integrableOn_compact
            (isCompact_Icc.prod (isCompact_univ_pi fun _ => CompactIccSpace.isCompact_Icc)))
          |> fun h => h.mono_set
            (Set.prod_mono (Set.Ioc_subset_Icc_self)
              (Set.pi_mono fun _ _ => Set.Ioc_subset_Icc_self))


/-- For periodic `F`, the slice integral `∫₀¹ ∂F/∂xᵢ along the `i`-th line vanishes. -/
private lemma box3_ftc_slice_zero (F : (Fin 3 → ℝ) → ℝ) (i : Fin 3) (hF : ContDiff ℝ 1 F)
    (hper : ∀ x, F (x + Pi.single i 1) = F x) (z : Fin 2 → ℝ) :
    ∫ y in Set.Ioc 0 1, (fderiv ℝ F (Fin.insertNth i y z)) (Pi.single i 1) = 0 := by
        have h_ftc : ∫ y in (0 : ℝ)..1, (fderiv ℝ F (Fin.insertNth i y z)) (Pi.single i 1) =
            F (Fin.insertNth i 1 z) - F (Fin.insertNth i 0 z) := by
          rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ]
          rotate_right
          · exact fun x => F (Fin.insertNth i x z)
          · rfl
          · intro x hx
            convert HasFDerivAt.hasDerivAt
                (HasFDerivAt.comp x
                  (hF.contDiffAt.differentiableAt one_ne_zero |> DifferentiableAt.hasFDerivAt)
                  (hasFDerivAt_pi.mpr _)) using 1
            rotate_left
            · exact fun j => if j = i then 1 else 0
            · intro j
              split_ifs <;>
                simp_all only [zero_le_one, Set.uIcc_of_le, Set.mem_Icc,
                  Fin.insertNth_apply_same, hasFDerivAt_iff_isLittleO_nhds_zero,
                  add_sub_cancel_left, ContinuousLinearMap.one_apply, sub_self,
                  Asymptotics.isLittleO_const_left, true_or, ContinuousLinearMap.zero_apply,
                  sub_zero]
              simp_all only [Fin.insertNth, Fin.succAbove_cases_eq_insertNth, Nat.reduceAdd]
              fin_cases i <;> fin_cases j <;>
                simp_all only [Fin.zero_eta, Fin.isValue, not_true_eq_false, Fin.mk_one,
                  one_ne_zero, not_false_eq_true, Fin.succAboveCases, Nat.reduceAdd, ↓reduceDIte,
                  Fin.not_lt_zero, Fin.pred_one, sub_self, Asymptotics.isLittleO_const_left,
                  true_or, Fin.reduceFinMk, Fin.reduceEq, Fin.reducePred, zero_ne_one,
                  Fin.lt_one_iff, Fin.castPred_zero, Fin.reduceLT, Fin.castPred_one]
            · simp only [ContinuousLinearMap.comp_apply]
              congr 1
              ext j
              simp only [ContinuousLinearMap.pi_apply, Pi.single_apply]
              split <;> simp
          · apply_rules [ Continuous.intervalIntegrable ]
            have h_cont : Continuous (fun y => fderiv ℝ F (Fin.insertNth i y z)) := by
              exact hF.continuous_fderiv one_ne_zero |> Continuous.comp <|
                continuous_pi_iff.mpr fun j => by fin_cases i <;> fin_cases j <;> continuity
            exact h_cont.clm_apply continuous_const
        convert h_ftc using 1 <;> norm_num [ intervalIntegral.integral_of_le zero_le_one ]
        rw [ eq_comm, sub_eq_zero ]
        convert hper (Fin.insertNth i 0 z) using 2
        ext j
        fin_cases i <;> fin_cases j <;> simp [ Fin.insertNth ]
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl


/-- ∫ ∂F/∂xᵢ over [0,1]³ = 0 for periodic F (FTC + periodicity). -/
lemma integral_derivative_periodic_zero (F : (Fin 3 → ℝ) → ℝ) (i : Fin 3)
    (hF : ContDiff ℝ 1 F) (hper : ∀ x, F (x + Pi.single i 1) = F x) :
    ∫ y in box3, fderiv ℝ F y (Pi.single i 1) = 0 := by
      have h_ftc := box3_ftc_slice_zero F i hF hper
      convert box3_fubini_slice i _ _ using 1
      · rw [ MeasureTheory.integral_integral_swap ]
        · simp_rw [h_ftc]; simp
        · have h_cont : Continuous
              (fun p : ℝ × (Fin 2 → ℝ) => (fderiv ℝ F (i.insertNth p.1 p.2)) (Pi.single i 1)) := by
            have h_cont : Continuous
                (fun p : ℝ × (Fin 2 → ℝ) => fderiv ℝ F (i.insertNth p.1 p.2)) := by
              have h_cont : Continuous (fun p : Fin 3 → ℝ => fderiv ℝ F p) := by
                exact hF.continuous_fderiv one_ne_zero
              refine h_cont.comp ?_
              refine continuous_pi_iff.mpr ?_
              intro j
              fin_cases j <;>
                simp only [Fin.insertNth, Fin.succAbove_cases_eq_insertNth, Nat.reduceAdd,
                  Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
              · fin_cases i <;>
                  simp only [Fin.succAboveCases, Nat.reduceAdd, Fin.isValue, Fin.zero_eta,
                    ↓reduceDIte, Fin.mk_one, zero_ne_one, Fin.lt_one_iff, Fin.castPred_zero,
                    Fin.reduceFinMk, Fin.reduceEq, Fin.reduceLT]
                · exact continuous_fst
                · exact continuous_apply 0 |> Continuous.comp <| continuous_snd
                · exact continuous_apply 0 |> Continuous.comp <| continuous_snd
              · fin_cases i <;>
                  simp only [Fin.succAboveCases, Nat.reduceAdd, Fin.isValue, Fin.zero_eta,
                    one_ne_zero, ↓reduceDIte, Fin.not_lt_zero, Fin.pred_one, Fin.mk_one,
                    Fin.reduceFinMk, Fin.reduceEq, Fin.reduceLT, Fin.castPred_one]
                · exact continuous_apply 0 |> Continuous.comp <| continuous_snd
                · exact continuous_fst
                · exact continuous_apply _ |> Continuous.comp <| continuous_snd
              · fin_cases i <;>
                  simp only [Fin.succAboveCases, Nat.reduceAdd, Fin.isValue, Fin.zero_eta,
                    Fin.reduceEq, ↓reduceDIte, Fin.not_lt_zero, Fin.reducePred, Fin.mk_one,
                    Fin.lt_one_iff, Fin.reduceFinMk]
                · exact continuous_apply _ |> Continuous.comp <| continuous_snd
                · exact continuous_apply _ |> Continuous.comp <| continuous_snd
                · exact continuous_fst
            exact Continuous.eval_const h_cont (Pi.single i 1)
          rw [ MeasureTheory.Measure.prod_restrict ]
          exact ContinuousOn.integrableOn_compact
              (isCompact_Icc.prod (isCompact_univ_pi fun _ => CompactIccSpace.isCompact_Icc))
              (h_cont.continuousOn)
            |> fun h => h.mono_set
              (Set.prod_mono (Set.Ioc_subset_Icc_self)
                (Set.pi_mono fun _ _ => Set.Ioc_subset_Icc_self))
      · fun_prop (disch := norm_num)

end AristotleLemmas

-- ============================================================================
-- IBP and Stokes axioms
-- ============================================================================

/-- ∫ torusGradX f x i = 0 on T³ (FTC + periodicity on the box). Proved by Aristotle. -/
lemma torus_gradX_integral_zero (f : Torus3 → ℝ) (i : Fin 3)
    (hf : ContDiff ℝ 1 (periodicLift f)) :
    ∫ x : Torus3, torusGradX f x i = 0 := by
  convert integral_derivative_periodic_zero (periodicLift f) i hf _ using 1
  · convert integral_torus_eq_integral_box (fun x => torusGradX f x i)
      (continuous_torusGradX f i hf) using 1
    congr! 2; exact (periodicLift_torusGradX f i _).symm
  · exact fun y => periodicLift_periodic f y i

/-- Product rule: ∂(φψ)/∂xᵢ = φ · ∂ψ/∂xᵢ + ψ · ∂φ/∂xᵢ. Proved by Aristotle. -/
lemma torusGradX_mul (φ ψ : Torus3 → ℝ) (i : Fin 3)
    (hφ : Differentiable ℝ (periodicLift φ))
    (hψ : Differentiable ℝ (periodicLift ψ)) :
    ∀ x : Torus3, torusGradX (fun z => φ z * ψ z) x i =
      φ x * torusGradX ψ x i + ψ x * torusGradX φ x i := by
  intro x
  simp only [torusGradX]
  have hlift : periodicLift (fun z => φ z * ψ z) = periodicLift φ * periodicLift ψ := by
    ext y; simp [periodicLift, Pi.mul_apply]
  rw [hlift]
  let x₀ := (torusMk_surjective x).choose
  have hx₀ := (torusMk_surjective x).choose_spec
  rw [fderiv_mul hφ.differentiableAt hψ.differentiableAt]
  simp only [ContinuousLinearMap.add_apply, periodicLift, Function.comp_apply]
  rw [show torusMk x₀ = x from hx₀]
  simp [smul_eq_mul]

private lemma integrable_mul_torusGradX (φ ψ : Torus3 → ℝ) (i : Fin 3)
    (hφ : ContDiff ℝ 1 (periodicLift φ)) (hψ : ContDiff ℝ 1 (periodicLift ψ)) :
    Integrable (fun x => φ x * torusGradX ψ x i) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (isOpenQuotientMap_torusMk.isQuotientMap.continuous_iff.mpr hφ.continuous).mul
      (continuous_torusGradX ψ i hψ)
  · exact HasCompactSupport.of_compactSpace _

/-- IBP on T³: ∫ φ · ∂ψ/∂xᵢ = -∫ ψ · ∂φ/∂xᵢ. Proved by Aristotle. -/
theorem torus_hIBP_spatial (φ ψ : Torus3 → ℝ) (i : Fin 3)
    (hφ : ContDiff ℝ 1 (periodicLift φ)) (hψ : ContDiff ℝ 1 (periodicLift ψ)) :
    (∫ x, φ x * torusGradX ψ x i) = -(∫ x, ψ x * torusGradX φ x i) := by
  have hprod : ∫ x : Torus3, torusGradX (fun z => φ z * ψ z) x i =
    (∫ x : Torus3, φ x * torusGradX ψ x i) + ∫ x : Torus3, ψ x * torusGradX φ x i := by
    simp_rw [torusGradX_mul φ ψ i (hφ.differentiable one_ne_zero) (hψ.differentiable one_ne_zero)]
    exact integral_add (integrable_mul_torusGradX φ ψ i hφ hψ)
      (integrable_mul_torusGradX ψ φ i hψ hφ)
  have hzero : ∫ x : Torus3, torusGradX (fun z => φ z * ψ z) x i = 0 := by
    apply torus_gradX_integral_zero
    have : periodicLift (fun z => φ z * ψ z) = fun y => periodicLift φ y * periodicLift ψ y := by
      ext y; simp [periodicLift]
    rw [this]; exact hφ.mul hψ
  linarith [hprod ▸ hzero]

/-- ∫ u · (∇×F) = 0 on T³. Each gradient integral vanishes by periodicity. -/
theorem torus_hCurlIntZero (F : Torus3 → Fin 3 → ℝ) (u : Fin 3 → ℝ)
    (hF_diff : ∀ j, ContDiff ℝ 1 (periodicLift (fun x => F x j))) :
    ∫ x, dotProduct u (torusCurlX F x) = 0 := by
  have hzero := fun j i => torus_gradX_integral_zero (fun z => F z j) i (hF_diff j)
  have hint : ∀ j i, Integrable (fun x : Torus3 => torusGradX (fun z => F z j) x i) :=
    fun j i =>
      (continuous_torusGradX (fun z => F z j) i (hF_diff j)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  -- Key: torusCurlX F x k = torusGradX difference (by rfl, same choose)
  have hcurl0 : ∀ x, torusCurlX F x 0 =
      torusGradX (fun z => F z 2) x 1 - torusGradX (fun z => F z 1) x 2 := fun _ => rfl
  have hcurl1 : ∀ x, torusCurlX F x 1 =
      torusGradX (fun z => F z 0) x 2 - torusGradX (fun z => F z 2) x 0 := fun _ => rfl
  have hcurl2 : ∀ x, torusCurlX F x 2 =
      torusGradX (fun z => F z 1) x 0 - torusGradX (fun z => F z 0) x 1 := fun _ => rfl
  -- Rewrite integrand
  have key : (fun x => dotProduct u (torusCurlX F x)) = fun x =>
      u 0 * (torusGradX (fun z => F z 2) x 1 - torusGradX (fun z => F z 1) x 2) +
      (u 1 * (torusGradX (fun z => F z 0) x 2 - torusGradX (fun z => F z 2) x 0) +
       u 2 * (torusGradX (fun z => F z 1) x 0 - torusGradX (fun z => F z 0) x 1)) := by
    ext x
    simp only [dotProduct, Fin.sum_univ_three, hcurl0, hcurl1, hcurl2]
    ring
  rw [key]
  have h₀ : ∫ x : Torus3, u 0 * (torusGradX (fun z => F z 2) x 1 -
      torusGradX (fun z => F z 1) x 2) = 0 := by
    rw [integral_const_mul, integral_sub (hint 2 1) (hint 1 2),
        hzero 2 1, hzero 1 2, sub_self, mul_zero]
  have h₁ : ∫ x : Torus3, u 1 * (torusGradX (fun z => F z 0) x 2 -
      torusGradX (fun z => F z 2) x 0) = 0 := by
    rw [integral_const_mul, integral_sub (hint 0 2) (hint 2 0),
        hzero 0 2, hzero 2 0, sub_self, mul_zero]
  have h₂ : ∫ x : Torus3, u 2 * (torusGradX (fun z => F z 1) x 0 -
      torusGradX (fun z => F z 0) x 1) = 0 := by
    rw [integral_const_mul, integral_sub (hint 1 0) (hint 0 1),
        hzero 1 0, hzero 0 1, sub_self, mul_zero]
  have hA := (hint 2 1).sub (hint 1 2) |>.const_mul (u 0)
  have hB := (hint 0 2).sub (hint 2 0) |>.const_mul (u 1)
  have hC := (hint 1 0).sub (hint 0 1) |>.const_mul (u 2)
  refine (integral_add hA (hB.add hC)).trans ?_
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [h₀, zero_add]
  refine (integral_add hB hC).trans ?_
  simp only [Pi.sub_apply]
  rw [h₁, h₂, add_zero]

/-- Harmonic → constant on T³. Energy method using IBP. -/
theorem torus_hHarmonic_const (φ : Torus3 → ℝ)
    (hd : ContDiff ℝ 2 (periodicLift φ))
    (hharmonic : ∀ x, torusDivX (torusGradX φ) x = 0) :
    ∀ x y, φ x = φ y := by
  -- Smoothness of gradient components (C¹ suffices for IBP)
  have hgrad_pl : ∀ i, periodicLift (fun x => torusGradX φ x i) =
      fun y => fderiv ℝ (periodicLift φ) y (Pi.single i 1) :=
    fun i => funext (periodicLift_torusGradX φ i)
  have hgrad_c1 : ∀ i, ContDiff ℝ 1 (periodicLift (fun x => torusGradX φ x i)) := by
    intro i
    rw [hgrad_pl]
    exact ((hd.fderiv_right
      (show (1 : WithTop ℕ∞) + 1 ≤ 2 by decide)).clm_apply
      contDiff_const).of_le le_rfl
  have hφ_cont : Continuous φ :=
    isOpenQuotientMap_torusMk.isQuotientMap.continuous_iff.mpr
      (hd.of_le (show 0 ≤ 2 by decide)).continuous
  -- IBP: ∫ (∂φ/∂xᵢ)² = -∫ φ·∂²φ/∂xᵢ²
  have hIBP_i : ∀ i, ∫ x : Torus3, torusGradX φ x i * torusGradX φ x i =
      -(∫ x : Torus3, φ x * torusGradX (fun y => torusGradX φ y i) x i) :=
    fun i => torus_hIBP_spatial (fun y => torusGradX φ y i)
      φ i (hgrad_c1 i)
      (hd.of_le (show 1 ≤ 2 by decide))
  -- Each φ * ∂²φ/∂xᵢ² is integrable (continuous on compact)
  have hint : ∀ i, Integrable (fun x : Torus3 =>
      φ x * torusGradX (fun y => torusGradX φ y i) x i) :=
    fun i => (hφ_cont.mul (continuous_torusGradX _ i (hgrad_c1 i))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  -- ∑ᵢ ∫ (∂φ/∂xᵢ)² = 0 via harmonicity
  have hsum_zero : ∑ i : Fin 3, ∫ x : Torus3, torusGradX φ x i * torusGradX φ x i = 0 := by
    simp_rw [hIBP_i]
    rw [Finset.sum_neg_distrib, neg_eq_zero,
      ← integral_finset_sum _ (fun i _ => hint i)]
    simp_rw [← Finset.mul_sum]
    simp_rw [show ∀ x, ∑ i : Fin 3, torusGradX (fun y => torusGradX φ y i) x i =
        torusDivX (torusGradX φ) x from fun _ => rfl, hharmonic, mul_zero, integral_zero]
  -- Each ∫ (∂φ/∂xᵢ)² = 0 (nonneg + sum = 0)
  have h_nonneg : ∀ i, 0 ≤ ∫ x : Torus3, torusGradX φ x i * torusGradX φ x i :=
    fun i => integral_nonneg (fun x => mul_self_nonneg _)
  have hgrad_sq_zero : ∀ i, ∫ x : Torus3, torusGradX φ x i * torusGradX φ x i = 0 := by
    intro i; apply le_antisymm _ (h_nonneg i)
    have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => h_nonneg j) (Finset.mem_univ i)
    linarith [hsum_zero]
  -- ∂φ/∂xᵢ = 0 everywhere (nonneg continuous, integral = 0, compact space)
  have hgrad_zero : ∀ i x, torusGradX φ x i = 0 := by
    intro i x
    have hcont := continuous_torusGradX φ i (hd.of_le (by decide))
    have hae : (fun x => torusGradX φ x i * torusGradX φ x i) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg _)
        ((hcont.mul hcont).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))).mp (hgrad_sq_zero i)
    have hae' : (fun x => torusGradX φ x i) =ᵐ[volume] 0 := by
      filter_upwards [hae] with x hx; exact mul_self_eq_zero.mp hx
    exact congr_fun (MeasureTheory.Measure.eq_of_ae_eq hae' hcont continuous_const) x
  -- fderiv of periodicLift φ is zero everywhere
  have hfderiv_zero : ∀ y, fderiv ℝ (periodicLift φ) y = 0 := by
    intro y; ext v
    have hv : v = ∑ i : Fin 3, v i • (Pi.single i (1 : ℝ) : Fin 3 → ℝ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [hv, map_sum, ContinuousLinearMap.zero_apply]
    apply Finset.sum_eq_zero; intro i _
    rw [map_smul, smul_eq_mul, show (fderiv ℝ (periodicLift φ) y) (Pi.single i 1) =
        torusGradX φ (torusMk y) i from (periodicLift_torusGradX φ i y).symm,
      hgrad_zero, mul_zero]
  -- φ is constant via periodicLift constant
  intro x y
  obtain ⟨x₀, hx⟩ := torusMk_surjective x
  obtain ⟨y₀, hy⟩ := torusMk_surjective y
  have := is_const_of_fderiv_eq_zero (hd.differentiable (by decide)) hfderiv_zero x₀ y₀
  rw [← hx, ← hy]; exact this

end
