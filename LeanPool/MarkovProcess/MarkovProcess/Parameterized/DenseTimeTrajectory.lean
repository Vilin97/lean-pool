/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Parameterized.DenseTimeConditionalKernel
public import LeanPool.MarkovProcess.MarkovProcess.DenseTime.Trajectory
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj


/-! # Parameterized trajectories on countable dense time -/

@[expose] public section

noncomputable section PortComputability

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

section

universe uTheta uAlpha

variable {Theta : Type uTheta} {D : Type*} {alpha : Type uAlpha}
  [MeasurableSpace Theta] [MeasurableSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

private def trajectoryCoordinate : ℕ → Type (max uTheta uAlpha)
  | 0 => ULift.{max uTheta uAlpha} (Theta × alpha)
  | _ + 1 => ULift.{max uTheta uAlpha} alpha

private instance instMeasurableSpaceTrajectoryCoordinate (n : ℕ) : MeasurableSpace
    (trajectoryCoordinate (Theta := Theta) (alpha := alpha) n) :=
  match n with
  | 0 => (inferInstance : MeasurableSpace (ULift.{max uTheta uAlpha} (Theta × alpha)))
  | _ + 1 => (inferInstance : MeasurableSpace (ULift.{max uTheta uAlpha} alpha))

omit [StandardBorelSpace alpha] [Nonempty alpha] in
/-- Bridging lemma: `ULift.down` out of the `(n + 1)`-st trajectory coordinate is measurable
w.r.t. the project's registered `MeasurableSpace (trajectoryCoordinate (n + 1))` instance, not
just the generic `ULift.instMeasurableSpace` instance that `measurable_down` is stated for. -/
private theorem measurable_down_trajectoryCoordinate :
    Measurable (ULift.down : ULift.{max uTheta uAlpha} alpha → alpha) := by
  simpa only [trajectoryCoordinate] using! measurable_down

private def historyInitial (n : ℕ)
    (path : (i : ↑(Finset.Iic n)) →
      trajectoryCoordinate (Theta := Theta) (alpha := alpha) i) :
    ULift.{max uTheta uAlpha} (Theta × alpha) :=
  path ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩

private def historyObservation (n : ℕ)
    (path : (i : ↑(Finset.Iic n)) →
      trajectoryCoordinate (Theta := Theta) (alpha := alpha) i) (i : Fin n) :
    ULift.{max uTheta uAlpha} alpha :=
  path ⟨i + 1, Finset.mem_Iic.mpr i.isLt⟩

/-- An augmented history is exactly the immutable data and its observed prefix. -/
private def historyEquiv (n : ℕ) :
    ((i : ↑(Finset.Iic n)) → trajectoryCoordinate (Theta := Theta) (alpha := alpha) i) ≃ᵐ
      ((Theta × alpha) × (Fin n → alpha)) where
  toFun path :=
    ((historyInitial n path).down, fun i ↦ (historyObservation n path i).down)
  invFun z i := by
    rcases i with ⟨_ | k, hi⟩
    · exact ULift.up z.1
    · exact ULift.up (z.2 ⟨k, by
        rw [Finset.mem_Iic] at hi
        exact Nat.succ_le_iff.mp hi⟩)
  left_inv path := by
    funext i
    rcases i with ⟨_ | k, hi⟩
    · rfl
    · rfl
  right_inv z := by
    apply Prod.ext
    · rfl
    · funext i
      rfl
  measurable_toFun := by
    apply Measurable.prodMk
    · have h := measurable_pi_apply
        (X := fun i : ↑(Finset.Iic n) ↦
          trajectoryCoordinate (Theta := Theta) (alpha := alpha) i)
        ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩
      simpa only [trajectoryCoordinate] using! measurable_down.comp h
    · rw [measurable_pi_iff]
      intro i
      have h := measurable_pi_apply
        (X := fun i : ↑(Finset.Iic n) ↦
          trajectoryCoordinate (Theta := Theta) (alpha := alpha) i)
        ⟨i + 1, Finset.mem_Iic.mpr i.isLt⟩
      simpa only [trajectoryCoordinate] using! measurable_down.comp h
  measurable_invFun := by
    rw [measurable_pi_iff]
    rintro ⟨_ | k, hi⟩
    · simpa only [trajectoryCoordinate] using! measurable_up.comp measurable_fst
    · simpa only [trajectoryCoordinate] using! measurable_up.comp
        ((measurable_pi_apply
          (X := fun _ : Fin n ↦ alpha)
          ⟨k, Nat.succ_le_iff.mp (Finset.mem_Iic.mp hi)⟩).comp
          measurable_snd)

omit [StandardBorelSpace alpha] [Nonempty alpha] in
private theorem historyEquiv_fst (n : ℕ) (path) :
    (historyEquiv (Theta := Theta) (alpha := alpha) n path).1 =
      (historyInitial n path).down := rfl

omit [StandardBorelSpace alpha] [Nonempty alpha] in
private theorem historyEquiv_snd_apply (n : ℕ) (path) (i : Fin n) :
    (historyEquiv (Theta := Theta) (alpha := alpha) n path).2 i =
      (historyObservation n path i).down := rfl

attribute [irreducible] historyEquiv

private def parameterizedTrajStep
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (n : ℕ) :
    Kernel ((i : ↑(Finset.Iic n)) → trajectoryCoordinate (Theta := Theta) (alpha := alpha) i)
      (trajectoryCoordinate (Theta := Theta) (alpha := alpha) (n + 1)) :=
  ((P.parameterizedObservationCondKernel hP e iota n).map
      (γ := trajectoryCoordinate (Theta := Theta) (alpha := alpha) (n + 1)) ULift.up).comap
    (historyEquiv n) (historyEquiv n).measurable

private instance isMarkovKernel_parameterizedTrajStep
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (n : ℕ) :
    IsMarkovKernel (parameterizedTrajStep P hP e iota n) := by
  rw [parameterizedTrajStep]
  let _ := P.isMarkovKernel_parameterizedObservationCondKernel hP e iota n
  let _ : IsMarkovKernel ((P.parameterizedObservationCondKernel hP e iota n).map
      (γ := trajectoryCoordinate (Theta := Theta) (alpha := alpha) (n + 1)) ULift.up) :=
    Kernel.IsMarkovKernel.map _
      (by simpa only [trajectoryCoordinate] using! measurable_up)
  exact Kernel.IsMarkovKernel.comap _ (historyEquiv n).measurable

private def initialHistory (q : Theta × alpha) :
    (i : ↑(Finset.Iic 0)) → trajectoryCoordinate (Theta := Theta) (alpha := alpha) i :=
  fun i ↦ by
    rcases i with ⟨_ | k, hi⟩
    · exact ULift.up q
    · simp only [Finset.mem_Iic] at hi
      omega

omit [StandardBorelSpace alpha] [Nonempty alpha] in
private theorem measurable_initialHistory :
    Measurable (initialHistory (Theta := Theta) (alpha := alpha)) := by
  rw [measurable_pi_iff]
  rintro ⟨_ | k, hi⟩
  · simpa only [trajectoryCoordinate] using!
      (measurable_up : Measurable (ULift.up : Theta × alpha →
        ULift.{max uTheta uAlpha} (Theta × alpha)))
  · simp only [Finset.mem_Iic] at hi
    omega

private def eraseAugmentation (e : ℕ ≃ D)
    (path : (n : ℕ) → trajectoryCoordinate (Theta := Theta) (alpha := alpha) n) : D → alpha :=
  fun d ↦ (path (e.symm d + 1)).down

omit [StandardBorelSpace alpha] [Nonempty alpha] in
private theorem measurable_eraseAugmentation (e : ℕ ≃ D) :
    Measurable (eraseAugmentation (Theta := Theta) (alpha := alpha) e) := by
  rw [measurable_pi_iff]
  intro d
  simpa only [trajectoryCoordinate] using! measurable_down.comp
    (measurable_pi_apply
      (X := trajectoryCoordinate (Theta := Theta) (alpha := alpha)) (e.symm d + 1))

private def rawTrajAppend (n : ℕ) :
    (((i : ↑(Finset.Iic n)) → trajectoryCoordinate (Theta := Theta) (alpha := alpha) i) ×
      trajectoryCoordinate (Theta := Theta) (alpha := alpha) (n + 1)) →
      ((i : ↑(Finset.Iic (n + 1))) →
        trajectoryCoordinate (Theta := Theta) (alpha := alpha) i) :=
  IicProdIoc (X := trajectoryCoordinate (Theta := Theta) (alpha := alpha)) n (n + 1) ∘
    Prod.map id (MeasurableEquiv.piSingleton
      (X := trajectoryCoordinate (Theta := Theta) (alpha := alpha)) n)

omit [StandardBorelSpace alpha] [Nonempty alpha] in
private theorem rawTrajAppend_apply_cast (n : ℕ) (z) (i : ↑(Finset.Iic n)) :
    rawTrajAppend (Theta := Theta) (alpha := alpha) n z
      ⟨i, Finset.mem_Iic.mpr ((Finset.mem_Iic.mp i.2).trans n.le_succ)⟩ = z.1 i := by
  simp only [rawTrajAppend, Function.comp_apply, IicProdIoc_def]
  rw [dite_eq_left (Finset.mem_Iic.mp i.2)]
  rfl

omit [StandardBorelSpace alpha] [Nonempty alpha] in
private theorem rawTrajAppend_apply_last (n : ℕ) (z) :
    rawTrajAppend (Theta := Theta) (alpha := alpha) n z
      ⟨n + 1, Finset.mem_Iic.mpr (Nat.le_refl (n + 1))⟩ = z.2 := by
  simp only [rawTrajAppend, Function.comp_apply, IicProdIoc_def]
  rw [dite_eq_right (Nat.not_succ_le_self n)]
  change (MeasurableEquiv.piSingleton
    (X := trajectoryCoordinate (Theta := Theta) (alpha := alpha)) n).symm
      (MeasurableEquiv.piSingleton n z.2) = z.2
  exact MeasurableEquiv.symm_apply_apply _ _

private def appendObservation (n : ℕ) :
    (((Theta × alpha) × (Fin n → alpha)) ×
      ULift.{max uTheta uAlpha} alpha) → (Theta × alpha) × (Fin (n + 1) → alpha) :=
  fun z ↦ (z.1.1, (DenseTimeHistory.splitLast n).symm (z.1.2, z.2.down))

omit [StandardBorelSpace alpha] [Nonempty alpha] in
private theorem measurable_appendObservation (n : ℕ) :
    Measurable (appendObservation (Theta := Theta) (alpha := alpha) n) := by
  apply Measurable.prodMk
  · exact measurable_fst.comp measurable_fst
  · exact (DenseTimeHistory.splitLast n).symm.measurable.comp
      ((measurable_snd.comp measurable_fst).prodMk
        (measurable_down.comp measurable_snd))

omit [StandardBorelSpace alpha] [Nonempty alpha] in
private theorem historyEquiv_rawTrajAppend (n : ℕ)
    (z : (((i : ↑(Finset.Iic n)) →
      trajectoryCoordinate (Theta := Theta) (alpha := alpha) i) ×
      trajectoryCoordinate (Theta := Theta) (alpha := alpha) (n + 1))) :
    historyEquiv (Theta := Theta) (alpha := alpha) (n + 1) (rawTrajAppend n z) =
      ((historyEquiv n z.1).1,
        (DenseTimeHistory.splitLast n).symm
          ((historyEquiv n z.1).2,
            (show ULift.{max uTheta uAlpha} alpha from z.2).down)) := by
  apply Prod.ext
  · rw [historyEquiv_fst]
    rw [historyEquiv_fst]
    change (rawTrajAppend n z
      ⟨0, Finset.mem_Iic.mpr (Nat.zero_le (n + 1))⟩).down =
        (z.1 ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩).down
    have h := rawTrajAppend_apply_cast (Theta := Theta) (alpha := alpha) n z
      (⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩ : ↑(Finset.Iic n))
    exact congrArg ULift.down h
  · change _ = (DenseTimeHistory.splitLast n).symm (_, _)
    apply (DenseTimeHistory.splitLast n).injective
    rw [MeasurableEquiv.apply_symm_apply]
    apply Prod.ext
    · funext i
      rw [DenseTimeHistory.splitLast_fst_apply]
      rw [historyEquiv_snd_apply]
      change _ = (historyEquiv n z.1).2 i
      rw [historyEquiv_snd_apply]
      change (rawTrajAppend n z
        ⟨i + 1, Finset.mem_Iic.mpr (Nat.succ_le_succ i.isLt.le)⟩).down =
          (z.1 ⟨i + 1, Finset.mem_Iic.mpr i.isLt⟩).down
      have h := rawTrajAppend_apply_cast (Theta := Theta) (alpha := alpha) n z
        (⟨i + 1, Finset.mem_Iic.mpr i.isLt⟩ : ↑(Finset.Iic n))
      exact congrArg ULift.down h
    · rw [DenseTimeHistory.splitLast_snd]
      rw [historyEquiv_snd_apply]
      change _ = z.2.down
      change (rawTrajAppend n z
        ⟨n + 1, Finset.mem_Iic.mpr (Nat.le_refl (n + 1))⟩).down = z.2.down
      exact congrArg ULift.down
        (rawTrajAppend_apply_last (Theta := Theta) (alpha := alpha) n z)

private theorem transport_traj_step {X H Z Y T : Type*}
    [MeasurableSpace X] [MeasurableSpace H] [MeasurableSpace Z]
    [MeasurableSpace Y] [MeasurableSpace T]
    (kappa : Kernel X Z) (eta : Kernel Z Y) [IsSFiniteKernel eta] (E : H ≃ᵐ Z)
    (g : H × Y → T) (hg : Measurable g) (q : Z × Y → T)
    (hcompat : g ∘ Prod.map E.symm id = q) :
    (((Kernel.id ×ₖ eta.comap E E.measurable) ∘ₖ kappa.map E.symm).map g) =
      ((Kernel.id ×ₖ eta) ∘ₖ kappa).map q := by
  rw [Kernel.comp_map kappa (Kernel.id ×ₖ eta.comap E E.measurable) E.symm.measurable]
  rw [Kernel.comap_prod, Kernel.id_comap, ← Kernel.id_map,
    ← Kernel.comap_comp_right]
  have hcomap : eta.comap ((E : H → Z) ∘ E.symm)
      (E.measurable.comp E.symm.measurable) = eta := by
    ext z
    rw [Kernel.comap_apply]
    change eta (E (E.symm z)) _ = eta z _
    rw [E.apply_symm_apply]
  rw [hcomap, ← Kernel.map_id' eta, Kernel.map_prod_map,
    ← Kernel.map_comp, ← Kernel.map_comp_right, Kernel.map_id']
  · change (Kernel.id ×ₖ eta ∘ₖ kappa).map (g ∘ Prod.map E.symm id) = _
    rw [hcompat]
  all_goals first | exact hg | fun_prop

private theorem prod_comp_prod_map_prodAssoc {X A B : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    (kappa : Kernel X A) [IsSFiniteKernel kappa]
    (eta : Kernel (X × A) B) [IsSFiniteKernel eta] :
    (((Kernel.id ×ₖ eta) ∘ₖ (Kernel.id ×ₖ kappa)).map MeasurableEquiv.prodAssoc) =
      Kernel.id ×ₖ (kappa ⊗ₖ eta) := by
  ext x s hs
  rw [Kernel.map_apply' _ MeasurableEquiv.prodAssoc.measurable _ hs, Kernel.comp_apply]
  rw [← Measure.compProd_eq_comp_prod]
  have hfirst : (Kernel.id ×ₖ kappa) x = Measure.dirac x ⊗ₘ kappa := by
    rw [Measure.compProd_eq_comp_prod]
    exact (Measure.dirac_bind (Kernel.measurable (Kernel.id ×ₖ kappa)) x).symm
  rw [hfirst]
  rw [← Measure.map_apply MeasurableEquiv.prodAssoc.measurable hs]
  rw [Measure.compProd_assoc']
  have hlast : (Kernel.id ×ₖ (kappa ⊗ₖ eta)) x =
      Measure.dirac x ⊗ₘ (kappa ⊗ₖ eta) := by
    rw [Measure.compProd_eq_comp_prod]
    exact (Measure.dirac_bind (Kernel.measurable (Kernel.id ×ₖ (kappa ⊗ₖ eta))) x).symm
  rw [hlast]

omit [StandardBorelSpace alpha] [Nonempty alpha] in
private theorem compProd_map_ulift_down {X A : Type*}
    [MeasurableSpace X] [MeasurableSpace A]
    (kappa : Kernel X A) [IsSFiniteKernel kappa]
    (eta : Kernel (X × A) alpha) [IsSFiniteKernel eta] :
    (kappa ⊗ₖ eta.map (ULift.up : alpha → ULift.{max uTheta uAlpha} alpha)).map
        (Prod.map id ULift.down) = kappa ⊗ₖ eta := by
  ext x s hs
  rw [Kernel.map_apply _ (measurable_id.prodMap measurable_down)]
  rw [Measure.map_apply (measurable_id.prodMap measurable_down) hs]
  rw [Kernel.compProd_apply (hs.preimage (measurable_id.prodMap measurable_down))]
  rw [Kernel.compProd_apply hs]
  congr with a
  rw [Kernel.map_apply _ measurable_up]
  rw [Measure.map_apply measurable_up
    ((hs.preimage (measurable_id.prodMap measurable_down)).preimage measurable_prodMk_left)]
  apply congrArg (eta (x, a))
  ext y
  simp only [Set.mem_preimage, Prod.map_apply, id_eq]

private def initialHistoryKernel : Kernel (Theta × alpha)
    ((i : ↑(Finset.Iic 0)) → trajectoryCoordinate (Theta := Theta) (alpha := alpha) i) :=
  Kernel.deterministic initialHistory measurable_initialHistory

omit [StandardBorelSpace alpha] [Nonempty alpha] in
private theorem markovKernel_finZero (kappa : Kernel (Theta × alpha) (Fin 0 → alpha))
    [IsMarkovKernel kappa] :
    kappa = Kernel.const (Theta × alpha)
      (Measure.dirac (FiniteOrderedTimes.emptyPath alpha)) := by
  ext q s hs
  rcases s.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
  · simp
  · have hsu : s = Set.univ := by
      apply Set.eq_univ_of_forall
      intro y
      simpa only [Subsingleton.elim y z] using hz
    rw [hsu]
    simp only [Kernel.const_apply, IsProbabilityMeasure.measure_univ]

private theorem partialTraj_map_historyEquiv
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (n : ℕ) :
    ((Kernel.partialTraj
        (X := trajectoryCoordinate (Theta := Theta) (alpha := alpha))
        (parameterizedTrajStep P hP e iota) 0 n ∘ₖ initialHistoryKernel).map
          (historyEquiv n)) =
      Kernel.id ×ₖ P.parameterizedDenseTimePrefixKernel e iota n := by
  induction n with
  | zero =>
      rw [Kernel.partialTraj_self, Kernel.id_comp, initialHistoryKernel,
        Kernel.deterministic_map]
      · let _ : IsMarkovKernel (P.parameterizedDenseTimePrefixKernel e iota 0) :=
          P.isMarkovKernel_parameterizedDenseTimePrefixKernel hP e iota 0
        rw [markovKernel_finZero (P.parameterizedDenseTimePrefixKernel e iota 0)]
        have hconst : Kernel.const (Theta × alpha)
            (Measure.dirac (FiniteOrderedTimes.emptyPath alpha)) =
            Kernel.deterministic (fun _ : Theta × alpha ↦ FiniteOrderedTimes.emptyPath alpha)
              measurable_const := by
          ext q s hs
          simp only [Kernel.const_apply, Kernel.deterministic_apply,
            Measure.dirac_apply' _ hs]
        rw [hconst, Kernel.id, Kernel.deterministic_prod_deterministic]
        apply Kernel.deterministic_congr
        funext q
        apply Prod.ext
        · change (historyEquiv 0 (initialHistory q)).1 = q
          rw [historyEquiv_fst]
          rfl
        · exact Subsingleton.elim _ _
      all_goals fun_prop
  | succ n ih =>
      let _ : IsMarkovKernel (P.parameterizedDenseTimePrefixKernel e iota n) :=
        P.isMarkovKernel_parameterizedDenseTimePrefixKernel hP e iota n
      let _ : IsMarkovKernel (P.parameterizedObservationCondKernel hP e iota n) :=
        P.isMarkovKernel_parameterizedObservationCondKernel hP e iota n
      let _ : IsMarkovKernel ((P.parameterizedObservationCondKernel hP e iota n).map
          (γ := trajectoryCoordinate (Theta := Theta) (alpha := alpha) (n + 1)) ULift.up) :=
        Kernel.IsMarkovKernel.map _
          (by simpa only [trajectoryCoordinate] using! measurable_up)
      let _ : IsMarkovKernel
          (((P.parameterizedObservationCondKernel hP e iota n).map
            (γ := trajectoryCoordinate (Theta := Theta) (alpha := alpha) (n + 1)) ULift.up).comap
              (historyEquiv n) (historyEquiv n).measurable) :=
        Kernel.IsMarkovKernel.comap _ (historyEquiv n).measurable
      rw [Kernel.partialTraj_succ_of_le (Nat.zero_le n)]
      rw [← Kernel.map_comp]
      rw [Kernel.comp_assoc]
      rw [← Kernel.map_comp_right]
      · rw [parameterizedTrajStep]
        rw [← Kernel.map_id' Kernel.id, Kernel.map_prod_map] <;> try fun_prop
        rw [← Kernel.map_comp]
        rw [← Kernel.map_comp_right]
        · have hkraw :=
            (Kernel.map_apply_eq_iff_map_symm_apply_eq
              (Kernel.partialTraj
                  (X := trajectoryCoordinate (Theta := Theta) (alpha := alpha))
                  (parameterizedTrajStep P hP e iota) 0 n ∘ₖ initialHistoryKernel)
              (Kernel.id ×ₖ P.parameterizedDenseTimePrefixKernel e iota n)).mp ih
          rw [hkraw]
          have htransport := transport_traj_step
            (Kernel.id ×ₖ P.parameterizedDenseTimePrefixKernel e iota n)
            ((P.parameterizedObservationCondKernel hP e iota n).map
              (γ := trajectoryCoordinate (Theta := Theta) (alpha := alpha) (n + 1)) ULift.up)
            (historyEquiv n)
            (historyEquiv (n + 1) ∘ rawTrajAppend n)
            ((historyEquiv (n + 1)).measurable.comp
              (measurable_IicProdIoc.comp
                (measurable_id.prodMap (MeasurableEquiv.piSingleton n).measurable)))
            (appendObservation n) (by
              funext z
              change historyEquiv (n + 1)
                (rawTrajAppend n ((historyEquiv n).symm z.1, z.2)) = _
              rw [historyEquiv_rawTrajAppend]
              rw [MeasurableEquiv.apply_symm_apply]
              rfl)
          have hfun :
              ((historyEquiv (Theta := Theta) (alpha := alpha) (n + 1) ∘
                  IicProdIoc
                    (X := trajectoryCoordinate (Theta := Theta) (alpha := alpha))
                    n (n + 1)) ∘
                Prod.map (fun a ↦ a) (MeasurableEquiv.piSingleton
                  (X := trajectoryCoordinate (Theta := Theta) (alpha := alpha)) n)) =
                historyEquiv (Theta := Theta) (alpha := alpha) (n + 1) ∘
                  rawTrajAppend n := by
            rfl
          rw [hfun, htransport]
          let r : (Theta × alpha) ×
              ((Fin n → alpha) × trajectoryCoordinate (Theta := Theta) (alpha := alpha) (n + 1)) →
              (Theta × alpha) × (Fin (n + 1) → alpha) :=
            fun z ↦ (z.1, (DenseTimeHistory.splitLast n).symm (z.2.1, z.2.2.down))
          have hq : appendObservation n = r ∘ MeasurableEquiv.prodAssoc := by
            rfl
          have hr_meas : Measurable r :=
            measurable_fst.prodMk ((DenseTimeHistory.splitLast n).symm.measurable.comp
              ((measurable_fst.comp measurable_snd).prodMk
                (measurable_down_trajectoryCoordinate.comp
                  (measurable_snd.comp measurable_snd))))
          rw [hq, Kernel.map_comp_right _ MeasurableEquiv.prodAssoc.measurable hr_meas]
          rw [prod_comp_prod_map_prodAssoc]
          have hr : r = Prod.map id
              ((DenseTimeHistory.splitLast n).symm ∘
                Prod.map (β₁ := trajectoryCoordinate (Theta := Theta) (alpha := alpha) (n + 1))
                  id ULift.down) := by
            rfl
          rw [hr, ← Kernel.map_id' Kernel.id]
          rw [← Kernel.map_prod_map (Kernel.id.map (fun a : Theta × alpha => a))
            (P.parameterizedDenseTimePrefixKernel e iota n ⊗ₖ
              (P.parameterizedObservationCondKernel hP e iota n).map
                (γ := trajectoryCoordinate (Theta := Theta) (alpha := alpha) (n + 1)) ULift.up)
            measurable_id
            ((DenseTimeHistory.splitLast n).symm.measurable.comp
              (measurable_id.prodMap measurable_down_trajectoryCoordinate))]
          rw [Kernel.map_comp_right
            (P.parameterizedDenseTimePrefixKernel e iota n ⊗ₖ
              (P.parameterizedObservationCondKernel hP e iota n).map
                (γ := trajectoryCoordinate (Theta := Theta) (alpha := alpha) (n + 1)) ULift.up)
            (measurable_id.prodMap measurable_down_trajectoryCoordinate)
            (DenseTimeHistory.splitLast n).symm.measurable]
          have hcpmud :
              (P.parameterizedDenseTimePrefixKernel e iota n ⊗ₖ
                (P.parameterizedObservationCondKernel hP e iota n).map
                  (γ := trajectoryCoordinate (Theta := Theta) (alpha := alpha) (n + 1))
                  ULift.up).map (Prod.map id ULift.down) =
                P.parameterizedDenseTimePrefixKernel e iota n ⊗ₖ
                  P.parameterizedObservationCondKernel hP e iota n :=
            compProd_map_ulift_down _ _
          rw [hcpmud]
          rw [P.compProd_parameterizedObservationCondKernel hP e iota n]
          rw [parameterizedNextObservationJoint, Kernel.mapOfMeasurable_eq_map]
          rw [← Kernel.map_comp_right _
            (DenseTimeHistory.splitLast n).measurable
            (DenseTimeHistory.splitLast n).symm.measurable]
          have hsplit : (DenseTimeHistory.splitLast n).symm ∘
              DenseTimeHistory.splitLast n =
                (id : (Fin (n + 1) → alpha) → (Fin (n + 1) → alpha)) := by
            funext z
            exact (DenseTimeHistory.splitLast n).symm_apply_apply z
          rw [hsplit, Kernel.map_id, Kernel.map_id]
        · exact measurable_id.prodMap (MeasurableEquiv.piSingleton
            (X := trajectoryCoordinate (Theta := Theta) (alpha := alpha)) n).measurable
        · exact (historyEquiv (n + 1)).measurable.comp measurable_IicProdIoc
      · exact measurable_IicProdIoc
      · exact (historyEquiv (n + 1)).measurable

/-- The jointly measurable dense-time trajectory kernel. -/
def parameterizedDenseTimeTrajectory
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) : Kernel (Theta × alpha) (D → alpha) :=
  ((Kernel.traj (X := trajectoryCoordinate (Theta := Theta) (alpha := alpha))
      (parameterizedTrajStep P hP e iota) 0).comap initialHistory
        measurable_initialHistory).map (eraseAugmentation e)

/-- The parameterized dense-time trajectory kernel is Markov. -/
theorem isMarkovKernel_parameterizedDenseTimeTrajectory
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) :
    IsMarkovKernel (P.parameterizedDenseTimeTrajectory hP e iota) := by
  rw [parameterizedDenseTimeTrajectory]
  exact Kernel.IsMarkovKernel.map _ (measurable_eraseAugmentation e)

omit [StandardBorelSpace alpha] [Nonempty alpha] in
private theorem denseTimeTrajectoryPrefix_eraseAugmentation
    (e : ℕ ≃ D) (n : ℕ) :
    SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectoryPrefix
        (α := alpha) e n ∘
          eraseAugmentation (Theta := Theta) (alpha := alpha) e =
      (Prod.snd : ((Theta × alpha) × (Fin n → alpha)) → (Fin n → alpha)) ∘
        historyEquiv (Theta := Theta) (alpha := alpha) n ∘
          Preorder.frestrictLe n := by
  funext path i
  change (path (e.symm (e i) + 1)).down =
    (historyEquiv n (Preorder.frestrictLe n path)).2 i
  rw [historyEquiv_snd_apply]
  rw [e.symm_apply_apply]
  rfl

/-- Restricting the trajectory to the first `n` enumeration labels gives exactly the
parameterized prefix kernel. -/
theorem parameterizedDenseTimeTrajectory_map_prefix
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (n : ℕ) :
    (P.parameterizedDenseTimeTrajectory hP e iota).map
        (SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectoryPrefix e n) =
      P.parameterizedDenseTimePrefixKernel e iota n := by
  let _ : IsMarkovKernel (P.parameterizedDenseTimePrefixKernel e iota n) :=
    P.isMarkovKernel_parameterizedDenseTimePrefixKernel hP e iota n
  rw [parameterizedDenseTimeTrajectory, ← Kernel.map_comp_right]
  · rw [denseTimeTrajectoryPrefix_eraseAugmentation]
    rw [Kernel.map_comp_right]
    · rw [Kernel.map_comp_right _ (Preorder.measurable_frestrictLe n)
        (historyEquiv n).measurable]
      rw [← Kernel.comap_map_comm _ measurable_initialHistory
        (Preorder.measurable_frestrictLe n)]
      rw [Kernel.traj_map_frestrictLe]
      rw [← Kernel.comp_deterministic_eq_comap]
      change ((Kernel.partialTraj
        (X := trajectoryCoordinate (Theta := Theta) (alpha := alpha))
        (parameterizedTrajStep P hP e iota) 0 n ∘ₖ initialHistoryKernel).map
          (historyEquiv n)).map Prod.snd = _
      rw [partialTraj_map_historyEquiv]
      rw [← Kernel.snd_eq, Kernel.snd_prod]
    · exact (historyEquiv n).measurable.comp (Preorder.measurable_frestrictLe n)
    · exact measurable_snd
  · exact measurable_eraseAugmentation e
  · exact SubMarkovKernelSemigroup.IsConservative.measurable_denseTimeTrajectoryPrefix e n

end
end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess

end PortComputability
