/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.DenseTime.PrefixRecursion
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj


/-!
# Trajectories on countable dense time

This file transports the finite-history transition kernels to the history carrier used by
Mathlib's Ionescu--Tulcea construction, starts the resulting trajectory at a deterministic state,
and reindexes its positive coordinates by a countable dense-time enumeration.
-/

@[expose] public section

noncomputable section PortComputability

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative

section

variable {D α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]

/-- Mathlib's locally finite interval and the set interval used by `DenseTimeHistory` give
measurably equivalent history spaces. -/
def denseTimeHistoryMeasurableEquiv (n : ℕ) :
    ((↑(Finset.Iic n) → α) ≃ᵐ DenseTimeHistory α n) :=
  MeasurableEquiv.piCongrLeft (fun _ : Set.Iic n ↦ α) (Equiv.IicFinsetSet n)

/-- The dense-time transition kernel on Mathlib's finite-history carrier. -/
def trajDenseStep (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) : Kernel (↑(Finset.Iic n) → α) α :=
  (denseStep P hP e ι n).comap (denseTimeHistoryMeasurableEquiv n)
    (denseTimeHistoryMeasurableEquiv n).measurable

/-- The transported dense-time transition kernel is Markov. -/
instance isMarkovKernel_trajDenseStep (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    IsMarkovKernel (trajDenseStep P hP e ι n) := by
  rw [trajDenseStep]
  let : IsMarkovKernel (denseStep P hP e ι n) :=
    isMarkovKernel_denseStep P hP e ι n
  infer_instance

/-- The time-zero history determined by an initial state. -/
def initialTrajHistory (x : α) : ↑(Finset.Iic 0) → α :=
  fun _ ↦ x

omit [StandardBorelSpace α] [Nonempty α] in
/-- The deterministic time-zero history is a measurable function of its initial state. -/
theorem measurable_initialTrajHistory : Measurable (initialTrajHistory (α := α)) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_id

/-- The deterministic kernel from an initial state to its time-zero history. -/
def initialTrajHistoryKernel : Kernel α (↑(Finset.Iic 0) → α) :=
  Kernel.deterministic initialTrajHistory measurable_initialTrajHistory

/-- Remove the augmented initial-state coordinate from a natural-number trajectory. -/
def dropInitialTrajCoordinate (path : ℕ → α) : ℕ → α :=
  fun n ↦ path (n + 1)

omit [StandardBorelSpace α] [Nonempty α] in
/-- Dropping the initial trajectory coordinate is measurable. -/
theorem measurable_dropInitialTrajCoordinate :
    Measurable (dropInitialTrajCoordinate (α := α)) := by
  rw [measurable_pi_iff]
  intro n
  exact measurable_pi_apply (n + 1)

/-- The countable trajectory in enumeration order, with coordinate zero corresponding to the
first observation rather than the augmented initial state. -/
def enumeratedDenseTimeTrajectory (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) : Kernel α (ℕ → α) :=
  ((Kernel.traj (X := fun _ ↦ α) (trajDenseStep P hP e ι) 0).comap
      initialTrajHistory measurable_initialTrajHistory).map dropInitialTrajCoordinate

/-- The trajectory in enumeration order is a Markov kernel. -/
instance isMarkovKernel_enumeratedDenseTimeTrajectory (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) :
    IsMarkovKernel (enumeratedDenseTimeTrajectory P hP e ι) := by
  rw [enumeratedDenseTimeTrajectory]
  exact Kernel.IsMarkovKernel.map _ measurable_dropInitialTrajCoordinate

/-- Reindex the enumerated trajectory by its dense-time labels. -/
def denseTimeTrajectory (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) : Kernel α (D → α) :=
  (enumeratedDenseTimeTrajectory P hP e ι).map
    (CountableEnumeration.measurableEquivPath e α)

/-- The dense-time trajectory is a Markov kernel. -/
instance isMarkovKernel_denseTimeTrajectory (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) :
    IsMarkovKernel (denseTimeTrajectory P hP e ι) := by
  rw [denseTimeTrajectory]
  exact Kernel.IsMarkovKernel.map _
    (CountableEnumeration.measurableEquivPath e α).measurable

/-- Before dropping the initial coordinate, every finite marginal of the trajectory is the
corresponding `partialTraj`, started from the deterministic time-zero history. -/
theorem trajDenseStep_map_frestrictLe (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    ((Kernel.traj (X := fun _ ↦ α) (trajDenseStep P hP e ι) 0).comap
        initialTrajHistory measurable_initialTrajHistory).map (Preorder.frestrictLe n) =
      Kernel.partialTraj (X := fun _ ↦ α) (trajDenseStep P hP e ι) 0 n ∘ₖ
        initialTrajHistoryKernel := by
  rw [← Kernel.comap_map_comm _ measurable_initialTrajHistory
    (Preorder.measurable_frestrictLe n), Kernel.traj_map_frestrictLe,
    ← Kernel.comp_deterministic_eq_comap]
  rfl

private def rawTrajAppend (n : ℕ) :
    ((↑(Finset.Iic n) → α) × α) → (↑(Finset.Iic (n + 1)) → α) :=
  IicProdIoc (X := fun _ ↦ α) n (n + 1) ∘
    Prod.map id (MeasurableEquiv.piSingleton (X := fun _ ↦ α) n)

omit [StandardBorelSpace α] [Nonempty α] in
private theorem denseTimeHistoryMeasurableEquiv_rawTrajAppend (n : ℕ) :
    denseTimeHistoryMeasurableEquiv (α := α) (n + 1) ∘ rawTrajAppend n =
      DenseTimeHistory.append n ∘
        Prod.map (denseTimeHistoryMeasurableEquiv (α := α) n) id := by
  funext z
  funext i
  rcases i with ⟨i, hi⟩
  dsimp only [Function.comp_apply, Prod.map_apply, id_eq]
  change rawTrajAppend n z ⟨i, Finset.mem_Iic.mpr hi⟩ =
    DenseTimeHistory.append n (denseTimeHistoryMeasurableEquiv n z.1, z.2) ⟨i, hi⟩
  by_cases hiz : i = 0
  · subst i
    rfl
  · by_cases hin : i = n + 1
    · subst i
      change (if h : n + 1 ≤ n then
        z.1 ⟨n + 1, Finset.mem_Iic.mpr h⟩ else z.2) = _
      rw [DenseTimeHistory.append_apply_last]
      simp only [Nat.not_succ_le_self, dite_false]
    · have hi' : i ≤ n + 1 := hi
      have hil : i ≤ n := by omega
      let j : Set.Iic n := ⟨i, hil⟩
      simp only [rawTrajAppend, Function.comp_apply, IicProdIoc_def,
        MeasurableEquiv.piSingleton]
      rw [dite_eq_left hil]
      rw [DenseTimeHistory.append_apply_castSucc n
        (denseTimeHistoryMeasurableEquiv n z.1) z.2 j]
      rfl

private theorem transport_traj_step {X H Z Y T : Type*}
    [MeasurableSpace X] [MeasurableSpace H] [MeasurableSpace Z]
    [MeasurableSpace Y] [MeasurableSpace T]
    (κ : Kernel X Z) (η : Kernel Z Y) [IsSFiniteKernel η] (E : H ≃ᵐ Z)
    (g : H × Y → T) (hg : Measurable g) (q : Z × Y → T)
    (hcompat : g ∘ Prod.map E.symm id = q) :
    (((Kernel.id ×ₖ η.comap E E.measurable) ∘ₖ κ.map E.symm).map g) =
      ((Kernel.id ×ₖ η) ∘ₖ κ).map q := by
  rw [Kernel.comp_map κ (Kernel.id ×ₖ η.comap E E.measurable) E.symm.measurable]
  rw [Kernel.comap_prod, Kernel.id_comap, ← Kernel.id_map,
    ← Kernel.comap_comp_right]
  have hcomap : η.comap ((E : H → Z) ∘ E.symm)
      (E.measurable.comp E.symm.measurable) = η := by
    ext z
    rw [Kernel.comap_apply]
    change η (E (E.symm z)) _ = η z _
    rw [E.apply_symm_apply]
  rw [hcomap, ← Kernel.map_id' η, Kernel.map_prod_map,
    ← Kernel.map_comp, ← Kernel.map_comp_right, Kernel.map_id']
  · change (Kernel.id ×ₖ η ∘ₖ κ).map (g ∘ Prod.map E.symm id) = _
    rw [hcompat]
  all_goals first | exact hg | fun_prop

omit [StandardBorelSpace α] [Nonempty α] in
private theorem markovKernel_finZero (κ : Kernel α (Fin 0 → α)) [IsMarkovKernel κ] :
    κ = Kernel.const α (Measure.dirac (FiniteOrderedTimes.emptyPath α)) := by
  ext x s hs
  rcases s.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
  · simp
  · have hsu : s = Set.univ := by
      apply Set.eq_univ_of_forall
      intro y
      simpa only [Subsingleton.elim y z] using hz
    rw [hsu]
    simp only [Kernel.const_apply, IsProbabilityMeasure.measure_univ]

/-- Every finite augmented marginal of the iterated dense-time trajectory is the prescribed
augmented prefix law. -/
theorem partialTraj_map_denseTimeHistoryMeasurableEquiv
    (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    ((Kernel.partialTraj (X := fun _ ↦ α) (trajDenseStep P hP e ι) 0 n ∘ₖ
      initialTrajHistoryKernel).map (denseTimeHistoryMeasurableEquiv n)) =
      augmentedPrefixKernel P e ι n := by
  induction n with
  | zero =>
      rw [Kernel.partialTraj_self, Kernel.id_comp]
      let : IsMarkovKernel (denseTimePrefixKernel P e ι 0) :=
        hP.isMarkovKernel_denseTimePrefixKernel P e ι 0
      rw [augmentedPrefixKernel,
        markovKernel_finZero (denseTimePrefixKernel P e ι 0)]
      have hconst : Kernel.const α (Measure.dirac (FiniteOrderedTimes.emptyPath α)) =
          Kernel.deterministic (fun _ : α ↦ FiniteOrderedTimes.emptyPath α)
            measurable_const := by
        ext x s hs
        simp only [Kernel.const_apply, Kernel.deterministic_apply,
          Measure.dirac_apply' _ hs]
      rw [initialTrajHistoryKernel, Kernel.deterministic_map, hconst, Kernel.id,
        Kernel.deterministic_prod_deterministic, Kernel.mapOfMeasurable_eq_map,
        Kernel.deterministic_map]
      · apply Kernel.deterministic_congr
        funext x i
        rcases i with ⟨i, hi⟩
        have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
        subst i
        rfl
      all_goals fun_prop
  | succ n ih =>
      let : IsMarkovKernel (denseStep P hP e ι n) :=
        isMarkovKernel_denseStep P hP e ι n
      let : IsMarkovKernel (augmentedPrefixKernel P e ι n) :=
        isMarkovKernel_augmentedPrefixKernel P hP e ι n
      rw [Kernel.partialTraj_succ_of_le (Nat.zero_le n)]
      rw [← Kernel.map_comp]
      rw [Kernel.comp_assoc]
      rw [← Kernel.map_comp_right]
      · rw [← Kernel.map_id' Kernel.id, Kernel.map_prod_map] <;> try fun_prop
        rw [← Kernel.map_comp]
        rw [← Kernel.map_comp_right]
        · have hfun :
              ((denseTimeHistoryMeasurableEquiv (α := α) (n + 1) :
                  (↑(Finset.Iic (n + 1)) → α) → DenseTimeHistory α (n + 1)) ∘
                IicProdIoc (X := fun _ ↦ α) n (n + 1)) ∘
                  Prod.map (fun a ↦ a)
                    (MeasurableEquiv.piSingleton (X := fun _ ↦ α) n) =
                denseTimeHistoryMeasurableEquiv (n + 1) ∘ rawTrajAppend n := by
              rfl
          rw [hfun, denseTimeHistoryMeasurableEquiv_rawTrajAppend]
          have hkraw :=
            (Kernel.map_apply_eq_iff_map_symm_apply_eq
              (Kernel.partialTraj (X := fun _ ↦ α) (trajDenseStep P hP e ι) 0 n ∘ₖ
                initialTrajHistoryKernel)
              (augmentedPrefixKernel P e ι n)).mp ih
          rw [hkraw, trajDenseStep, transport_traj_step, augmentedPrefixKernel_step]
          · exact (DenseTimeHistory.measurable_append n).comp
              ((denseTimeHistoryMeasurableEquiv n).measurable.prodMap measurable_id)
          · funext z
            change DenseTimeHistory.append n
              ((denseTimeHistoryMeasurableEquiv n)
                ((denseTimeHistoryMeasurableEquiv n).symm z.1), z.2) =
              DenseTimeHistory.append n z
            rw [MeasurableEquiv.apply_symm_apply]
        · exact measurable_id.prodMap
            (MeasurableEquiv.piSingleton (X := fun _ ↦ α) n).measurable
        · exact (denseTimeHistoryMeasurableEquiv (α := α) (n + 1)).measurable.comp
            measurable_IicProdIoc
      · exact measurable_IicProdIoc
      · exact (denseTimeHistoryMeasurableEquiv (α := α) (n + 1)).measurable

/-- Restrict an enumeration-ordered trajectory to its first `n` observations. -/
def enumeratedDenseTimePrefix (n : ℕ) (path : ℕ → α) : Fin n → α :=
  fun i ↦ path i

omit [StandardBorelSpace α] [Nonempty α] in
/-- Restriction to the first `n` enumeration coordinates is measurable. -/
theorem measurable_enumeratedDenseTimePrefix (n : ℕ) :
    Measurable (enumeratedDenseTimePrefix (α := α) n) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_pi_apply (X := fun _ : ℕ ↦ α) i

omit [StandardBorelSpace α] [Nonempty α] in
private theorem enumeratedDenseTimePrefix_dropInitialTrajCoordinate (n : ℕ) :
    enumeratedDenseTimePrefix (α := α) n ∘ dropInitialTrajCoordinate =
      Prod.snd ∘ DenseTimeHistory.historyEquiv n ∘
        denseTimeHistoryMeasurableEquiv n ∘ Preorder.frestrictLe n := by
  funext path i
  rfl

/-- The first `n` coordinates of the enumeration-ordered trajectory have exactly the prescribed
enumeration-prefix law. -/
theorem enumeratedDenseTimeTrajectory_map_prefix
    (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    (enumeratedDenseTimeTrajectory P hP e ι).map
        (enumeratedDenseTimePrefix (α := α) n) =
      denseTimePrefixKernel P e ι n := by
  let : IsMarkovKernel (denseTimePrefixKernel P e ι n) :=
    hP.isMarkovKernel_denseTimePrefixKernel P e ι n
  rw [enumeratedDenseTimeTrajectory, ← Kernel.map_comp_right]
  · rw [enumeratedDenseTimePrefix_dropInitialTrajCoordinate]
    rw [Kernel.map_comp_right]
    · rw [← Function.comp_assoc]
      rw [Kernel.map_comp_right _ (Preorder.measurable_frestrictLe n)
          ((DenseTimeHistory.historyEquiv n).measurable.comp
            (denseTimeHistoryMeasurableEquiv (α := α) n).measurable)]
      rw [trajDenseStep_map_frestrictLe]
      rw [Kernel.map_comp_right _
        (denseTimeHistoryMeasurableEquiv (α := α) n).measurable
        (DenseTimeHistory.historyEquiv n).measurable]
      rw [partialTraj_map_denseTimeHistoryMeasurableEquiv]
      rw [augmentedPrefixKernel_map_historyEquiv]
      rw [← Kernel.snd_eq, Kernel.snd_prod]
    · exact ((DenseTimeHistory.historyEquiv n).measurable.comp
        (denseTimeHistoryMeasurableEquiv (α := α) n).measurable).comp
          (Preorder.measurable_frestrictLe n)
    · exact measurable_snd
  · exact measurable_dropInitialTrajCoordinate
  · exact measurable_enumeratedDenseTimePrefix n

/-- Restrict a dense-time-labelled trajectory to the first `n` labels of an enumeration. -/
def denseTimeTrajectoryPrefix (e : ℕ ≃ D) (n : ℕ) (path : D → α) : Fin n → α :=
  fun i ↦ path (e i)

omit [StandardBorelSpace α] [Nonempty α] in
/-- Restriction to the first `n` dense-time labels is measurable. -/
theorem measurable_denseTimeTrajectoryPrefix (e : ℕ ≃ D) (n : ℕ) :
    Measurable (denseTimeTrajectoryPrefix (α := α) e n) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_pi_apply (X := fun _ : D ↦ α) (e i)

omit [StandardBorelSpace α] [Nonempty α] in
private theorem denseTimeTrajectoryPrefix_measurableEquivPath
    (e : ℕ ≃ D) (n : ℕ) :
    denseTimeTrajectoryPrefix (α := α) e n ∘
        CountableEnumeration.measurableEquivPath e α =
      enumeratedDenseTimePrefix n := by
  funext path i
  dsimp only [Function.comp_apply, denseTimeTrajectoryPrefix,
    enumeratedDenseTimePrefix]
  exact MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : D ↦ α) e path i

/-- Restricting the dense-time-labelled trajectory to the first `n` enumerated labels gives
exactly the prescribed enumeration-prefix law. -/
theorem denseTimeTrajectory_map_prefix
    (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    (denseTimeTrajectory P hP e ι).map
        (denseTimeTrajectoryPrefix e n) =
      denseTimePrefixKernel P e ι n := by
  rw [denseTimeTrajectory, ← Kernel.map_comp_right]
  · rw [denseTimeTrajectoryPrefix_measurableEquivPath]
    exact enumeratedDenseTimeTrajectory_map_prefix P hP e ι n
  · exact (CountableEnumeration.measurableEquivPath e α).measurable
  · exact measurable_denseTimeTrajectoryPrefix e n

end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess

end PortComputability
