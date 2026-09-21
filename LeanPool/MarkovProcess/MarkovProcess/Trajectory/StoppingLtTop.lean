/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Main

/-!
# The strong Markov property at a stopping time that may be infinite

Mathlib's stopping times take values in `WithTop ℝ≥0`, so a stopping time of the canonical
filtration on continuous-path space may be infinite, while the strong Markov property of
`MarkovProcess/Main.lean` is stated for finite, `ℝ≥0`-valued stopping times.  This file removes
that restriction on the event `{tau < ⊤}` where the time is finite, writing the finite value as
`(tau omega).untopD 0`:

* `IsFellerKernelSemigroup.continuousProcess_restrict_map_shift_stoppingTime_lt_top`: the
  restart identity, after restricting the law of the process to `A ∩ {tau < ⊤}` for an event `A`
  of the stopped sigma-algebra;
* `IsFellerKernelSemigroup.continuousProcess_condExp_shift_stoppingTime_lt_top`: the same fact
  in conditional-expectation form, for a bounded strongly measurable functional of the shifted
  path, with the indicator of `{tau < ⊤}` on both sides.
* `StoppingTime.lintegral_mul_indicator_of_restrict_map`: integration of a restricted restart
  identity against a nonnegative weight measurable at the conditioning sigma-algebra.

The route is truncation: `truncTime tau K` is the finite stopping time `min tau K`, and the
slices `stoppingTimeSlice A tau K` partition `A ∩ {tau < ⊤}` into countably many events on which
`tau` is finite and bounded by `K`.  On each slice the finite theorems of `Main.lean` apply, and
both sides of the restart identity are countably additive in the restricted measure; the
conditional-expectation form is then obtained from the slicewise restart identity through a
generic indicator bridge, `condExp_indicator_ae_eq_integral_kernel_of_restrict_map`.

Nothing is asserted about the event `{tau = ⊤}`: on it the shifted path is the path itself, and
neither statement constrains it.  No Hunt-process property is claimed.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Function

namespace MarkovProcess

/-! Generic stopping-time material: truncation at a deterministic horizon, the countable slicing
of the event where a `WithTop`-valued stopping time is finite, and the reassembly of restart
identities over the slices.  Nothing here is specific to path space. -/

namespace StoppingTime

section RestrictedRestartIntegral

variable {Omega beta : Type*} {m mOmega : MeasurableSpace Omega}
  {mBeta : MeasurableSpace beta}

/-- A restricted restart identity may be integrated against an arbitrary nonnegative weight
measurable at the conditioning sigma-algebra. -/
theorem lintegral_mul_indicator_of_restrict_map
    (mu : @Measure Omega mOmega) (kappa : @Kernel Omega beta mOmega mBeta)
    (Y : Omega → beta) (hY : @Measurable Omega beta mOmega mBeta Y)
    (hm : m ≤ mOmega) (S : Set Omega) (hS : MeasurableSet[m] S)
    (hJoint : ∀ A : Set Omega, MeasurableSet[m] A →
      (mu.restrict (A ∩ S)).map Y = kappa ∘ₘ (mu.restrict (A ∩ S)))
    (F : beta → ℝ≥0∞) (hF : Measurable F)
    (W : Omega → ℝ≥0∞) (hW : Measurable[m] W) :
    ∫⁻ omega, W omega * S.indicator (fun omega ↦ F (Y omega)) omega ∂mu =
      ∫⁻ omega, W omega * S.indicator
        (fun omega ↦ ∫⁻ y, F y ∂kappa omega) omega ∂mu := by
  have hSm : MeasurableSet S := hm S hS
  have hSet : ∀ A : Set Omega, MeasurableSet[m] A →
      ∫⁻ omega in A ∩ S, F (Y omega) ∂mu =
        ∫⁻ omega in A ∩ S, (∫⁻ y, F y ∂kappa omega) ∂mu := by
    intro A hA
    calc
      ∫⁻ omega in A ∩ S, F (Y omega) ∂mu =
          ∫⁻ y, F y ∂((mu.restrict (A ∩ S)).map Y) := by
            rw [lintegral_map hF hY]
      _ = ∫⁻ y, F y ∂(kappa ∘ₘ (mu.restrict (A ∩ S))) := by rw [hJoint A hA]
      _ = ∫⁻ omega in A ∩ S, (∫⁻ y, F y ∂kappa omega) ∂mu := by
        rw [Measure.comp_eq_comp_const_apply]
        exact Measure.lintegral_bind kappa.aemeasurable hF.aemeasurable
  refine @Measurable.ennreal_induction Omega m
    (fun W ↦ ∫⁻ omega, W omega * S.indicator (fun omega ↦ F (Y omega)) omega ∂mu =
      ∫⁻ omega, W omega * S.indicator
        (fun omega ↦ ∫⁻ y, F y ∂kappa omega) omega ∂mu) ?_ ?_ ?_ W hW
  · intro c A hA
    have hA' : MeasurableSet A := hm A hA
    have hAS : MeasurableSet (A ∩ S) := hA'.inter hSm
    have hleft : (fun omega ↦ A.indicator (fun _ ↦ c) omega *
          S.indicator (fun omega ↦ F (Y omega)) omega) =
        (A ∩ S).indicator (fun omega ↦ c * F (Y omega)) := by
      funext omega
      by_cases ha : omega ∈ A <;> by_cases hs : omega ∈ S <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, ha, hs]
    have hright : (fun omega ↦ A.indicator (fun _ ↦ c) omega *
          S.indicator (fun omega ↦ ∫⁻ y, F y ∂kappa omega) omega) =
        (A ∩ S).indicator (fun omega ↦ c * ∫⁻ y, F y ∂kappa omega) := by
      funext omega
      by_cases ha : omega ∈ A <;> by_cases hs : omega ∈ S <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, ha, hs]
    rw [hleft, hright, lintegral_indicator hAS, lintegral_indicator hAS]
    calc
      ∫⁻ omega in A ∩ S, c * F (Y omega) ∂mu =
          c * ∫⁻ omega in A ∩ S, F (Y omega) ∂mu :=
        lintegral_const_mul c (hF.comp hY)
      _ = c * ∫⁻ omega in A ∩ S, (∫⁻ y, F y ∂kappa omega) ∂mu := by
        rw [hSet A hA]
      _ = ∫⁻ omega in A ∩ S, c * (∫⁻ y, F y ∂kappa omega) ∂mu :=
        (lintegral_const_mul c hF.lintegral_kernel).symm
  · intro W Z _hdisj hWm hZm hWi hZi
    simp_rw [Pi.add_apply, add_mul]
    rw [lintegral_add_left]
    · rw [lintegral_add_left]
      · exact congrArg₂ (· + ·) hWi hZi
      · exact (hWm.mono hm le_rfl).mul (hF.lintegral_kernel.indicator hSm)
    · exact (hWm.mono hm le_rfl).mul ((hF.comp hY).indicator hSm)
  · intro W hWm hmono hWi
    change (∫⁻ omega, (⨆ n, W n omega) *
      S.indicator (fun omega ↦ F (Y omega)) omega ∂mu) = _
    rw [show (fun omega ↦ (⨆ n, W n omega) *
        S.indicator (fun omega ↦ F (Y omega)) omega) =
      fun omega ↦ ⨆ n, W n omega * S.indicator (fun omega ↦ F (Y omega)) omega by
        funext omega; exact ENNReal.iSup_mul (fun n ↦ W n omega) _]
    rw [show (fun omega ↦ (⨆ n, W n omega) * S.indicator
        (fun omega ↦ ∫⁻ y, F y ∂kappa omega) omega) =
      fun omega ↦ ⨆ n, W n omega * S.indicator
        (fun omega ↦ ∫⁻ y, F y ∂kappa omega) omega by
        funext omega; exact ENNReal.iSup_mul (fun n ↦ W n omega) _]
    rw [lintegral_iSup]
    · rw [lintegral_iSup]
      · exact iSup_congr fun n ↦ hWi n
      · exact fun n ↦ (hWm n).mono hm le_rfl |>.mul
          (hF.lintegral_kernel.indicator hSm)
      · exact fun i j hij omega ↦ mul_le_mul_left (hmono hij omega) _
    · exact fun n ↦ (hWm n).mono hm le_rfl |>.mul
        ((hF.comp hY).indicator hSm)
    · exact fun i j hij omega ↦ mul_le_mul_left (hmono hij omega) _

end RestrictedRestartIntegral

section Trunc

variable {Omega : Type*} {mOmega : MeasurableSpace Omega}

/-- A `WithTop ℝ≥0`-valued time truncated at the deterministic horizon `K`: the finite,
`ℝ≥0`-valued time equal to `tau omega` when that is at most `K`, and to `K` otherwise. -/
def truncTime (tau : Omega → WithTop NNReal) (K : NNReal) (omega : Omega) : NNReal :=
  (min (tau omega) (K : WithTop NNReal)).untopD 0

/-- The truncated time, read back in `WithTop ℝ≥0`, is the minimum of the time and the
horizon. -/
theorem coe_truncTime (tau : Omega → WithTop NNReal) (K : NNReal) (omega : Omega) :
    ((truncTime tau K omega : NNReal) : WithTop NNReal) = min (tau omega) (K : WithTop NNReal) := by
  have hne : min (tau omega) (K : WithTop NNReal) ≠ ⊤ := by
    intro htop
    have hle := min_le_right (tau omega) (K : WithTop NNReal)
    rw [htop, top_le_iff] at hle
    exact WithTop.coe_ne_top hle
  rw [truncTime]
  lift min (tau omega) (K : WithTop NNReal) to NNReal using hne with a ha
  rw [WithTop.untopD_coe]

/-- Below the horizon the truncated time is the untopped time itself. -/
theorem truncTime_eq_untopD {tau : Omega → WithTop NNReal} {K : NNReal} {omega : Omega}
    (h : tau omega ≤ (K : WithTop NNReal)) :
    truncTime tau K omega = (tau omega).untopD 0 := by
  rw [truncTime, min_eq_left h]

/-- The truncation of a stopping time at a deterministic horizon is a finite stopping time. -/
theorem isStoppingTime_truncTime {f : Filtration NNReal mOmega} {tau : Omega → WithTop NNReal}
    (htau : IsStoppingTime f tau) (K : NNReal) :
    IsStoppingTime f (fun omega ↦ ((truncTime tau K omega : NNReal) : WithTop NNReal)) := by
  simp only [coe_truncTime]
  exact htau.min_const K

/-- Pointwise equal stopping times have the same stopped sigma-algebra. -/
theorem measurableSpace_stoppingTime_congr {f : Filtration NNReal mOmega}
    {tau sigma : Omega → WithTop NNReal}
    (htau : IsStoppingTime f tau) (hsigma : IsStoppingTime f sigma)
    (h : ∀ omega, tau omega = sigma omega) :
    htau.measurableSpace = hsigma.measurableSpace := by
  have hfun : tau = sigma := funext h
  subst hfun
  rfl

/-- The stopped sigma-algebra of a truncated stopping time is the stopped sigma-algebra of the
minimum of the time and the constant horizon. -/
theorem measurableSpace_truncTime {f : Filtration NNReal mOmega} {tau : Omega → WithTop NNReal}
    (htau : IsStoppingTime f tau) (K : NNReal) :
    (isStoppingTime_truncTime htau K).measurableSpace = (htau.min_const K).measurableSpace :=
  measurableSpace_stoppingTime_congr _ _ (coe_truncTime tau K)

end Trunc

section Slices

variable {Omega : Type*} {mOmega : MeasurableSpace Omega} {f : Filtration NNReal mOmega}
  {tau : Omega → WithTop NNReal}

/-- The event that a stopping time is finite belongs to its stopped sigma-algebra: intersecting
it with `{tau ≤ i}` leaves that event unchanged. -/
theorem measurableSet_stoppingTime_lt_top (htau : IsStoppingTime f tau) :
    MeasurableSet[htau.measurableSpace] {omega | tau omega < ⊤} := by
  refine ⟨?_, fun i ↦ ?_⟩
  · have h : {omega | tau omega < ⊤} = {omega | tau omega = ⊤}ᶜ := by
      ext omega
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, lt_top_iff_ne_top]
    rw [h]
    exact htau.measurableSet_eq_top'.compl
  · have h : {omega | tau omega < ⊤} ∩ {omega | tau omega ≤ (i : WithTop NNReal)} =
        {omega | tau omega ≤ (i : WithTop NNReal)} :=
      Set.inter_eq_right.mpr fun omega homega ↦ lt_of_le_of_lt homega (WithTop.coe_lt_top i)
    rw [h]
    exact htau i

/-- The time-zero sigma-algebra of the filtration is contained in the stopped sigma-algebra of
every stopping time. -/
theorem filtration_zero_le_measurableSpace_stoppingTime (htau : IsStoppingTime f tau) :
    f 0 ≤ htau.measurableSpace := by
  intro s hs
  exact ⟨le_iSup f 0 s hs, fun i ↦ (f.mono zero_le s hs).inter (htau i)⟩

/-- The `K`-th slice of an event `A` of the stopped sigma-algebra of `tau`: the part of `A` on
which `tau` is at most `K` but larger than every smaller natural number.  These slices are
pairwise disjoint and exhaust `A ∩ {tau < ⊤}`. -/
def stoppingTimeSlice (A : Set Omega) (tau : Omega → WithTop NNReal) (K : ℕ) : Set Omega :=
  (A ∩ ⋂ j ∈ Set.Iio K, {omega | ((j : NNReal) : WithTop NNReal) < tau omega}) ∩
    {omega | tau omega ≤ ((K : NNReal) : WithTop NNReal)}

/-- Each slice of an event of the stopped sigma-algebra of `tau` lies in the stopped
sigma-algebra of `tau` truncated at the corresponding horizon. -/
theorem measurableSet_stoppingTimeSlice (htau : IsStoppingTime f tau) {A : Set Omega}
    (hA : MeasurableSet[htau.measurableSpace] A) (K : ℕ) :
    MeasurableSet[(htau.min_const ((K : NNReal))).measurableSpace] (stoppingTimeSlice A tau K) := by
  refine (htau.measurableSet_inter_le_const_iff _ ((K : NNReal))).mp ?_
  refine (hA.inter ?_).inter (htau.measurableSet_le' (K : NNReal))
  refine MeasurableSet.biInter (Set.to_countable _) fun j _ ↦ ?_
  exact htau.measurableSet_gt' (j : NNReal)

/-- Each slice of an event of the stopped sigma-algebra is measurable in the ambient
sigma-algebra. -/
theorem measurableSet_stoppingTimeSlice' (htau : IsStoppingTime f tau) {A : Set Omega}
    (hA : MeasurableSet[htau.measurableSpace] A) (K : ℕ) :
    MeasurableSet (stoppingTimeSlice A tau K) :=
  (htau.min_const ((K : NNReal))).measurableSpace_le _
    (measurableSet_stoppingTimeSlice htau hA K)

/-- The slices of an event are pairwise disjoint. -/
theorem pairwise_disjoint_stoppingTimeSlice (A : Set Omega) :
    Pairwise (Disjoint on (stoppingTimeSlice A tau)) := by
  have key : ∀ K L : ℕ, K < L →
      Disjoint (stoppingTimeSlice A tau K) (stoppingTimeSlice A tau L) := by
    intro K L h
    refine Set.disjoint_left.mpr fun omega hK hL ↦ ?_
    have h1 : tau omega ≤ ((K : NNReal) : WithTop NNReal) := hK.2
    have h2 : ((K : NNReal) : WithTop NNReal) < tau omega := by
      have hmem := hL.1.2
      simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hmem
      exact hmem K (Set.mem_Iio.mpr h)
    exact absurd h1 (not_le_of_gt h2)
  intro K L hKL
  rcases lt_or_gt_of_ne hKL with h | h
  · exact key K L h
  · exact (key L K h).symm

/-- The slices of an event `A` exhaust the part of `A` on which the stopping time is finite. -/
theorem iUnion_stoppingTimeSlice (A : Set Omega) :
    ⋃ K : ℕ, stoppingTimeSlice A tau K = A ∩ {omega | tau omega < ⊤} := by
  classical
  apply Set.eq_of_subset_of_subset
  · refine Set.iUnion_subset fun K omega homega ↦ ⟨homega.1.1, ?_⟩
    have hle : tau omega ≤ ((K : NNReal) : WithTop NNReal) := homega.2
    exact lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top (WithTop.coe_ne_top) hle)
  · rintro omega ⟨hA, hlt⟩
    lift tau omega to NNReal using hlt.ne with t ht
    have hex : ∃ K : ℕ, t ≤ (K : NNReal) := by
      obtain ⟨K, hK⟩ := exists_nat_ge (t : ℝ)
      exact ⟨K, by exact_mod_cast hK⟩
    refine Set.mem_iUnion.mpr ⟨Nat.find hex, ⟨hA, ?_⟩, ?_⟩
    · refine Set.mem_iInter₂.mpr fun j hj ↦ ?_
      show ((j : NNReal) : WithTop NNReal) < tau omega
      rw [← ht, WithTop.coe_lt_coe]
      exact lt_of_not_ge (Nat.find_min hex (Set.mem_Iio.mp hj))
    · show tau omega ≤ ((Nat.find hex : NNReal) : WithTop NNReal)
      rw [← ht, WithTop.coe_le_coe]
      exact Nat.find_spec hex

/-- On the `K`-th slice the time truncated at `K` is the untopped time itself. -/
theorem truncTime_eq_untopD_of_mem_stoppingTimeSlice {A : Set Omega} {K : ℕ} {omega : Omega}
    (h : omega ∈ stoppingTimeSlice A tau K) :
    truncTime tau (K : NNReal) omega = (tau omega).untopD 0 :=
  truncTime_eq_untopD h.2

end Slices

section Reassembly

variable {Omega beta : Type*} [MeasurableSpace Omega] [MeasurableSpace beta]

/-- A restart identity for the measure restricted to each member of a countable disjoint family
of measurable events holds for the measure restricted to their union: both sides of the identity
are countably additive in the restricted measure. -/
theorem map_restrict_iUnion_eq_comp_of_forall (mu : Measure Omega) (kappa : Kernel Omega beta)
    (g : Omega → beta) (hg : Measurable g) (D : ℕ → Set Omega)
    (hD : ∀ i, MeasurableSet (D i)) (hdisj : Pairwise (Disjoint on D))
    (h : ∀ i, (mu.restrict (D i)).map g = kappa ∘ₘ (mu.restrict (D i))) :
    (mu.restrict (⋃ i, D i)).map g = kappa ∘ₘ (mu.restrict (⋃ i, D i)) := by
  ext s hs
  rw [Measure.bind_apply hs kappa.aemeasurable, Measure.map_apply hg hs,
    Measure.restrict_apply (hg hs), Set.inter_iUnion,
    measure_iUnion (fun i j hij ↦ (hdisj hij).mono Set.inter_subset_right Set.inter_subset_right)
      (fun i ↦ (hg hs).inter (hD i)),
    lintegral_iUnion hD hdisj]
  refine tsum_congr fun i ↦ ?_
  rw [← Measure.restrict_apply (hg hs), ← Measure.map_apply hg hs, h i,
    Measure.bind_apply hs kappa.aemeasurable]

end Reassembly

end StoppingTime

open StoppingTime

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]
  [TopologicalSpace.PseudoMetrizableSpace alpha] [SecondCountableTopology alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

omit [TopologicalSpace.PseudoMetrizableSpace alpha] [SecondCountableTopology alpha] in
/-- The untopped value of a stopping time of the canonical filtration is Borel measurable. -/
theorem measurable_untopD_stoppingTime (tau : ContinuousPath alpha → WithTop NNReal)
    (htau : IsStoppingTime (canonicalFiltration (alpha := alpha)) tau) :
    Measurable (fun omega ↦ (tau omega).untopD 0) :=
  htau.measurable'.untopD 0

omit [TopologicalSpace.PseudoMetrizableSpace alpha] [SecondCountableTopology alpha] in
/-- Shifting a path by the untopped value of a stopping time of the canonical filtration is
Borel measurable. -/
theorem measurable_shift_untopD_stoppingTime (tau : ContinuousPath alpha → WithTop NNReal)
    (htau : IsStoppingTime (canonicalFiltration (alpha := alpha)) tau) :
    Measurable (fun omega ↦ shift ((tau omega).untopD 0) omega) :=
  measurable_shift_of_measurable _ (measurable_untopD_stoppingTime tau htau)

omit [TopologicalSpace.PseudoMetrizableSpace alpha] [SecondCountableTopology alpha] in
/-- Evaluating a path at the untopped value of a stopping time of the canonical filtration is
Borel measurable. -/
theorem measurable_eval_untopD_stoppingTime (tau : ContinuousPath alpha → WithTop NNReal)
    (htau : IsStoppingTime (canonicalFiltration (alpha := alpha)) tau) :
    Measurable (fun omega : ContinuousPath alpha ↦ omega ((tau omega).untopD 0)) :=
  measurable_eval_of_measurable _ (measurable_untopD_stoppingTime tau htau)

/-- The state at the untopped value of a stopping time of the canonical filtration is measurable
for the stopped sigma-algebra: where the time is finite this is the stopped value of the
progressively measurable coordinate process, and where it is infinite it is the time-zero
state. -/
theorem measurable_eval_untopD_stoppingTime_stopped
    (tau : ContinuousPath alpha → WithTop NNReal)
    (htau : IsStoppingTime (canonicalFiltration (alpha := alpha)) tau) :
    Measurable[htau.measurableSpace]
      (fun omega : ContinuousPath alpha ↦ omega ((tau omega).untopD 0)) := by
  intro B hB
  have hsplit : (fun omega : ContinuousPath alpha ↦ omega ((tau omega).untopD 0)) ⁻¹' B =
      ((stoppedValue (coordinateProcess (alpha := alpha)) tau) ⁻¹' B ∩
          {omega | tau omega < ⊤}) ∪
        ((coordinateProcess (alpha := alpha) 0) ⁻¹' B ∩ {omega | tau omega < ⊤}ᶜ) := by
    ext omega
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
      Set.mem_compl_iff, stoppedValue, coordinateProcess]
    by_cases h : tau omega = ⊤
    · rw [h]
      simp only [WithTop.untopD_top, lt_self_iff_false, and_false, not_false_eq_true, and_true,
        false_or]
    · have hlt : tau omega < ⊤ := lt_top_iff_ne_top.mpr h
      have hval : (tau omega).untopD 0 = (tau omega).untopA := by
        lift tau omega to NNReal using h with t
        rfl
      rw [hval]
      simp only [hlt, and_true, not_true_eq_false, and_false, or_false]
  rw [hsplit]
  refine MeasurableSet.union ?_ ?_
  · exact (measurable_stoppedValue progMeasurable_coordinateProcess htau hB).inter
      (measurableSet_stoppingTime_lt_top htau)
  · exact (filtration_zero_le_measurableSpace_stoppingTime htau _
      (measurable_coordinateProcess_canonicalFiltration 0 hB)).inter
      (measurableSet_stoppingTime_lt_top htau).compl

end ContinuousPath

namespace StoppingTime

section Bridge

variable {Omega beta E : Type*} {m : MeasurableSpace Omega}
  {mOmega : MeasurableSpace Omega} {mBeta : MeasurableSpace beta}
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- If the law of `Y` after restriction to an event is obtained by mixing `kappa`, then the
integral over that event of a bounded strongly measurable observable of `Y` is the integral over
it of the `kappa`-expectation of the observable. -/
theorem setIntegral_integral_kernel_of_restrict_map
    (mu : @Measure Omega mOmega) [IsFiniteMeasure mu]
    (kappa : @Kernel Omega beta mOmega mBeta)
    (Y : Omega → beta) (hY : @Measurable Omega beta mOmega mBeta Y) (A : Set Omega)
    (hJoint : (mu.restrict A).map Y = kappa ∘ₘ (mu.restrict A))
    (F : beta → E) (hF : StronglyMeasurable F) (C : Real) (hFC : ∀ y, ‖F y‖ ≤ C) :
    ∫ omega in A, (∫ y, F y ∂kappa omega) ∂mu = ∫ omega in A, F (Y omega) ∂mu := by
  have hfMeas : AEStronglyMeasurable (fun omega ↦ F (Y omega)) mu :=
    (hF.comp_measurable hY).aestronglyMeasurable
  have hfInt : Integrable (fun omega ↦ F (Y omega)) mu :=
    Integrable.of_bound hfMeas C (ae_of_all _ fun omega ↦ hFC (Y omega))
  have hFA : Integrable F ((mu.restrict A).map Y) := by
    rw [integrable_map_measure hF.aestronglyMeasurable hY.aemeasurable]
    exact hfInt.restrict
  have hFAComp : Integrable F (kappa ∘ₘ (mu.restrict A)) := by
    rw [← hJoint]
    exact hFA
  rw [Measure.comp_eq_comp_const_apply] at hFAComp
  have hIntegralComp := Kernel.integral_comp hFAComp
  calc
    ∫ omega in A, (∫ y, F y ∂kappa omega) ∂mu =
        ∫ omega, (∫ y, F y ∂kappa omega) ∂(mu.restrict A) := rfl
    _ = ∫ y, F y ∂(kappa ∘ₘ (mu.restrict A)) := by
      rw [Measure.comp_eq_comp_const_apply]
      simpa only [Kernel.const_apply] using hIntegralComp.symm
    _ = ∫ y, F y ∂((mu.restrict A).map Y) := by rw [hJoint]
    _ = ∫ omega, F (Y omega) ∂(mu.restrict A) := by
      rw [integral_map hY.aemeasurable hF.aestronglyMeasurable]
    _ = ∫ omega in A, F (Y omega) ∂mu := rfl

/-- If the law of `Y` after restriction to the intersection of `S` with every conditioning event
is obtained by mixing `kappa`, then the conditional expectation of the `S`-indicator of a bounded
strongly measurable observable of `Y` is the `S`-indicator of that observable's
`kappa`-expectation.  This is the indicator form of
`condExp_comp_ae_eq_integral_kernel_of_restrict_map`; nothing is asserted off `S`. -/
theorem condExp_indicator_ae_eq_integral_kernel_of_restrict_map
    (mu : @Measure Omega mOmega) [IsFiniteMeasure mu]
    (kappa : @Kernel Omega beta mOmega mBeta) [IsMarkovKernel kappa]
    (Y : Omega → beta) (hY : @Measurable Omega beta mOmega mBeta Y)
    (hm : m ≤ mOmega) (S : Set Omega) (hS : MeasurableSet[m] S)
    (hJoint : ∀ A : Set Omega, MeasurableSet[m] A →
      (mu.restrict (A ∩ S)).map Y = kappa ∘ₘ (mu.restrict (A ∩ S)))
    (F : beta → E) (hF : StronglyMeasurable F)
    (hFm : StronglyMeasurable[m] (fun omega ↦ ∫ y, F y ∂kappa omega))
    (C : Real) (hFC : ∀ y, ‖F y‖ ≤ C) :
    mu[S.indicator (fun omega ↦ F (Y omega))|m] =ᵐ[mu]
      S.indicator (fun omega ↦ ∫ y, F y ∂kappa omega) := by
  have hSm : MeasurableSet S := hm S hS
  have hfMeas : AEStronglyMeasurable (S.indicator (fun omega ↦ F (Y omega))) mu :=
    ((hF.comp_measurable hY).indicator hSm).aestronglyMeasurable
  have hbound : ∀ omega, ‖S.indicator (fun omega ↦ F (Y omega)) omega‖ ≤ max C 0 := by
    intro omega
    by_cases homega : omega ∈ S
    · rw [Set.indicator_of_mem homega]
      exact le_trans (hFC (Y omega)) (le_max_left C 0)
    · rw [Set.indicator_of_notMem homega, norm_zero]
      exact le_max_right C 0
  have hfInt : Integrable (S.indicator (fun omega ↦ F (Y omega))) mu :=
    Integrable.of_bound hfMeas (max C 0) (ae_of_all _ hbound)
  have hgMeas : AEStronglyMeasurable[m] (S.indicator (fun omega ↦ ∫ y, F y ∂kappa omega)) mu :=
    (hFm.indicator hS).aestronglyMeasurable
  have hgbound : ∀ omega, ‖S.indicator (fun omega ↦ ∫ y, F y ∂kappa omega) omega‖ ≤ max C 0 := by
    intro omega
    by_cases homega : omega ∈ S
    · rw [Set.indicator_of_mem homega]
      refine le_trans ?_ (le_max_left C 0)
      simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
        norm_integral_le_of_norm_le_const (μ := kappa omega) (ae_of_all _ hFC)
    · rw [Set.indicator_of_notMem homega, norm_zero]
      exact le_max_right C 0
  refine (ae_eq_condExp_of_forall_setIntegral_eq
    (m := m) (m₀ := mOmega) (μ := mu) hm hfInt ?_ ?_ hgMeas).symm
  · intro A _hA _hmuA
    exact (Integrable.of_bound (hgMeas.mono hm) (max C 0) (ae_of_all _ hgbound)).restrict
  · intro A hA _hmuA
    rw [setIntegral_indicator hSm, setIntegral_indicator hSm]
    exact setIntegral_integral_kernel_of_restrict_map mu kappa Y hY (A ∩ S) (hJoint A hA) F hF C hFC

end Bridge

end StoppingTime

namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- **Strong Markov property at a stopping time that may be infinite, in restart form.**  Let
`tau` be a stopping time of the canonical filtration on continuous-path space, possibly taking
the value `⊤`, and let `A` be an event of its stopped sigma-algebra.  After restricting the law
of the process to the part of `A` on which `tau` is finite, the law of the path shifted by
`(tau omega).untopD 0` is the process started from the state at that time.  On the event
`{tau = ⊤}` nothing is asserted. -/
theorem IsFellerKernelSemigroup.continuousProcess_restrict_map_shift_stoppingTime_lt_top
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (x : alpha) (tau : ContinuousPath alpha → WithTop NNReal)
    (htau : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha)) tau)
    (A : Set (ContinuousPath alpha)) (hA : MeasurableSet[htau.measurableSpace] A) :
    (((continuousProcess P hP) x).restrict (A ∩ {omega | tau omega < ⊤})).map
        (fun omega ↦ ContinuousPath.shift ((tau omega).untopD 0) omega) =
      Kernel.comap (continuousProcess P hP) (fun omega ↦ omega ((tau omega).untopD 0))
          (ContinuousPath.measurable_eval_untopD_stoppingTime tau htau) ∘ₘ
        (((continuousProcess P hP) x).restrict (A ∩ {omega | tau omega < ⊤})) := by
  have hslice : ∀ K : ℕ,
      ((((continuousProcess P hP) x).restrict (stoppingTimeSlice A tau K)).map
          (fun omega ↦ ContinuousPath.shift ((tau omega).untopD 0) omega)) =
        Kernel.comap (continuousProcess P hP) (fun omega ↦ omega ((tau omega).untopD 0))
            (ContinuousPath.measurable_eval_untopD_stoppingTime tau htau) ∘ₘ
          (((continuousProcess P hP) x).restrict (stoppingTimeSlice A tau K)) := by
    intro K
    have hDK : MeasurableSet (stoppingTimeSlice A tau K) :=
      measurableSet_stoppingTimeSlice' htau hA K
    have hAK : MeasurableSet[(isStoppingTime_truncTime htau (K : NNReal)).measurableSpace]
        (stoppingTimeSlice A tau K) := by
      rw [measurableSpace_truncTime htau (K : NNReal)]
      exact measurableSet_stoppingTimeSlice htau hA K
    have hmain := hFeller.continuousProcess_restrict_map_shift_stoppingTime P hP hK x
      (truncTime tau (K : NNReal)) (isStoppingTime_truncTime htau (K : NNReal))
      (stoppingTimeSlice A tau K) hAK
    have hL : ((((continuousProcess P hP) x).restrict (stoppingTimeSlice A tau K)).map
          (fun omega ↦ ContinuousPath.shift (truncTime tau (K : NNReal) omega) omega)) =
        ((((continuousProcess P hP) x).restrict (stoppingTimeSlice A tau K)).map
          (fun omega ↦ ContinuousPath.shift ((tau omega).untopD 0) omega)) := by
      refine Measure.map_congr ((ae_restrict_iff' hDK).mpr (ae_of_all _ fun omega homega ↦ ?_))
      exact congrArg (fun s ↦ ContinuousPath.shift s omega)
        (truncTime_eq_untopD_of_mem_stoppingTimeSlice homega)
    have hR : (Kernel.comap (continuousProcess P hP)
            (fun omega ↦ omega (truncTime tau (K : NNReal) omega))
            (ContinuousPath.measurable_eval_stoppingTime_borel (truncTime tau (K : NNReal))
              (isStoppingTime_truncTime htau (K : NNReal))) ∘ₘ
          (((continuousProcess P hP) x).restrict (stoppingTimeSlice A tau K))) =
        Kernel.comap (continuousProcess P hP) (fun omega ↦ omega ((tau omega).untopD 0))
            (ContinuousPath.measurable_eval_untopD_stoppingTime tau htau) ∘ₘ
          (((continuousProcess P hP) x).restrict (stoppingTimeSlice A tau K)) := by
      refine Measure.comp_congr ((ae_restrict_iff' hDK).mpr (ae_of_all _ fun omega homega ↦ ?_))
      simp only [Kernel.comap_apply]
      rw [truncTime_eq_untopD_of_mem_stoppingTimeSlice homega]
    rw [← hL, hmain, hR]
  rw [← iUnion_stoppingTimeSlice (tau := tau) A]
  exact map_restrict_iUnion_eq_comp_of_forall _ _ _
    (ContinuousPath.measurable_shift_untopD_stoppingTime tau htau) (stoppingTimeSlice A tau)
    (fun K ↦ measurableSet_stoppingTimeSlice' htau hA K)
    (pairwise_disjoint_stoppingTimeSlice A) hslice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/-- **Strong Markov property at a stopping time that may be infinite, in
conditional-expectation form.**  For a bounded strongly measurable functional `F` of the path
and a stopping time `tau` of the canonical filtration that may take the value `⊤`, the
conditional expectation, given the stopped sigma-algebra, of the indicator of `{tau < ⊤}` times
`F` of the path shifted by `(tau omega).untopD 0` is the indicator of `{tau < ⊤}` times the
expectation of `F` under the process started from the state at that time. -/
theorem IsFellerKernelSemigroup.continuousProcess_condExp_shift_stoppingTime_lt_top
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (x : alpha) (tau : ContinuousPath alpha → WithTop NNReal)
    (htau : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha)) tau)
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : Real) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    ((continuousProcess P hP) x)[Set.indicator {omega | tau omega < ⊤}
        (fun omega ↦ F (ContinuousPath.shift ((tau omega).untopD 0) omega))|
          htau.measurableSpace] =ᵐ[(continuousProcess P hP) x]
      Set.indicator {omega | tau omega < ⊤}
        (fun omega ↦ ∫ eta, F eta ∂(continuousProcess P hP) (omega ((tau omega).untopD 0))) := by
  have hkappa := condExp_indicator_ae_eq_integral_kernel_of_restrict_map
    ((continuousProcess P hP) x)
    (Kernel.comap (continuousProcess P hP) (fun omega ↦ omega ((tau omega).untopD 0))
      (ContinuousPath.measurable_eval_untopD_stoppingTime tau htau))
    (fun omega ↦ ContinuousPath.shift ((tau omega).untopD 0) omega)
    (ContinuousPath.measurable_shift_untopD_stoppingTime tau htau)
    htau.measurableSpace_le {omega | tau omega < ⊤} (measurableSet_stoppingTime_lt_top htau)
    (fun A hA ↦ hFeller.continuousProcess_restrict_map_shift_stoppingTime_lt_top P hP hK x tau
      htau A hA)
    F hF ?_ C hFC
  · simpa only [Kernel.comap_apply] using hkappa
  · have hBase : StronglyMeasurable[htau.measurableSpace]
        (fun omega ↦ ∫ eta, F eta ∂(continuousProcess P hP) (omega ((tau omega).untopD 0))) :=
      hF.integral_kernel.comp_measurable
        (ContinuousPath.measurable_eval_untopD_stoppingTime_stopped tau htau)
    simpa only [Kernel.comap_apply] using hBase

end

end SubMarkovKernelSemigroup

end MarkovProcess
