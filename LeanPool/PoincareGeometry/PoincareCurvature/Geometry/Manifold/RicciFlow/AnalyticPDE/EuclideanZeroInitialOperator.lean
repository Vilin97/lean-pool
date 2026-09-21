/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanMildFiniteBanach
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.GlobalSourceSlice

/-!
# The zero-initial Euclidean heat solution operator

This file turns the heat-kernel Duhamel construction into a bounded linear
map from global parabolic `C^{0,α}` source data to the genuine finite-cylinder
`C^{2+α,1+α/2}` Banach space.  It is the constant-principal-part inverse used
in the coordinate parametrix for the manifold tensor heat operator.
-/

@[expose] public noncomputable section
open Real Set MeasureTheory Metric Filter
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

section ScalarZeroInitial

variable {n : ℕ}

/-- The identically-zero bounded `C²` initial datum. -/
def euclideanZeroC2Data (n : ℕ) : EuclideanBoundedC2Data n where
  value := 0
  first := fun _ => 0
  second := fun _ _ => 0
  hasDeriv_value := by
    intro k x
    simpa using (hasDerivAt_const (x := x k) (c := (0 : ℝ)))
  hasDeriv_first := by
    intro j k x
    simpa using (hasDerivAt_const (x := x j) (c := (0 : ℝ)))

@[simp] theorem euclideanZeroC2Data_value :
    (euclideanZeroC2Data n).value = 0 := rfl

@[simp] theorem euclideanZeroC2Data_first (k : Fin n) :
    (euclideanZeroC2Data n).first k = 0 := rfl

@[simp] theorem euclideanZeroC2Data_second (j k : Fin n) :
    (euclideanZeroC2Data n).second j k = 0 := rfl

theorem euclideanZeroC2Data_secondHolder (α : ℝ) :
    ∀ j k x y,
      |(euclideanZeroC2Data n).second j k x -
          (euclideanZeroC2Data n).second j k y| ≤
        0 * ∑ ell : Fin n, |(x - y) ell| ^ α := by
  intro j k x y
  simp

/-- The global source class, read as a continuous path of bounded spatial
functions. -/
def globalScalarSourcePath (hα : 0 < α)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) :
    ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  ParabolicC0AlphaBanach.globalTimeSlice hα q

@[simp] theorem globalScalarSourcePath_apply (hα : 0 < α)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) (t : ℝ) (x : Fin n → ℝ) :
    globalScalarSourcePath hα q t x =
      ParabolicC0AlphaBanach.evalCLM (t, x) (Set.mem_univ (t, x)) q := rfl

theorem continuous_globalScalarSourcePath (hα : 0 < α)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) :
    Continuous (globalScalarSourcePath hα q) :=
  ParabolicC0AlphaBanach.continuous_globalTimeSlice hα q

theorem globalScalarSourcePath_bounded (hα : 0 < α)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) (s : ℝ) (y : Fin n → ℝ) :
    ‖globalScalarSourcePath hα q s y‖ ≤ ‖q‖ :=
  ParabolicC0AlphaBanach.norm_globalTimeSlice_apply_le hα q s y

/-- The Euclidean sup norm is bounded by the coordinate `ℓ¹` norm, and hence
the global parabolic Hölder estimate supplies the coordinate-sum spatial
estimate expected by the heat-kernel Schauder theorem. -/
theorem globalScalarSourcePath_spatialHolder (hα : 0 < α) (hα1 : α < 1)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) (s : ℝ)
    (x y : Fin n → ℝ) :
    |globalScalarSourcePath hα q s y - globalScalarSourcePath hα q s x| ≤
      ‖q‖ * ∑ ell : Fin n, |(x - y) ell| ^ α := by
  have hglobal := q.global_eval_parabolicHolderWith
    (Set.mem_univ (s, y)) (Set.mem_univ (s, x))
  rw [parabolicDistance.same_time] at hglobal
  have hl1 : ‖y - x‖ ≤ ∑ ell : Fin n, |(x - y) ell| := by
    rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg ((x - y) i))]
    intro i
    calc
      ‖(y - x) i‖ = |(x - y) i| := by simp [abs_sub_comm]
      _ ≤ ∑ ell : Fin n, |(x - y) ell| :=
        Finset.single_le_sum (fun j _ => abs_nonneg ((x - y) j)) (Finset.mem_univ i)
  have hpow := Real.rpow_le_rpow (norm_nonneg (y - x)) hl1 hα.le
  have hsum :
      (∑ ell : Fin n, |(x - y) ell|) ^ α ≤
        ∑ ell : Fin n, |(x - y) ell| ^ α := by
    classical
    let f : Fin n → ℝ := fun ell => |(x - y) ell|
    change (∑ ell : Fin n, f ell) ^ α ≤ ∑ ell : Fin n, f ell ^ α
    generalize (Finset.univ : Finset (Fin n)) = S
    induction S using Finset.induction_on with
    | empty => simp [Real.zero_rpow hα.ne']
    | @insert a S ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        exact (Real.rpow_add_le_add_rpow (abs_nonneg _)
          (Finset.sum_nonneg fun i _ => abs_nonneg _) hα.le hα1.le).trans
            (add_le_add_right ih (f a ^ α))
  calc
    |globalScalarSourcePath hα q s y - globalScalarSourcePath hα q s x|
        ≤ ‖q‖ * ‖y - x‖ ^ α := by
          simpa [globalScalarSourcePath, Real.norm_eq_abs, dist_eq_norm] using hglobal
    _ ≤ ‖q‖ * (∑ ell : Fin n, |(x - y) ell|) ^ α :=
      mul_le_mul_of_nonneg_left hpow (norm_nonneg q)
    _ ≤ ‖q‖ * ∑ ell : Fin n, |(x - y) ell| ^ α :=
      mul_le_mul_of_nonneg_left hsum (norm_nonneg q)

theorem globalScalarSourcePath_parabolicHolder (hα : 0 < α)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) {t₀ T : ℝ} :
    ParabolicHolderWith ‖q‖ α
      (fun z : ℝ × (Fin n → ℝ) => globalScalarSourcePath hα q z.1 z.2)
      (euclideanMildFiniteCylinderND n t₀ T) := by
  intro p hp z hz
  simpa [globalScalarSourcePath] using
    q.global_eval_parabolicHolderWith (Set.mem_univ p) (Set.mem_univ z)

/-- The explicit zero-initial Duhamel solution in the finite-cylinder higher
parabolic Banach space. -/
def euclideanZeroInitialSolution
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) :
    FiniteParabolicC2AlphaBanach (Fin n → ℝ) ℝ t₀ T α :=
  heatMildFiniteBanachND hT.le hα hα1 (euclideanZeroC2Data n)
    (H₀ := 0) (show (0 : ℝ) ≤ 0 by norm_num) (euclideanZeroC2Data_secondHolder α)
    (continuous_globalScalarSourcePath hα q)
    (C := ‖q‖) (H := ‖q‖) (Hq := ‖q‖)
    (norm_nonneg q) (norm_nonneg q) (norm_nonneg q)
    (globalScalarSourcePath_bounded hα q)
    (globalScalarSourcePath_spatialHolder hα hα1 q)
    (globalScalarSourcePath_parabolicHolder hα q)

@[simp] theorem euclideanZeroInitialSolution_value
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
      (Set.univ : Set (ℝ × (Fin n → ℝ))))
    {z : ℝ × (Fin n → ℝ)}
    (hz : z ∈ parabolicFiniteCylinder (Fin n → ℝ) t₀ T) :
    FiniteParabolicC2AlphaBanach.value
        (euclideanZeroInitialSolution hT hα hα1 q) z =
      heatMildSpaceTimeND t₀ 0 (globalScalarSourcePath hα q) z := by
  exact heatMildFiniteBanachND_value hT.le hα hα1 (euclideanZeroC2Data n)
    (show (0 : ℝ) ≤ 0 by norm_num) (euclideanZeroC2Data_secondHolder α)
    (continuous_globalScalarSourcePath hα q)
    (norm_nonneg q) (norm_nonneg q) (norm_nonneg q)
    (globalScalarSourcePath_bounded hα q)
    (globalScalarSourcePath_spatialHolder hα hα1 q)
    (globalScalarSourcePath_parabolicHolder hα q) hz

theorem euclideanZeroInitialSolution_heatEquation
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
      (Set.univ : Set (ℝ × (Fin n → ℝ))))
    {t : ℝ} (ht : t ∈ Set.Ioc t₀ T) (x : Fin n → ℝ) :
    FiniteParabolicC2AlphaBanach.timeDeriv
        (euclideanZeroInitialSolution hT hα hα1 q) (t, x) =
      (∑ k : Fin n,
        FiniteParabolicC2AlphaBanach.spaceSecondDeriv
            (euclideanZeroInitialSolution hT hα hα1 q) (t, x)
          (Pi.single k 1) (Pi.single k 1)) + globalScalarSourcePath hα q t x := by
  exact heatMildFiniteBanachND_heatEquation hT.le hα hα1
    (euclideanZeroC2Data n) (show (0 : ℝ) ≤ 0 by norm_num)
    (euclideanZeroC2Data_secondHolder α)
    (continuous_globalScalarSourcePath hα q)
    (norm_nonneg q) (norm_nonneg q) (norm_nonneg q)
    (globalScalarSourcePath_bounded hα q)
    (globalScalarSourcePath_spatialHolder hα hα1 q)
    (globalScalarSourcePath_parabolicHolder hα q) ht x

theorem norm_euclideanZeroInitialSolution_le
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) :
    ‖euclideanZeroInitialSolution hT hα hα1 q‖ ≤
      heatMildC2AlphaNormConstantND n t₀ T α 0 ‖q‖ ‖q‖ ‖q‖
        (euclideanZeroC2Data n) := by
  exact norm_heatMildFiniteBanachND_le hT.le hα hα1
    (euclideanZeroC2Data n) (show (0 : ℝ) ≤ 0 by norm_num)
    (euclideanZeroC2Data_secondHolder α)
    (continuous_globalScalarSourcePath hα q)
    (norm_nonneg q) (norm_nonneg q) (norm_nonneg q)
    (globalScalarSourcePath_bounded hα q)
    (globalScalarSourcePath_spatialHolder hα hα1 q)
    (globalScalarSourcePath_parabolicHolder hα q)

/-- The value trajectory of the zero-initial solution on the closed time
interval, including its strong `C_b` trace at `t₀`. -/
def euclideanZeroInitialValuePathIcc
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) :
    BoundedContinuousFunction (↥(Set.Icc t₀ T))
      (BoundedContinuousFunction (Fin n → ℝ) ℝ) :=
  heatMildValuePathBcfIcc t₀ T 0 (L := 0)
    (show (0 : ℝ) ≤ 0 by norm_num) (by intro a b; simp)
    (continuous_globalScalarSourcePath hα q)
    (globalScalarSourcePath_bounded hα q)

@[simp] theorem euclideanZeroInitialValuePathIcc_initial
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) :
    euclideanZeroInitialValuePathIcc hT hα q
      ⟨t₀, le_rfl, hT.le⟩ = 0 := by
  change heatMildValuePathBcf t₀ 0
    (continuous_globalScalarSourcePath hα q)
    (globalScalarSourcePath_bounded hα q) t₀ = 0
  exact heatMildValuePathBcf_initial t₀ 0
    (continuous_globalScalarSourcePath hα q)
    (globalScalarSourcePath_bounded hα q)

/-- At every positive time, the closed value trajectory is exactly the value
component of the packaged `C^{2+α,1+α/2}` solution. -/
theorem euclideanZeroInitialValuePathIcc_eq_solution
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
      (Set.univ : Set (ℝ × (Fin n → ℝ))))
    (t : ↥(Set.Ioc t₀ T)) (x : Fin n → ℝ) :
    euclideanZeroInitialValuePathIcc hT hα q
        ⟨t, (Set.mem_Ioc.mp t.2).1.le, (Set.mem_Ioc.mp t.2).2⟩ x =
      FiniteParabolicC2AlphaBanach.value
        (euclideanZeroInitialSolution hT hα hα1 q) (t, x) := by
  rw [euclideanZeroInitialSolution_value hT hα hα1 q
    (by simp [parabolicFiniteCylinder, t.2])]
  change heatMildValuePathBcf t₀ 0
      (continuous_globalScalarSourcePath hα q)
      (globalScalarSourcePath_bounded hα q) (t : ℝ) x =
    heatMildSpaceTimeND t₀ 0 (globalScalarSourcePath hα q) (t, x)
  rw [heatMildValuePathBcf_of_lt (Set.mem_Ioc.mp t.2).1 0
      (continuous_globalScalarSourcePath hα q)
      (globalScalarSourcePath_bounded hα q),
    heatMildValueNDbcf_apply]
  rfl

/-- Linearity of the zero-initial Duhamel formula in its global source. -/
theorem heatMildSpaceTimeND_zero_global_add
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α)
    (q r : ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
      (Set.univ : Set (ℝ × (Fin n → ℝ))))
    {z : ℝ × (Fin n → ℝ)}
    (hz : z ∈ parabolicFiniteCylinder (Fin n → ℝ) t₀ T) :
    heatMildSpaceTimeND t₀ 0 (globalScalarSourcePath hα (q + r)) z =
      heatMildSpaceTimeND t₀ 0 (globalScalarSourcePath hα q) z +
        heatMildSpaceTimeND t₀ 0 (globalScalarSourcePath hα r) z := by
  rcases z with ⟨t, x⟩
  have ht : t₀ < t := (mem_parabolicFiniteCylinder.mp hz).1
  have hqi := intervalIntegrable_heatSemigroupND_duhamel ht.le
    (continuous_globalScalarSourcePath hα q)
    (globalScalarSourcePath_bounded hα q) x
  have hri := intervalIntegrable_heatSemigroupND_duhamel ht.le
    (continuous_globalScalarSourcePath hα r)
    (globalScalarSourcePath_bounded hα r) x
  have htne : ∀ᵐ (s : ℝ), s ≠ t := by
    have hset : {s : ℝ | ¬ s ≠ t} = {t} := by
      ext s
      simp
    rw [MeasureTheory.ae_iff, hset]
    exact MeasureTheory.measure_singleton t
  have hadd :
      (∫ s in t₀..t, heatSemigroupND (t - s)
          (globalScalarSourcePath hα (q + r) s) x) =
        (∫ s in t₀..t, heatSemigroupND (t - s)
          (globalScalarSourcePath hα q s) x) +
        ∫ s in t₀..t, heatSemigroupND (t - s)
          (globalScalarSourcePath hα r s) x := by
    calc
      (∫ s in t₀..t, heatSemigroupND (t - s)
          (globalScalarSourcePath hα (q + r) s) x) =
          ∫ s in t₀..t,
            (heatSemigroupND (t - s) (globalScalarSourcePath hα q s) x +
              heatSemigroupND (t - s) (globalScalarSourcePath hα r s) x) := by
            apply intervalIntegral.integral_congr_ae
            filter_upwards [htne] with s hst hmem
            rw [Set.uIoc_of_le ht.le] at hmem
            have hstlt : s < t := lt_of_le_of_ne hmem.2 hst
            rw [show globalScalarSourcePath hα (q + r) s =
                globalScalarSourcePath hα q s + globalScalarSourcePath hα r s by
              exact ParabolicC0AlphaBanach.globalTimeSlice_add hα q r s]
            have hm := congrArg
              (fun f : BoundedContinuousFunction (Fin n → ℝ) ℝ => f x)
              (map_add (heatSemigroupNDclm (show 0 < t - s by linarith))
                (globalScalarSourcePath hα q s) (globalScalarSourcePath hα r s))
            simpa using hm
      _ = _ := intervalIntegral.integral_add hqi hri
  change heatMildSpatialND t₀ t 0 (globalScalarSourcePath hα (q + r)) x =
    heatMildSpatialND t₀ t 0 (globalScalarSourcePath hα q) x +
      heatMildSpatialND t₀ t 0 (globalScalarSourcePath hα r) x
  unfold heatMildSpatialND
  rw [hadd]
  have hzero : heatSemigroupND (t - t₀)
      (⇑(0 : BoundedContinuousFunction (Fin n → ℝ) ℝ)) x = 0 := by
    change heatSemigroupND (t - t₀) (fun _ : Fin n → ℝ => 0) x = 0
    simpa using heatSemigroupND_smul (n := n) (t := t - t₀)
      0 (fun _ : Fin n → ℝ => 0) x
  rw [hzero]
  ring

/-- Homogeneity of the zero-initial Duhamel formula in its global source. -/
theorem heatMildSpaceTimeND_zero_global_smul
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (c : ℝ)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
      (Set.univ : Set (ℝ × (Fin n → ℝ))))
    {z : ℝ × (Fin n → ℝ)}
    (hz : z ∈ parabolicFiniteCylinder (Fin n → ℝ) t₀ T) :
    heatMildSpaceTimeND t₀ 0 (globalScalarSourcePath hα (c • q)) z =
      c • heatMildSpaceTimeND t₀ 0 (globalScalarSourcePath hα q) z := by
  rcases z with ⟨t, x⟩
  have hsmul : ∀ s : ℝ,
      heatSemigroupND (t - s) (globalScalarSourcePath hα (c • q) s) x =
        c * heatSemigroupND (t - s) (globalScalarSourcePath hα q s) x := by
    intro s
    rw [show globalScalarSourcePath hα (c • q) s =
        c • globalScalarSourcePath hα q s by
      exact ParabolicC0AlphaBanach.globalTimeSlice_smul hα c q s]
    exact heatSemigroupND_smul c (globalScalarSourcePath hα q s) x
  have hint :
      (∫ s in t₀..t, heatSemigroupND (t - s)
          (globalScalarSourcePath hα (c • q) s) x) =
        c * ∫ s in t₀..t,
          heatSemigroupND (t - s) (globalScalarSourcePath hα q s) x := by
    calc
      _ = ∫ s in t₀..t,
          c * heatSemigroupND (t - s) (globalScalarSourcePath hα q s) x := by
        apply intervalIntegral.integral_congr_ae
        exact Filter.Eventually.of_forall fun s _ => hsmul s
      _ = _ := intervalIntegral.integral_const_mul c _
  change heatMildSpatialND t₀ t 0 (globalScalarSourcePath hα (c • q)) x =
    c • heatMildSpatialND t₀ t 0 (globalScalarSourcePath hα q) x
  unfold heatMildSpatialND
  rw [hint]
  have hzero : heatSemigroupND (t - t₀)
      (⇑(0 : BoundedContinuousFunction (Fin n → ℝ) ℝ)) x = 0 := by
    change heatSemigroupND (t - t₀) (fun _ : Fin n → ℝ => 0) x = 0
    simpa using heatSemigroupND_smul (n := n) (t := t - t₀)
      0 (fun _ : Fin n → ℝ => 0) x
  rw [hzero]
  ring

@[simp] theorem euclideanZeroInitialSolution_add
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (q r : ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) :
    euclideanZeroInitialSolution hT hα hα1 (q + r) =
      euclideanZeroInitialSolution hT hα hα1 q +
        euclideanZeroInitialSolution hT hα hα1 r := by
  apply FiniteParabolicC2AlphaBanach.ext_value hα hT
  intro z hz
  rw [show FiniteParabolicC2AlphaBanach.value
      (euclideanZeroInitialSolution hT hα hα1 q +
        euclideanZeroInitialSolution hT hα hα1 r) z =
      FiniteParabolicC2AlphaBanach.value
          (euclideanZeroInitialSolution hT hα hα1 q) z +
        FiniteParabolicC2AlphaBanach.value
          (euclideanZeroInitialSolution hT hα hα1 r) z by
    exact FiniteParabolicC2AlphaAmbient.value_add _ _ z]
  rw [euclideanZeroInitialSolution_value hT hα hα1 (q + r) hz,
    euclideanZeroInitialSolution_value hT hα hα1 q hz,
    euclideanZeroInitialSolution_value hT hα hα1 r hz]
  exact heatMildSpaceTimeND_zero_global_add hT hα q r hz

@[simp] theorem euclideanZeroInitialSolution_smul
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (c : ℝ)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) :
    euclideanZeroInitialSolution hT hα hα1 (c • q) =
      c • euclideanZeroInitialSolution hT hα hα1 q := by
  apply FiniteParabolicC2AlphaBanach.ext_value hα hT
  intro z hz
  rw [show FiniteParabolicC2AlphaBanach.value
      (c • euclideanZeroInitialSolution hT hα hα1 q) z =
      c • FiniteParabolicC2AlphaBanach.value
        (euclideanZeroInitialSolution hT hα hα1 q) z by
    exact FiniteParabolicC2AlphaAmbient.value_smul _ _ z]
  rw [euclideanZeroInitialSolution_value hT hα hα1 (c • q) hz,
    euclideanZeroInitialSolution_value hT hα hα1 q hz]
  exact heatMildSpaceTimeND_zero_global_smul hT hα c q hz

/-- The explicit operator norm coefficient for the zero-initial Euclidean
Schauder inverse. -/
def euclideanZeroInitialSchauderConstant
    (n : ℕ) (t₀ T α : ℝ) : ℝ :=
  heatMildC2AlphaNormConstantND n t₀ T α 0 1 1 1
    (euclideanZeroC2Data n)

private theorem heatDuhamelHessianOldConstant_homogeneous
    (n : ℕ) (α a : ℝ) (j k : Fin n) :
    heatDuhamelHessianOldConstant n α a j k =
      a * heatDuhamelHessianOldConstant n α 1 j k := by
  unfold heatDuhamelHessianOldConstant
  ring

private theorem heatDuhamelHessianSpatialHolderEntryConstant_homogeneous
    (n : ℕ) (α a : ℝ) (j k : Fin n) :
    heatDuhamelHessianSpatialHolderEntryConstant n α a j k =
      a * heatDuhamelHessianSpatialHolderEntryConstant n α 1 j k := by
  unfold heatDuhamelHessianSpatialHolderEntryConstant
  rw [heatDuhamelHessianOldConstant_homogeneous]
  ring

private theorem heatDuhamelHessianSpatialHolderConstant_homogeneous
    (n : ℕ) (α a : ℝ) :
    heatDuhamelHessianSpatialHolderConstant n α a =
      a * heatDuhamelHessianSpatialHolderConstant n α 1 := by
  unfold heatDuhamelHessianSpatialHolderConstant
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact heatDuhamelHessianSpatialHolderEntryConstant_homogeneous n α a j k

private theorem heatDuhamelHessianTimeSmallEntryConstant_homogeneous
    (n : ℕ) (α a : ℝ) (j k : Fin n) :
    heatDuhamelHessianTimeSmallEntryConstant n α a j k =
      a * heatDuhamelHessianTimeSmallEntryConstant n α 1 j k := by
  unfold heatDuhamelHessianTimeSmallEntryConstant
  rw [heatDuhamelHessianOldConstant_homogeneous]
  ring

private theorem heatDuhamelHessianTimeLargeEntryConstant_homogeneous
    (n : ℕ) (α a : ℝ) (j k : Fin n) :
    heatDuhamelHessianTimeLargeEntryConstant n α a j k =
      a * heatDuhamelHessianTimeLargeEntryConstant n α 1 j k := by
  unfold heatDuhamelHessianTimeLargeEntryConstant
  ring

private theorem heatDuhamelHessianTimeHolderEntryConstant_homogeneous
    (n : ℕ) (α a : ℝ) (j k : Fin n) :
    heatDuhamelHessianTimeHolderEntryConstant n α a j k =
      a * heatDuhamelHessianTimeHolderEntryConstant n α 1 j k := by
  unfold heatDuhamelHessianTimeHolderEntryConstant
  rw [heatDuhamelHessianTimeSmallEntryConstant_homogeneous,
    heatDuhamelHessianTimeLargeEntryConstant_homogeneous]
  ring

private theorem heatDuhamelHessianTimeHolderConstant_homogeneous
    (n : ℕ) (α a : ℝ) :
    heatDuhamelHessianTimeHolderConstant n α a =
      a * heatDuhamelHessianTimeHolderConstant n α 1 := by
  unfold heatDuhamelHessianTimeHolderConstant
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact heatDuhamelHessianTimeHolderEntryConstant_homogeneous n α a j k

private theorem heatMildHessianParabolicHolderConstant_zero_homogeneous
    (n : ℕ) (α a : ℝ) :
    heatMildHessianParabolicHolderConstant n α 0 a =
      a * heatMildHessianParabolicHolderConstant n α 0 1 := by
  calc
    heatMildHessianParabolicHolderConstant n α 0 a =
        heatDuhamelHessianSpatialHolderConstant n α a +
          heatDuhamelHessianTimeHolderConstant n α a := by
      simp [heatMildHessianParabolicHolderConstant,
        heatInitialHessianSpatialHolderConstant,
        heatInitialHessianTimeHolderConstant]
    _ = a * heatDuhamelHessianSpatialHolderConstant n α 1 +
          a * heatDuhamelHessianTimeHolderConstant n α 1 := by
      rw [heatDuhamelHessianSpatialHolderConstant_homogeneous,
        heatDuhamelHessianTimeHolderConstant_homogeneous]
    _ = a * heatMildHessianParabolicHolderConstant n α 0 1 := by
      simp [heatMildHessianParabolicHolderConstant,
        heatInitialHessianSpatialHolderConstant,
        heatInitialHessianTimeHolderConstant]
      ring

private theorem heatMildHessianSupConstantND_zero_homogeneous
    (n : ℕ) (t₀ T α a : ℝ) :
    heatMildHessianSupConstantND t₀ T α a (euclideanZeroC2Data n) =
      a * heatMildHessianSupConstantND t₀ T α 1 (euclideanZeroC2Data n) := by
  unfold heatMildHessianSupConstantND
  simp only [euclideanZeroC2Data_second, norm_zero, Finset.sum_const_zero, zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem heatMildGradientSupConstantND_zero_homogeneous
    (n : ℕ) (t₀ T a : ℝ) :
    heatMildGradientSupConstantND t₀ T a (euclideanZeroC2Data n) =
      a * heatMildGradientSupConstantND t₀ T 1 (euclideanZeroC2Data n) := by
  unfold heatMildGradientSupConstantND
  simp [Finset.mul_sum]
  ring

private theorem heatMildValueSupConstantND_zero_homogeneous
    (n : ℕ) (t₀ T a : ℝ) :
    heatMildValueSupConstantND t₀ T a (euclideanZeroC2Data n) =
      a * heatMildValueSupConstantND t₀ T 1 (euclideanZeroC2Data n) := by
  simp [heatMildValueSupConstantND]

private theorem heatMildTimeDerivSupConstantND_zero_homogeneous
    (n : ℕ) (t₀ T α a : ℝ) :
    heatMildTimeDerivSupConstantND t₀ T α a a (euclideanZeroC2Data n) =
      a * heatMildTimeDerivSupConstantND t₀ T α 1 1 (euclideanZeroC2Data n) := by
  unfold heatMildTimeDerivSupConstantND
  rw [heatMildHessianSupConstantND_zero_homogeneous]
  ring

private theorem heatMildTimeDerivParabolicHolderConstantND_zero_homogeneous
    (n : ℕ) (α a : ℝ) :
    heatMildTimeDerivParabolicHolderConstantND n α 0 a a =
      a * heatMildTimeDerivParabolicHolderConstantND n α 0 1 1 := by
  unfold heatMildTimeDerivParabolicHolderConstantND
  rw [heatMildHessianParabolicHolderConstant_zero_homogeneous]
  ring

theorem heatMildC2AlphaNormConstantND_zero_eq_mul
    (qnorm : ℝ) :
    heatMildC2AlphaNormConstantND n t₀ T α 0 qnorm qnorm qnorm
        (euclideanZeroC2Data n) =
      euclideanZeroInitialSchauderConstant n t₀ T α * qnorm := by
  unfold euclideanZeroInitialSchauderConstant heatMildC2AlphaNormConstantND
    heatMildValueC0AlphaNormConstantND heatMildGradientC0AlphaNormConstantND
  rw [heatMildValueSupConstantND_zero_homogeneous,
    heatMildGradientSupConstantND_zero_homogeneous,
    heatMildHessianSupConstantND_zero_homogeneous,
    heatMildTimeDerivSupConstantND_zero_homogeneous,
    heatMildHessianParabolicHolderConstant_zero_homogeneous,
    heatMildTimeDerivParabolicHolderConstantND_zero_homogeneous]
  ring

theorem euclideanZeroInitialSchauderConstant_nonneg
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    0 ≤ euclideanZeroInitialSchauderConstant n t₀ T α := by
  have hBu := heatMildValueSupConstantND_nonneg hT.le zero_le_one
    (euclideanZeroC2Data n)
  have hBx := heatMildGradientSupConstantND_nonneg hT.le zero_le_one
    (euclideanZeroC2Data n)
  have hBxx := heatMildHessianSupConstantND_nonneg hT.le hα zero_le_one
    (euclideanZeroC2Data n)
  have hBt := heatMildTimeDerivSupConstantND_nonneg hT.le hα zero_le_one zero_le_one
    (euclideanZeroC2Data n)
  have hHess := heatMildHessianParabolicHolderConstant_nonneg n hα hα1
    (show (0 : ℝ) ≤ 0 by norm_num) zero_le_one
  have hTime := heatMildTimeDerivParabolicHolderConstantND_nonneg n hα hα1
    (show (0 : ℝ) ≤ 0 by norm_num) zero_le_one zero_le_one
  unfold euclideanZeroInitialSchauderConstant heatMildC2AlphaNormConstantND
    heatMildValueC0AlphaNormConstantND heatMildGradientC0AlphaNormConstantND
  positivity

/-- The algebraic zero-initial Duhamel solution map. -/
def euclideanZeroInitialLinearMap
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
        (Set.univ : Set (ℝ × (Fin n → ℝ))) →ₗ[ℝ]
      FiniteParabolicC2AlphaBanach (Fin n → ℝ) ℝ t₀ T α where
  toFun := euclideanZeroInitialSolution hT hα hα1
  map_add' := euclideanZeroInitialSolution_add hT hα hα1
  map_smul' := euclideanZeroInitialSolution_smul hT hα hα1

/-- The bounded zero-initial Euclidean Schauder inverse. -/
def euclideanZeroInitialOperator
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
        (Set.univ : Set (ℝ × (Fin n → ℝ))) →L[ℝ]
      FiniteParabolicC2AlphaBanach (Fin n → ℝ) ℝ t₀ T α :=
  LinearMap.mkContinuous (euclideanZeroInitialLinearMap hT hα hα1)
    (euclideanZeroInitialSchauderConstant n t₀ T α) (fun q =>
      (norm_euclideanZeroInitialSolution_le hT hα hα1 q).trans_eq
        (heatMildC2AlphaNormConstantND_zero_eq_mul ‖q‖))

@[simp] theorem euclideanZeroInitialOperator_apply
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) :
    euclideanZeroInitialOperator hT hα hα1 q =
      euclideanZeroInitialSolution hT hα hα1 q := rfl

theorem norm_euclideanZeroInitialOperator_le
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ‖euclideanZeroInitialOperator (n := n) hT hα hα1‖ ≤
      euclideanZeroInitialSchauderConstant n t₀ T α := by
  exact LinearMap.mkContinuous_norm_le _
    (euclideanZeroInitialSchauderConstant_nonneg hT hα hα1)
    _

/-- Trace of a Euclidean bilinear form on the standard orthonormal basis. -/
def euclideanBilinearTraceCLM (n : ℕ) :
    ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ :=
  ∑ k : Fin n,
    ((ContinuousLinearMap.apply ℝ ℝ) (Pi.single k 1)).comp
      ((ContinuousLinearMap.apply ℝ ((Fin n → ℝ) →L[ℝ] ℝ)) (Pi.single k 1))

@[simp] theorem euclideanBilinearTraceCLM_apply
    (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) :
    euclideanBilinearTraceCLM n A =
      ∑ k : Fin n, A (Pi.single k 1) (Pi.single k 1) := by
  simp [euclideanBilinearTraceCLM]

/-- The constant-coefficient Euclidean heat Cauchy operator `∂ₜ - Δ` on
the finite-cylinder higher parabolic Banach space. -/
def euclideanHeatCauchyL
    (n : ℕ) (t₀ T α : ℝ) :
    FiniteParabolicC2AlphaBanach (Fin n → ℝ) ℝ t₀ T α →L[ℝ]
      ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
        (parabolicFiniteCylinder (Fin n → ℝ) t₀ T) :=
  FiniteParabolicC2AlphaBanach.timeDerivComponentL -
    (ParabolicC0AlphaBanach.compL (euclideanBilinearTraceCLM n)).comp
      FiniteParabolicC2AlphaBanach.spaceSecondDerivComponentL

theorem evalCLM_euclideanHeatCauchyL
    {t₀ T α : ℝ}
    (u : FiniteParabolicC2AlphaBanach (Fin n → ℝ) ℝ t₀ T α)
    (z : ℝ × (Fin n → ℝ))
    (hz : z ∈ parabolicFiniteCylinder (Fin n → ℝ) t₀ T) :
    ParabolicC0AlphaBanach.evalCLM z hz (euclideanHeatCauchyL n t₀ T α u) =
      FiniteParabolicC2AlphaBanach.timeDeriv u z -
        ∑ k : Fin n, FiniteParabolicC2AlphaBanach.spaceSecondDeriv u z
          (Pi.single k 1) (Pi.single k 1) := by
  rw [euclideanHeatCauchyL, ContinuousLinearMap.sub_apply, map_sub,
    FiniteParabolicC2AlphaBanach.evalCLM_timeDerivComponentL,
    ContinuousLinearMap.comp_apply,
    ParabolicC0AlphaBanach.evalCLM_compL_apply,
    FiniteParabolicC2AlphaBanach.evalCLM_spaceSecondDerivComponentL,
    euclideanBilinearTraceCLM_apply]

/-- Restriction of a global source to the positive finite cylinder. -/
def restrictGlobalSourceToFiniteL
    (n : ℕ) (t₀ T α : ℝ) :
    ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
        (Set.univ : Set (ℝ × (Fin n → ℝ))) →L[ℝ]
      ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
        (parabolicFiniteCylinder (Fin n → ℝ) t₀ T) :=
  ParabolicC0AlphaBanach.restrictL (fun _ _ => Set.mem_univ _)

/-- The zero-initial Duhamel operator is a right inverse of `∂ₜ - Δ`, with
the global source restricted to the finite cylinder. -/
theorem euclideanHeatCauchyL_comp_zeroInitialOperator
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    (euclideanHeatCauchyL n t₀ T α).comp
        (euclideanZeroInitialOperator (n := n) hT hα hα1) =
      restrictGlobalSourceToFiniteL n t₀ T α := by
  ext q
  apply (ParabolicC0AlphaBanach.eq_iff_forall_evalCLM _ _).2
  intro z hz
  rcases z with ⟨t, x⟩
  have ht : t ∈ Set.Ioc t₀ T := by
    simpa [parabolicFiniteCylinder] using hz
  rw [ContinuousLinearMap.comp_apply, euclideanZeroInitialOperator_apply,
    evalCLM_euclideanHeatCauchyL]
  rw [euclideanZeroInitialSolution_heatEquation hT hα hα1 q ht x]
  unfold restrictGlobalSourceToFiniteL
  rw [ParabolicC0AlphaBanach.evalCLM_restrictL_apply
    (Set.subset_univ _) (t, x) hz q]
  simp [globalScalarSourcePath_apply]

end ScalarZeroInitial

end AnalyticPDE
end RicciFlow
