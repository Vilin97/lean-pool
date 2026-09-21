/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Main

/-!
# The deterministic drift semigroup and its continuous-path process

On a finite-dimensional real normed space the transition semigroup that translates by `t • v` in
time `t` is a conservative Feller semigroup satisfying the Kolmogorov moment criterion with
exponents `p = q = 2` and constant `‖v‖²`.  The existence-and-uniqueness theorem of
`MarkovProcess.Main` therefore applies, and the process it produces is identified: from every
starting point `x` its law is the Dirac mass at the straight line `t ↦ x + t • v`.

Together with `MarkovProcess.Examples.Identity` this shows that the hypotheses of the main
theorem are satisfiable by a semigroup that genuinely moves.  Nothing here is claimed about a
semigroup with a nonzero diffusion part; for that see `MarkovProcess.Examples.HeatSemigroup`.
-/

noncomputable section PortComputability

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section Definition

omit [FiniteDimensional ℝ E] in
/-- Translation by `t • v` is measurable. -/
theorem measurable_driftTranslate (v : E) (t : NNReal) :
    Measurable (fun x : E ↦ x + (t : ℝ) • v) := by
  fun_prop

/-- The deterministic drift semigroup with velocity `v`: at time `t` it moves every point by
`t • v`. -/
def driftSemigroup (v : E) : SubMarkovKernelSemigroup E where
  kernel := fun t ↦ Kernel.deterministic (fun x ↦ x + (t : ℝ) • v) (measurable_driftTranslate v t)
  measurable_kernel := by
    have hg : Measurable (fun p : NNReal × E ↦ p.2 + (p.1 : ℝ) • v) := by fun_prop
    exact (Kernel.deterministic (fun p : NNReal × E ↦ p.2 + (p.1 : ℝ) • v) hg).measurable
  kernel_zero := by
    refine Kernel.ext fun x ↦ ?_
    rw [Kernel.deterministic_apply, Kernel.id_apply, NNReal.coe_zero, zero_smul, add_zero]
  kernel_add := fun s t ↦ by
    rw [Kernel.deterministic_comp_deterministic]
    refine Kernel.ext fun x ↦ ?_
    rw [Kernel.deterministic_apply, Kernel.deterministic_apply, Function.comp_apply,
      NNReal.coe_add, add_smul, add_assoc]
  isSubMarkovKernel := fun _ ↦ IsSubMarkovKernel.of_isMarkovKernel _

/-- The transition measure of the drift semigroup is the Dirac mass at the translated point. -/
theorem driftSemigroup_apply (v : E) (t : NNReal) (x : E) :
    (driftSemigroup v) t x = Measure.dirac (x + (t : ℝ) • v) := rfl

/-- The drift semigroup is conservative: every transition measure has total mass one. -/
theorem isConservative_driftSemigroup (v : E) : (driftSemigroup v).IsConservative := by
  intro t x
  rw [driftSemigroup_apply]
  exact measure_univ

end Definition

section Feller

/-- Integrating a `C₀` function against the drift semigroup evaluates it at the translated
point. -/
theorem kernelIntegral_driftSemigroup_apply (v : E) (t : NNReal) (f : C₀(E, ℝ)) (x : E) :
    kernelIntegral ((driftSemigroup v) t) f x = f (x + (t : ℝ) • v) := by
  rw [kernelIntegral, driftSemigroup_apply]
  exact integral_dirac' (f : E → ℝ) _ f.continuous.stronglyMeasurable

/-- The `C₀` kernel integral of the drift semigroup is the translate of the function. -/
theorem kernelIntegral_driftSemigroup (v : E) (t : NNReal) (f : C₀(E, ℝ)) :
    kernelIntegral ((driftSemigroup v) t) f = fun x ↦ f (x + (t : ℝ) • v) :=
  funext (kernelIntegral_driftSemigroup_apply v t f)

/-- The drift semigroup maps `C₀` into itself: translating a continuous function vanishing at
infinity gives another one, because translation is a cocompact map. -/
theorem mapsC0_driftSemigroup (v : E) : (driftSemigroup v).MapsC0 := by
  intro t f
  rw [kernelIntegral_driftSemigroup]
  refine ⟨f.continuous.comp (continuous_id.add continuous_const), ?_⟩
  have htranslate : Filter.Tendsto (fun x : E ↦ x + (t : ℝ) • v)
      (Filter.cocompact E) (Filter.cocompact E) :=
    CocompactMapClass.cocompact_tendsto
      ((Homeomorph.addRight ((t : ℝ) • v)).toCocompactMap)
  exact (f.zero_at_infty').comp htranslate

/-- The `C₀` orbits of the drift semigroup are continuous in time: a `C₀` function is uniformly
continuous, and the two translates at times `a` and `b` differ pointwise by a displacement of
size `|a - b| ‖v‖`. -/
theorem hasContinuousC0Orbits_driftSemigroup (v : E) :
    (driftSemigroup v).HasContinuousC0Orbits (mapsC0_driftSemigroup v) := by
  intro f
  rw [Metric.continuous_iff]
  intro b eps heps
  obtain ⟨delta, hdelta, hf⟩ := Metric.uniformContinuous_iff.mp
    (ZeroAtInftyContinuousMap.uniformContinuous f) (eps / 2) (half_pos heps)
  have hv : (0 : ℝ) < ‖v‖ + 1 := by positivity
  refine ⟨delta / (‖v‖ + 1), div_pos hdelta hv, fun a hab ↦ ?_⟩
  have hab' : |(a : ℝ) - (b : ℝ)| < delta / (‖v‖ + 1) := by
    rw [← NNReal.dist_eq]
    exact hab
  have hkey : ∀ x : E, dist (f (x + (a : ℝ) • v)) (f (x + (b : ℝ) • v)) ≤ eps / 2 := by
    intro x
    refine le_of_lt (hf ?_)
    have hsub : (x + (a : ℝ) • v) - (x + (b : ℝ) • v) = ((a : ℝ) - (b : ℝ)) • v := by
      rw [sub_smul]
      abel
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs]
    calc |(a : ℝ) - (b : ℝ)| * ‖v‖ ≤ |(a : ℝ) - (b : ℝ)| * (‖v‖ + 1) :=
          mul_le_mul_of_nonneg_left (by linarith only []) (abs_nonneg _)
      _ < delta / (‖v‖ + 1) * (‖v‖ + 1) := mul_lt_mul_of_pos_right hab' hv
      _ = delta := div_mul_cancel₀ delta (ne_of_gt hv)
  have hle : dist ((driftSemigroup v).c0Operator (mapsC0_driftSemigroup v) a f)
      ((driftSemigroup v).c0Operator (mapsC0_driftSemigroup v) b f) ≤ eps / 2 := by
    rw [← ZeroAtInftyContinuousMap.dist_toBCF_eq_dist]
    refine (BoundedContinuousFunction.dist_le (le_of_lt (half_pos heps))).2 fun x ↦ ?_
    change dist ((driftSemigroup v).c0Operator (mapsC0_driftSemigroup v) a f x)
      ((driftSemigroup v).c0Operator (mapsC0_driftSemigroup v) b f x) ≤ eps / 2
    rw [SubMarkovKernelSemigroup.c0Operator_apply, SubMarkovKernelSemigroup.c0Operator_apply,
      kernelIntegral_driftSemigroup_apply, kernelIntegral_driftSemigroup_apply]
    exact hkey x
  linarith only [hle, heps]

/-- The drift semigroup is a Feller semigroup. -/
theorem isFellerKernelSemigroup_driftSemigroup (v : E) :
    (driftSemigroup v).IsFellerKernelSemigroup :=
  ⟨mapsC0_driftSemigroup v, hasContinuousC0Orbits_driftSemigroup v⟩

end Feller

section Moments

/-- The drift semigroup satisfies the Kolmogorov moment criterion with `p = q = 2` and constant
`‖v‖²`: the displacement over time `h` is exactly `h ‖v‖`. -/
theorem hasKolmogorovMoments_driftSemigroup (v : E) :
    (driftSemigroup v).HasKolmogorovMoments 2 2 (‖v‖₊ ^ 2) := by
  refine ⟨two_pos, one_lt_two, fun h y ↦ ?_⟩
  have hmeas : Measurable (fun z : E ↦ edist z y ^ (2 : ℝ)) :=
    (measurable_edist_left (x := y)).pow_const 2
  have hnn : nndist (y + (h : ℝ) • v) y = h * ‖v‖₊ := by
    rw [nndist_eq_nnnorm, add_sub_cancel_left, nnnorm_smul]
    congr 1
    apply NNReal.coe_injective
    rw [coe_nnnorm, Real.norm_of_nonneg h.coe_nonneg]
  rw [driftSemigroup_apply, lintegral_dirac' _ hmeas, edist_nndist, hnn,
    ENNReal.rpow_two, ENNReal.rpow_two, ENNReal.coe_mul, mul_pow, ENNReal.coe_pow]
  exact le_of_eq (mul_comm _ _)

end Moments

section Process

/-- The drift semigroup is Kolmogorov regular, by its moment bound. -/
theorem kolmogorovRegular_driftSemigroup (v : E) :
    (driftSemigroup v).KolmogorovRegular (isConservative_driftSemigroup v) :=
  SubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments _
    (isConservative_driftSemigroup v) (hasKolmogorovMoments_driftSemigroup v)

/-- **The main theorem, applied to the drift semigroup.**  There is exactly one Markov kernel
from the state space to continuous paths whose finite-dimensional distributions are those of the
deterministic drift with velocity `v`. -/
theorem existsUnique_continuousProcess_driftSemigroup (v : E) :
    ∃! Q : Kernel E (ContinuousPath E), IsMarkovKernel Q ∧
      ∀ I : Finset NNReal,
        Q.map (ContinuousPath.finsetEvaluation I) =
          SubMarkovKernelSemigroup.finiteSetKernel (driftSemigroup v) I :=
  (isFellerKernelSemigroup_driftSemigroup v).existsUnique_continuousProcess_of_hasKolmogorovMoments
    (driftSemigroup v) (isConservative_driftSemigroup v) (hasKolmogorovMoments_driftSemigroup v)

/-- The straight line started at `x` with velocity `v`, as a continuous path. -/
def driftPath (v : E) (x : E) : ContinuousPath E where
  toFun := fun t ↦ x + (t : ℝ) • v
  continuous_toFun := by fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The straight line, evaluated at a time. -/
@[simp]
theorem driftPath_apply (v : E) (x : E) (t : NNReal) :
    driftPath v x t = x + (t : ℝ) • v := rfl

private theorem ae_eq_driftPath (v : E) (x : E) :
    (fun omega : ContinuousPath E ↦ omega) =ᵐ[
      SubMarkovKernelSemigroup.IsConservative.continuousProcess (driftSemigroup v)
        (isConservative_driftSemigroup v) x]
      fun _ ↦ driftPath v x := by
  set mu := SubMarkovKernelSemigroup.IsConservative.continuousProcess (driftSemigroup v)
    (isConservative_driftSemigroup v) x with hmu
  have hcoord : ∀ q : DenseTime, ∀ᵐ omega ∂mu,
      omega (DenseTime.castOrderEmbedding q) = driftPath v x (DenseTime.castOrderEmbedding q) := by
    intro q
    have hmeas : Measurable
        (fun omega : ContinuousPath E ↦ omega (DenseTime.castOrderEmbedding q)) :=
      ContinuousPath.measurable_coordinateProcess (alpha := E) _
    have hmap := SubMarkovKernelSemigroup.IsConservative.continuousProcess_map_eval
      (driftSemigroup v) (isConservative_driftSemigroup v) (kolmogorovRegular_driftSemigroup v) q
    have hmapx : Measure.map (fun omega : ContinuousPath E ↦
        omega (DenseTime.castOrderEmbedding q)) mu =
        Measure.dirac (driftPath v x (DenseTime.castOrderEmbedding q)) := by
      rw [hmu, ← Kernel.map_apply _ hmeas, hmap, driftSemigroup_apply, driftPath_apply]
    set y := driftPath v x (DenseTime.castOrderEmbedding q) with hy
    have hsingleton : MeasurableSet ({y}ᶜ : Set E) :=
      (isClosed_singleton (x := y)).measurableSet.compl
    change mu ((fun omega : ContinuousPath E ↦
      omega (DenseTime.castOrderEmbedding q)) ⁻¹' ({y}ᶜ : Set E)) = 0
    rw [← Measure.map_apply hmeas hsingleton, hmapx, Measure.dirac_apply' y hsingleton,
      Set.indicator_of_notMem (by simp only [Set.mem_compl_iff, Set.mem_singleton_iff,
        not_true_eq_false, not_false_eq_true])]
  have hall : ∀ᵐ omega ∂mu, ∀ q : DenseTime,
      omega (DenseTime.castOrderEmbedding q) =
        driftPath v x (DenseTime.castOrderEmbedding q) := ae_all_iff.mpr hcoord
  filter_upwards [hall] with omega homega
  apply ContinuousPath.denseRestriction_injective
  funext q
  rw [ContinuousPath.denseRestriction_apply, ContinuousPath.denseRestriction_apply, homega q]

/-- **The continuous-path process of the drift semigroup is the straight-line path.**  From every
starting point `x`, the law of the process is the Dirac mass at the path `t ↦ x + t • v`. -/
theorem continuousProcess_driftSemigroup_eq (v : E) (x : E) :
    SubMarkovKernelSemigroup.IsConservative.continuousProcess (driftSemigroup v)
        (isConservative_driftSemigroup v) x =
      Measure.dirac (driftPath v x) := by
  set mu := SubMarkovKernelSemigroup.IsConservative.continuousProcess (driftSemigroup v)
    (isConservative_driftSemigroup v) x with hmu
  have hprob : IsProbabilityMeasure mu := by
    rw [hmu]
    infer_instance
  calc mu = mu.map id := (Measure.map_id).symm
    _ = mu.map (fun _ ↦ driftPath v x) := Measure.map_congr (ae_eq_driftPath v x)
    _ = mu Set.univ • Measure.dirac (driftPath v x) := Measure.map_const _ _
    _ = Measure.dirac (driftPath v x) := by rw [measure_univ, one_smul]

end Process

end

end MarkovProcess

end PortComputability
