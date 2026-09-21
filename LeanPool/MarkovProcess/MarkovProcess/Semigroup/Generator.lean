/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Semigroup.Basic
import LeanPool.MarkovProcess.MarkovProcess.Semigroup.StrongOperatorLimit
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The generator of a strongly continuous contraction semigroup

For `S : StronglyContinuousContractionSemigroup E` this file defines the generator domain
`S.generatorDomain`, the submodule of vectors `f` whose difference quotients
`t⁻¹ • (S t f - f)` converge as `t → 0⁺`, and the generator
`S.generator : S.generatorDomain →ₗ[ℝ] E` as that limit.  The main results are:

* `tendsto_generator`: the defining limit, and `generator_eq_of_tendsto`, its uniqueness;
* `operator_mem_generatorDomain` and `generator_operator`: the domain is invariant under every
  `S t`, and `S t` commutes with the generator;
* `tendsto_differenceQuotient_add`: every orbit `t ↦ S t f` of a vector in the domain is right
  differentiable at every time, with derivative `S t (S.generator f)`; its real-variable forms are
  `hasDerivWithinAt_Ioi` and `hasDerivWithinAt_Ici`, and at positive times the derivative is
  two-sided, `hasDerivAt_operator_toNNReal`;
* `operator_sub_eq_integral` and `exp_smul_operator_sub_eq_integral`: the fundamental identity
  and its exponentially weighted form;
* `orbitIntegral_mem_generatorDomain` and `generator_orbitIntegral`: for every vector `f`, the
  orbit integral `∫₀ᵗ S s f ds` lies in the domain with generator `S t f - f`; hence
  `dense_generatorDomain`, the domain is dense.

Times are `NNReal` throughout the library; the real-variable statements read the semigroup at
`Real.toNNReal s`.  The fundamental identity is what Dynkin's formula consumes.
-/

open Filter Topology
open scoped NNReal

namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S : StronglyContinuousContractionSemigroup E)

section DifferenceQuotient

/-- The difference quotient `t⁻¹ • (S t f - f)` of the orbit of `f` at time zero. -/
def differenceQuotient (f : E) (t : NNReal) : E := (t : ℝ)⁻¹ • (S t f - f)

/-- The difference quotient, unfolded. -/
theorem differenceQuotient_apply (f : E) (t : NNReal) :
    S.differenceQuotient f t = (t : ℝ)⁻¹ • (S t f - f) := rfl

/-- Difference quotients are additive in the vector. -/
theorem differenceQuotient_add (f g : E) (t : NNReal) :
    S.differenceQuotient (f + g) t = S.differenceQuotient f t + S.differenceQuotient g t := by
  rw [differenceQuotient, differenceQuotient, differenceQuotient, map_add, add_sub_add_comm,
    smul_add]

/-- Difference quotients are homogeneous in the vector. -/
theorem differenceQuotient_smul (c : ℝ) (f : E) (t : NNReal) :
    S.differenceQuotient (c • f) t = c • S.differenceQuotient f t := by
  rw [differenceQuotient, differenceQuotient, map_smul, ← smul_sub, smul_comm]

/-- The difference quotient of the zero vector vanishes. -/
theorem differenceQuotient_zero (t : NNReal) : S.differenceQuotient 0 t = 0 := by
  rw [differenceQuotient, map_zero, sub_zero, smul_zero]

/-- The operator `S s` commutes with difference quotients. -/
theorem differenceQuotient_operator (f : E) (s t : NNReal) :
    S.differenceQuotient (S s f) t = S s (S.differenceQuotient f t) := by
  rw [differenceQuotient, differenceQuotient, map_smul, map_sub, S.commute_apply]

end DifferenceQuotient

section Domain

/-- The generator domain of `S`: the vectors whose difference quotients `t⁻¹ • (S t f - f)`
converge as `t → 0⁺`.  It is a linear subspace of `E`. -/
def generatorDomain : Submodule ℝ E where
  carrier := {f | ∃ g : E, Tendsto (S.differenceQuotient f) (𝓝[>] 0) (𝓝 g)}
  add_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, (ha.add hb).congr fun t ↦ ?_⟩
    exact (S.differenceQuotient_add f g t).symm
  zero_mem' := by
    refine ⟨0, ?_⟩
    have hzero : S.differenceQuotient 0 = fun _ ↦ 0 := funext (S.differenceQuotient_zero)
    rw [hzero]
    exact tendsto_const_nhds
  smul_mem' := by
    rintro c f ⟨a, ha⟩
    refine ⟨c • a, (ha.const_smul c).congr fun t ↦ ?_⟩
    exact (S.differenceQuotient_smul c f t).symm

/-- Membership in the generator domain, unfolded. -/
theorem mem_generatorDomain_iff {f : E} :
    f ∈ S.generatorDomain ↔ ∃ g : E, Tendsto (S.differenceQuotient f) (𝓝[>] 0) (𝓝 g) :=
  Iff.rfl

/-- A vector whose difference quotients converge lies in the generator domain. -/
theorem mem_generatorDomain_of_tendsto {f g : E}
    (h : Tendsto (fun t : NNReal ↦ (t : ℝ)⁻¹ • (S t f - f)) (𝓝[>] 0) (𝓝 g)) :
    f ∈ S.generatorDomain :=
  ⟨g, h⟩

end Domain

section Generator

/-- The limit of the difference quotients, for a vector of the domain. -/
private noncomputable def generatorFun (f : S.generatorDomain) : E :=
  limUnder (𝓝[>] (0 : NNReal)) (S.differenceQuotient f)

private theorem tendsto_generatorFun (f : S.generatorDomain) :
    Tendsto (S.differenceQuotient f) (𝓝[>] 0) (𝓝 (S.generatorFun f)) :=
  tendsto_nhds_limUnder (S.mem_generatorDomain_iff.mp f.2)

private theorem generatorFun_eq_of_tendsto (f : S.generatorDomain) {g : E}
    (h : Tendsto (S.differenceQuotient f) (𝓝[>] 0) (𝓝 g)) : S.generatorFun f = g :=
  tendsto_nhds_unique (S.tendsto_generatorFun f) h

/-- The generator of `S`, as a linear map on its domain: `S.generator f` is the limit of the
difference quotients `t⁻¹ • (S t f - f)` as `t → 0⁺`. -/
noncomputable def generator : S.generatorDomain →ₗ[ℝ] E where
  toFun := S.generatorFun
  map_add' f g := by
    apply S.generatorFun_eq_of_tendsto
    refine ((S.tendsto_generatorFun f).add (S.tendsto_generatorFun g)).congr fun t ↦ ?_
    rw [Submodule.coe_add, differenceQuotient_add]
  map_smul' c f := by
    apply S.generatorFun_eq_of_tendsto
    refine ((S.tendsto_generatorFun f).const_smul c).congr fun t ↦ ?_
    rw [Submodule.coe_smul, differenceQuotient_smul]

/-- The defining property of the generator: the difference quotients of a vector of the domain
converge to its generator. -/
theorem tendsto_generator (f : S.generatorDomain) :
    Tendsto (S.differenceQuotient f) (𝓝[>] 0) (𝓝 (S.generator f)) :=
  S.tendsto_generatorFun f

/-- The defining property of the generator, with the difference quotient written out. -/
theorem tendsto_generator' (f : S.generatorDomain) :
    Tendsto (fun t : NNReal ↦ (t : ℝ)⁻¹ • (S t f - f)) (𝓝[>] 0) (𝓝 (S.generator f)) :=
  S.tendsto_generatorFun f

/-- The generator is the unique limit of the difference quotients. -/
theorem generator_eq_of_tendsto (f : S.generatorDomain) {g : E}
    (h : Tendsto (fun t : NNReal ↦ (t : ℝ)⁻¹ • (S t f - f)) (𝓝[>] 0) (𝓝 g)) :
    S.generator f = g :=
  S.generatorFun_eq_of_tendsto f h

/-- The generator of a vector given by a convergence proof. -/
theorem generator_mk_eq {f g : E}
    (h : Tendsto (fun t : NNReal ↦ (t : ℝ)⁻¹ • (S t f - f)) (𝓝[>] 0) (𝓝 g)) :
    S.generator ⟨f, S.mem_generatorDomain_of_tendsto h⟩ = g :=
  S.generator_eq_of_tendsto _ h

end Generator

section Invariance

/-- The generator domain is invariant under the semigroup. -/
theorem operator_mem_generatorDomain (f : S.generatorDomain) (t : NNReal) :
    S t f ∈ S.generatorDomain := by
  refine ⟨S t (S.generator f), ?_⟩
  refine (((S t).continuous.tendsto _).comp (S.tendsto_generator f)).congr fun h ↦ ?_
  exact (S.differenceQuotient_operator f t h).symm

/-- The semigroup commutes with its generator on the generator domain. -/
theorem generator_operator (f : S.generatorDomain) (t : NNReal) :
    S.generator ⟨S t f, S.operator_mem_generatorDomain f t⟩ = S t (S.generator f) := by
  apply S.generator_eq_of_tendsto
  refine (((S t).continuous.tendsto _).comp (S.tendsto_generator f)).congr fun h ↦ ?_
  exact (S.differenceQuotient_operator f t h).symm

/-- Right differentiability of orbits: for `f` in the generator domain and every time `t`, the
difference quotients of `h ↦ S (t + h) f` at `h = 0⁺` converge to `S t (S.generator f)`. -/
theorem tendsto_differenceQuotient_add (f : S.generatorDomain) (t : NNReal) :
    Tendsto (fun h : NNReal ↦ (h : ℝ)⁻¹ • (S (t + h) f - S t f)) (𝓝[>] 0)
      (𝓝 (S t (S.generator f))) := by
  refine (((S t).continuous.tendsto _).comp (S.tendsto_generator f)).congr fun h ↦ ?_
  show S t ((h : ℝ)⁻¹ • (S h f - f)) = (h : ℝ)⁻¹ • (S (t + h) f - S t f)
  rw [map_smul, map_sub, S.add_apply]

end Invariance

section RealVariable

/-- Reading `NNReal` times from the right of a real time: `y ↦ Real.toNNReal (y - t)` sends the
right neighbourhood filter of `t` to the right neighbourhood filter of `0`. -/
theorem tendsto_toNNReal_sub (t : NNReal) :
    Tendsto (fun y : ℝ ↦ Real.toNNReal (y - t)) (𝓝[>] (t : ℝ)) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have h : Tendsto (fun y : ℝ ↦ Real.toNNReal (y - t)) (𝓝 (t : ℝ))
        (𝓝 (Real.toNNReal ((t : ℝ) - t))) :=
      (continuous_real_toNNReal.tendsto _).comp ((continuous_id.sub continuous_const).tendsto _)
    rw [sub_self, Real.toNNReal_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact Set.mem_Ioi.mpr (Real.toNNReal_pos.mpr (sub_pos.mpr hy))

/-- Reading `NNReal` times from the left of a real time: `y ↦ Real.toNNReal (t - y)` sends the
left neighbourhood filter of `t` to the right neighbourhood filter of `0`. -/
theorem tendsto_toNNReal_const_sub (t : ℝ) :
    Tendsto (fun y : ℝ ↦ Real.toNNReal (t - y)) (𝓝[<] t) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have h : Tendsto (fun y : ℝ ↦ Real.toNNReal (t - y)) (𝓝 t)
        (𝓝 (Real.toNNReal (t - t))) :=
      (continuous_real_toNNReal.tendsto _).comp ((continuous_const.sub continuous_id).tendsto _)
    rw [sub_self, Real.toNNReal_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact Set.mem_Ioi.mpr (Real.toNNReal_pos.mpr (sub_pos.mpr hy))

/-- The orbit of any vector, read in the real variable, is continuous. -/
theorem continuous_operator_toNNReal (f : E) :
    Continuous fun s : ℝ ↦ S (Real.toNNReal s) f :=
  (S.continuous f).comp continuous_real_toNNReal

/-- Right derivative in the real variable: for `f` in the generator domain and every
`t : NNReal`, the orbit `s ↦ S (Real.toNNReal s) f` has right derivative `S t (S.generator f)`
at `t`. -/
theorem hasDerivWithinAt_Ioi (f : S.generatorDomain) (t : NNReal) :
    HasDerivWithinAt (fun s : ℝ ↦ S (Real.toNNReal s) f) (S t (S.generator f))
      (Set.Ioi (t : ℝ)) t := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hdiff : Set.Ioi (t : ℝ) \ {(t : ℝ)} = Set.Ioi (t : ℝ) := by
    ext y
    simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_singleton_iff, and_iff_left_iff_imp]
    exact fun hy ↦ ne_of_gt hy
  rw [hdiff]
  refine ((S.tendsto_differenceQuotient_add f t).comp (tendsto_toNNReal_sub t)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hyt : (t : ℝ) < y := hy
  have hy0 : (0 : ℝ) ≤ y := le_trans t.coe_nonneg hyt.le
  have hcoe : ((Real.toNNReal (y - t) : NNReal) : ℝ) = y - t :=
    Real.coe_toNNReal _ (sub_nonneg.mpr hyt.le)
  have htoNN : Real.toNNReal y = t + Real.toNNReal (y - t) := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add, hcoe, Real.coe_toNNReal y hy0]
    ring
  show ((Real.toNNReal (y - t) : NNReal) : ℝ)⁻¹ •
      (S (t + Real.toNNReal (y - t)) f - S t f) =
    slope (fun s : ℝ ↦ S (Real.toNNReal s) f) (t : ℝ) y
  rw [slope_def_module, hcoe, Real.toNNReal_coe, htoNN]

/-- Right derivative in the real variable, on the closed right neighbourhood: for `f` in the
generator domain and every `t : NNReal`, the orbit `s ↦ S (Real.toNNReal s) f` has derivative
`S t (S.generator f)` within `Ici t` at `t`.  This is the form consumed by Grönwall estimates. -/
theorem hasDerivWithinAt_Ici (f : S.generatorDomain) (t : NNReal) :
    HasDerivWithinAt (fun s : ℝ ↦ S (Real.toNNReal s) f) (S t (S.generator f))
      (Set.Ici (t : ℝ)) t :=
  (S.hasDerivWithinAt_Ioi f t).Ici_of_Ioi

/-- Left derivative in the real variable: at a positive time `t`, the left difference quotients
of the orbit of a vector of the generator domain also converge to `S t (S.generator f)`.  The
identity `S t f - S y f = S y (S (t - y) f - f)` for `y < t` moves the increment to time zero,
where the generator limit applies, and contractivity carries it back. -/
theorem hasDerivWithinAt_Iic (f : S.generatorDomain) {t : ℝ} (ht : 0 < t) :
    HasDerivWithinAt (fun s : ℝ ↦ S (Real.toNNReal s) f)
      (S (Real.toNNReal t) (S.generator f)) (Set.Iic t) t := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hdiff : Set.Iic t \ {t} = Set.Iio t := by
    ext y
    simp only [Set.mem_sdiff, Set.mem_Iic, Set.mem_singleton_iff, Set.mem_Iio]
    exact ⟨fun hy ↦ lt_of_le_of_ne hy.1 hy.2, fun hy ↦ ⟨hy.le, hy.ne⟩⟩
  rw [hdiff]
  have horbit : Tendsto (fun y : ℝ ↦ S (Real.toNNReal y) (S.generator f)) (𝓝[<] t)
      (𝓝 (S (Real.toNNReal t) (S.generator f))) :=
    ((S.continuous_operator_toNNReal (S.generator f)).tendsto t).mono_left nhdsWithin_le_nhds
  have hquot : Tendsto (fun y : ℝ ↦ S.differenceQuotient f (Real.toNNReal (t - y))) (𝓝[<] t)
      (𝓝 (S.generator f)) :=
    (S.tendsto_generator f).comp (tendsto_toNNReal_const_sub t)
  have hmain := tendsto_apply_of_opNorm_le_one (fun y : ℝ ↦ S (Real.toNNReal y))
    (S (Real.toNNReal t)) (fun y : ℝ ↦ S.differenceQuotient f (Real.toNNReal (t - y)))
    (S.generator f) (fun y ↦ S.norm_operator_le_one _) horbit hquot
  refine hmain.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT ht] with y hy
  have hcoe : ((Real.toNNReal (t - y) : NNReal) : ℝ) = t - y :=
    Real.coe_toNNReal _ (sub_nonneg.mpr hy.2.le)
  have hsum : Real.toNNReal y + Real.toNNReal (t - y) = Real.toNNReal t := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add, hcoe, Real.coe_toNNReal y hy.1.le,
      Real.coe_toNNReal t (hy.1.trans hy.2).le]
    ring
  have hinv : (y - t)⁻¹ = -(t - y)⁻¹ := by rw [neg_inv, neg_sub]
  show S (Real.toNNReal y) (S.differenceQuotient f (Real.toNNReal (t - y)))
    = slope (fun s : ℝ ↦ S (Real.toNNReal s) f) t y
  rw [S.differenceQuotient_apply, map_smul, map_sub, ← S.add_apply, hsum, hcoe,
    slope_def_module, hinv, neg_smul, ← smul_neg, neg_sub]

/-- **Two-sided differentiability of orbits.**  For `f` in the generator domain and every positive
time `t`, the orbit `s ↦ S (Real.toNNReal s) f` has derivative `S t (S.generator f)` at `t`. -/
theorem hasDerivAt_operator_toNNReal (f : S.generatorDomain) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ ↦ S (Real.toNNReal s) f) (S (Real.toNNReal t) (S.generator f)) t := by
  have hright := S.hasDerivWithinAt_Ici f (Real.toNNReal t)
  rw [Real.coe_toNNReal t ht.le] at hright
  have hunion := (S.hasDerivWithinAt_Iic f ht).union hright
  rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at hunion

variable [CompleteSpace E]

/-- **The fundamental identity of the generator.**  For `f` in the generator domain and every
time `t`, `S t f - f = ∫₀ᵗ S s (S.generator f) ds`, the integral being the Bochner interval
integral of the continuous orbit of `S.generator f`. -/
theorem operator_sub_eq_integral (f : S.generatorDomain) (t : NNReal) :
    S t f - f = ∫ s in (0 : ℝ)..t, S (Real.toNNReal s) (S.generator f) := by
  have hcont : ContinuousOn (fun s : ℝ ↦ S (Real.toNNReal s) f) (Set.Icc 0 t) :=
    (S.continuous_operator_toNNReal f).continuousOn
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) t,
      HasDerivWithinAt (fun s : ℝ ↦ S (Real.toNNReal s) f)
        (S (Real.toNNReal x) (S.generator f)) (Set.Ioi x) x := by
    intro x hx
    have h := S.hasDerivWithinAt_Ioi f (Real.toNNReal x)
    rwa [Real.coe_toNNReal x hx.1.le] at h
  have hint : IntervalIntegrable (fun s : ℝ ↦ S (Real.toNNReal s) (S.generator f))
      MeasureTheory.volume 0 t :=
    (S.continuous_operator_toNNReal _).intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le t.coe_nonneg hcont
    hderiv hint
  rw [hftc, Real.toNNReal_coe, Real.toNNReal_zero, S.zero_apply]

/-- The exponentially weighted fundamental identity for a strongly continuous contraction
semigroup. -/
theorem exp_smul_operator_sub_eq_integral (f : S.generatorDomain) (lam : ℝ) (t : NNReal) :
    Real.exp (-lam * (t : ℝ)) • S t (f : E) - f =
      ∫ s in (0 : ℝ)..t, Real.exp (-lam * s) •
        S (Real.toNNReal s) (S.generator f - lam • (f : E)) := by
  let F : ℝ → E := fun s ↦ Real.exp (-lam * s) • S (Real.toNNReal s) (f : E)
  let F' : ℝ → E := fun s ↦
    Real.exp (-lam * s) • S (Real.toNNReal s) (S.generator f - lam • (f : E))
  have hcont : ContinuousOn F (Set.Icc 0 (t : ℝ)) := by
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      (S.continuous_operator_toNNReal f)).continuousOn
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) t,
      HasDerivWithinAt F (F' x) (Set.Ioi x) x := by
    intro x hx
    have hexp : HasDerivAt (fun s : ℝ ↦ Real.exp (-lam * s))
        ((-lam) * Real.exp (-lam * x)) x := by
      have h : HasDerivAt (fun s : ℝ ↦ Real.exp (-lam * s))
          (Real.exp (-lam * x) * (-lam * 1)) x := by
        simpa only [id_eq] using ((hasDerivAt_id x).const_mul (-lam)).exp
      exact h.congr_deriv (by ring)
    have horbit := S.hasDerivWithinAt_Ioi f (Real.toNNReal x)
    rw [Real.coe_toNNReal x hx.1.le] at horbit
    have hprod := hexp.hasDerivWithinAt.smul horbit
    refine hprod.congr_deriv ?_
    dsimp only [F']
    rw [map_sub, map_smul]
    module
  have hint : IntervalIntegrable F' MeasureTheory.volume 0 t := by
    have hc : Continuous F' :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
        (S.continuous_operator_toNNReal _)
    exact hc.intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le t.coe_nonneg hcont
    hderiv hint
  simpa only [F, F', Real.toNNReal_coe, Real.toNNReal_zero, S.zero_apply, mul_zero,
    Real.exp_zero, one_smul] using hftc.symm

end RealVariable

section OrbitIntegral

/-- The right difference quotients of a differentiable function, indexed by `NNReal` increments,
converge to its derivative. -/
private theorem tendsto_slope_add_of_hasDerivAt {F : ℝ → E} {F' : E} {u : ℝ}
    (hF : HasDerivAt F F' u) :
    Tendsto (fun h : NNReal ↦ (h : ℝ)⁻¹ • (F (u + h) - F u)) (𝓝[>] 0) (𝓝 F') := by
  have hslope := (hasDerivAt_iff_tendsto_slope.mp hF)
  have hmap : Tendsto (fun h : NNReal ↦ u + (h : ℝ)) (𝓝[>] 0) (𝓝[≠] u) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h0 : Tendsto (fun h : NNReal ↦ u + (h : ℝ)) (𝓝 0) (𝓝 (u + ((0 : NNReal) : ℝ))) :=
        (continuous_const.add NNReal.continuous_coe).tendsto _
      rw [NNReal.coe_zero, add_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      have hpos : (0 : ℝ) < h := NNReal.coe_pos.mpr hh
      exact ne_of_gt (lt_add_of_pos_right u hpos)
  refine (hslope.comp hmap).congr fun h ↦ ?_
  show slope F u (u + h) = (h : ℝ)⁻¹ • (F (u + h) - F u)
  rw [slope_def_module, add_sub_cancel_left]

/-- The orbit integral `∫₀ᵘ S s f ds` of a vector `f`, as a function of the real upper limit
`u` (the semigroup is read at `Real.toNNReal s`). -/
def orbitIntegral (f : E) (u : ℝ) : E := ∫ s in (0 : ℝ)..u, S (Real.toNNReal s) f

/-- The orbit integral, unfolded. -/
theorem orbitIntegral_apply (f : E) (u : ℝ) :
    S.orbitIntegral f u = ∫ s in (0 : ℝ)..u, S (Real.toNNReal s) f := rfl

/-- The orbit integral over an empty window vanishes. -/
theorem orbitIntegral_zero (f : E) : S.orbitIntegral f 0 = 0 :=
  intervalIntegral.integral_same

variable [CompleteSpace E]

/-- The orbit integral is differentiable in its upper limit, with derivative the orbit. -/
theorem hasDerivAt_orbitIntegral (f : E) (u : ℝ) :
    HasDerivAt (S.orbitIntegral f) (S (Real.toNNReal u) f) u :=
  ((S.continuous_operator_toNNReal f).integral_hasStrictDerivAt 0 u).hasDerivAt

/-- The semigroup acting on an orbit integral shifts the integration window. -/
theorem operator_orbitIntegral (f : E) (t h : NNReal) :
    S h (S.orbitIntegral f t) = S.orbitIntegral f (t + h) - S.orbitIntegral f h := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun s : ℝ ↦ S (Real.toNNReal s) f)
      MeasureTheory.volume a b :=
    fun a b ↦ (S.continuous_operator_toNNReal f).intervalIntegrable a b
  have hshift : Set.EqOn (fun s : ℝ ↦ S h (S (Real.toNNReal s) f))
      (fun s : ℝ ↦ S (Real.toNNReal (s + h)) f) (Set.uIcc (0 : ℝ) t) := by
    intro s hs
    have hs0 : (0 : ℝ) ≤ s := by
      rw [Set.uIcc_of_le t.coe_nonneg] at hs
      exact hs.1
    have hcoe : Real.toNNReal (s + h) = h + Real.toNNReal s := by
      apply NNReal.coe_injective
      rw [NNReal.coe_add, Real.coe_toNNReal s hs0, Real.coe_toNNReal _ (add_nonneg hs0 h.coe_nonneg),
        add_comm]
    show S h (S (Real.toNNReal s) f) = S (Real.toNNReal (s + h)) f
    rw [hcoe, S.add_apply]
  rw [orbitIntegral, ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hint 0 t),
    intervalIntegral.integral_congr hshift,
    intervalIntegral.integral_comp_add_right (fun s : ℝ ↦ S (Real.toNNReal s) f) (h : ℝ), zero_add,
    orbitIntegral, orbitIntegral, intervalIntegral.integral_interval_sub_left (hint 0 _) (hint 0 _)]

/-- The difference quotients of an orbit integral converge to the increment of the orbit. -/
theorem tendsto_differenceQuotient_orbitIntegral (f : E) (t : NNReal) :
    Tendsto (fun h : NNReal ↦ (h : ℝ)⁻¹ • (S h (S.orbitIntegral f t) - S.orbitIntegral f t))
      (𝓝[>] 0) (𝓝 (S t f - f)) := by
  have ht := tendsto_slope_add_of_hasDerivAt (S.hasDerivAt_orbitIntegral f t)
  have h0 := tendsto_slope_add_of_hasDerivAt (S.hasDerivAt_orbitIntegral f 0)
  rw [Real.toNNReal_coe] at ht
  rw [Real.toNNReal_zero, S.zero_apply] at h0
  refine (ht.sub h0).congr fun h ↦ ?_
  rw [S.operator_orbitIntegral, zero_add, S.orbitIntegral_zero, sub_zero, ← smul_sub,
    sub_right_comm]

/-- Every orbit integral lies in the generator domain. -/
theorem orbitIntegral_mem_generatorDomain (f : E) (t : NNReal) :
    S.orbitIntegral f t ∈ S.generatorDomain :=
  S.mem_generatorDomain_of_tendsto (S.tendsto_differenceQuotient_orbitIntegral f t)

/-- The generator of an orbit integral is the increment of the orbit:
`L (∫₀ᵗ S s f ds) = S t f - f`, for every `f`, in the domain or not. -/
theorem generator_orbitIntegral (f : E) (t : NNReal) :
    S.generator ⟨S.orbitIntegral f t, S.orbitIntegral_mem_generatorDomain f t⟩ = S t f - f :=
  S.generator_eq_of_tendsto _ (S.tendsto_differenceQuotient_orbitIntegral f t)

/-- Time averages of the orbit converge to the vector: `t⁻¹ • ∫₀ᵗ S s f ds → f` as `t → 0⁺`. -/
theorem tendsto_inv_smul_orbitIntegral (f : E) :
    Tendsto (fun t : NNReal ↦ (t : ℝ)⁻¹ • S.orbitIntegral f t) (𝓝[>] 0) (𝓝 f) := by
  have h0 := tendsto_slope_add_of_hasDerivAt (S.hasDerivAt_orbitIntegral f 0)
  rw [Real.toNNReal_zero, S.zero_apply] at h0
  refine h0.congr fun t ↦ ?_
  rw [zero_add, S.orbitIntegral_zero, sub_zero]

/-- **The generator domain is dense.** -/
theorem dense_generatorDomain : Dense (S.generatorDomain : Set E) := by
  intro f
  refine mem_closure_of_tendsto (S.tendsto_inv_smul_orbitIntegral f) ?_
  exact Eventually.of_forall fun t ↦
    S.generatorDomain.smul_mem _ (S.orbitIntegral_mem_generatorDomain f t)

end OrbitIntegral

end

end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
