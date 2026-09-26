/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import LeanPool.SpectralTheory.Spectral.Stone.Generator


/-!
# Self-adjointness of the Stone generator

This file shows the infinitesimal generator of a strongly continuous
one-parameter unitary group is self-adjoint, via the group's unitarity and
the fundamental theorem of calculus for the difference quotient.
-/

@[expose] public section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

namespace StrongContUnitary

open MeasureTheory Filter

private theorem norm_toFun (U : StrongContUnitary E) (t : ℝ) (x : E) :
    ‖U.toFun t x‖ = ‖x‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (U.isUnitary t) x

private theorem adjoint_toFun (U : StrongContUnitary E) (t : ℝ) :
    (U.toFun t).adjoint = U.toFun (-t) := by
  apply left_inv_eq_right_inv (Unitary.star_mul_self_of_mem (U.isUnitary t))
  calc
    U.toFun t * U.toFun (-t) = U.toFun (t + -t) := (U.add t (-t)).symm
    _ = U.toFun 0 := by rw [add_neg_cancel]
    _ = 1 := U.zero

private theorem inner_differenceQuotient (U : StrongContUnitary E)
    (t : ℝ) (x y : E) :
    inner ℂ ((Complex.I * (t : ℂ))⁻¹ • (U.toFun t x - x)) y =
      inner ℂ x
        ((Complex.I * ((-t : ℝ) : ℂ))⁻¹ • (U.toFun (-t) y - y)) := by
  rw [inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right]
  rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_toFun]
  simp only [mul_inv_rev, Complex.inv_I, mul_neg, map_neg, map_mul, map_inv₀,
    Complex.conj_ofReal, Complex.conj_I, neg_neg, Complex.ofReal_neg, inv_neg]

private theorem tendsto_neg_punctured : Filter.Tendsto (fun t : ℝ ↦ -t)
    (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
  change Filter.map (Homeomorph.neg ℝ) (nhdsWithin 0 {0}ᶜ) ≤
    nhdsWithin 0 {0}ᶜ
  rw [(Homeomorph.neg ℝ).map_punctured_nhds_eq]
  change nhdsWithin (-(0 : ℝ)) {-(0 : ℝ)}ᶜ ≤ nhdsWithin 0 {0}ᶜ
  rw [neg_zero]

/-- The generator domain is invariant under its unitary group. -/
theorem generator_domain_invariant (U : StrongContUnitary E)
    (s : ℝ) (x : U.generator.domain) :
    U.toFun s (x : E) ∈ U.generator.domain := by
  rw [U.mem_generator_domain_iff]
  refine ⟨U.toFun s (U.generator x), ?_⟩
  convert Filter.Tendsto.comp (U.toFun s).continuous.continuousAt
    (U.tendsto_generator x) using 1
  funext t
  change (Complex.I * (t : ℂ))⁻¹ •
      (U.toFun t (U.toFun s (x : E)) - U.toFun s (x : E)) =
    U.toFun s ((Complex.I * (t : ℂ))⁻¹ • (U.toFun t (x : E) - x))
  rw [map_smul, map_sub]
  congr 1
  rw [← mul_apply_eq_comp, ← U.add]
  rw [add_comm, U.add, mul_apply_eq_comp]

private theorem integral_toFun_mem_generator_domain (U : StrongContUnitary E)
    (x : E) (a : ℝ) :
    (∫ t in 0..a, U.toFun t x) ∈ U.generator.domain := by
  rw [U.mem_generator_domain_iff]
  let f : ℝ → E := fun t ↦ U.toFun t x
  let F : ℝ → E := fun b ↦ ∫ t in 0..b, f t
  let g : ℝ → E := fun h ↦ F (a + h) - F h
  have hfcont : Continuous f := U.stronglyContinuous x
  have hFderiv (b : ℝ) : HasDerivAt F (f b) b := by
    exact intervalIntegral.integral_hasDerivAt_right
      (hfcont.intervalIntegrable 0 b)
      hfcont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hfcont.continuousAt
  have hgderiv : HasDerivAt g (f a - f 0) 0 := by
    dsimp [g]
    have ha : HasDerivAt F (f a) (a + 0) := by
      simpa only [add_zero] using hFderiv a
    have hderiv := (ha.comp_const_add a 0).sub (hFderiv 0)
    change HasDerivAt (fun h ↦ F (a + h) - F h) (f a - f 0) 0 at hderiv
    exact hderiv
  have horbit (h : ℝ) : U.toFun h (∫ t in 0..a, f t) = g h := by
    calc
      U.toFun h (∫ t in 0..a, f t) =
          ∫ t in 0..a, U.toFun h (f t) := by
            rw [(U.toFun h).intervalIntegral_comp_comm
              (hfcont.intervalIntegrable 0 a)]
      _ = ∫ t in 0..a, f (t + h) := by
            apply intervalIntegral.integral_congr
            intro t _
            dsimp [f]
            rw [← mul_apply_eq_comp, ← U.add]
            rw [add_comm]
      _ = ∫ t in h..a + h, f t := by
            simpa only [zero_add] using
              intervalIntegral.integral_comp_add_right (a := 0) (b := a) f h
      _ = g h := by
            dsimp [g, F]
            rw [intervalIntegral.integral_interval_sub_left
              (hfcont.intervalIntegrable 0 (a + h))
              (hfcont.intervalIntegrable 0 h)]
  refine ⟨(-Complex.I) • (f a - f 0), ?_⟩
  have hslope := hgderiv.tendsto_slope_zero
  have hscaled := hslope.const_smul (-Complex.I)
  convert hscaled using 1
  funext h
  rw [horbit]
  dsimp [g, F, f]
  simp only [zero_add, add_zero, intervalIntegral.integral_same, sub_zero]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rw [← mul_smul]
  congr 1
  rw [mul_inv_rev, Complex.inv_I]
  calc
    (h : ℂ)⁻¹ * (-Complex.I) = -Complex.I * (h : ℂ)⁻¹ := mul_comm _ _
    _ = -Complex.I * (algebraMap ℝ ℂ) h⁻¹ := by
      rw [map_inv₀ (algebraMap ℝ ℂ) h]
      rw [RCLike.algebraMap_eq_ofReal]
      rfl

private theorem generator_domain_dense (U : StrongContUnitary E) :
    Dense (U.generator.domain : Set E) := by
  intro x
  let f : ℝ → E := fun t ↦ U.toFun t x
  let F : ℝ → E := fun b ↦ ∫ t in 0..b, f t
  have hfcont : Continuous f := U.stronglyContinuous x
  have hFderiv : HasDerivAt F (f 0) 0 := by
    exact intervalIntegral.integral_hasDerivAt_right
      (hfcont.intervalIntegrable 0 0)
      hfcont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hfcont.continuousAt
  have havg : Filter.Tendsto
      (fun a : ℝ ↦ a⁻¹ • (∫ t in 0..a, U.toFun t x))
      (nhdsWithin 0 {0}ᶜ) (nhds x) := by
    simpa only [F, f, zero_add, intervalIntegral.integral_same, sub_zero,
      U.zero, one_apply_eq_self] using hFderiv.tendsto_slope_zero
  apply mem_closure_of_tendsto havg
  filter_upwards [] with a
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact U.generator.domain.smul_mem (((a⁻¹ : ℝ) : ℂ))
    (integral_toFun_mem_generator_domain U x a)

private theorem generator_isFormalAdjoint (U : StrongContUnitary E) :
    U.generator.IsFormalAdjoint U.generator := by
  intro x y
  have hxconst : Filter.Tendsto (fun _ : ℝ ↦ (x : E))
      (nhdsWithin 0 {0}ᶜ) (nhds (x : E)) := tendsto_const_nhds
  have hyconst : Filter.Tendsto (fun _ : ℝ ↦ (y : E))
      (nhdsWithin 0 {0}ᶜ) (nhds (y : E)) := tendsto_const_nhds
  apply tendsto_nhds_unique
    (Filter.Tendsto.inner (𝕜 := ℂ) (U.tendsto_generator x) hyconst)
  have hright := Filter.Tendsto.inner (𝕜 := ℂ) hxconst
    ((U.tendsto_generator y).comp tendsto_neg_punctured)
  convert hright using 1
  funext t
  simp only [Function.comp_apply]
  exact inner_differenceQuotient U t x y

private theorem isSelfAdjoint_of_surjective_add_sub_I (T : E →ₗ.[ℂ] E)
    (hdense : Dense (T.domain : Set E))
    (hsym : T.IsFormalAdjoint T)
    (hplus : Function.Surjective
      (fun x : T.domain ↦ T x + Complex.I • (x : E)))
    (hminus : Function.Surjective
      (fun x : T.domain ↦ T x - Complex.I • (x : E))) :
    IsSelfAdjoint T := by
  rw [LinearPMap.isSelfAdjoint_def]
  have hle : T ≤ T.adjoint := hsym.le_adjoint hdense
  have hdomain : T.domain = T.adjoint.domain := by
    apply le_antisymm hle.1
    intro y hy
    let yAdj : T.adjoint.domain := ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hplus (T.adjoint yAdj + Complex.I • (yAdj : E))
    let w : E := (yAdj : E) - (x : E)
    have hkernel : T.adjoint yAdj - T x + Complex.I • w = 0 := by
      calc
        T.adjoint yAdj - T x + Complex.I • w =
            (T.adjoint yAdj + Complex.I • (yAdj : E)) -
              (T x + Complex.I • (x : E)) := by
                dsimp [w]
                rw [smul_sub]
                abel
        _ = 0 := sub_eq_zero.mpr hx.symm
    obtain ⟨v, hv⟩ := hminus w
    change T v - Complex.I • (v : E) = w at hv
    have hadj : T.IsFormalAdjoint T.adjoint :=
      (LinearPMap.adjoint_isFormalAdjoint hdense).symm
    have hinner :
        inner ℂ (T v - Complex.I • (v : E)) w =
          inner ℂ (v : E) (T.adjoint yAdj - T x + Complex.I • w) := by
      dsimp [w]
      simp only [inner_sub_left, inner_sub_right, inner_add_right,
        inner_smul_left, inner_smul_right, Complex.conj_I]
      rw [hadj v yAdj, hsym v x]
      ring
    have hwinner : inner ℂ w w = 0 := by
      calc
        inner ℂ w w = inner ℂ (T v - Complex.I • (v : E)) w := by
          rw [hv]
        _ = inner ℂ (v : E)
            (T.adjoint yAdj - T x + Complex.I • w) := hinner
        _ = 0 := by rw [hkernel, inner_zero_right]
    have hw : w = 0 := inner_self_eq_zero.mp hwinner
    have hyx : (yAdj : E) = (x : E) := sub_eq_zero.mp hw
    change (yAdj : E) ∈ T.domain
    rw [hyx]
    exact x.property
  exact (LinearPMap.eq_of_le_of_domain_eq hle hdomain).symm

-- The range argument has three stages: prove the generator graph is closed,
-- construct `(A + i)⁻¹` as a Laplace integral of the positive-time orbit,
-- then obtain the negative-sign range by reversing time.
private theorem weightedOrbit_integrableOn_Ioi
    (U : StrongContUnitary E) (x : E) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-t) • U.toFun t x) (Set.Ioi 0) := by
  refine ((integrableOn_exp_neg_Ioi 0).const_mul ‖x‖).mono' ?_ ?_
  · exact ((Real.continuous_exp.comp continuous_neg).smul
      (U.stronglyContinuous x)).aestronglyMeasurable
  · filter_upwards [] with t
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_toFun]
    exact (mul_comm _ _).le

/-- The derivative of a unitary orbit is given by its generator. -/
theorem orbit_hasDerivAt (U : StrongContUnitary E)
    (x : U.generator.domain) (s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ U.toFun t (x : E))
      (Complex.I • U.toFun s (U.generator x)) s := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hscaled := (U.tendsto_generator x).const_smul Complex.I
  have hmapped := Filter.Tendsto.comp (U.toFun s).continuous.continuousAt hscaled
  convert hmapped using 1
  · funext t
    change (t⁻¹ : ℝ) • (U.toFun (s + t) (x : E) - U.toFun s (x : E)) =
      U.toFun s (Complex.I • ((Complex.I * (t : ℂ))⁻¹ •
        (U.toFun t (x : E) - (x : E))))
    rw [U.add, mul_apply_eq_comp]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rw [← map_sub, ← map_smul]
    congr 1
    rw [smul_smul]
    congr 1
    rw [mul_inv_rev, Complex.inv_I]
    ring_nf
    rw [Complex.I_sq]
    rw [neg_mul, one_mul, neg_neg]
    change ((t⁻¹ : ℝ) : ℂ) = ((t : ℝ) : ℂ)⁻¹
    exact Complex.ofReal_inv t
  · rw [map_smul]

private theorem orbit_sub_eq_integral_generator
    (U : StrongContUnitary E) (x : U.generator.domain) (a : ℝ) :
    U.toFun a (x : E) - (x : E) =
      ∫ t in 0..a, Complex.I • U.toFun t (U.generator x) := by
  symm
  have hcont : Continuous
      (fun t : ℝ ↦ Complex.I • U.toFun t (U.generator x)) :=
    continuous_const.smul (U.stronglyContinuous (U.generator x))
  calc
    (∫ t in 0..a, Complex.I • U.toFun t (U.generator x)) =
        U.toFun a (x : E) - U.toFun 0 (x : E) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ ↦ orbit_hasDerivAt U x t)
        (hcont.intervalIntegrable 0 a)
    _ = U.toFun a (x : E) - (x : E) := by
      rw [U.zero, one_apply_eq_self]

private theorem intervalIntegral_orbit_tendsto
    (U : StrongContUnitary E) {y : ℕ → E} {y₀ : E}
    (hy : Tendsto y atTop (nhds y₀)) (a : ℝ) :
    Tendsto (fun n ↦ ∫ t in 0..a, Complex.I • U.toFun t (y n)) atTop
      (nhds (∫ t in 0..a, Complex.I • U.toFun t y₀)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g := fun n ↦ ‖y n - y₀‖ * |a - 0|)
    (Eventually.of_forall fun _ ↦ norm_nonneg _)
    (Eventually.of_forall fun n ↦ ?_) ?_
  · have hncont : Continuous (fun t : ℝ ↦ Complex.I • U.toFun t (y n)) :=
      continuous_const.smul (U.stronglyContinuous (y n))
    have h₀cont : Continuous (fun t : ℝ ↦ Complex.I • U.toFun t y₀) :=
      continuous_const.smul (U.stronglyContinuous y₀)
    rw [← intervalIntegral.integral_sub
      (hncont.intervalIntegrable 0 a) (h₀cont.intervalIntegrable 0 a)]
    apply intervalIntegral.norm_integral_le_of_norm_le_const_ae
    filter_upwards [] with t
    intro _
    rw [← smul_sub, ← map_sub, norm_smul, norm_toFun, Complex.norm_I, one_mul]
  · simpa only [zero_mul] using
      (tendsto_iff_norm_sub_tendsto_zero.mp hy).mul_const |a - 0|

private theorem generator_isClosed (U : StrongContUnitary E) :
    U.generator.IsClosed := by
  rw [LinearPMap.IsClosed]
  apply IsSeqClosed.isClosed
  intro z p hz hp
  have hz' (n : ℕ) := (LinearPMap.mem_graph_iff U.generator).mp (hz n)
  choose x hx hAx using hz'
  have hfst : Tendsto (fun n ↦ (z n).1) atTop (nhds p.1) :=
    Filter.Tendsto.comp continuous_fst.continuousAt hp
  have hsnd : Tendsto (fun n ↦ (z n).2) atTop (nhds p.2) :=
    Filter.Tendsto.comp continuous_snd.continuousAt hp
  have hxlim : Tendsto (fun n ↦ (x n : E)) atTop (nhds p.1) :=
    hfst.congr' (Eventually.of_forall fun n ↦ (hx n).symm)
  have hAlim : Tendsto (fun n ↦ U.generator (x n)) atTop (nhds p.2) :=
    hsnd.congr' (Eventually.of_forall fun n ↦ (hAx n).symm)
  have horbit (a : ℝ) :
      U.toFun a p.1 - p.1 =
        ∫ t in 0..a, Complex.I • U.toFun t p.2 := by
    have hleft : Tendsto
        (fun n ↦ U.toFun a (x n : E) - (x n : E)) atTop
        (nhds (U.toFun a p.1 - p.1)) :=
      (Filter.Tendsto.comp (U.toFun a).continuous.continuousAt hxlim).sub hxlim
    apply tendsto_nhds_unique hleft
    convert intervalIntegral_orbit_tendsto U hAlim a using 1
    funext n
    exact orbit_sub_eq_integral_generator U (x n) a
  have hcont : Continuous (fun t : ℝ ↦ Complex.I • U.toFun t p.2) :=
    continuous_const.smul (U.stronglyContinuous p.2)
  let F : ℝ → E := fun a ↦ ∫ t in 0..a, Complex.I • U.toFun t p.2
  have hFderiv : HasDerivAt F (Complex.I • p.2) 0 := by
    simpa only [F, U.zero, one_apply_eq_self] using
      intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 0)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hcont.continuousAt
  have horbitderiv :
      HasDerivAt (fun t : ℝ ↦ U.toFun t p.1) (Complex.I • p.2) 0 := by
    convert hFderiv.const_add p.1 using 1
    funext t
    calc
      U.toFun t p.1 = F t + p.1 := sub_eq_iff_eq_add.mp (horbit t)
      _ = p.1 + F t := add_comm _ _
  have hscaled := horbitderiv.tendsto_slope_zero.const_smul (-Complex.I)
  have hquot : Filter.Tendsto
      (fun t : ℝ ↦ (Complex.I * (t : ℂ))⁻¹ • (U.toFun t p.1 - p.1))
      (nhdsWithin 0 {0}ᶜ) (nhds p.2) := by
    convert hscaled using 1
    · funext t
      simp only [zero_add, U.zero, one_apply_eq_self]
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      rw [← mul_smul]
      congr 1
      rw [mul_inv_rev, Complex.inv_I]
      calc
        (t : ℂ)⁻¹ * (-Complex.I) = -Complex.I * (t : ℂ)⁻¹ := mul_comm _ _
        _ = -Complex.I * ((t⁻¹ : ℝ) : ℂ) := by rw [Complex.ofReal_inv]
    · rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
  have hpdom : p.1 ∈ U.generator.domain :=
    (U.mem_generator_domain_iff p.1).mpr ⟨p.2, hquot⟩
  let xp : U.generator.domain := ⟨p.1, hpdom⟩
  apply (LinearPMap.mem_graph_iff U.generator).mpr
  refine ⟨xp, rfl, ?_⟩
  exact tendsto_nhds_unique (U.tendsto_generator xp) hquot

private theorem weightedOrbit_shift (U : StrongContUnitary E)
    (x : E) (a h : ℝ) :
    U.toFun h (∫ t in 0..a, Real.exp (-t) • U.toFun t x) =
      Real.exp h • (∫ t in h..a + h, Real.exp (-t) • U.toFun t x) := by
  let f : ℝ → E := fun t ↦ Real.exp (-t) • U.toFun t x
  have hfcont : Continuous f :=
    (Real.continuous_exp.comp continuous_neg).smul (U.stronglyContinuous x)
  calc
    U.toFun h (∫ t in 0..a, f t) =
        ∫ t in 0..a, U.toFun h (f t) := by
      rw [(U.toFun h).intervalIntegral_comp_comm (hfcont.intervalIntegrable 0 a)]
    _ = ∫ t in 0..a, Real.exp h • f (t + h) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp [f]
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
      rw [← RCLike.real_smul_eq_coe_smul (K := ℂ)]
      rw [← mul_apply_eq_comp, ← U.add]
      rw [add_comm t h, smul_smul]
      congr 1
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp h • (∫ t in 0..a, f (t + h)) := by
      rw [intervalIntegral.integral_smul]
    _ = Real.exp h • (∫ t in h..a + h, f t) := by
      rw [intervalIntegral.integral_comp_add_right, zero_add]

private theorem weightedOrbit_quotient_tendsto
    (U : StrongContUnitary E) (x : E) (a : ℝ) :
    Filter.Tendsto
      (fun h : ℝ ↦ (Complex.I * (h : ℂ))⁻¹ •
        (U.toFun h (∫ t in 0..a, Real.exp (-t) • U.toFun t x) -
          ∫ t in 0..a, Real.exp (-t) • U.toFun t x))
      (nhdsWithin 0 {0}ᶜ)
      (nhds ((-Complex.I) •
        ((∫ t in 0..a, Real.exp (-t) • U.toFun t x) +
          Real.exp (-a) • U.toFun a x - x))) := by
  let f : ℝ → E := fun t ↦ Real.exp (-t) • U.toFun t x
  let F : ℝ → E := fun b ↦ ∫ t in 0..b, f t
  let H : ℝ → E := fun h ↦ F (a + h) - F h
  let g : ℝ → E := fun h ↦ Real.exp h • H h
  have hfcont : Continuous f :=
    (Real.continuous_exp.comp continuous_neg).smul (U.stronglyContinuous x)
  have hFderiv (b : ℝ) : HasDerivAt F (f b) b := by
    exact intervalIntegral.integral_hasDerivAt_right
      (hfcont.intervalIntegrable 0 b)
      hfcont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hfcont.continuousAt
  have hHderiv : HasDerivAt H (f a - f 0) 0 := by
    dsimp [H]
    have ha : HasDerivAt F (f a) (a + 0) := by
      simpa only [add_zero] using hFderiv a
    exact (ha.comp_const_add a 0).sub (hFderiv 0)
  have hgderiv : HasDerivAt g (F a + f a - f 0) 0 := by
    have hgraw := (Real.hasDerivAt_exp 0).smul hHderiv
    convert hgraw using 1
    change F a + f a - f 0 =
        Real.exp 0 • (f a - f 0) + Real.exp 0 • (F (a + 0) - F 0)
    simp only [Real.exp_zero, one_smul, add_zero, F,
      intervalIntegral.integral_same, sub_zero]
    abel
  have horbit (h : ℝ) :
      U.toFun h (∫ t in 0..a, f t) = g h := by
    rw [weightedOrbit_shift]
    dsimp [g, H, F]
    rw [intervalIntegral.integral_interval_sub_left
      (hfcont.intervalIntegrable 0 (a + h))
      (hfcont.intervalIntegrable 0 h)]
  have hscaled := hgderiv.tendsto_slope_zero.const_smul (-Complex.I)
  convert hscaled using 1
  · funext h
    have hg0 : g 0 = ∫ t in 0..a, f t := by
      dsimp [g, H, F]
      simp only [add_zero, Real.exp_zero, one_smul,
        intervalIntegral.integral_same, sub_zero]
    simp only [zero_add]
    rw [horbit, hg0]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rw [← mul_smul]
    congr 1
    rw [mul_inv_rev, Complex.inv_I]
    calc
      (h : ℂ)⁻¹ * (-Complex.I) = -Complex.I * (h : ℂ)⁻¹ := mul_comm _ _
      _ = -Complex.I * ((h⁻¹ : ℝ) : ℂ) := by rw [Complex.ofReal_inv]
  · dsimp [F, f]
    rw [U.zero, one_apply_eq_self]
    simp only [neg_zero, Real.exp_zero, one_smul]

private theorem weightedOrbit_mem_graph
    (U : StrongContUnitary E) (x : E) (a : ℝ) :
    let y := ∫ t in 0..a, Real.exp (-t) • U.toFun t x
    (y, (-Complex.I) • (y + Real.exp (-a) • U.toFun a x - x)) ∈
      U.generator.graph := by
  dsimp only
  have hquot := weightedOrbit_quotient_tendsto U x a
  have hy : (∫ t in 0..a, Real.exp (-t) • U.toFun t x) ∈
      U.generator.domain :=
    (U.mem_generator_domain_iff _).mpr ⟨_, hquot⟩
  let y : U.generator.domain :=
    ⟨∫ t in 0..a, Real.exp (-t) • U.toFun t x, hy⟩
  apply (LinearPMap.mem_graph_iff U.generator).mpr
  refine ⟨y, rfl, ?_⟩
  exact tendsto_nhds_unique (U.tendsto_generator y) hquot

private theorem generator_add_I_surjective (U : StrongContUnitary E) :
    Function.Surjective
      (fun y : U.generator.domain ↦ U.generator y + Complex.I • (y : E)) := by
  intro z
  let x : E := (-Complex.I) • z
  let f : ℝ → E := fun t ↦ Real.exp (-t) • U.toFun t x
  let y : E := ∫ t in Set.Ioi 0, f t
  have hy : Tendsto (fun n : ℕ ↦ ∫ t in 0..(n : ℝ), f t) atTop (nhds y) := by
    exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0
      (weightedOrbit_integrableOn_Ioi U x)
      tendsto_natCast_atTop_atTop
  have hexp : Tendsto (fun n : ℕ ↦ Real.exp (-(n : ℝ))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have htail : Tendsto
      (fun n : ℕ ↦ Real.exp (-(n : ℝ)) • U.toFun (n : ℝ) x)
      atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    convert hexp.mul_const ‖x‖ using 1
    · funext n
      simp only [sub_zero, norm_smul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), norm_toFun]
    · rw [zero_mul]
  have hA : Tendsto
      (fun n : ℕ ↦ (-Complex.I) •
        ((∫ t in 0..(n : ℝ), f t) +
          Real.exp (-(n : ℝ)) • U.toFun (n : ℝ) x - x))
      atTop (nhds ((-Complex.I) • (y - x))) := by
    simpa only [add_zero] using
      ((hy.add htail).sub tendsto_const_nhds).const_smul (-Complex.I)
  have hpair : Tendsto
      (fun n : ℕ ↦
        (∫ t in 0..(n : ℝ), f t,
          (-Complex.I) • ((∫ t in 0..(n : ℝ), f t) +
            Real.exp (-(n : ℝ)) • U.toFun (n : ℝ) x - x)))
      atTop (nhds (y, (-Complex.I) • (y - x))) :=
    hy.prodMk_nhds hA
  have hmem : ∀ n : ℕ,
      (∫ t in 0..(n : ℝ), f t,
        (-Complex.I) • ((∫ t in 0..(n : ℝ), f t) +
          Real.exp (-(n : ℝ)) • U.toFun (n : ℝ) x - x)) ∈
        U.generator.graph := by
    intro n
    exact weightedOrbit_mem_graph U x (n : ℝ)
  have hlimit :
      (y, (-Complex.I) • (y - x)) ∈ U.generator.graph :=
    (generator_isClosed U).mem_of_tendsto hpair
      (Eventually.of_forall hmem)
  obtain ⟨yd, hyd, hAyd⟩ :=
    (LinearPMap.mem_graph_iff U.generator).mp hlimit
  refine ⟨yd, ?_⟩
  calc
    U.generator yd + Complex.I • (yd : E) =
        (-Complex.I) • (y - x) + Complex.I • y := by
      rw [hAyd, hyd]
    _ = z := by
      have hII : (-Complex.I) * (-Complex.I) = (-1 : ℂ) := by
        rw [neg_mul_neg, Complex.I_mul_I]
      dsimp [x]
      rw [smul_sub, smul_smul, hII, neg_one_smul, neg_smul]
      abel

private def timeReverse (U : StrongContUnitary E) :
    StrongContUnitary E where
  toFun t := U.toFun (-t)
  isUnitary t := U.isUnitary (-t)
  zero := by
    simpa only [neg_zero] using U.zero
  add s t := by
    calc
      U.toFun (-(s + t)) = U.toFun ((-s) + (-t)) := by congr 1; ring
      _ = U.toFun (-s) * U.toFun (-t) := U.add (-s) (-t)
  stronglyContinuous x := (U.stronglyContinuous x).comp continuous_neg

private theorem timeReverse_quotient_tendsto
    (U : StrongContUnitary E) (x y : E)
    (h : Filter.Tendsto
      (fun t : ℝ ↦ (Complex.I * (t : ℂ))⁻¹ • (U.toFun t x - x))
      (nhdsWithin 0 {0}ᶜ) (nhds y)) :
    Filter.Tendsto
      (fun t : ℝ ↦ (Complex.I * (t : ℂ))⁻¹ •
        ((timeReverse U).toFun t x - x))
      (nhdsWithin 0 {0}ᶜ) (nhds (-y)) := by
  have h' := (h.comp tendsto_neg_punctured).neg
  convert h' using 1
  funext t
  dsimp [timeReverse]
  simp only [Complex.ofReal_neg, mul_neg, inv_neg, neg_smul, neg_neg]

private theorem timeReverse_mem_generator_domain_iff
    (U : StrongContUnitary E) (x : E) :
    x ∈ (timeReverse U).generator.domain ↔ x ∈ U.generator.domain := by
  rw [(timeReverse U).mem_generator_domain_iff,
    U.mem_generator_domain_iff]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨-y, ?_⟩
    have h := timeReverse_quotient_tendsto (timeReverse U) x y hy
    convert h using 1
    funext t
    dsimp [timeReverse]
    rw [neg_neg]
  · rintro ⟨y, hy⟩
    exact ⟨-y, timeReverse_quotient_tendsto U x y hy⟩

private theorem generator_sub_I_surjective (U : StrongContUnitary E) :
    Function.Surjective
      (fun y : U.generator.domain ↦ U.generator y - Complex.I • (y : E)) := by
  intro z
  obtain ⟨yv, hyv⟩ := generator_add_I_surjective
    (timeReverse U) (-z)
  have hyU : (yv : E) ∈ U.generator.domain :=
    (timeReverse_mem_generator_domain_iff U (yv : E)).mp yv.property
  let yu : U.generator.domain := ⟨(yv : E), hyU⟩
  have hrev := timeReverse_quotient_tendsto U (yu : E) (U.generator yu)
    (U.tendsto_generator yu)
  have hvval : (timeReverse U).generator yv = -U.generator yu :=
    tendsto_nhds_unique ((timeReverse U).tendsto_generator yv) hrev
  refine ⟨yu, ?_⟩
  change (timeReverse U).generator yv + Complex.I • (yv : E) = -z at hyv
  change U.generator yu - Complex.I • (yu : E) = z
  rw [hvval] at hyv
  calc
    U.generator yu - Complex.I • (yu : E) =
        -(-U.generator yu + Complex.I • (yv : E)) := by
      change U.generator yu - Complex.I • (yu : E) =
        -(-U.generator yu + Complex.I • (yu : E))
      abel
    _ = -(-z) := by rw [hyv]
    _ = z := neg_neg z

theorem generator_isSelfAdjoint
    (U : StrongContUnitary E) :
    IsSelfAdjoint U.generator :=
  isSelfAdjoint_of_surjective_add_sub_I U.generator
    (generator_domain_dense U) (generator_isFormalAdjoint U)
    (generator_add_I_surjective U) (generator_sub_I_surjective U)

end StrongContUnitary
