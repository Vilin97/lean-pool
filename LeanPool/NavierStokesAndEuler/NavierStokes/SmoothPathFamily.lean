/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricODE
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Jointly smooth functions as smooth families of continuous paths

The first derivative is proved with a uniform mean-value remainder estimate.
Continuity into the supremum-norm path space follows from compact-open currying.
All path derivatives are constructed from genuine parameter derivatives.
-/

@[expose] public section


namespace NavierStokes.SmoothPathFamily

noncomputable section

open Set Filter Function Metric Asymptotics
open scoped Topology ContDiff

universe u

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {a b : ℝ}

/-- Canonical continuous path where the slice is continuous, zero elsewhere.
Only values in the stated open parameter domain enter any theorem. -/
noncomputable def pathFamily (F : P × ℝ → E) (p : P) : C(Icc a b, E) := by
  classical
  exact if h : Continuous (fun t : Icc a b => F (p, t)) then ⟨_, h⟩ else 0

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℝ E] in
theorem pathFamily_apply (F : P × ℝ → E) (p : P)
    (hp : Continuous (fun t : Icc a b => F (p, t))) (t : Icc a b) :
    pathFamily (a := a) (b := b) F p t = F (p, t) := by
  simp only [pathFamily, dite_eq_left hp, ContinuousMap.coe_mk]

omit [NormedSpace ℝ P] [NormedSpace ℝ E] in
theorem slice_continuous {U : Set P} {F : P × ℝ → E}
    (hF : ContinuousOn F (U ×ˢ Icc a b)) {p : P} (hp : p ∈ U) :
    Continuous (fun t : Icc a b => F (p, t)) :=
  hF.comp_continuous (continuous_const.prodMk continuous_subtype_val)
    (fun t => ⟨hp, t.2⟩)

omit [NormedSpace ℝ P] [NormedSpace ℝ E] in
/-- Compact-open continuity becomes norm continuity because the time interval
is compact. No smoothness of a path map is assumed here. -/
theorem continuousOn_pathFamily {U : Set P} {F : P × ℝ → E}
    (hF : ContinuousOn F (U ×ˢ Icc a b)) :
    ContinuousOn (pathFamily (a := a) (b := b) F) U := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hc : Continuous (fun z : U × Icc a b => F (z.1, z.2)) :=
    hF.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
      (fun z => ⟨z.1.2, z.2.2⟩)
  convert! hc using 1
  funext z
  exact pathFamily_apply F z.1 (slice_continuous hF z.1.2) z.2

/-- Flip linear, bundling `toFun`, `toFun`, `map_add`, `map_smul` and the required compatibility
proofs. -/
noncomputable def flipLinear : C(Icc a b, P →L[ℝ] E) →ₗ[ℝ] P →ₗ[ℝ] C(Icc a b, E) where
  toFun g := {
    toFun := fun v => ⟨fun t => g t v, g.continuous.clm_apply continuous_const⟩
    map_add' := by intros; ext t; exact map_add (g t) _ _
    map_smul' := by intros; ext t; exact map_smul (g t) _ _ }
  map_add' := by intros; ext v t; rfl
  map_smul' := by intros; ext v t; rfl

theorem norm_flipLinear_le (g : C(Icc a b, P →L[ℝ] E)) (v : P) :
    ‖flipLinear g v‖ ≤ ‖g‖ * ‖v‖ := by
  apply (ContinuousMap.norm_le (flipLinear g v)
    (mul_nonneg (norm_nonneg g) (norm_nonneg v))).mpr
  intro t
  exact ((g t).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (g.norm_coe_le_norm t) (norm_nonneg v))

/-- Reorder the continuous time variable and the bounded linear parameter
variable. This is a proved bounded linear operation. -/
noncomputable def flipPath : C(Icc a b, P →L[ℝ] E) →L[ℝ] P →L[ℝ] C(Icc a b, E) :=
  (flipLinear (P := P) (E := E) (a := a) (b := b)).mkContinuous₂
    (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜₃ := ℝ) 1
    (fun (g : C(Icc a b, P →L[ℝ] E)) (v : P) => by
      simpa only [one_mul] using norm_flipLinear_le g v)

theorem flipPath_apply (g : C(Icc a b, P →L[ℝ] E)) (v : P) (t : Icc a b) :
    flipPath (P := P) (E := E) g v t = g t v := rfl

/-- The key uniform differentiability theorem. Joint continuity of the actual
slice derivative supplies a common remainder estimate for every time point. -/
theorem hasFDerivAt_pathFamily {U : Set P} (hU : IsOpen U)
    (F : P × ℝ → E) (G : P × ℝ → P →L[ℝ] E)
    (hF : ContinuousOn F (U ×ˢ Icc a b))
    (hG : ContinuousOn G (U ×ˢ Icc a b))
    (hderiv : ∀ p ∈ U, ∀ t : Icc a b, HasFDerivAt (fun q => F (q, t)) (G (p, t)) p)
    {p : P} (hp : p ∈ U) :
    HasFDerivAt (pathFamily (a := a) (b := b) F)
      (flipPath (P := P) (E := E) (pathFamily (a := a) (b := b) G p)) p := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply isLittleO_iff.mpr
  intro ε hε
  have hgc : ContinuousAt (pathFamily (a := a) (b := b) G) p :=
    (continuousOn_pathFamily hG).continuousAt (hU.mem_nhds hp)
  have hsmall : ∀ᶠ q in 𝓝 p,
      ‖pathFamily (a := a) (b := b) G q - pathFamily G p‖ < ε := by
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp hgc ε hε)
  have hnear : ∀ᶠ q in 𝓝 p, q ∈ U := hU.mem_nhds hp
  obtain ⟨δ, hδ, hδmem⟩ := Metric.eventually_nhds_iff.mp
    (hnear.and hsmall)
  filter_upwards [Metric.ball_mem_nhds (0 : P) hδ] with v hv
  have hv' : p + v ∈ ball p δ := by
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hv
  have hq := (hδmem hv').1
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg v))).mpr
  intro t
  simp only [ContinuousMap.sub_apply, flipPath_apply,
    pathFamily_apply F (p + v) (slice_continuous hF hq),
    pathFamily_apply F p (slice_continuous hF hp),
    pathFamily_apply G p (slice_continuous hG hp)]
  have hd : ∀ q ∈ ball p δ,
      HasFDerivWithinAt (fun q => F (q, t) - G (p, t) q)
        (G (q, t) - G (p, t)) (ball p δ) q := by
    intro q hq'
    exact ((hderiv q (hδmem hq').1 t).sub (G (p, t)).hasFDerivAt).hasFDerivWithinAt
  have hb : ∀ q ∈ ball p δ, ‖G (q, t) - G (p, t)‖ ≤ ε := by
    intro q hq'
    have hcontq := slice_continuous hG (hδmem hq').1
    have hcontp := slice_continuous hG hp
    calc
      _ = ‖(pathFamily G q - pathFamily G p : C(Icc a b, P →L[ℝ] E)) t‖ := by
        simp only [ContinuousMap.sub_apply, pathFamily_apply G q hcontq,
          pathFamily_apply G p hcontp]
      _ ≤ ‖pathFamily (a := a) (b := b) G q - pathFamily G p‖ :=
        ContinuousMap.norm_coe_le_norm _ t
      _ ≤ ε := (hδmem hq').2.le
  have hmean := (convex_ball p δ).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hd hb (mem_ball_self hδ) hv'
  have heq : F (p + v, t) - F (p, t) - G (p, t) v =
      (F (p + v, t) - G (p, t) (p + v)) - (F (p, t) - G (p, t) p) := by
    rw [map_add]
    abel
  rw [heq]
  simpa only [add_sub_cancel_left] using hmean

/-- The actual parameter derivative, obtained by restricting the joint derivative
to the parameter direction. -/
noncomputable def parameterDerivative (F : P × ℝ → E) (z : P × ℝ) : P →L[ℝ] E :=
  (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ P ℝ)

/-- Every finite joint differentiability order lifts to the path Banach space.
The induction changes the target to the space of parameter derivatives. -/
theorem contDiffOn_pathFamily_nat (U : Set P) (V : Set ℝ)
    (hU : IsOpen U) (hV : IsOpen V) (hI : Icc a b ⊆ V) (n : ℕ) :
    ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] (F : P × ℝ → W),
      ContDiffOn ℝ n F (U ×ˢ V) →
      ContDiffOn ℝ n (pathFamily (a := a) (b := b) F) U := by
  induction n with
  | zero =>
    intro W _ _ F hF
    exact contDiffOn_zero.mpr (continuousOn_pathFamily
      (hF.continuousOn.mono (Set.prod_mono Subset.rfl hI)))
  | succ n ih =>
    intro W _ _ F hF
    have hFs : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) F (U ×ˢ V) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hF
    have hdata := (contDiffOn_succ_iff_fderiv_of_isOpen (hU.prod hV)).mp hFs
    have hD : ContDiffOn ℝ n (parameterDerivative F) (U ×ˢ V) :=
      hdata.2.2.clm_comp contDiffOn_const
    have hFc : ContinuousOn F (U ×ˢ Icc a b) :=
      hF.continuousOn.mono (Set.prod_mono Subset.rfl hI)
    have hDc : ContinuousOn (parameterDerivative F) (U ×ˢ Icc a b) :=
      hD.continuousOn.mono (Set.prod_mono Subset.rfl hI)
    have hd : ∀ p ∈ U, HasFDerivAt (pathFamily (a := a) (b := b) F)
        (flipPath (P := P) (E := W) (pathFamily (a := a) (b := b) (parameterDerivative F) p)) p :=
            by
      intro p hp
      apply hasFDerivAt_pathFamily hU F (parameterDerivative F) hFc hDc _ hp
      intro q hq t
      have hDF := (hdata.1 (q, (t : ℝ)) ⟨hq, hI t.2⟩).differentiableAt
        ((hU.prod hV).mem_nhds ⟨hq, hI t.2⟩)
      exact hDF.hasFDerivAt.comp q (hasFDerivAt_prodMk_left q (t : ℝ))
    have hpathD := ih (parameterDerivative F) hD
    let L : C(Icc a b, P →L[ℝ] W) →L[ℝ] P →L[ℝ] C(Icc a b, W) :=
      flipPath (P := P) (E := W) (a := a) (b := b)
    have hL : ContDiff ℝ (n : WithTop ℕ∞) L :=
      ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n)
        (E := C(Icc a b, P →L[ℝ] W)) (F := P →L[ℝ] C(Icc a b, W)) L
    have hflip : ContDiffOn ℝ n
        (fun p => flipPath (P := P) (E := W) (a := a) (b := b)
          (pathFamily (a := a) (b := b) (parameterDerivative F) p)) U := by
      exact hL.comp_contDiffOn hpathD
    have hresult : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1)
        (pathFamily (a := a) (b := b) F) U := by
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn).mpr
      refine ⟨?_, _, hflip, fun p hp => (hd p hp).hasFDerivWithinAt⟩
      intro hω
      exact (WithTop.coe_ne_top hω).elim
    simpa only [Nat.cast_add, Nat.cast_one] using hresult

/-- Joint C∞ regularity on an open product containing the compact time interval
implies C∞ dependence as a path in the supremum norm. -/
theorem contDiffOn_pathFamily_of_joint (U : Set P) (V : Set ℝ)
    (hU : IsOpen U) (hV : IsOpen V) (hI : Icc a b ⊆ V)
    (F : P × ℝ → E) (hF : ContDiffOn ℝ ∞ F (U ×ˢ V)) :
    ContDiffOn ℝ ∞ (pathFamily (a := a) (b := b) F) U := by
  apply contDiffOn_infty.mpr
  intro n
  exact contDiffOn_pathFamily_nat U V hU hV hI n F
    (hF.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n))

/-- Every actual path jet evaluates to the genuine iterated parameter derivative
of the original scalar-time slice. -/
theorem iteratedFDeriv_pathFamily_apply (U : Set P) (V : Set ℝ)
    (hU : IsOpen U) (hV : IsOpen V) (hI : Icc a b ⊆ V)
    (F : P × ℝ → E) (hF : ContDiffOn ℝ ∞ F (U ×ˢ V))
    {p : P} (hp : p ∈ U) (k : ℕ) (v : Fin k → P) (t : Icc a b) :
    (iteratedFDeriv ℝ k (pathFamily (a := a) (b := b) F) p v) t =
      iteratedFDeriv ℝ k (fun q => F (q, t)) p v := by
  let ev : C(Icc a b, E) →L[ℝ] E := ContinuousMap.evalCLM ℝ t
  have hpath := contDiffOn_pathFamily_of_joint U V hU hV hI F hF
  have hcomp := ev.iteratedFDerivWithin_comp_left (hpath p hp) hU.uniqueDiffOn hp
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)
  have hsame : EqOn (ev ∘ pathFamily (a := a) (b := b) F) (fun q => F (q, t)) U := by
    intro q hq
    exact pathFamily_apply F q
      (slice_continuous (hF.continuousOn.mono (Set.prod_mono Subset.rfl hI)) hq) t
  have heq := iteratedFDerivWithin_congr (𝕜 := ℝ) hsame hp k
  have hv := congrArg (fun L : P [×k]→L[ℝ] E => L v) (hcomp.symm.trans heq)
  change (iteratedFDerivWithin ℝ k (pathFamily F) U p v) t =
    iteratedFDerivWithin ℝ k (fun q => F (q, t)) U p v at hv
  simpa only [iteratedFDerivWithin_of_isOpen k hU hp] using hv

section ODE

variable [CompleteSpace E] (hab : a ≤ b)

/-- The actual finite-interval ODE solution for the supplied joint coefficient
and forcing families. -/
noncomputable def odeFamily (A : P × ℝ → E →L[ℝ] E) (x₀ : P → E)
    (f : P × ℝ → E) (p : P) : C(Icc a b, E) :=
  ParametricODE.solution hab (pathFamily A p) (x₀ p) (pathFamily f p)

/-- Directly closes the joint-smoothness interface of `ParametricODE`. -/
theorem contDiffOn_odeFamily_of_joint (U : Set P) (V : Set ℝ)
    (hU : IsOpen U) (hV : IsOpen V) (hI : Icc a b ⊆ V)
    (A : P × ℝ → E →L[ℝ] E) (x₀ : P → E) (f : P × ℝ → E)
    (hA : ContDiffOn ℝ ∞ A (U ×ˢ V)) (hx₀ : ContDiffOn ℝ ∞ x₀ U)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ V)) :
    ContDiffOn ℝ ∞ (odeFamily hab A x₀ f) U :=
  ParametricODE.contDiffOn_solution_family hab (pathFamily A) x₀ (pathFamily f)
    (contDiffOn_pathFamily_of_joint U V hU hV hI A hA) hx₀
    (contDiffOn_pathFamily_of_joint U V hU hV hI f hf)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem odeFamily_initial (A : P × ℝ → E →L[ℝ] E) (x₀ : P → E)
    (f : P × ℝ → E) (p : P) :
    odeFamily hab A x₀ f p ⟨a, le_rfl, hab⟩ = x₀ p :=
  ParametricODE.solution_initial hab (pathFamily A p) (x₀ p) (pathFamily f p)

omit [NormedSpace ℝ P] in
/-- The smooth path family satisfies the ODE with the originally supplied
coefficient values at every time in the closed interval. -/
theorem odeFamily_hasDerivWithinAt (U : Set P) (V : Set ℝ)
    (hI : Icc a b ⊆ V) (A : P × ℝ → E →L[ℝ] E) (x₀ : P → E) (f : P × ℝ → E)
    (hA : ContinuousOn A (U ×ˢ V)) (hf : ContinuousOn f (U ×ˢ V))
    {p : P} (hp : p ∈ U) (t : Icc a b) :
    HasDerivWithinAt (ParametricODE.extend hab (odeFamily hab A x₀ f p))
      (A (p, t) (odeFamily hab A x₀ f p t) + f (p, t)) (Icc a b) t := by
  have hAc := slice_continuous (hA.mono (Set.prod_mono Subset.rfl hI)) hp
  have hfc := slice_continuous (hf.mono (Set.prod_mono Subset.rfl hI)) hp
  unfold odeFamily
  simpa only [pathFamily_apply A p hAc, pathFamily_apply f p hfc] using
    ParametricODE.solution_hasDerivWithinAt hab (pathFamily A p) (x₀ p) (pathFamily f p) t

end ODE

end

end NavierStokes.SmoothPathFamily
