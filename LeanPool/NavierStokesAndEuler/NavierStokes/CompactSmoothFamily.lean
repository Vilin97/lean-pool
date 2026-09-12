/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Jointly smooth functions as smooth families on a compact set

This generalizes `SmoothPathFamily` from a compact real interval to any
compact subset of a real normed space. The Fréchet derivative in the
supremum norm is proved by a uniform mean-value remainder estimate.
-/

@[expose] public section


namespace NavierStokes.CompactSmoothFamily

noncomputable section

open Set Filter Function Metric Asymptotics
open scoped Topology ContDiff

universe u

variable {P Z E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual slice when continuous, with a zero fallback outside the domain
where the hypotheses guarantee continuity. -/
noncomputable def family (K : Set Z) (F : P × Z → E) (p : P) : C(K, E) := by
  classical
  exact if h : Continuous (fun z : K => F (p, z)) then ⟨_, h⟩ else 0

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℝ Z] [NormedSpace ℝ E] in
theorem family_apply (K : Set Z) (F : P × Z → E) (p : P)
    (hp : Continuous (fun z : K => F (p, z))) (z : K) :
    family K F p z = F (p, z) := by
  simp only [family, dite_eq_left hp, ContinuousMap.coe_mk]

omit [NormedSpace ℝ P] [NormedSpace ℝ Z] [NormedSpace ℝ E] in
theorem slice_continuous {K : Set Z} {U : Set P} {F : P × Z → E}
    (hF : ContinuousOn F (U ×ˢ K)) {p : P} (hp : p ∈ U) :
    Continuous (fun z : K => F (p, z)) :=
  hF.comp_continuous (continuous_const.prodMk continuous_subtype_val)
    (fun z => ⟨hp, z.2⟩)

omit [NormedSpace ℝ P] [NormedSpace ℝ Z] [NormedSpace ℝ E] in
theorem continuousOn_family {K : Set Z} {U : Set P} {F : P × Z → E}
    (hF : ContinuousOn F (U ×ˢ K)) : ContinuousOn (family K F) U := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hc : Continuous (fun z : U × K => F (z.1, z.2)) :=
    hF.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
      (fun z => ⟨z.1.2, z.2.2⟩)
  convert! hc using 1
  funext z
  exact family_apply K F z.1 (slice_continuous hF z.1.2) z.2

/-- Flip linear, bundling `toFun`, `toFun`, `map_add`, `map_smul` and the required compatibility
proofs. -/
noncomputable def flipLinear (K : Set Z) :
    C(K, P →L[ℝ] E) →ₗ[ℝ] P →ₗ[ℝ] C(K, E) where
  toFun g := {
    toFun := fun v => ⟨fun z => g z v, g.continuous.clm_apply continuous_const⟩
    map_add' := by intros; ext z; exact map_add (g z) _ _
    map_smul' := by intros; ext z; exact map_smul (g z) _ _ }
  map_add' := by intros; ext v z; rfl
  map_smul' := by intros; ext v z; rfl

omit [NormedSpace ℝ Z] in
theorem norm_flipLinear_le (K : Set Z) [CompactSpace K]
    (g : C(K, P →L[ℝ] E)) (v : P) : ‖flipLinear K g v‖ ≤ ‖g‖ * ‖v‖ := by
  apply (ContinuousMap.norm_le (flipLinear K g v)
    (mul_nonneg (norm_nonneg g) (norm_nonneg v))).mpr
  intro z
  exact ((g z).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (g.norm_coe_le_norm z) (norm_nonneg v))

/-- Flip continuous linear map as an element of `C(K, P →L[ℝ] E) →L[ℝ] P →L[ℝ] C(K, E)`. -/
noncomputable def flipCLM (K : Set Z) [CompactSpace K] :
    C(K, P →L[ℝ] E) →L[ℝ] P →L[ℝ] C(K, E) :=
  (flipLinear (P := P) (E := E) K).mkContinuous₂
    (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜₃ := ℝ) 1
    (fun (g : C(K, P →L[ℝ] E)) (v : P) => by
      simpa only [one_mul] using norm_flipLinear_le K g v)

omit [NormedSpace ℝ Z] in
theorem flipCLM_apply (K : Set Z) [CompactSpace K]
    (g : C(K, P →L[ℝ] E)) (v : P) (z : K) :
    flipCLM (P := P) (E := E) K g v z = g z v := rfl

omit [NormedSpace ℝ Z] in
/-- Actual slice derivatives and their joint continuity give the Fréchet
derivative of the compact-family map in the supremum norm. -/
theorem hasFDerivAt_family (K : Set Z) [CompactSpace K] {U : Set P} (hU : IsOpen U)
    (F : P × Z → E) (G : P × Z → P →L[ℝ] E)
    (hF : ContinuousOn F (U ×ˢ K)) (hG : ContinuousOn G (U ×ˢ K))
    (hderiv : ∀ p ∈ U, ∀ z : K, HasFDerivAt (fun q => F (q, z)) (G (p, z)) p)
    {p : P} (hp : p ∈ U) :
    HasFDerivAt (family K F) (flipCLM (P := P) (E := E) K (family K G p)) p := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply isLittleO_iff.mpr
  intro ε hε
  have hgc : ContinuousAt (family K G) p :=
    (continuousOn_family hG).continuousAt (hU.mem_nhds hp)
  have hsmall : ∀ᶠ q in 𝓝 p, ‖family K G q - family K G p‖ < ε := by
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp hgc ε hε)
  have hnear : ∀ᶠ q in 𝓝 p, q ∈ U := hU.mem_nhds hp
  obtain ⟨δ, hδ, hδmem⟩ := Metric.eventually_nhds_iff.mp (hnear.and hsmall)
  filter_upwards [Metric.ball_mem_nhds (0 : P) hδ] with v hv
  have hv' : p + v ∈ ball p δ := by
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hv
  have hq := (hδmem hv').1
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg v))).mpr
  intro z
  simp only [ContinuousMap.sub_apply, flipCLM_apply,
    family_apply K F (p + v) (slice_continuous hF hq),
    family_apply K F p (slice_continuous hF hp),
    family_apply K G p (slice_continuous hG hp)]
  have hd : ∀ q ∈ ball p δ,
      HasFDerivWithinAt (fun q => F (q, z) - G (p, z) q)
        (G (q, z) - G (p, z)) (ball p δ) q := by
    intro q hq'
    exact ((hderiv q (hδmem hq').1 z).sub (G (p, z)).hasFDerivAt).hasFDerivWithinAt
  have hb : ∀ q ∈ ball p δ, ‖G (q, z) - G (p, z)‖ ≤ ε := by
    intro q hq'
    have hcontq := slice_continuous hG (hδmem hq').1
    have hcontp := slice_continuous hG hp
    calc
      _ = ‖(family K G q - family K G p : C(K, P →L[ℝ] E)) z‖ := by
        simp only [ContinuousMap.sub_apply, family_apply K G q hcontq,
          family_apply K G p hcontp]
      _ ≤ ‖family K G q - family K G p‖ := ContinuousMap.norm_coe_le_norm _ z
      _ ≤ ε := (hδmem hq').2.le
  have hmean := (convex_ball p δ).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hd hb (mem_ball_self hδ) hv'
  have heq : F (p + v, z) - F (p, z) - G (p, z) v =
      (F (p + v, z) - G (p, z) (p + v)) - (F (p, z) - G (p, z) p) := by
    rw [map_add]
    abel
  rw [heq]
  simpa only [add_sub_cancel_left] using hmean

/-- Parameter derivative, given by `(fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ P Z)`. -/
noncomputable def parameterDerivative (F : P × Z → E) (z : P × Z) : P →L[ℝ] E :=
  (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ P Z)

/-- Every finite joint differentiability order lifts to the compact-family space. -/
theorem contDiffOn_family_nat (K : Set Z) [CompactSpace K] (U : Set P) (V : Set Z)
    (hU : IsOpen U) (hV : IsOpen V) (hK : K ⊆ V) (n : ℕ) :
    ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] (F : P × Z → W),
      ContDiffOn ℝ n F (U ×ˢ V) → ContDiffOn ℝ n (family K F) U := by
  induction n with
  | zero =>
    intro W _ _ F hF
    exact contDiffOn_zero.mpr (continuousOn_family
      (hF.continuousOn.mono (Set.prod_mono Subset.rfl hK)))
  | succ n ih =>
    intro W _ _ F hF
    have hFs : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) F (U ×ˢ V) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hF
    have hdata := (contDiffOn_succ_iff_fderiv_of_isOpen (hU.prod hV)).mp hFs
    have hD : ContDiffOn ℝ n (parameterDerivative F) (U ×ˢ V) :=
      hdata.2.2.clm_comp contDiffOn_const
    have hFc : ContinuousOn F (U ×ˢ K) :=
      hF.continuousOn.mono (Set.prod_mono Subset.rfl hK)
    have hDc : ContinuousOn (parameterDerivative F) (U ×ˢ K) :=
      hD.continuousOn.mono (Set.prod_mono Subset.rfl hK)
    have hd : ∀ p ∈ U, HasFDerivAt (family K F)
        (flipCLM (P := P) (E := W) K (family K (parameterDerivative F) p)) p := by
      intro p hp
      apply hasFDerivAt_family K hU F (parameterDerivative F) hFc hDc _ hp
      intro q hq z
      have hDF := (hdata.1 (q, (z : Z)) ⟨hq, hK z.2⟩).differentiableAt
        ((hU.prod hV).mem_nhds ⟨hq, hK z.2⟩)
      exact hDF.hasFDerivAt.comp q (hasFDerivAt_prodMk_left q (z : Z))
    have hfamilyD := ih (parameterDerivative F) hD
    let L : C(K, P →L[ℝ] W) →L[ℝ] P →L[ℝ] C(K, W) := flipCLM K
    have hL : ContDiff ℝ (n : WithTop ℕ∞) L :=
      ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n)
        (E := C(K, P →L[ℝ] W)) (F := P →L[ℝ] C(K, W)) L
    have hflip : ContDiffOn ℝ n
        (fun p => flipCLM (P := P) (E := W) K (family K (parameterDerivative F) p)) U :=
      hL.comp_contDiffOn hfamilyD
    have hresult : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) (family K F) U := by
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn).mpr
      refine ⟨?_, _, hflip, fun p hp => (hd p hp).hasFDerivWithinAt⟩
      intro hω
      exact (WithTop.coe_ne_top hω).elim
    simpa only [Nat.cast_add, Nat.cast_one] using hresult

/-- Joint smoothness near the compact set gives smoothness in the supremum norm. -/
theorem contDiffOn_family_of_joint (K : Set Z) [CompactSpace K] (U : Set P) (V : Set Z)
    (hU : IsOpen U) (hV : IsOpen V) (hK : K ⊆ V)
    (F : P × Z → E) (hF : ContDiffOn ℝ ∞ F (U ×ˢ V)) :
    ContDiffOn ℝ ∞ (family K F) U := by
  apply contDiffOn_infty.mpr
  intro n
  exact contDiffOn_family_nat K U V hU hV hK n F
    (hF.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n))

/-- Evaluating an actual compact-family jet gives the genuine parameter jet
of the original fixed-point slice. -/
theorem iteratedFDeriv_family_apply (K : Set Z) [CompactSpace K] (U : Set P) (V : Set Z)
    (hU : IsOpen U) (hV : IsOpen V) (hK : K ⊆ V)
    (F : P × Z → E) (hF : ContDiffOn ℝ ∞ F (U ×ˢ V))
    {p : P} (hp : p ∈ U) (k : ℕ) (v : Fin k → P) (z : K) :
    (iteratedFDeriv ℝ k (family K F) p v) z =
      iteratedFDeriv ℝ k (fun q => F (q, z)) p v := by
  let ev : C(K, E) →L[ℝ] E := ContinuousMap.evalCLM ℝ z
  have hfamily := contDiffOn_family_of_joint K U V hU hV hK F hF
  have hcomp := ev.iteratedFDerivWithin_comp_left (hfamily p hp) hU.uniqueDiffOn hp
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)
  have hsame : EqOn (ev ∘ family K F) (fun q => F (q, z)) U := by
    intro q hq
    exact family_apply K F q
      (slice_continuous (hF.continuousOn.mono (Set.prod_mono Subset.rfl hK)) hq) z
  have heq := iteratedFDerivWithin_congr (𝕜 := ℝ) hsame hp k
  have hv := congrArg (fun L : P [×k]→L[ℝ] E => L v) (hcomp.symm.trans heq)
  change (iteratedFDerivWithin ℝ k (family K F) U p v) z =
    iteratedFDerivWithin ℝ k (fun q => F (q, z)) U p v at hv
  simpa only [iteratedFDerivWithin_of_isOpen k hU hp] using hv

omit [NormedSpace ℝ P] [NormedSpace ℝ Z] [NormedSpace ℝ E] in
theorem family_apply_of_joint (K : Set Z) {U : Set P} {V : Set Z}
    (hK : K ⊆ V) (F : P × Z → E) (hF : ContinuousOn F (U ×ˢ V))
    {p : P} (hp : p ∈ U) (z : K) : family K F p z = F (p, z) :=
  family_apply K F p (slice_continuous (hF.mono (Set.prod_mono Subset.rfl hK)) hp) z

/-- An arbitrary open neighborhood of `U × K` suffices; a fixed product
neighborhood is extracted locally at each parameter using compactness. -/
theorem contDiffOn_family_of_neighborhood (K : Set Z) [CompactSpace K]
    (U : Set P) (W : Set (P × Z)) (hW : IsOpen W) (hUK : U ×ˢ K ⊆ W)
    (F : P × Z → E) (hF : ContDiffOn ℝ ∞ F W) :
    ContDiffOn ℝ ∞ (family K F) U := by
  intro p hp
  have hKc : IsCompact K := isCompact_iff_compactSpace.mpr inferInstance
  have hs : ({p} : Set P) ×ˢ K ⊆ W := by
    rintro ⟨q, z⟩ ⟨hq, hz⟩
    have hqp : q = p := by simpa only [mem_singleton_iff] using hq
    subst q
    exact hUK ⟨hp, hz⟩
  obtain ⟨U', V', hU', hV', hpU, hKV, hsub⟩ :=
    generalized_tube_lemma isCompact_singleton hKc hW hs
  have hp' : p ∈ U' := hpU (by simp)
  have hlocal := contDiffOn_family_of_joint K U' V' hU' hV' hKV F (hF.mono hsub)
  exact (hlocal.contDiffAt (hU'.mem_nhds hp')).contDiffWithinAt

theorem iteratedFDeriv_family_apply_of_neighborhood (K : Set Z) [CompactSpace K]
    (U : Set P) (W : Set (P × Z)) (hW : IsOpen W) (hUK : U ×ˢ K ⊆ W)
    (F : P × Z → E) (hF : ContDiffOn ℝ ∞ F W)
    {p : P} (hp : p ∈ U) (k : ℕ) (v : Fin k → P) (z : K) :
    (iteratedFDeriv ℝ k (family K F) p v) z =
      iteratedFDeriv ℝ k (fun q => F (q, z)) p v := by
  have hKc : IsCompact K := isCompact_iff_compactSpace.mpr inferInstance
  have hs : ({p} : Set P) ×ˢ K ⊆ W := by
    rintro ⟨q, z⟩ ⟨hq, hz⟩
    have hqp : q = p := by simpa only [mem_singleton_iff] using hq
    subst q
    exact hUK ⟨hp, hz⟩
  obtain ⟨U', V', hU', hV', hpU, hKV, hsub⟩ :=
    generalized_tube_lemma isCompact_singleton hKc hW hs
  exact iteratedFDeriv_family_apply K U' V' hU' hV' hKV F (hF.mono hsub)
    (hpU (by simp)) k v z

end

end NavierStokes.CompactSmoothFamily
