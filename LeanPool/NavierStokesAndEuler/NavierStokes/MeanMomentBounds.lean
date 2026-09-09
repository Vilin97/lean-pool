/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.WeightedRadialPrimitive
public import LeanPool.NavierStokesAndEuler.NavierStokes.PressureStream
public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothParameterIntegral
public import LeanPool.NavierStokesAndEuler.NavierStokes.IntegratedMeanBalances

@[expose] public section

/-!
# Actual slow moments of flat weighted mean fields

The two-edge weight absorbs every fixed inverse-edge polynomial.  Consequently
the actual derivatives of a supported mean field have global band bounds.
Finite torus averaging and radial integration preserve these bounds.  All
derivatives in this file are `iteratedFDeriv` of the actual integral.
-/

namespace NavierStokes.MeanMomentBounds

noncomputable section

open Set Function MeasureTheory Filter
open scoped ContDiff Topology Interval BigOperators
open WeightedClasses WeightedRadialPrimitive

variable {D E F : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A global finite-prefix bound, with the discrete band and slow polynomial
still visible.  This is a proved consequence of the flat weighted class below. -/
noncomputable def GlobalBandJets (ε S : ℕ → ℝ) (α : ℝ) (f : ℕ → D → E) : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ,
    ∀ n x, ∀ j : ℕ, j ≤ m →
      ‖iteratedFDeriv ℝ j (f n) x‖ ≤ C * (ε n) ^ α * (S n) ^ p

omit [NormedSpace ℝ D] [NormedSpace ℝ E] in
theorem supported_zero_outside_open {a b : ℝ} {f : ℝ × D → E}
    (hf : Continuous f) (hs : RadialAlias.RadiallySupported a b f)
    {x : ℝ × D} (hx : x.1 ∉ Ioo a b) : f x = 0 := by
  have hslice : Continuous (fun r => f (r, x.2)) :=
    hf.comp (continuous_id.prodMk continuous_const)
  have hclosed : support (fun r => f (r, x.2)) ⊆ Icc a b := fun r hr => hs hr
  have hopen : support (fun r => f (r, x.2)) ⊆ Ioo a b := by
    simpa only [interior_Icc] using hslice.isOpen_support.subset_interior_iff.mpr hclosed
  by_contra hn
  exact hx (hopen hn)

/-- Flatness, rather than a new global-bound hypothesis, removes the radial
edge loss.  The input is the manuscript's concrete logarithmic mean class. -/
theorem meanClass_globalBandJets
    {a b cL cR : ℝ} (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1)
    (hS : ∀ n, 1 ≤ S n) {α : ℝ} {f : ℕ → ℝ × D → E}
    (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hs : ∀ n, RadialAlias.RadiallySupported a b (f n))
    (hclass : MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α f) :
    GlobalBandJets ε S α f := by
  intro m
  obtain ⟨C, hC, p, hb⟩ := hclass.bounds m
  obtain ⟨B, hB, hweight⟩ := weight_uniform_bound hcL hcR (logLength a b) p
  refine ⟨C * B, mul_nonneg hC hB, p, ?_⟩
  intro n x j hj
  have hA : 0 ≤ C * (ε n) ^ α * (S n) ^ p :=
    mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos (hε n) α).le)
      (pow_nonneg (zero_le_one.trans (hS n)) p)
  by_cases hx : x.1 ∈ Ioo a b
  · have h := hb n x hx j hj
    rw [logStrip_majorant_eq ha hcL hcR ε S hε hεone hS α C p n x hx] at h
    calc
      _ ≤ (C * (ε n) ^ α * (S n) ^ p) * logWeight cL cR a b p x.1 := h
      _ ≤ (C * (ε n) ^ α * (S n) ^ p) * B :=
        mul_le_mul_of_nonneg_left (hweight _ (logPosition_mem ha hx)) hA
      _ = _ := by ring
  · rw [supported_zero_outside_open (TransportPrimitive.iteratedFDeriv_contDiff (hf n) j).continuous
      (TransportPrimitive.iteratedFDeriv_supported (hs n) j) hx, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC hB)
      (Real.rpow_pos_of_pos (hε n) α).le) (pow_nonneg (zero_le_one.trans (hS n)) p)

/-- Exact higher chain rule for an affine map. -/
theorem iteratedFDeriv_affine (L : D →L[ℝ] E) (v : E) {f : E → F}
    (hf : ContDiff ℝ ∞ f) (j : ℕ) (x : D) :
    iteratedFDeriv ℝ j (fun y => f (L y + v)) x =
      (iteratedFDeriv ℝ j f (L x + v)).compContinuousLinearMap (fun _ => L) := by
  have ht : ContDiff ℝ ∞ (fun y => f (y + v)) :=
    hf.comp (contDiff_id.add contDiff_const)
  have he := L.iteratedFDeriv_comp_right ht x
    (show (j : WithTop ℕ∞) ≤ ∞ from by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
  simpa only [Function.comp_def, iteratedFDeriv_comp_add_right] using he

theorem norm_iteratedFDeriv_affine_le (L : D →L[ℝ] E) (hL : ‖L‖ ≤ 1)
    (v : E) {f : E → F} (hf : ContDiff ℝ ∞ f) (j : ℕ) (x : D) :
    ‖iteratedFDeriv ℝ j (fun y => f (L y + v)) x‖ ≤
      ‖iteratedFDeriv ℝ j f (L x + v)‖ := by
  rw [iteratedFDeriv_affine L v hf]
  refine ((iteratedFDeriv ℝ j f (L x + v)).norm_compContinuousLinearMap_le _).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg L) hL)

/-- The unweighted slow strip keeps precisely the same band scales. -/
noncomputable def slowStripData (ε S : ℕ → ℝ)
    (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hS : ∀ n, 1 ≤ S n) :
    StripData D where
  domain := univ
  isOpen_domain := isOpen_univ
  epsilon := ε
  epsilon_pos := hε
  epsilon_le_one := hεone
  slow := S
  one_le_slow := hS
  delta := fun _ => 1
  delta_pos := fun _ _ => zero_lt_one
  zeta := fun _ => 1
  zeta_smooth := contDiffOn_const
  zeta_nonneg := fun _ _ => zero_le_one

theorem globalBandJets_unweighted {ε S : ℕ → ℝ} {α : ℝ} {f : ℕ → D → E}
    (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hS : ∀ n, 1 ≤ S n)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hjets : GlobalBandJets ε S α f) :
    UnweightedClass (slowStripData (D := D) ε S hε hεone hS) α f := by
  refine ⟨fun _ _ _ => zero_le_one, fun n => (hf n).contDiffOn, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hjets m
  refine ⟨C, hC, p, ?_⟩
  intro n x _ j hj
  simpa only [majorant, StripData.growth, slowStripData, inv_one, max_self, mul_one]
    using hb n x j hj

theorem globalBandJets_unweighted_log {a b cL cR : ℝ}
    (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    {ε S : ℕ → ℝ} {α : ℝ} {f : ℕ → ℝ × D → E}
    (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hS : ∀ n, 1 ≤ S n)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hjets : GlobalBandJets ε S α f) :
    UnweightedClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α f := by
  let s := logStripData (E := D) a b cL cR ha hcL hcR ε S hε hεone hS
  refine ⟨fun _ _ _ => zero_le_one, fun n => (hf n).contDiffOn, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hjets m
  refine ⟨C, hC, p, ?_⟩
  intro n x _ j hj
  apply (hb n x j hj).trans
  change C * (ε n) ^ α * (S n) ^ p ≤ C * (ε n) ^ α * s.growth n x ^ p * 1
  rw [mul_one]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (zero_le_one.trans (hS n)) (s.slow_le_growth n x) p)
    (mul_nonneg hC (Real.rpow_pos_of_pos (hε n) α).le)

theorem GlobalBandJets.compLinear {ε S : ℕ → ℝ} {α : ℝ} {f : ℕ → E → F}
    (hjets : GlobalBandJets ε S α f) (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (L : D →L[ℝ] E) (hL : ‖L‖ ≤ 1) :
    GlobalBandJets ε S α (fun n x => f n (L x)) := by
  intro m
  obtain ⟨C, hC, p, hb⟩ := hjets m
  refine ⟨C, hC, p, ?_⟩
  intro n x j hj
  have h := norm_iteratedFDeriv_affine_le L hL 0 (hf n) j x
  simp only [add_zero] at h
  exact h.trans (hb n (L x) j hj)

section AffineAverage

variable [CompleteSpace F]

/-- A finite affine average; coordinate projections and torus insertion are
special cases. -/
noncomputable def affineAverage (L : D →L[ℝ] E) (v : E) (a b : ℝ) (f : E → F) (x : D) : F :=
  ∫ t in a..b, f (L x + t • v)

theorem affineAverage_contDiff (L : D →L[ℝ] E) (v : E) (a b : ℝ) {f : E → F}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (affineAverage L v a b f) := by
  exact TransportPrimitive.parameterIntegral_contDiff
    (g := fun q : D × ℝ => f (L q.1 + q.2 • v))
    (hf.comp ((L.contDiff.comp contDiff_fst).add (contDiff_snd.smul contDiff_const))) a b

omit [CompleteSpace F] in
theorem iteratedFDeriv_affineAverage (L : D →L[ℝ] E) (hL : ‖L‖ ≤ 1)
    (v : E) {a b : ℝ} (hab : a ≤ b) {f : E → F} (hf : ContDiff ℝ ∞ f)
    (hb : ∀ k : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ C)
    (j : ℕ) (x : D) :
    iteratedFDeriv ℝ j (affineAverage L v a b f) x =
      ∫ t in a..b, iteratedFDeriv ℝ j (fun y => f (L y + t • v)) x := by
  let μ := volume.restrict (Ioc a b)
  let g : D → ℝ → F := fun y t => f (L y + t • v)
  have hsm : ∀ᵐ t ∂μ, ContDiff ℝ ∞ (fun y => g y t) :=
    Eventually.of_forall fun t => hf.comp (L.contDiff.add contDiff_const)
  have hm : ∀ k y, AEStronglyMeasurable (SmoothParameterIntegral.jet g k y) μ := by
    intro k y
    have hc : Continuous (fun t : ℝ =>
        (iteratedFDeriv ℝ k f (L y + t • v)).compContinuousLinearMap (fun _ => L)) :=
      (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin k => L)).continuous.comp
        ((hf.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).comp
          (continuous_const.add (continuous_id.smul continuous_const)))
    have he : SmoothParameterIntegral.jet g k y = fun t : ℝ =>
        (iteratedFDeriv ℝ k f (L y + t • v)).compContinuousLinearMap (fun _ => L) :=
      funext fun t => iteratedFDeriv_affine L (t • v) hf k y
    rw [he]
    exact hc.aestronglyMeasurable
  have hd : SmoothParameterIntegral.LocallyDominated g μ := by
    intro k y
    obtain ⟨C, hC⟩ := hb k
    refine ⟨1, zero_lt_one, fun _ => C, ?_, Eventually.of_forall fun t z _ => ?_⟩
    · exact integrable_const _
    · exact (norm_iteratedFDeriv_affine_le L hL (t • v) hf k z).trans (hC _)
  have he := SmoothParameterIntegral.iteratedFDeriv_integral hsm hm hd j x
  have hg : affineAverage L v a b f = fun y => ∫ t, g y t ∂μ := by
    funext y
    exact intervalIntegral.integral_of_le hab
  rw [hg]
  simpa only [μ, g, ← intervalIntegral.integral_of_le hab] using he

omit [CompleteSpace F] in
theorem affineAverage_jet_bound (L : D →L[ℝ] E) (hL : ‖L‖ ≤ 1)
    (v : E) {a b : ℝ} (hab : a ≤ b) {f : E → F} (hf : ContDiff ℝ ∞ f)
    (hb : ∀ k : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ C)
    (j : ℕ) (x : D) (C : ℝ)
    (hC : ∀ t ∈ Icc a b, ‖iteratedFDeriv ℝ j f (L x + t • v)‖ ≤ C) :
    ‖iteratedFDeriv ℝ j (affineAverage L v a b f) x‖ ≤ C * (b - a) := by
  rw [iteratedFDeriv_affineAverage L hL v hab hf hb]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (fun t ht => (norm_iteratedFDeriv_affine_le L hL (t • v) hf j x).trans
      (hC t (by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc ht)))
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using h

omit [CompleteSpace F] in
theorem GlobalBandJets.affineAverage {ε S : ℕ → ℝ} {α : ℝ} {f : ℕ → E → F}
    (hjets : GlobalBandJets ε S α f) (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (L : D →L[ℝ] E) (hL : ‖L‖ ≤ 1) (v : E) {a b : ℝ} (hab : a ≤ b) :
    GlobalBandJets ε S α (fun n => affineAverage L v a b (f n)) := by
  intro m
  obtain ⟨C, hC, p, hb⟩ := hjets m
  refine ⟨C * (b - a), mul_nonneg hC (sub_nonneg.mpr hab), p, ?_⟩
  intro n x j hj
  have hall : ∀ k : ℕ, ∃ B : ℝ, ∀ y, ‖iteratedFDeriv ℝ k (f n) y‖ ≤ B := by
    intro k
    obtain ⟨B, _, q, hB⟩ := hjets k
    exact ⟨B * (ε n) ^ α * (S n) ^ q, fun y => hB n y k le_rfl⟩
  have h := affineAverage_jet_bound L hL v hab (hf n) hall j x
    (C * (ε n) ^ α * (S n) ^ p) (fun t _ => hb n _ j hj)
  convert! h using 1; ring

end AffineAverage

section Torus

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

noncomputable def eraseAuxX : PressureStream.Lift P →L[ℝ] PressureStream.Lift P where
  toFun x := (x.1, (x.2.1, (0, x.2.2.2)))
  map_add' := by intros; ext <;> simp
  map_smul' := by intros; ext <;> simp
  cont := continuous_fst.prodMk (continuous_snd.fst.prodMk
    (continuous_const.prodMk continuous_snd.snd.snd))

noncomputable def eraseAuxY : PressureStream.Lift P →L[ℝ] PressureStream.Lift P where
  toFun x := (x.1, (x.2.1, (x.2.2.1, 0)))
  map_add' := by intros; ext <;> simp
  map_smul' := by intros; ext <;> simp
  cont := continuous_fst.prodMk (continuous_snd.fst.prodMk
    (continuous_snd.snd.fst.prodMk continuous_const))

theorem norm_eraseAuxX_le : ‖eraseAuxX (P := P)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖(x.1, (x.2.1, (0, x.2.2.2)))‖ ≤ 1 * ‖x‖
  simp only [one_mul, Prod.norm_def, norm_zero]
  exact max_le_max le_rfl (max_le_max le_rfl (max_le_max (norm_nonneg _) le_rfl))

theorem norm_eraseAuxY_le : ‖eraseAuxY (P := P)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖(x.1, (x.2.1, (x.2.2.1, 0)))‖ ≤ 1 * ‖x‖
  simp only [one_mul, Prod.norm_def, norm_zero]
  exact max_le_max le_rfl (max_le_max le_rfl (max_le_max le_rfl (norm_nonneg _)))

noncomputable def auxX : PressureStream.Lift P := (0, (0, (1, 0)))
noncomputable def auxY : PressureStream.Lift P := (0, (0, (0, 1)))

@[simp] theorem eraseAuxX_add_smul (x : PressureStream.Lift P) (t : ℝ) :
    eraseAuxX x + t • auxX = (x.1, (x.2.1, (t, x.2.2.2))) := by
  ext <;> simp [eraseAuxX, auxX]

@[simp] theorem eraseAuxY_add_smul (x : PressureStream.Lift P) (t : ℝ) :
    eraseAuxY x + t • auxY = (x.1, (x.2.1, (x.2.2.1, t))) := by
  ext <;> simp [eraseAuxY, auxY]

noncomputable def liftedTorusAverage (f : PressureStream.Lift P → ℝ)
    (x : PressureStream.Lift P) : ℝ := PressureStream.torusAverage f (x.1, x.2.1)

theorem liftedTorusAverage_eq_affine (f : PressureStream.Lift P → ℝ) :
    liftedTorusAverage f = affineAverage eraseAuxY auxY 0 1
      (affineAverage eraseAuxX auxX 0 1 f) := by
  funext x
  simp only [affineAverage, eraseAuxY_add_smul, eraseAuxX_add_smul,
    liftedTorusAverage, PressureStream.torusAverage, PressureStream.torusInner]

theorem liftedTorusAverage_contDiff {f : PressureStream.Lift P → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (liftedTorusAverage f) :=
  (PressureStream.torusAverage_contDiff hf).comp (contDiff_fst.prodMk contDiff_snd.fst)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem liftedTorusAverage_supported {a b : ℝ} {f : PressureStream.Lift P → ℝ}
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (liftedTorusAverage f) := by
  intro x hx
  exact PressureStream.torusAverage_supported hs hx

theorem GlobalBandJets.liftedTorusAverage {ε S : ℕ → ℝ} {α : ℝ}
    {f : ℕ → PressureStream.Lift P → ℝ}
    (hjets : GlobalBandJets ε S α f) (hf : ∀ n, ContDiff ℝ ∞ (f n)) :
    GlobalBandJets ε S α (fun n => liftedTorusAverage (f n)) := by
  have hinner := hjets.affineAverage hf eraseAuxX norm_eraseAuxX_le auxX zero_le_one
  have houter := hinner.affineAverage
    (fun n => affineAverage_contDiff eraseAuxX auxX 0 1 (hf n))
    eraseAuxY norm_eraseAuxY_le auxY zero_le_one
  simpa only [liftedTorusAverage_eq_affine] using houter

end Torus

section RadialIntegral

variable [CompleteSpace E]

omit [CompleteSpace E] in
theorem totalIntegral_zero_eq (f : ℝ × D → E) (x : ℝ × D) :
    TransportPrimitive.totalIntegral 0 0 f x = ∫ r, f (r, x.2) := by
  simp only [TransportPrimitive.totalIntegral, TransportPrimitive.shift, zero_mul,
    zero_smul]
  change (∫ u, f (x.1 + u, x.2 + 0)) = _
  simp only [add_zero]
  exact integral_add_left_eq_self (μ := volume) (fun r => f (r, x.2)) x.1

theorem GlobalBandJets.radialIntegral {ε S : ℕ → ℝ} {α a b : ℝ}
    {f : ℕ → ℝ × D → E} (hjets : GlobalBandJets ε S α f)
    (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hs : ∀ n, RadialAlias.RadiallySupported a b (f n)) (hab : a ≤ b) :
    GlobalBandJets ε S α (fun n => TransportPrimitive.totalIntegral 0 0 (f n)) := by
  intro m
  obtain ⟨C, hC, p, hb⟩ := hjets m
  refine ⟨C * (b - a), mul_nonneg hC (sub_nonneg.mpr hab), p, ?_⟩
  intro n x j hj
  have h := TransportPrimitive.iteratedFDeriv_totalIntegral_norm_le
    (M := 0) (v := (0 : D)) hab (hf n) (hs n) j
    (fun r _ y => hb n (r, y) j hj) x
  convert! h using 1; ring

end RadialIntegral

section PressureMass

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

noncomputable def liftedPressureMass (f : PressureStream.Lift P → ℝ)
    (x : PressureStream.Lift P) : ℝ := PressureStream.pressureMass f x.2.1

theorem liftedPressureMass_eq (f : PressureStream.Lift P → ℝ) :
    liftedPressureMass f = TransportPrimitive.totalIntegral 0 0 (liftedTorusAverage f) := by
  funext x
  rw [totalIntegral_zero_eq]
  rfl

theorem liftedPressureMass_contDiff {a b : ℝ} {f : PressureStream.Lift P → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f) :
    ContDiff ℝ ∞ (liftedPressureMass f) :=
  (PressureStream.pressureMass_contDiff hf hs).comp contDiff_snd.fst

theorem GlobalBandJets.liftedPressureMass {ε S : ℕ → ℝ} {α a b : ℝ}
    {f : ℕ → PressureStream.Lift P → ℝ}
    (hjets : GlobalBandJets ε S α f) (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hs : ∀ n, RadialAlias.RadiallySupported a b (f n)) (hab : a ≤ b) :
    GlobalBandJets ε S α (fun n => liftedPressureMass (f n)) := by
  have h := (hjets.liftedTorusAverage hf).radialIntegral
    (fun n => liftedTorusAverage_contDiff (hf n))
    (fun n => liftedTorusAverage_supported (hs n)) hab
  simpa only [liftedPressureMass_eq] using h

/-- The actual pressure defect, lifted to the original strip, belongs to
`S_α`.  There is no pressure-mass or differentiated-integral estimate premise. -/
theorem meanClass_pressureMass_lift
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1)
    (hS : ∀ n, 1 ≤ S n) {α : ℝ} {f : ℕ → PressureStream.Lift P → ℝ}
    (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hs : ∀ n, RadialAlias.RadiallySupported a b (f n))
    (hclass : MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α f) :
    UnweightedClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α
      (fun n (x : PressureStream.Lift P) => PressureStream.pressureMass (f n) x.2.1) := by
  apply globalBandJets_unweighted_log ha hcL hcR hε hεone hS
    (fun n => liftedPressureMass_contDiff (hf n) (hs n))
  exact (meanClass_globalBandJets ha hcL hcR ε S hε hεone hS hf hs hclass).liftedPressureMass
    hf hs hab.le

noncomputable def insertSlow : P →L[ℝ] PressureStream.Lift P where
  toFun p := (0, (p, (0, 0)))
  map_add' := by intros; ext <;> simp
  map_smul' := by intros; ext <;> simp
  cont := continuous_const.prodMk (continuous_id.prodMk continuous_const)

theorem norm_insertSlow_le : ‖insertSlow (P := P)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  change ‖((0 : ℝ), (p, ((0 : ℝ), (0 : ℝ))))‖ ≤ 1 * ‖p‖
  simp only [one_mul, Prod.norm_def, norm_zero, max_self,
    max_eq_left (norm_nonneg p), max_eq_right (norm_nonneg p)]
  exact le_rfl

/-- The same actual pressure moment as a function of only the slow variables. -/
theorem meanClass_pressureMass
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1)
    (hS : ∀ n, 1 ≤ S n) {α : ℝ} {f : ℕ → PressureStream.Lift P → ℝ}
    (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hs : ∀ n, RadialAlias.RadiallySupported a b (f n))
    (hclass : MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α f) :
    UnweightedClass (slowStripData (D := P) ε S hε hεone hS) α
      (fun n => PressureStream.pressureMass (f n)) := by
  apply globalBandJets_unweighted hε hεone hS
    (fun n => PressureStream.pressureMass_contDiff (hf n) (hs n))
  have hbase := meanClass_globalBandJets ha hcL hcR ε S hε hεone hS hf hs hclass
  have h := (hbase.liftedPressureMass hf hs hab.le).compLinear
      (fun n => liftedPressureMass_contDiff (hf n) (hs n)) insertSlow norm_insertSlow_le
  exact h

end PressureMass

section WeightedMoments

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem radialCoefficient_unweighted
    {a b cL cR : ℝ} (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1)
    (hS : ∀ n, 1 ≤ S n) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    UnweightedClass (logStripData (E := P) a b cL cR ha hcL hcR ε S hε hεone hS) 0
      (fun _ x => g x.1) := by
  apply unweighted_of_finiteJetBounds _ _ (hg.comp contDiff_fst).contDiffOn
  intro m
  obtain ⟨C, _, hb⟩ := cutoff_finiteJet_bound (E := P) a b g hg m
  exact ⟨C, fun j hj x hx => hb j hj x ⟨hx.1.le, hx.2.le⟩⟩

noncomputable def radialWeighted (k : ℕ) (f : ℝ × P → ℝ) (x : ℝ × P) : ℝ :=
  x.1 ^ k * f x

theorem radialWeighted_contDiff (k : ℕ) {f : ℝ × P → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (radialWeighted k f) := (contDiff_fst.pow k).mul hf

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem radialWeighted_supported (k : ℕ) {a b : ℝ} {f : ℝ × P → ℝ}
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (radialWeighted k f) := by
  intro x hx
  exact hs (right_ne_zero_of_mul hx)

theorem meanClass_radialWeighted
    {a b cL cR : ℝ} (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1)
    (hS : ∀ n, 1 ≤ S n) {α : ℝ} {f : ℕ → ℝ × P → ℝ}
    (hclass : MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α f)
    (k : ℕ) :
    MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α
      (fun n => radialWeighted k (f n)) := by
  have hc := radialCoefficient_unweighted (P := P) (b := b) ha hcL hcR ε S hε hεone hS
    (g := fun r : ℝ => r ^ k) (contDiff_id.pow k)
  have h := hc.mul hclass
  simp only [zero_add, one_mul] at h
  exact h

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The radial power is outside the auxiliary torus average, exactly as in
the pressure and two integrated flux defects. -/
theorem pressureMass_radialWeighted (k : ℕ) (f : PressureStream.Lift P → ℝ) (p : P) :
    PressureStream.pressureMass (radialWeighted k f) p =
      IntegratedMeanBalances.radialMoment k (PressureStream.torusAverage f) p := by
  simp only [PressureStream.pressureMass, PressureStream.torusAverage,
    PressureStream.torusInner, radialWeighted, IntegratedMeanBalances.radialMoment,
    IntegratedMeanBalances.moment, intervalIntegral.integral_const_mul]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem pressureMass_radialWeighted_fun (k : ℕ) (f : PressureStream.Lift P → ℝ) :
    PressureStream.pressureMass (radialWeighted k f) =
      IntegratedMeanBalances.radialMoment k (PressureStream.torusAverage f) :=
  funext (pressureMass_radialWeighted k f)

/-- Every fixed radial moment of the actual torus mean is an unweighted slow
coefficient of the same band order. -/
theorem meanClass_radialMoment
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1)
    (hS : ∀ n, 1 ≤ S n) {α : ℝ} {f : ℕ → PressureStream.Lift P → ℝ}
    (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hs : ∀ n, RadialAlias.RadiallySupported a b (f n))
    (hclass : MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α f)
    (k : ℕ) :
    UnweightedClass (slowStripData (D := P) ε S hε hεone hS) α
      (fun n => IntegratedMeanBalances.radialMoment k (PressureStream.torusAverage (f n))) := by
  have h := meanClass_pressureMass ha hab hcL hcR ε S hε hεone hS
    (fun n => radialWeighted_contDiff k (hf n))
    (fun n => radialWeighted_supported k (hs n))
    (meanClass_radialWeighted ha hcL hcR ε S hε hεone hS hclass k)
  simpa only [pressureMass_radialWeighted_fun] using h

theorem meanClass_radialMoment_lift
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1)
    (hS : ∀ n, 1 ≤ S n) {α : ℝ} {f : ℕ → PressureStream.Lift P → ℝ}
    (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hs : ∀ n, RadialAlias.RadiallySupported a b (f n))
    (hclass : MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α f)
    (k : ℕ) :
    UnweightedClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α
      (fun n (x : PressureStream.Lift P) => IntegratedMeanBalances.radialMoment k
        (PressureStream.torusAverage (f n)) x.2.1) := by
  have h := meanClass_pressureMass_lift ha hab hcL hcR ε S hε hεone hS
    (fun n => radialWeighted_contDiff k (hf n))
    (fun n => radialWeighted_supported k (hs n))
    (meanClass_radialWeighted ha hcL hcR ε S hε hεone hS hclass k)
  simpa only [pressureMass_radialWeighted] using h

end WeightedMoments

end

end NavierStokes.MeanMomentBounds
