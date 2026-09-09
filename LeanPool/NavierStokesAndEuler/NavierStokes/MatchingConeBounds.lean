/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.MatchingDebtBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.OutgoingEntranceCone

/-!
# Cone bounds through the shape transition and moment repair

The source estimates use the actual fields and their radial averages.  The
large natural logarithmic gradient is retained in the growing term rather
than estimated by an absolute constant.
-/

@[expose] public section


noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff BigOperators

namespace NavierStokes.MatchingConeBounds

open ProfileHistories NaturalAxisData


theorem logShape_hasDerivAt (eta : ℝ) :
    HasDerivAt ShapeTransition.logShape (-OutgoingEntranceCone.shapeGradient eta) eta := by
  have he : ShapeTransition.logShape = fun e : ℝ => -Real.log (1 + e ^ 2) := by
    funext e
    simp [ShapeTransition.logShape, OutgoingSchedule.shape, Real.log_inv]
  rw [he]
  convert! ((((hasDerivAt_id eta).fun_pow 2).const_add 1).log (by positivity)).fun_neg using 1
  simp [OutgoingEntranceCone.shapeGradient, id_eq]

theorem shape_axis_lower {h j eta ell theta : ℝ}
    (hs : SmallParameters h j) (hη : eta ∈ Icc (-1 : ℝ) 1)
    (hl : 11 / 20 ≤ ell) (ht : theta ∈ Icc (0 : ℝ) 1) :
    (8 / 5 : ℝ) < -W h j eta * ell - h * (1 - 2 * eta * U j eta) +
      theta * H h j eta * OutgoingEntranceCone.shapeGradient eta := by
  have heta : |eta| ≤ 1 := abs_le.mpr hη
  have hd0 := d_nonneg hη
  have hd1 : d eta ≤ 1 := by unfold d; nlinarith [sq_nonneg eta]
  have hD := D_pos hs
  have hu : |U j eta| ≤ 4001 / 1000 := by
    calc
      _ ≤ |4 * eta| + |j| := abs_add_le _ _
      _ = 4 * |eta| + j := by rw [abs_mul, abs_of_pos hs.j_pos]; norm_num
      _ ≤ _ := by linarith [hs.j_le]
  have hup : |eta * U j eta| ≤ 4001 / 1000 := by
    rw [abs_mul]
    exact (mul_le_mul heta hu (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have hterm : h * (1 - 2 * eta * U j eta) ≤ 4501 / 500000 := by
    have he : 1 - 2 * eta * U j eta ≤ 4501 / 500 := by
      linarith [(abs_le.mp hup).1]
    have h1 := mul_le_mul_of_nonneg_left he hs.h_pos.le
    have h2 := mul_le_mul_of_nonneg_right hs.h_le (by norm_num : (0 : ℝ) ≤ 4501 / 500)
    linarith
  have hgabs : |OutgoingEntranceCone.shapeGradient eta| ≤ 2 :=
    (OutgoingEntranceCone.abs_shapeGradient_le eta).trans (by linarith)
  have hget : 0 ≤ eta * OutgoingEntranceCone.shapeGradient eta :=
    (sq_nonneg eta).trans (OutgoingEntranceCone.eta_shapeGradient_bounds heta).1
  have hmain : 0 ≤ (D h + 4 * d eta) * (eta * OutgoingEntranceCone.shapeGradient eta) :=
    mul_nonneg (by positivity) hget
  have hdj : 0 ≤ d eta * j := mul_nonneg hd0 hs.j_pos.le
  have hdj1 : d eta * j ≤ 1 / 1000 :=
    (mul_le_of_le_one_left hs.j_pos.le hd1).trans hs.j_le
  have herr : -(1 / 500 : ℝ) ≤ d eta * j * OutgoingEntranceCone.shapeGradient eta := by
    have hm := mul_le_mul_of_nonneg_left (abs_le.mp hgabs).1 hdj
    nlinarith
  have hid : H h j eta * OutgoingEntranceCone.shapeGradient eta =
      (D h + 4 * d eta) * (eta * OutgoingEntranceCone.shapeGradient eta) +
        d eta * j * OutgoingEntranceCone.shapeGradient eta := by
    unfold H U
    ring
  have hH : -(1 / 500 : ℝ) ≤ H h j eta * OutgoingEntranceCone.shapeGradient eta := by
    rw [hid]
    linarith
  have htheta : -(1 / 500 : ℝ) ≤ theta * H h j eta * OutgoingEntranceCone.shapeGradient eta := by
    have hm := mul_le_mul_of_nonneg_left hH ht.1
    nlinarith [ht.2]
  have hW := neg_W_lower_bound hs hη
  have hbase : (2991 / 1000 : ℝ) * (11 / 20) ≤ -W h j eta * ell :=
    mul_le_mul hW hl (by norm_num) (by linarith)
  linarith

/-- Shape remainder as an element of `ℝ`. -/
noncomputable def shapeRemainder (h j sigma eta theta ell : ℝ) (v : Fin 5 → ℝ) (t : ℝ) : ℝ :=
  let Wc := W h j eta - t * (2 * D h * eta * v 2 + d eta * v 3)
  let Uc := U j eta + t * v 1
  let Hc := H h j eta + t * d eta * v 1
  show ℝ from -Wc * ell - h * (1 - 2 * eta * Uc) + theta * Hc * OutgoingEntranceCone.shapeGradient
      eta -
    (1 - theta) * (Hc * v 4 + d eta * v 1 * NaturalAxisCoefficients.realGradient h j sigma eta)

/-- Shape parameter: an abbreviation for `Icc (-1 : ℝ) 1 × (Icc (0 : ℝ) 1 × (Icc (11 / 20 : ℝ)
(13 / 20) × ReferenceBounds.BoundedJets B))`. -/
abbrev ShapeParameter (B : ℝ) :=
  Icc (-1 : ℝ) 1 × (Icc (0 : ℝ) 1 × (Icc (11 / 20 : ℝ) (13 / 20) × ReferenceBounds.BoundedJets B))

/-- Shape model, given by `shapeRemainder h j sigma p.1.val p.2.1.val p.2.2.1.val p.2.2.2.val
t`. -/
noncomputable def shapeModel (h j sigma B : ℝ) (p : ShapeParameter B) (t : ℝ) : ℝ :=
  shapeRemainder h j sigma p.1.val p.2.1.val p.2.2.1.val p.2.2.2.val t

theorem shapeModel_continuous (h j B : ℝ) {sigma : ℝ} (hsigma : 0 < sigma) :
    Continuous (fun p : ShapeParameter B × ℝ => shapeModel h j sigma B p.1 p.2) := by
  have hg := NaturalEntrance.realGradient_continuous h j hsigma
  have hs := OutgoingEntranceCone.shapeGradient_contDiff.continuous
  have he : Continuous (fun p : ShapeParameter B × ℝ => p.1.1.val) := by fun_prop
  have hv (i : Fin 5) : Continuous (fun p : ShapeParameter B × ℝ => p.1.2.2.2.val i) :=
    (continuous_apply i).comp (by fun_prop)
  have hgc := hg.comp he
  have hsc := hs.comp he
  dsimp only [shapeModel, shapeRemainder, W, H, U, D, d]
  fun_prop

theorem shapeModel_zero_lower {h j sigma B : ℝ} (hs : SmallParameters h j)
    (hsigma : 0 < sigma) (p : ShapeParameter B)
    (hz : (1 - p.2.1.val) * L h p.1.val * chi h j sigma p.1.val = 0) :
    (3 / 2 : ℝ) < shapeModel h j sigma B p 0 := by
  have ha := shape_axis_lower hs p.1.property p.2.2.1.property.1 p.2.1.property
  have hcases : p.2.1.val = 1 ∨ chi h j sigma p.1.val = 0 := by
    rcases mul_eq_zero.mp hz with hleft | hright
    · have ht := (mul_eq_zero.mp hleft).resolve_right (L_pos hs p.1.property).ne'
      left
      linarith
    · exact Or.inr hright
  rcases hcases with ht | hc
  · simp only [shapeModel, shapeRemainder, ht, zero_mul, sub_zero, add_zero,
      sub_self, one_mul] at ha ⊢
    linarith
  · have hH := NaturalEntrance.chi_zero_imp_H_zero h j hsigma hc
    have hg := NaturalEntrance.gradient_zero_of_chi_zero h j hsigma hc
    simp only [shapeModel, shapeRemainder, zero_mul, mul_zero, sub_zero, add_zero, hH, hg]
    rw [hH] at ha
    simp only [mul_zero, zero_mul, add_zero] at ha
    linarith

theorem shapeModel_uniform_lower {h j sigma : ℝ} (hs : SmallParameters h j)
    (hsigma : 0 < sigma) (B : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ Λ : ℝ, M ≤ Λ → ∀ p : ShapeParameter B,
      (5 / 4 : ℝ) < Λ * ((1 - p.2.1.val) * L h p.1.val * chi h j sigma p.1.val) +
        shapeModel h j sigma B p (1 / Λ) := by
  have hcoef : Continuous (fun p : ShapeParameter B =>
      (1 - p.2.1.val) * L h p.1.val * chi h j sigma p.1.val) := by
    have hc := NaturalEntrance.chi_continuous h j hsigma
    unfold L
    fun_prop
  have hbase : Continuous (fun p : ShapeParameter B => shapeModel h j sigma B p 0) := by
    simpa only [Function.comp_def, id_eq] using (shapeModel_continuous h j B hsigma).comp
      (continuous_id.prodMk (continuous_const (y := (0 : ℝ))))
  obtain ⟨M0, hM0, hmain⟩ := NaturalEntrance.compact_absorption _ _ hcoef hbase
    (fun p => mul_nonneg (mul_nonneg (sub_nonneg.mpr p.2.1.property.2)
      (L_pos hs p.1.property).le) (NaturalAxisData.chi_bounds h j hsigma p.1.val).1)
    (3 / 2 : ℝ) (shapeModel_zero_lower hs hsigma)
  obtain ⟨tau, htau, hpert⟩ := NaturalEntrance.compact_small_perturbation _
    (shapeModel_continuous h j B hsigma) (by norm_num : (0 : ℝ) < 1 / 4)
  refine ⟨max M0 (1 + 1 / tau), hM0.trans_le (le_max_left _ _), ?_⟩
  intro Λ hΛ p
  have hΛp : 0 < Λ := hM0.trans_le ((le_max_left _ _).trans hΛ)
  have ht : ‖(1 / Λ : ℝ)‖ < tau := by
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hΛp), div_lt_iff₀ hΛp]
    have hm := (div_lt_iff₀ htau).mp (show 1 / tau < Λ by
      have := (le_max_right M0 (1 + 1 / tau)).trans hΛ
      linarith)
    nlinarith
  have he := (abs_lt.mp (hpert p (1 / Λ) ht)).1
  have hm := hmain Λ ((le_max_left _ _).trans hΛ) p
  linarith

/-- Shape jet, given by `![1, Λ * (P.U p - U j p.2), Λ * (P.Ubar p - U j p.2), Λ * (average
(parameterPartial P.U) p - 4), g]`. -/
noncomputable def shapeJet {D : RadialDomain} (P : Profiles D) (_h j Λ g : ℝ)
    (p : Point) : Fin 5 → ℝ :=
  ![1, Λ * (P.U p - U j p.2), Λ * (P.Ubar p - U j p.2),
    Λ * (average (parameterPartial P.U) p - 4), g]

theorem shapeSource_identity {D : RadialDomain} (P : Profiles D)
    (h j sigma Λ theta ell g : ℝ) (hΛ : Λ ≠ 0) (p : Point)
    (hl : ReferenceBounds.logSlope P p = ell)
    (hg : parameterPartial P.f p / P.f p =
      (1 - theta) * (Λ * NaturalAxisCoefficients.realGradient h j sigma p.2 + g) -
        theta * OutgoingEntranceCone.shapeGradient p.2) :
    ReferenceBounds.sourceQ P h p =
      Λ * ((1 - theta) * L h p.2 * chi h j sigma p.2) +
        shapeRemainder h j sigma p.2 theta ell (shapeJet P h j Λ g p) (1 / Λ) := by
  have hU : U j p.2 + (1 / Λ) * (Λ * (P.U p - U j p.2)) = P.U p := by
    field_simp; ring
  have hW : W h j p.2 - (1 / Λ) *
      (2 * NaturalAxisData.D h * p.2 * (Λ * (P.Ubar p - U j p.2)) +
        d p.2 * (Λ * (average (parameterPartial P.U) p - 4))) = P.W h p := by
    unfold W U Profiles.W NaturalAxisData.D d StressAlgebra.axialExponent
        StressAlgebra.coordinateFactor
    field_simp; ring
  have hH : H h j p.2 + (1 / Λ) * d p.2 * (Λ * (P.U p - U j p.2)) =
      NaturalAxisData.D h * p.2 + d p.2 * P.U p := by
    unfold H
    field_simp; ring
  rw [ReferenceBounds.sourceQ, hl, hg]
  simp only [shapeRemainder, shapeJet, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.isValue, hU, hW, hH]
  have hid := NaturalProfile.gradient_identity h j sigma p.2
  unfold H at hid
  dsimp only [StressAlgebra.axialExponent, StressAlgebra.coordinateFactor, NaturalAxisData.D, d] at
      *
  linear_combination -(1 - theta) * Λ * hid

/-- Uniform positivity for the literal convex interpolation of the old and
target parameter gradients.  The hypotheses concern only low-order actual
field jets; no angular-stock or cone estimate is assumed. -/
theorem actual_shape_source_threshold {h j sigma B : ℝ}
    (hs : SmallParameters h j) (hsigma : 0 < sigma) (hB : 1 ≤ B) :
    ∃ M : ℝ, 0 < M ∧ ∀ Λ : ℝ, M ≤ Λ →
      ∀ {D : RadialDomain} (P : Profiles D) (p : Point) (theta ell g : ℝ),
      p.2 ∈ Icc (-1 : ℝ) 1 → theta ∈ Icc (0 : ℝ) 1 → ell ∈ Icc (11 / 20 : ℝ) (13 / 20) →
      ReferenceBounds.logSlope P p = ell →
      parameterPartial P.f p / P.f p =
        (1 - theta) * (Λ * NaturalAxisCoefficients.realGradient h j sigma p.2 + g) -
          theta * OutgoingEntranceCone.shapeGradient p.2 →
      |Λ * (P.U p - U j p.2)| ≤ B → |Λ * (P.Ubar p - U j p.2)| ≤ B →
      |Λ * (average (parameterPartial P.U) p - 4)| ≤ B → |g| ≤ B →
      (5 / 4 : ℝ) < ReferenceBounds.sourceQ P h p := by
  obtain ⟨M, hM, hm⟩ := shapeModel_uniform_lower hs hsigma B
  refine ⟨M, hM, ?_⟩
  intro Λ hΛ D P p theta ell g hη ht hl hle hg hu hv hvη hgb
  have hj : shapeJet P h j Λ g p ∈ ReferenceBounds.BoundedJets B := by
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (zero_le_one.trans hB)]
    intro i
    fin_cases i
    · simpa [shapeJet] using hB
    · simpa [shapeJet, Real.norm_eq_abs, abs_mul] using hu
    · simpa [shapeJet, Real.norm_eq_abs, abs_mul] using hv
    · simpa [shapeJet, Real.norm_eq_abs, abs_mul] using hvη
    · simpa [shapeJet, Real.norm_eq_abs] using hgb
  let sample : ShapeParameter B := (⟨p.2, hη⟩, ⟨theta, ht⟩, ⟨ell, hl⟩, ⟨shapeJet P h j Λ g p, hj⟩)
  have he := hm Λ hΛ sample
  rw [shapeSource_identity P h j sigma Λ theta ell g (hM.trans_le hΛ).ne' p hle hg]
  exact he

/-- Angular gap, given by `primitive (P.angularSource h) (X, eta) - 2 * L h eta * P.H (X, eta)`. -/
noncomputable def angularGap {D : RadialDomain} (P : Profiles D) (h eta X : ℝ) : ℝ :=
  primitive (P.angularSource h) (X, eta) - 2 * L h eta * P.H (X, eta)

theorem angularGap_hasDerivAt {D : RadialDomain} (P : Profiles D) (h : ℝ)
    {eta X : ℝ} (hp : (X, eta) ∈ D.carrier) :
    HasDerivAt (angularGap P h eta)
      (P.angularSource h (X, eta) - 2 * L h eta * radialPartial P.H (X, eta)) X :=
  (primitive_hasDerivAt D (P.angularSource_smooth h) hp).sub
    ((radialPartial_hasDerivAt D P.H_smooth hp).const_mul (2 * L h eta))

/-- A barrier with a variable logarithmic slope. It uses the actual source
primitive and the actual integrating factor `H`. -/
theorem angular_barrier {D : RadialDomain} (P : Profiles D) {h eta a X : ℝ}
    (ha : 2 ≤ a) (haX : a ≤ X) (hL : 0 < L h eta) (hL1 : L h eta ≤ 1)
    (hmem : ∀ s ∈ Icc a X, (s, eta) ∈ D.carrier)
    (hf : ∀ s ∈ Icc a X, 0 < P.f (s, eta))
    (hl : ∀ s ∈ Icc a X, ReferenceBounds.logSlope P (s, eta) ≤ 1)
    (hq : ∀ s ∈ Icc a X, 1 < ReferenceBounds.sourceQ P h (s, eta))
    (hinit : 2 < ReferenceBounds.p1 P h (a, eta)) :
    2 < ReferenceBounds.p1 P h (X, eta) := by
  have hspos (s : ℝ) (hs : s ∈ Icc a X) : 0 < s := lt_of_lt_of_le (by linarith) hs.1
  have hHpos (s : ℝ) (hs : s ∈ Icc a X) : 0 < P.H (s, eta) := by
    change 0 < 2 * s * P.f (s, eta)
    exact mul_pos (mul_pos (by norm_num) (hspos s hs)) (hf s hs)
  have hder (s : ℝ) (hs : s ∈ Icc a X) :
      0 ≤ P.angularSource h (s, eta) - 2 * L h eta * radialPartial P.H (s, eta) := by
    have hdot : s * radialPartial P.H (s, eta) =
        P.H (s, eta) * ReferenceBounds.logSlope P (s, eta) := by
      rw [ReferenceBounds.H_radialPartial P (hmem s hs)]
      unfold Profiles.H ReferenceBounds.logSlope
      dsimp only
      field_simp [(hf s hs).ne']
    have he := ReferenceBounds.angularSource_eq P (hmem s hs) (hf s hs).ne' h
    have hterm : 2 * L h eta * ReferenceBounds.logSlope P (s, eta) ≤ 2 := by
      have hh := mul_le_mul_of_nonneg_left (hl s hs) (show 0 ≤ 2 * L h eta by positivity)
      nlinarith
    have hsq : 2 < s * ReferenceBounds.sourceQ P h (s, eta) := by
      have hh := mul_lt_mul_of_pos_left (hq s hs) (hspos s hs)
      linarith [hs.1]
    have hprod : 0 ≤ P.H (s, eta) *
        (s * ReferenceBounds.sourceQ P h (s, eta) - 2 * L h eta * ReferenceBounds.logSlope P (s,
            eta)) :=
      mul_nonneg (hHpos s hs).le (by linarith)
    rw [he]
    nlinarith [hspos s hs]
  have hm : MonotoneOn (angularGap P h eta) (Icc a X) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a X)
    · intro s hs
      exact (angularGap_hasDerivAt P h (hmem s hs)).continuousAt.continuousWithinAt
    · intro s hs
      exact (angularGap_hasDerivAt P h (hmem s (interior_subset hs))).hasDerivWithinAt
    · intro s hs
      exact hder s (interior_subset hs)
  have hini : 0 < angularGap P h eta a := by
    rw [ReferenceBounds.p1_primitive P (hspos a ⟨le_rfl, haX⟩).ne' h] at hinit
    have hi := (lt_div_iff₀ (mul_pos hL (hHpos a ⟨le_rfl, haX⟩))).mp hinit
    unfold angularGap
    nlinarith
  have hout : 0 < angularGap P h eta X := hini.trans_le (hm ⟨le_rfl, haX⟩ ⟨haX, le_rfl⟩ haX)
  rw [ReferenceBounds.p1_primitive P (hspos X ⟨haX, le_rfl⟩).ne' h]
  apply (lt_div_iff₀ (mul_pos hL (hHpos X ⟨haX, le_rfl⟩))).mpr
  unfold angularGap at hout
  nlinarith

theorem shape_relaxed_from_source {D : RadialDomain} (P : Profiles D) {h eta a X : ℝ}
    (ha : 2 ≤ a) (haX : a ≤ X) (hL : 0 < L h eta) (hL1 : L h eta ≤ 1)
    (hmem : ∀ s ∈ Icc a X, (s, eta) ∈ D.carrier)
    (hf : ∀ s ∈ Icc a X, 0 < P.f (s, eta))
    (hl : ∀ s ∈ Icc a X, ReferenceBounds.logSlope P (s, eta) ∈ Icc (11 / 20 : ℝ) (13 / 20))
    (hq : ∀ s ∈ Icc a X, 1 < ReferenceBounds.sourceQ P h (s, eta))
    (hinit : 2 < ReferenceBounds.p1 P h (a, eta))
    (hu : radialPartial P.U (X, eta) = 0) : ActivationContinuation.IsRelaxed P h (X, eta) := by
  have hp := angular_barrier P ha haX hL hL1 hmem hf
    (fun s hs => (hl s hs).2.trans (by norm_num)) hq hinit
  have he := ActivationContinuation.logSlope_eq_shear P (X, eta)
  have hb := hl X ⟨haX, le_rfl⟩
  exact ActivationContinuation.zero_axial_relaxed_profile P
    (by linarith [hb.1, hb.2]) (by linarith [hb.1, hb.2]) hu hp

theorem axial_error_jet {J K : Set ℝ} (R : TransitionRamp.StockReference J)
    (hJ : IsOpen J) (hKJ : K ⊆ J) {N : ℕ} {eps T kappa wU wE y eta : ℝ}
    (hb : 0 ≤ R.bigTime) (hwU : 0 < wU) (hwE : 0 < wE)
    (hc : R.SmallLogControl K N eps T kappa wU wE) (hy : 0 ≤ y) (hη : eta ∈ K)
    {n : ℕ} (hn : n ≤ N) :
    |iteratedDeriv n (fun e => R.axialVelocity T kappa wU (y, e) - R.initialU e) eta| ≤ eps := by
  by_cases hf : y ≤ R.finalTime
  · exact (hc.axial_jets y ⟨hy, hf⟩ eta hη n hn).le
  · have he : (fun e => R.axialVelocity T kappa wU (y, e) - R.initialU e) =ᶠ[𝓝 eta]
        (fun e => R.axialVelocity T kappa wU (R.finalTime, e) - R.initialU e) := by
      filter_upwards [hJ.mem_nhds (hKJ hη)] with e he
      rw [show R.axialVelocity T kappa wU (y, e) =
          R.axialVelocity T kappa wU (R.finalTime, e) from
        TransitionRamp.axialField_hold hwU hJ R.initialU (R.axialStock_smooth hJ)
          (by linarith [hc.finish_before]) (le_of_not_ge hf) he]
    rw [he.iteratedDeriv_eq n]
    exact (hc.axial_jets R.finalTime ⟨hb.trans R.finalTime_gt_bigTime.le, le_rfl⟩ eta hη n hn).le

section IncomingBounds

variable {F : OutgoingProfile.Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A)

theorem seedU_error_jets {N : ℕ} {eps X eta : ℝ}
    (hc : MatchingDebtBounds.SmallControl c N eps) (heps : 0 ≤ eps)
    (hX : 0 ≤ X) (hη : eta ∈ Icc (-1 : ℝ) 1) {n : ℕ} (hn : n ≤ N) :
    |iteratedDeriv n (fun e => c.seedU (X, e) - U A.j e) eta| ≤
      ReferenceJetBounds.jetConstant A.preparation.inputs.coefficients 0 n / A.scale + eps := by
  have hηJ := NaturalAxisCoefficients.original_interval_interior hη
  have hUstar : ContDiff ℝ ∞ (U A.j) := (contDiff_const.mul contDiff_id).add contDiff_const
  by_cases hx : X ≤ c.reference.radius0
  · have hxn : X ≤ 4 / A.scale := by simpa only [c.reference_radius] using hx
    have hY : A.scale * X ∈ Ioo (-20 : ℝ) 20 := by
      have hb := (le_div_iff₀ A.scale_pos).mp hxn
      constructor <;> nlinarith [mul_nonneg A.scale_pos.le hX]
    have he : (fun e => c.seedU (X, e) - U A.j e) =
        (fun e => A.natural.profile.family.U (X, e) - U A.j e) := by
      funext e
      rw [(c.seed_initial (p := (X, e)) hxn).2]
    rw [he, TransitionRamp.naturalU_error_jet A.preparation.inputs A.natural.profile hY hηJ n,
      abs_mul, abs_of_pos (one_div_pos.mpr A.scale_pos)]
    have hY5 : |A.scale * X| ≤ 5 := by
      rw [abs_of_nonneg (mul_nonneg A.scale_pos.le hX)]
      have hb := (le_div_iff₀ A.scale_pos).mp hxn
      nlinarith
    have hb := (ReferenceJetBounds.coefficient_jet_bound A.preparation.inputs.coefficients
      A.natural.profile.coefficients A.natural.profile.norm_ball 0 n (p := (A.scale * X, eta))
          hY5).2
    have hh := mul_le_mul_of_nonneg_left hb (one_div_nonneg.mpr A.scale_pos.le)
    calc
      _ ≤ (1 / A.scale) * ReferenceJetBounds.jetConstant A.preparation.inputs.coefficients 0 n := hh
      _ ≤ _ := by simpa only [one_div_mul_eq_div] using le_add_of_nonneg_right heps
  · have hxR : c.reference.radius0 < X := lt_of_not_ge hx
    have hy : 0 ≤ c.reference.logTime X :=
      Real.log_nonneg ((one_le_div c.reference.radius0_pos).mpr hxR.le)
    have he : (fun e => c.seedU (X, e)) =
        fun e => c.reference.axialVelocity c.activationTime c.kappa c.axialWidth
            (c.reference.logTime X, e) := by
      funext e
      exact ite_eq_right hx
    have hp : (X, eta) ∈ A.referenceInput.radialDomain.carrier :=
      ⟨lt_of_lt_of_le (by norm_num) (mul_nonneg A.scale_pos.le hX), hηJ⟩
    have hseed : ContDiffAt ℝ ∞ (fun e => c.seedU (X, e)) eta :=
      (c.seedU_smooth.contDiffAt (A.referenceInput.radialDomain.isOpen.mem_nhds
        hp)).comp eta
          (contDiffAt_const.prodMk contDiffAt_id)
    have hinit : ContDiffAt ℝ ∞ c.reference.initialU eta :=
      (c.reference.initialU_smooth ReferencePath.parameterInterval_open).contDiffAt
        (ReferencePath.parameterInterval_open.mem_nhds hηJ)
    apply TransitionRamp.jet_transfer n (hseed.sub hUstar.contDiffAt) (hinit.sub hUstar.contDiffAt)
    · have hh := axial_error_jet c.reference ReferencePath.parameterInterval_open
        NaturalAxisCoefficients.original_interval_interior c.reference_before_big.le
        c.axialWidth_pos c.angularWidth_pos hc hy hη hn
      have hfun : (fun e => (c.seedU (X, e) - U A.j e) - (c.reference.initialU e - U A.j e)) =
          fun e => c.reference.axialVelocity c.activationTime c.kappa c.axialWidth
            (c.reference.logTime X, e) - c.reference.initialU e := by
        funext e
        rw [congrFun he e]
        ring
      rwa [hfun]
    · exact TransitionRamp.initialU_error_jet_bound A.scale_pos A.small
        c.referenceWidth_pos c.referenceWidth_small F.axisDatum_contDiff A.natural.profile n hηJ

theorem seedU_scaled_error_jets {N : ℕ} {eps X eta : ℝ}
    (hc : MatchingDebtBounds.SmallControl c N eps) (heps : 0 ≤ eps)
    (hX : 0 ≤ X) (hη : eta ∈ Icc (-1 : ℝ) 1) {n : ℕ} (hn : n ≤ N) :
    |A.scale * iteratedDeriv n (fun e => c.seedU (X, e) - U A.j e) eta| ≤
      ReferenceJetBounds.jetConstant A.preparation.inputs.coefficients 0 n + A.scale * eps := by
  rw [abs_mul, abs_of_pos A.scale_pos]
  have hb := mul_le_mul_of_nonneg_left (seedU_error_jets c hc heps hX hη hn) A.scale_pos.le
  calc
    _ ≤ A.scale * (ReferenceJetBounds.jetConstant A.preparation.inputs.coefficients 0 n / A.scale +
        eps) := hb
    _ = _ := by rw [mul_add, mul_div_cancel₀ _ A.scale_pos.ne']

theorem initialShape_gradient_bound {N : ℕ} {eps eta : ℝ}
    (hc : MatchingDebtBounds.SmallControl c N eps) (hN : 1 ≤ N)
    (hscale : AxisReference.stabilityScale A.preparation.inputs.coefficients.epsilon
      (NaturalProfile.profileErrorConstant A.preparation.inputs) ≤ A.scale)
    (hη : eta ∈ Icc (-1 : ℝ) 1) :
    |deriv c.initialShape eta - A.scale * NaturalAxisCoefficients.realGradient
      F.data.h A.j A.preparation.sigma eta| ≤
      8 * ReferenceJetBounds.jetConstant A.preparation.inputs.coefficients 0 1 + eps := by
  have hηJ := NaturalAxisCoefficients.original_interval_interior hη
  let L0 := c.reference.initialLog
  let L1 := fun e => c.reference.logAmplitude c.activationTime c.kappa c.axialWidth
    c.angularWidth (c.reference.finalTime, e)
  have h0 : DifferentiableAt ℝ L0 eta :=
    (c.reference.initialLog_smooth ReferencePath.parameterInterval_open).differentiableOn
      (by simp) eta hηJ |>.differentiableAt (ReferencePath.parameterInterval_open.mem_nhds hηJ)
  have h1 : DifferentiableAt ℝ L1 eta := by
    have hp : (c.reference.finalTime, eta) ∈
        (StressActivation.logDomain ReferencePath.parameterInterval
          ReferencePath.parameterInterval_open).carrier := ⟨mem_univ _, hηJ⟩
    exact ((c.reference.logAmplitude_smooth ReferencePath.parameterInterval_open _ _ _ _).contDiffAt
      ((StressActivation.logDomain _ _).isOpen.mem_nhds hp)).differentiableAt (by simp) |>.comp eta
        ((differentiableAt_const c.reference.finalTime).prodMk differentiableAt_id)
  have herr := hc.positive_log_jets c.reference.finalTime
    ⟨c.reference_before_big.le.trans c.reference.finalTime_gt_bigTime.le, le_rfl⟩ eta hη 1 hN (by
        norm_num)
  change |iteratedDeriv 1 (fun e => L1 e - L0 e) eta| < eps at herr
  rw [iteratedDeriv_one, deriv_fun_sub h1 h0] at herr
  have hfinal : deriv c.initialShape eta = deriv L1 eta := by
    exact (h1.hasDerivAt.const_add (Real.log A.normalization + Real.log 220 / 2)).deriv
  have hi : L0 = fun e => Real.log (A.natural.profile.family.f (A.referenceInput.endpoint, e)) := by
    funext e
    exact TransitionRamp.initialLog_natural A.natural.profile.family A.scale_pos A.small
      c.referenceWidth_pos c.referenceWidth_small F.axisDatum_contDiff e
  have hm := ReferenceJetBounds.endpoint_mem A.referenceInput hη
  have hn := A.referenceInput.endpoint_f_pos hηJ
  have hd := (ReferenceJetBounds.parameter_deriv
    (A.natural.profile.family.natural.f_smooth.contDiffAt
      ((NaturalProfile.domain_isOpen A.scale).mem_nhds hm))).log hn.ne'
  have hinit : deriv L0 eta = parameterPartial A.natural.profile.family.f
      (A.referenceInput.endpoint, eta) / A.natural.profile.family.f (A.referenceInput.endpoint,
          eta) := by
    rw [hi]
    exact hd.deriv
  have hnat := ReferenceJetBounds.natural_log_bound A.natural.profile A.preparation.sigma_pos
    A.scale_pos A.normalization_pos hscale (p := (A.referenceInput.endpoint, eta))
      (by
        change NaturalProfile.rescalePoint A.scale
          ((ReferencePath.Input.ofNatural A.scale_pos A.natural.profile.family).endpoint, eta) ∈ _
        rw [TransitionRamp.endpoint_rescale A.natural.profile.family A.scale_pos]
        exact ⟨by norm_num, hη⟩)
  rw [hfinal]
  calc
    _ = |(deriv L1 eta - deriv L0 eta) + (deriv L0 eta - A.scale *
      NaturalAxisCoefficients.realGradient F.data.h A.j A.preparation.sigma eta)| := by
          congr 1; ring
    _ ≤ |deriv L1 eta - deriv L0 eta| + |deriv L0 eta - A.scale *
      NaturalAxisCoefficients.realGradient F.data.h A.j A.preparation.sigma eta| := abs_add_le _ _
    _ ≤ _ := by
      have hb : |deriv L0 eta - A.scale * NaturalAxisCoefficients.realGradient
          F.data.h A.j A.preparation.sigma eta| ≤
            8 * ReferenceJetBounds.jetConstant A.preparation.inputs.coefficients 0 1 := by
        simpa only [hinit] using hnat
      linarith

theorem seedU_source_jets {N : ℕ} {eps X eta : ℝ}
    (hc : MatchingDebtBounds.SmallControl c N eps) (heps : 0 ≤ eps) (hN : 1 ≤ N)
    (hX : 0 ≤ X) (hη : eta ∈ Icc (-1 : ℝ) 1) :
    |A.scale * (c.seedU (X, eta) - U A.j eta)| ≤
      ReferenceJetBounds.jetConstant A.preparation.inputs.coefficients 0 0 + A.scale * eps ∧
    |A.scale * (parameterPartial c.seedU (X, eta) - 4)| ≤
      ReferenceJetBounds.jetConstant A.preparation.inputs.coefficients 0 1 + A.scale * eps := by
  have h0 := seedU_scaled_error_jets c hc heps hX hη (n := 0) (Nat.zero_le _)
  have h1 := seedU_scaled_error_jets c hc heps hX hη hN
  have hp := ReferenceJetBounds.reference_mem A.referenceInput (p := (X, eta)) hX hη
  have hd := ReferenceJetBounds.parameter_deriv
    (c.seedU_smooth.contDiffAt (A.referenceInput.radialDomain.isOpen.mem_nhds hp))
  have hs : HasDerivAt (U A.j) 4 eta := by
    convert! ((hasDerivAt_id eta).const_mul 4).add_const A.j using 1
    simp []
  rw [iteratedDeriv_one, (hd.fun_sub hs).deriv] at h1
  exact ⟨h0, h1⟩

theorem profiles_before_restore (hsep : c.separation ≤ Real.exp (-8))
    {p : Point} (hX : p.1 ≤ c.radius * Real.exp (-8)) :
    (c.profiles hsep).U p = c.seedU p ∧ (c.profiles hsep).f p = c.shapedF p := by
  have hx : p.1 / c.radius ≤ Real.exp (-8) :=
    (div_le_iff₀ c.radius_pos).mpr (by simpa only [mul_comm] using hX)
  have hb : p.1 / c.radius ≤ NominalProfile.resetPatch.left := hx.trans
    (Real.exp_le_exp.mpr (by norm_num : (-8 : ℝ) ≤ -6))
  have he := NominalProfile.joined_before_patch F A.normalization c.shapeTime
    c.initialShape c.seedF c.seedU (p := (p.1 / c.radius, p.2)) hb
  have hU : c.U p = c.seedU p := by
    change NominalProfile.joinedU F A.normalization c.shapeTime c.initialShape c.seedF c.seedU
      (p.1 / c.radius, p.2) = _
    rw [he.1]
    change NominalProfile.restoredU c.radius c.seedU (c.radius * (p.1 / c.radius), p.2) = _
    rw [mul_div_cancel₀ _ c.radius_pos.ne', NominalProfile.restoredU_before c.radius_pos hX]
  have hE : c.E p = Real.sqrt (2 * p.1) * c.shapedF p := by
    change NominalProfile.joinedE F A.normalization c.shapeTime c.initialShape c.seedF c.seedU
      (p.1 / c.radius, p.2) = _
    rw [he.2]
    change Real.sqrt (2 * (c.radius * (p.1 / c.radius))) *
      c.shapedF (c.radius * (p.1 / c.radius), p.2) = _
    rw [mul_div_cancel₀ _ c.radius_pos.ne']
  refine ⟨hU, ?_⟩
  by_cases hi : p.1 ≤ NominalProfile.Xi
  · exact (c.f_before_Xi hi).trans
      (ShapeTransition.shapeField_before NominalProfile.Xi_pos c.shapeTime_pos hi _ _ _).symm
  · change c.f p = _
    rw [NominalProfile.Controls.f, ite_eq_right hi, hE]
    exact mul_div_cancel_left₀ _ (Real.sqrt_pos.mpr (show 0 < 2 * p.1 by
      have := NominalProfile.Xi_pos.trans (lt_of_not_ge hi)
      positivity)).ne'

theorem profiles_source_jets (hsep : c.separation ≤ Real.exp (-8))
    {N : ℕ} {eps X eta : ℝ}
    (hc : MatchingDebtBounds.SmallControl c N eps) (heps : 0 ≤ eps) (hN : 1 ≤ N)
    (hX : 0 ≤ X) (hR : X ≤ c.radius * Real.exp (-8))
    (hη : eta ∈ Icc (-1 : ℝ) 1) (hsmall : NominalProfile.SmallDebt F c.debt eta) :
    |A.scale * ((c.profiles hsep).U (X, eta) - U A.j eta)| ≤
      ReferenceJetBounds.jetConstant A.preparation.inputs.coefficients 0 0 + A.scale * eps ∧
    |A.scale * ((c.profiles hsep).Ubar (X, eta) - U A.j eta)| ≤
      ReferenceJetBounds.jetConstant A.preparation.inputs.coefficients 0 0 + A.scale * eps ∧
    |A.scale * (average (parameterPartial (c.profiles hsep).U) (X, eta) - 4)| ≤
      ReferenceJetBounds.jetConstant A.preparation.inputs.coefficients 0 1 + A.scale * eps := by
  have hh : ∀ t ∈ Icc (0 : ℝ) 1, t * X ≤ c.radius * Real.exp (-8) :=
    fun t ht => (mul_le_of_le_one_left hX ht.2).trans hR
  have hu : ∀ t ∈ Icc (0 : ℝ) 1,
      |A.scale * ((c.profiles hsep).U (t * X, eta) - U A.j eta)| ≤
        ReferenceJetBounds.jetConstant A.preparation.inputs.coefficients 0 0 + A.scale * eps := by
    intro t ht
    rw [(profiles_before_restore c hsep (hh t ht)).1]
    exact (seedU_source_jets c hc heps hN (mul_nonneg ht.1 hX) hη).1
  have huη : ∀ t ∈ Icc (0 : ℝ) 1,
      |A.scale * (parameterPartial (c.profiles hsep).U (t * X, eta) - 4)| ≤
        ReferenceJetBounds.jetConstant A.preparation.inputs.coefficients 0 1 + A.scale * eps := by
    intro t ht
    have hf : (fun e => (c.profiles hsep).U (t * X, e)) = fun e => c.seedU (t * X, e) := by
      funext e
      exact (profiles_before_restore c hsep (hh t ht)).1
    have hp := c.admissible_nonnegative (p := (t * X, eta)) (mul_nonneg ht.1 hX)
      (NaturalAxisCoefficients.original_interval_interior hη) hsmall
    have hseed := ReferenceJetBounds.reference_mem A.referenceInput
      (p := (t * X, eta)) (mul_nonneg ht.1 hX) hη
    have he := congrArg (fun f : ℝ → ℝ => deriv f eta) hf
    rw [(parameterPartial_hasDerivAt c.admissibleDomain (c.profiles hsep).U_smooth hp).deriv,
      (parameterPartial_hasDerivAt A.referenceInput.radialDomain c.seedU_smooth hseed).deriv] at he
    rw [he]
    exact (seedU_source_jets c hc heps hN (mul_nonneg ht.1 hX) hη).2
  have hp := c.admissible_nonnegative (p := (X, eta)) hX
    (NaturalAxisCoefficients.original_interval_interior hη) hsmall
  refine ⟨?_, ReferenceBounds.average_error_bound (c.profiles hsep).U_smooth hp hu,
    ReferenceBounds.average_error_bound (parameterPartial_smooth c.admissibleDomain
      (c.profiles hsep).U_smooth) hp huη⟩
  simpa only [one_mul] using hu 1 ⟨zero_le_one, le_rfl⟩

end IncomingBounds

theorem deriv_eqOn_Ici {f g : ℝ → ℝ} {a x : ℝ} (hx : a ≤ x)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (he : EqOn f g (Ici a)) : deriv f x = deriv g x := by
  exact (uniqueDiffOn_Ici a x hx).eq_deriv _ hf.hasDerivAt.hasDerivWithinAt
    (hg.hasDerivAt.hasDerivWithinAt.congr_of_mem he hx)

theorem deriv_eqOn_Iic {f g : ℝ → ℝ} {a x : ℝ} (hx : x ≤ a)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (he : EqOn f g (Iic a)) : deriv f x = deriv g x := by
  exact (uniqueDiffOn_Iic a x hx).eq_deriv _ hf.hasDerivAt.hasDerivWithinAt
    (hg.hasDerivAt.hasDerivWithinAt.congr_of_mem he hx)

/-- Shape value, given by `ShapeTransition.angular C T li (Real.log (X / NominalProfile.Xi),
eta) / Real.sqrt (2 * X)`. -/
noncomputable def shapeValue (C T : ℝ) (li : ℝ → ℝ) (X eta : ℝ) : ℝ :=
  ShapeTransition.angular C T li (Real.log (X / NominalProfile.Xi), eta) / Real.sqrt (2 * X)

theorem shapeValue_hasDerivAt_x (C T : ℝ) (li : ℝ → ℝ) {X : ℝ} (hX : 0 < X) (eta : ℝ) :
    HasDerivAt (fun s => shapeValue C T li s eta)
      (shapeValue C T li X eta *
        (ShapeTransition.logarithmicSlope T li (Real.log (X / NominalProfile.Xi), eta) - 1) / X) X
            := by
  have hx : HasDerivAt (fun s : ℝ => Real.log (s / NominalProfile.Xi)) (1 / X) X := by
    convert! ((hasDerivAt_id X).div_const NominalProfile.Xi).log
      (div_ne_zero hX.ne' NominalProfile.Xi_pos.ne') using 1
    norm_num [NominalProfile.Xi, div_eq_mul_inv]
    ring
  have ha := ((ShapeTransition.logProfile_hasDerivAt C T li
    (Real.log (X / NominalProfile.Xi)) eta).comp X hx).exp
  have hr : HasDerivAt (fun s : ℝ => Real.sqrt (2 * s)) (1 / Real.sqrt (2 * X)) X := by
    convert! ((hasDerivAt_id X).const_mul 2).sqrt (show 2 * X ≠ 0 by positivity) using 1
    simp only [id_eq]
    ring
  have hroot := Real.sqrt_pos.mpr (show 0 < 2 * X by positivity)
  have hsq := Real.sq_sqrt (show 0 ≤ 2 * X by positivity)
  convert! ha.div hr hroot.ne' using 1
  dsimp only [shapeValue, ShapeTransition.angular, Function.comp_def, Function.comp_apply]
  generalize hk : Real.exp (ShapeTransition.logProfile C T li
    (Real.log (X / NominalProfile.Xi), eta)) = k
  generalize hr' : Real.sqrt (2 * X) = r at hroot hsq ⊢
  field_simp [hX.ne', hroot.ne']
  linear_combination -k * hsq

theorem shapeValue_hasDerivAt_eta (C T : ℝ) {li : ℝ → ℝ} {X eta : ℝ}
    (hli : DifferentiableAt ℝ li eta) :
    HasDerivAt (shapeValue C T li X)
      (shapeValue C T li X eta *
        ((1 - OutgoingSchedule.sigma (Real.log (X / NominalProfile.Xi) / T)) * deriv li eta -
          OutgoingSchedule.sigma (Real.log (X / NominalProfile.Xi) / T) *
            OutgoingEntranceCone.shapeGradient eta)) eta := by
  have hd := (((hli.hasDerivAt.const_mul
      (1 - OutgoingSchedule.sigma (Real.log (X / NominalProfile.Xi) / T))).fun_add
    ((logShape_hasDerivAt eta).const_mul
      (OutgoingSchedule.sigma (Real.log (X / NominalProfile.Xi) / T)))).const_add
        (-Real.log C + Real.log (X / NominalProfile.Xi) / 10)).exp.div_const (Real.sqrt (2 * X))
  convert! hd using 1
  dsimp only [shapeValue, ShapeTransition.angular, ShapeTransition.logProfile,
      ShapeTransition.blend]
  ring

section ShapeCoordinates

variable {F : OutgoingProfile.Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) (hsep : c.separation ≤ Real.exp (-8))

theorem shapedF_value {X eta : ℝ} (hX : NominalProfile.Xi ≤ X)
    (hη : eta ∈ ReferencePath.parameterInterval) :
    c.shapedF (X, eta) = shapeValue A.normalization c.shapeTime c.initialShape X eta :=
  ShapeTransition.shapeField_eq_profile NominalProfile.Xi_pos A.normalization_pos
    c.shapeTime_pos (NominalProfile.Xi_pos.trans_le hX) _ _ _ (c.seedF_held hX hη)

theorem profiles_shape_value {X eta : ℝ} (hX : NominalProfile.Xi ≤ X)
    (hR : X ≤ c.radius * Real.exp (-8)) (hη : eta ∈ ReferencePath.parameterInterval) :
    (c.profiles hsep).f (X, eta) = shapeValue A.normalization c.shapeTime c.initialShape X eta :=
  (profiles_before_restore c hsep hR).2.trans (shapedF_value c hX hη)

theorem profiles_shape_positive {X eta : ℝ} (hX : 0 ≤ X)
    (hR : X ≤ c.radius * Real.exp (-8)) (hη : eta ∈ ReferencePath.parameterInterval) :
    0 < (c.profiles hsep).f (X, eta) := by
  rw [(profiles_before_restore c hsep hR).2]
  exact mul_pos (c.seedF_positive hη hX) (Real.exp_pos _)

theorem profiles_shape_radialU {X eta : ℝ} (hX : NominalProfile.Xi ≤ X)
    (hR : X ≤ c.radius * Real.exp (-8)) (hη : eta ∈ ReferencePath.parameterInterval)
    (hsmall : NominalProfile.SmallDebt F c.debt eta) :
    radialPartial (c.profiles hsep).U (X, eta) = 0 := by
  have hX0 := NominalProfile.Xi_pos.trans_le hX
  have hp := c.admissible_nonnegative (p := (X, eta)) hX0.le hη hsmall
  have hs : (X, eta) ∈ A.referenceInput.radialDomain.carrier := hp.1
  have hdP := radialPartial_hasDerivAt c.admissibleDomain (c.profiles hsep).U_smooth hp
  have hdS := radialPartial_hasDerivAt A.referenceInput.radialDomain c.seedU_smooth hs
  have he := deriv_eqOn_Iic hR hdP.differentiableAt hdS.differentiableAt
    (fun s hs => (profiles_before_restore c hsep (p := (s, eta)) hs).1)
  have hc := deriv_eqOn_Ici hX hdS.differentiableAt
    (differentiableAt_const (c.initialAxial eta)) (fun s hs => c.seedU_held hs hη)
  rw [hdP.deriv] at he
  rw [he, hc, deriv_const]

theorem profiles_shape_radialF {X eta : ℝ} (hX : NominalProfile.Xi ≤ X)
    (hR : X ≤ c.radius * Real.exp (-8)) (hη : eta ∈ ReferencePath.parameterInterval)
    (hsmall : NominalProfile.SmallDebt F c.debt eta) :
    radialPartial (c.profiles hsep).f (X, eta) =
      (c.profiles hsep).f (X, eta) *
        (ShapeTransition.logarithmicSlope c.shapeTime c.initialShape
          (Real.log (X / NominalProfile.Xi), eta) - 1) / X := by
  have hX0 := NominalProfile.Xi_pos.trans_le hX
  have hp := c.admissible_nonnegative (p := (X, eta)) hX0.le hη hsmall
  have hdP := radialPartial_hasDerivAt c.admissibleDomain (c.profiles hsep).f_smooth hp
  have hdS := radialPartial_hasDerivAt A.referenceInput.radialDomain c.shapedF_smooth hp.1
  have hdV := shapeValue_hasDerivAt_x A.normalization c.shapeTime c.initialShape hX0 eta
  have he := deriv_eqOn_Iic hR hdP.differentiableAt hdS.differentiableAt
    (fun s hs => (profiles_before_restore c hsep (p := (s, eta)) hs).2)
  have hv := deriv_eqOn_Ici hX hdS.differentiableAt hdV.differentiableAt
    (fun s hs => shapedF_value c hs hη)
  rw [hdP.deriv, hv, hdV.deriv] at he
  rw [he, profiles_shape_value c hsep hX hR hη]

theorem profiles_shape_logSlope {X eta : ℝ} (hX : NominalProfile.Xi ≤ X)
    (hR : X ≤ c.radius * Real.exp (-8)) (hη : eta ∈ ReferencePath.parameterInterval)
    (hsmall : NominalProfile.SmallDebt F c.debt eta) :
    ReferenceBounds.logSlope (c.profiles hsep) (X, eta) =
      ShapeTransition.logarithmicSlope c.shapeTime c.initialShape
        (Real.log (X / NominalProfile.Xi), eta) := by
  have hX0 := NominalProfile.Xi_pos.trans_le hX
  have hf := profiles_shape_positive c hsep hX0.le hR hη
  unfold ReferenceBounds.logSlope
  rw [profiles_shape_radialF c hsep hX hR hη hsmall]
  dsimp only
  field_simp; ring

theorem profiles_shape_gradient {X eta : ℝ} (hX : NominalProfile.Xi ≤ X)
    (hR : X ≤ c.radius * Real.exp (-8)) (hη : eta ∈ ReferencePath.parameterInterval)
    (hsmall : NominalProfile.SmallDebt F c.debt eta) :
    parameterPartial (c.profiles hsep).f (X, eta) / (c.profiles hsep).f (X, eta) =
      (1 - OutgoingSchedule.sigma (Real.log (X / NominalProfile.Xi) / c.shapeTime)) *
        deriv c.initialShape eta -
      OutgoingSchedule.sigma (Real.log (X / NominalProfile.Xi) / c.shapeTime) *
        OutgoingEntranceCone.shapeGradient eta := by
  have hX0 := NominalProfile.Xi_pos.trans_le hX
  have hp := c.admissible_nonnegative (p := (X, eta)) hX0.le hη hsmall
  have hf := profiles_shape_positive c hsep hX0.le hR hη
  have hdP := parameterPartial_hasDerivAt c.admissibleDomain (c.profiles hsep).f_smooth hp
  have hdV := shapeValue_hasDerivAt_eta A.normalization c.shapeTime
    (X := X) ((c.initialShape_smooth.contDiffAt
      (ReferencePath.parameterInterval_open.mem_nhds hη)).differentiableAt (by simp))
  have he : (fun e => (c.profiles hsep).f (X, e)) =ᶠ[𝓝 eta]
      shapeValue A.normalization c.shapeTime c.initialShape X := by
    filter_upwards [ReferencePath.parameterInterval_open.mem_nhds hη] with e he
    exact profiles_shape_value c hsep hX hR he
  have he' := he.deriv_eq
  rw [hdP.deriv, hdV.deriv] at he'
  rw [he', ← profiles_shape_value c hsep hX hR hη, mul_div_cancel_left₀ _ hf.ne']

end ShapeCoordinates

/-- Shape constant, given by `1 + ReferenceJetBounds.jetConstant prep.inputs.coefficients 0 0 +
9 * ReferenceJetBounds.jetConstant prep.inputs.coefficients 0 1`. -/
noncomputable def shapeConstant {F : OutgoingProfile.Profile} {j : ℝ}
    (prep : NominalProfile.AxisPreparation F j) : ℝ :=
  1 + ReferenceJetBounds.jetConstant prep.inputs.coefficients 0 0 +
    9 * ReferenceJetBounds.jetConstant prep.inputs.coefficients 0 1

theorem shapeConstant_one {F : OutgoingProfile.Profile} {j : ℝ}
    (prep : NominalProfile.AxisPreparation F j) : 1 ≤ shapeConstant prep := by
  have h0 := ReferenceJetBounds.jetConstant_nonneg prep.inputs.coefficients 0 0
  have h1 := ReferenceJetBounds.jetConstant_nonneg prep.inputs.coefficients 0 1
  unfold shapeConstant
  linarith

/-- The shape-source scale depends on the fixed natural-axis data, before
the normalization or continuation controls are chosen. -/
noncomputable def shapeScale {F : OutgoingProfile.Profile} {j : ℝ}
    (hj : SmallParameters F.data.h j) (prep : NominalProfile.AxisPreparation F j) : ℝ :=
  max 1 (max
    (AxisReference.stabilityScale prep.inputs.coefficients.epsilon
      (NaturalProfile.profileErrorConstant prep.inputs))
    (Classical.choose (actual_shape_source_threshold hj prep.sigma_pos (shapeConstant_one prep))))

theorem shapeScale_one {F : OutgoingProfile.Profile} {j : ℝ}
    (hj : SmallParameters F.data.h j) (prep : NominalProfile.AxisPreparation F j) :
    1 ≤ shapeScale hj prep := le_max_left _ _

section ActualShapeCone

variable {F : OutgoingProfile.Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) (hsep : c.separation ≤ Real.exp (-8))

theorem actual_shape_source {eps X eta : ℝ}
    (hscale : shapeScale A.small A.preparation ≤ A.scale)
    (hc : MatchingDebtBounds.SmallControl c 1 eps) (heps : 0 ≤ eps)
    (heps1 : eps ≤ min 1 (1 / A.scale))
    (hX : NominalProfile.Xi ≤ X) (hR : X ≤ c.radius * Real.exp (-8))
    (hη : eta ∈ Icc (-1 : ℝ) 1) (hsmall : NominalProfile.SmallDebt F c.debt eta)
    (hl : ReferenceBounds.logSlope (c.profiles hsep) (X, eta) ∈
      Icc (11 / 20 : ℝ) (13 / 20)) :
    (5 / 4 : ℝ) < ReferenceBounds.sourceQ (c.profiles hsep) F.data.h (X, eta) := by
  have hnatural : AxisReference.stabilityScale A.preparation.inputs.coefficients.epsilon
      (NaturalProfile.profileErrorConstant A.preparation.inputs) ≤ A.scale :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hscale)
  have hthreshold := Classical.choose_spec
    (actual_shape_source_threshold A.small A.preparation.sigma_pos (shapeConstant_one
        A.preparation))
  have hM : Classical.choose
      (actual_shape_source_threshold A.small A.preparation.sigma_pos (shapeConstant_one
          A.preparation)) ≤ A.scale :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hscale)
  have hjets := profiles_source_jets c hsep hc heps le_rfl
    (NominalProfile.Xi_pos.le.trans hX) hR hη hsmall
  have hgrad := initialShape_gradient_bound c hc le_rfl hnatural hη
  have h0 := ReferenceJetBounds.jetConstant_nonneg A.preparation.inputs.coefficients 0 0
  have h1 := ReferenceJetBounds.jetConstant_nonneg A.preparation.inputs.coefficients 0 1
  have he1 : eps ≤ 1 := heps1.trans (min_le_left _ _)
  have heL : A.scale * eps ≤ 1 := by
    have hh := (le_div_iff₀ A.scale_pos).mp (heps1.trans (min_le_right _ _))
    linarith
  let theta := OutgoingSchedule.sigma (Real.log (X / NominalProfile.Xi) / c.shapeTime)
  let g := deriv c.initialShape eta - A.scale * NaturalAxisCoefficients.realGradient
    F.data.h A.j A.preparation.sigma eta
  apply hthreshold.2 A.scale hM (c.profiles hsep) (X, eta) theta
    (ReferenceBounds.logSlope (c.profiles hsep) (X, eta)) g hη
    ⟨OutgoingSchedule.sigma_nonneg _, OutgoingSchedule.sigma_le_one _⟩ hl rfl
  · rw [profiles_shape_gradient c hsep hX hR
      (NaturalAxisCoefficients.original_interval_interior hη) hsmall]
    dsimp only [g, theta]
    ring
  · exact hjets.1.trans (by unfold shapeConstant; linarith)
  · exact hjets.2.1.trans (by unfold shapeConstant; linarith)
  · exact hjets.2.2.trans (by unfold shapeConstant; linarith)
  · exact hgrad.trans (by unfold shapeConstant; linarith)

/-- The actual shape interval satisfies the relaxed cone. The sole stock
input is the incoming value at `Xi`, supplied by the same continuation
witness; the angular source and its propagation are proved here. -/
theorem actual_shape_relaxed {N : ℕ} {rho eps X eta : ℝ}
    (hm : MatchingDebtBounds.MatchingBounds c N rho)
    (hrho : rho ≤ NominalProfile.resetSolver.radius)
    (hscale : shapeScale A.small A.preparation ≤ A.scale)
    (hc : MatchingDebtBounds.SmallControl c 1 eps) (heps : 0 ≤ eps)
    (heps1 : eps ≤ min 1 (1 / A.scale))
    (hX : NominalProfile.Xi ≤ X) (hR : X ≤ c.radius * Real.exp (-8))
    (hη : eta ∈ Icc (-1 : ℝ) 1)
    (hinit : 2 < ReferenceBounds.p1 (c.profiles hsep) F.data.h (NominalProfile.Xi, eta)) :
    2 < ReferenceBounds.p1 (c.profiles hsep) F.data.h (X, eta) ∧
      ActivationContinuation.IsRelaxed (c.profiles hsep) F.data.h (X, eta) := by
  have hsmall := hm.smallDebt hrho hη
  have hηJ := NaturalAxisCoefficients.original_interval_interior hη
  have hL := L_pos A.small hη
  have hL1 : L F.data.h eta ≤ 1 := by
    unfold L
    nlinarith [A.small.h_pos, sq_nonneg eta]
  have hmem : ∀ s ∈ Icc NominalProfile.Xi X, (s, eta) ∈ c.admissibleDomain.carrier := by
    intro s hs
    exact c.admissible_nonnegative (p := (s, eta)) (NominalProfile.Xi_pos.le.trans hs.1) hηJ hsmall
  have hf : ∀ s ∈ Icc NominalProfile.Xi X, 0 < (c.profiles hsep).f (s, eta) := by
    intro s hs
    exact profiles_shape_positive c hsep (NominalProfile.Xi_pos.le.trans hs.1)
      (hs.2.trans hR) hηJ
  have hl : ∀ s ∈ Icc NominalProfile.Xi X,
      ReferenceBounds.logSlope (c.profiles hsep) (s, eta) ∈ Icc (11 / 20 : ℝ) (13 / 20) := by
    intro s hs
    rw [profiles_shape_logSlope c hsep hs.1 (hs.2.trans hR) hηJ hsmall,
      ShapeTransition.logarithmicSlope_eq A.normalization]
    exact hm.shape_slope _ eta hη
  have hq : ∀ s ∈ Icc NominalProfile.Xi X,
      1 < ReferenceBounds.sourceQ (c.profiles hsep) F.data.h (s, eta) := by
    intro s hs
    exact (by norm_num : (1 : ℝ) < 5 / 4).trans
      (actual_shape_source c hsep hscale hc heps heps1 hs.1 (hs.2.trans hR) hη hsmall (hl s hs))
  have hp := angular_barrier (c.profiles hsep) (by norm_num [NominalProfile.Xi]) hX hL hL1
    hmem hf (fun s hs => (hl s hs).2.trans (by norm_num)) hq hinit
  refine ⟨hp, ?_⟩
  have hls := hl X ⟨hX, le_rfl⟩
  have he := ActivationContinuation.logSlope_eq_shear (c.profiles hsep) (X, eta)
  exact ActivationContinuation.zero_axial_relaxed_profile (c.profiles hsep)
    (by linarith [hls.1, hls.2]) (by linarith [hls.1, hls.2])
    (profiles_shape_radialU c hsep hX hR hηJ hsmall) hp

end ActualShapeCone

/-- Quantitative inputs for the shape and repair regions, obtained together
from one continuation. The endpoint drift is controlled separately from the
vanishing prefix debt. -/
structure PreparedBounds {F : OutgoingProfile.Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) (N : ℕ) (rho delta radiusFloor : ℝ) : Prop where
  matching : MatchingDebtBounds.MatchingBounds c N rho
  debt_radius : rho ≤ NominalProfile.resetSolver.radius
  scale_large : shapeScale A.small A.preparation ≤ A.scale
  control : MatchingDebtBounds.SmallControl c 1 (min 1 (1 / A.scale))
  radius_large : radiusFloor ≤ c.radius
  coefficients : JetBounds.FiniteJetBound N (NominalProfile.resetCoefficients F c.debt)
    (Icc (-1 : ℝ) 1) delta
  endpoint : ∀ eta ∈ Icc (-1 : ℝ) 1, ∀ n ≤ N,
    |iteratedDeriv n (fun e => c.initialAxial e - 4 * e) eta| ≤ delta

theorem PreparedBounds.shape_relaxed {F : OutgoingProfile.Profile} {A : NominalProfile.AxisStage F}
    {c : NominalProfile.Controls A} {N : ℕ} {rho delta radiusFloor : ℝ}
    (hb : PreparedBounds c N rho delta radiusFloor) {X eta : ℝ}
    (hX : NominalProfile.Xi ≤ X) (hR : X ≤ c.radius * Real.exp (-8))
    (hη : eta ∈ Icc (-1 : ℝ) 1)
    (hinit : 2 < ReferenceBounds.p1 (c.profiles hb.matching.separation.le)
      F.data.h (NominalProfile.Xi, eta)) :
    ActivationContinuation.IsRelaxed (c.profiles hb.matching.separation.le) F.data.h (X, eta) :=
  (actual_shape_relaxed c hb.matching.separation.le hb.matching hb.debt_radius hb.scale_large
    hb.control (le_min zero_le_one (one_div_nonneg.mpr A.scale_pos.le)) le_rfl hX hR hη hinit).2

/-- Ordered common-witness selection. The repair tolerance and requested
finite jet order are fixed before `j`; the source and endpoint scales are
fixed before `C`. Every sufficiently large `C` works. The same entrance
profile then supports every later finite control order and tolerance. -/
theorem exists_ordered_prepared_continuation (F : OutgoingProfile.Profile) (N : ℕ)
    (hN : 1 ≤ N) {delta : ℝ} (hdelta : 0 < delta) (radiusFloor : ℝ) :
    ∃ rho : ℝ, 0 < rho ∧ ∃ jcap : ℝ, 0 < jcap ∧ jcap ≤ 1 ∧
      ∀ j : ℝ, |j| ≤ jcap → ∀ hj : SmallParameters F.data.h j,
      ∀ prep : NominalProfile.AxisPreparation F j,
      ∀ nu : ℝ, 0 < nu →
      (∀ eta ∈ Icc (-1 : ℝ) 1, |Z F.data.h j F.axisDatum eta| ≤ nu →
        99 / 100 < chi F.data.h j prep.sigma eta) →
      ∃ Λ0 : ℝ, 1 ≤ Λ0 ∧ ∀ Λ : ℝ, ∀ hΛ : 0 < Λ, Λ0 ≤ Λ →
        ∃ T : ℝ, ∃ hT : 0 < T, ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ C : ℝ, C0 ≤ C →
          ∃ hΛlarge : prep.scaleBound ≤ Λ,
          ∃ hClarge : NaturalEntrance.entranceNormalization prep.inputs Λ prep.delta ≤ C,
          ∃ E : NaturalEntrance.EntranceProfile prep.inputs Λ C,
          ∀ J : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
            ∃ tolerance : ℝ, 0 < tolerance ∧ tolerance ≤ epsilon ∧
            ∃ w : ActivationContinuation.ContinuationWitness E hΛ hj F.axisDatum_contDiff
              (max N J) tolerance,
              let A := NominalProfile.AxisStage.ofEntrance hj prep Λ C hΛlarge hClarge E
              let c := NominalProfile.Controls.ofContinuation A w T hT
              PreparedBounds c N rho delta radiusFloor := by
  obtain ⟨K, hK, hcoeff⟩ := MatchingDebtBounds.resetCoefficients_jet_control N
  let tau := min (min 1 (NominalProfile.resetSolver.radius / 2)) (delta / (2 * K))
  have htau : 0 < tau := lt_min
    (lt_min zero_lt_one (div_pos NominalProfile.resetSolver.radius_pos (by norm_num)))
    (div_pos hdelta (by positivity))
  have hmax : tau ≤ min 1 (NominalProfile.resetSolver.radius / 2) := min_le_left _ _
  have ht1 : tau ≤ 1 := hmax.trans (min_le_left _ _)
  have hcoefdelta : K * tau ≤ delta := by
    have hm := (le_div_iff₀ (show 0 < 2 * K by positivity)).mp (min_le_right
      (min 1 (NominalProfile.resetSolver.radius / 2)) (delta / (2 * K)))
    change tau * (2 * K) ≤ delta at hm
    nlinarith [mul_nonneg hK.le htau.le]
  let rho := tau ^ (N + 1)
  have hrho : 0 < rho := pow_pos htau _
  have hpow : rho ≤ tau := by
    simpa only [pow_one] using pow_le_pow_of_le_one htau.le ht1 (show 1 ≤ N + 1 by omega)
  have hradius : rho ≤ NominalProfile.resetSolver.radius :=
    hpow.trans ((hmax.trans (min_le_right _ _)).trans
      (by linarith [NominalProfile.resetSolver.radius_pos]))
  obtain ⟨eps, heps, heps1, hmatching⟩ :=
    MatchingDebtBounds.exists_ordered_matching_continuation F N hrho hradius
  let jcap := min eps (delta / 3)
  have hjcap : 0 < jcap := lt_min heps (by positivity)
  refine ⟨rho, hrho, jcap, hjcap, (min_le_left _ _).trans heps1, ?_⟩
  intro j hjbound hj prep nu hnu hcut
  obtain ⟨Lmatch, hLmatch, hmatch⟩ :=
    hmatching j (hjbound.trans (min_le_left _ _)) hj prep nu hnu hcut
  obtain ⟨D, hD, hDb⟩ := TransitionRamp.finite_majorant
    (fun n => ReferenceJetBounds.jetConstant prep.inputs.coefficients 0 n) N
  let Λ0 := max Lmatch (max (shapeScale hj prep) (3 * D / delta))
  refine ⟨Λ0, hLmatch.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ hΛlarge
  have hLm : Lmatch ≤ Λ := (le_max_left _ _).trans hΛlarge
  have hLs : shapeScale hj prep ≤ Λ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hΛlarge)
  have hLD : 3 * D / delta ≤ Λ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hΛlarge)
  have hjet (n : ℕ) (hn : n ≤ N) :
      ReferenceJetBounds.jetConstant prep.inputs.coefficients 0 n / Λ ≤ delta / 3 := by
    apply (div_le_iff₀ hΛ).mpr
    have hmul := (div_le_iff₀ hdelta).mp hLD
    nlinarith [hDb n hn]
  obtain ⟨T, hT, Cmatch, hCmatch, hnorm⟩ := hmatch Λ hΛ hLm
  obtain ⟨Cgeo, hgeo⟩ := eventually_atTop.mp
    (NominalProfile.eventually_matching_geometry F T radiusFloor Cmatch)
  refine ⟨T, hT, max Cmatch Cgeo, hCmatch.trans (le_max_left _ _), ?_⟩
  intro C hC
  have hCm : Cmatch ≤ C := (le_max_left _ _).trans hC
  have hCg := hgeo C ((le_max_right _ _).trans hC)
  obtain ⟨hL, hCl, E, hcontrols⟩ := hnorm C hCm
  refine ⟨hL, hCl, E, ?_⟩
  intro J epsilon hepsilon
  let requested := min epsilon (min (1 / Λ) (delta / 3))
  have hrequested : 0 < requested := lt_min hepsilon (lt_min (one_div_pos.mpr hΛ) (by positivity))
  obtain ⟨w, hm, _hsmall⟩ := hcontrols J requested hrequested
  let tolerance := min eps requested
  have htol : 0 < tolerance := lt_min heps hrequested
  have hteps : tolerance ≤ epsilon := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨tolerance, htol, hteps, w, ?_⟩
  let A := NominalProfile.AxisStage.ofEntrance hj prep Λ C hL hCl E
  let c := NominalProfile.Controls.ofContinuation A w T hT
  have hc : MatchingDebtBounds.SmallControl c (max N J) tolerance := w.logarithmic_control
  have htol1 : tolerance ≤ 1 := (min_le_left _ _).trans heps1
  have htolL : tolerance ≤ 1 / Λ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have htolD : tolerance ≤ delta / 3 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨hm, hradius, hLs, ?_, hCg.2.2.1.le, ?_, ?_⟩
  · exact (hc.of_le (hN.trans (le_max_left _ _))).mono (le_min htol1 htolL)
  · have hco := hcoeff c hm.separation.le tau htau hmax
      (fun n hn eta hη => (hm.normalized_jets n hn eta hη).le)
    exact fun n hn eta hη => (hco n hn eta hη).trans hcoefdelta
  · intro eta hη n hn
    have hb := MatchingDebtBounds.actual_endpoint_drift c (hc.of_le (le_max_left _ _)) hη hn
    change _ ≤ ReferenceJetBounds.jetConstant prep.inputs.coefficients 0 n / Λ + tolerance + |j|
        at hb
    have hjD : |j| ≤ delta / 3 := hjbound.trans (min_le_right _ _)
    exact hb.trans (by linarith [hjet n hn])

/-- The actual entrance profile and continuation are stored, so subsequent
cone gluing uses the same controls that produced the small repair debt. -/
structure PreparedWitness (F : OutgoingProfile.Profile) (N : ℕ) (delta radiusFloor : ℝ) where
  /-- Axis of `PreparedWitness`, of type `NominalProfile.AxisStage F`. -/
  axis : NominalProfile.AxisStage F
  /-- Order of `PreparedWitness`, of type `ℕ`. -/
  order : ℕ
  order_ge : N ≤ order
  /-- Tolerance of `PreparedWitness`, of type `ℝ`. -/
  tolerance : ℝ
  tolerance_pos : 0 < tolerance
  /-- Continuation supplied by `PreparedWitness`. -/
  continuation : ActivationContinuation.ContinuationWitness axis.natural axis.scale_pos
    axis.small F.axisDatum_contDiff order tolerance
  /-- Shape time of `PreparedWitness`, of type `ℝ`. -/
  shapeTime : ℝ
  shapeTime_pos : 0 < shapeTime
  /-- Rho of `PreparedWitness`, of type `ℝ`. -/
  rho : ℝ
  rho_pos : 0 < rho
  bounds : PreparedBounds
    (NominalProfile.Controls.ofContinuation axis continuation shapeTime shapeTime_pos)
    N rho delta radiusFloor

/-- Controls, given by `NominalProfile.Controls.ofContinuation W.axis W.continuation W.shapeTime
W.shapeTime_pos`. -/
noncomputable def PreparedWitness.controls {F : OutgoingProfile.Profile} {N : ℕ}
    {delta radiusFloor : ℝ} (W : PreparedWitness F N delta radiusFloor) :
    NominalProfile.Controls W.axis :=
  NominalProfile.Controls.ofContinuation W.axis W.continuation W.shapeTime W.shapeTime_pos

/-- The final `j`, axis preparation, scale, normalization and continuation
are chosen in their required order. The incoming cone witness remains part
of the output, rather than being replaced by unrelated fields. -/
theorem preparedWitness_exists (F : OutgoingProfile.Profile) (hP : 2 ≤ F.data.core.P)
    (hh : F.data.h ≤ 1 / 1000) (N : ℕ) (hN : 1 ≤ N)
    {delta : ℝ} (hdelta : 0 < delta) (radiusFloor : ℝ) :
    Nonempty (PreparedWitness F N delta radiusFloor) := by
  obtain ⟨rho, hrho, jcap, hjcap, _hjcap1, hchoose⟩ :=
    exists_ordered_prepared_continuation F N hN hdelta radiusFloor
  let j := min (jcap / 2) (1 / 2000)
  have hjpos : 0 < j := lt_min (by positivity) (by norm_num)
  have hjbound : |j| ≤ jcap := by
    rw [abs_of_pos hjpos]
    exact (min_le_left _ _).trans (by linarith)
  have hj : SmallParameters F.data.h j :=
    ⟨F.data.h_pos, hh, hjpos, (min_le_right _ _).trans (by norm_num)⟩
  obtain ⟨prep, hcut⟩ := NominalProfile.prepare_axis_with_cutoff F hP hj
  obtain ⟨Λ0, hΛ0, hscale⟩ := hchoose j hjbound hj prep prep.delta prep.delta_pos hcut
  have hΛ : 0 < Λ0 := zero_lt_one.trans_le hΛ0
  obtain ⟨T, hT, C0, _hC0, hnormalization⟩ := hscale Λ0 hΛ le_rfl
  obtain ⟨hL, hC, E, hcontrols⟩ := hnormalization C0 le_rfl
  obtain ⟨tolerance, htol, _htol1, w, hb⟩ := hcontrols 0 1 zero_lt_one
  let A := NominalProfile.AxisStage.ofEntrance hj prep Λ0 C0 hL hC E
  exact ⟨⟨A, max N 0, le_max_left _ _, tolerance, htol, w, T, hT, rho, hrho, hb⟩⟩

end NavierStokes.MatchingConeBounds

end
