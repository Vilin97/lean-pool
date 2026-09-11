/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.HeatSwitchCone
public import LeanPool.NavierStokesAndEuler.NavierStokes.ModulatedCone
import LeanPool.NavierStokesAndEuler.NavierStokes.RepairConeBounds
import LeanPool.NavierStokesAndEuler.NavierStokes.TerminalHistoryBridge
public import LeanPool.NavierStokesAndEuler.NavierStokes.OutgoingCone
public import LeanPool.NavierStokesAndEuler.NavierStokes.NominalProfile
public import LeanPool.NavierStokesAndEuler.NavierStokes.TerminalCone
public import LeanPool.NavierStokesAndEuler.NavierStokes.MatchingDebtBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ExtendedHeatedOutgoing
public import LeanPool.NavierStokesAndEuler.NavierStokes.OutgoingEntranceCone

/-!
# Cone coordinates of one actual nominal profile

The physical coordinates below are computed from the genuine smooth profile
and its axis-integrated histories. The outgoing convention for axial shear
has the opposite sign to the signed shear used by the modulation theorem.
-/

section

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

end

end

section

/-!
# A common scheduled profile below caller-supplied parameter bounds

The reset coefficient bound is selected before lambda. The caller's lambda
cap is intersected with the existing reset and energy thresholds before any
profile is constructed. The actual core is then fixed before choosing h.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.ScheduledProfileChoice

open OutgoingProfile (Profile)
open ExtendedHeatedOutgoing (ScheduleBounds)

/-- The actual core and reset bound precede every subsequent height choice. -/
theorem exists_scheduled_core_below (P m : ℝ) (hP : 0 < P) (hm : 0 < m)
    (cap : ℝ → ℝ) (hcap : ∀ K : ℝ, 0 < K → 0 < cap K) :
    ∃ (K B : ℝ) (core : OutgoingSchedule.Parameters),
      0 < K ∧ 0 < B ∧ core.P = P ∧ core.m = m ∧
      core.wait = 60 * Real.log (1 / core.lam) ∧
      core.lam < cap K ∧ core.lam < 1 / 120 ∧
      ∀ h : ℝ, 0 < h → 2 * h < core.lam →
        ∃ F : Profile, F.data.core = core ∧ F.data.h = h ∧ F.coefficientBound = K ∧
          ScheduleBounds F ∧ OutgoingProfile.Specification F B := by
  obtain ⟨resetLam, K, hresetLam, hK, hreset⟩ := UniformAngularReset.exists_scheduled_reset
  obtain ⟨delta, hdelta, hrate⟩ := PulseAmplitude.exists_rate_threshold
    (CorrectedPulseAmplitude.combinedConstant P m K)
  let lam₀ := min (cap K) (min resetLam (min delta (1 / 120 : ℝ)))
  have hlam₀ : 0 < lam₀ := lt_min (hcap K hK) (lt_min hresetLam (lt_min hdelta (by norm_num)))
  let lam := lam₀ / 2
  have hlam : 0 < lam := half_pos hlam₀
  have hlam₀' : lam < lam₀ := half_lt_self hlam₀
  have hcaller : lam < cap K := hlam₀'.trans_le (min_le_left _ _)
  have hrest : lam < min resetLam (min delta (1 / 120 : ℝ)) :=
    hlam₀'.trans_le (min_le_right _ _)
  have hreset' : lam < resetLam := hrest.trans_le (min_le_left _ _)
  have hdelta' : lam < delta := hrest.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsmall : lam < 1 / 120 := hrest.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let core := OutgoingSchedule.paperParameters P m lam hP hm hlam (by linarith)
  refine ⟨K, 128 * CorrectedPulseAmplitude.combinedConstant P m K, core, hK,
    mul_pos (by norm_num) (CorrectedPulseAmplitude.combinedConstant_pos hP m K hK),
    rfl, rfl, rfl, hcaller, hsmall, ?_⟩
  intro h hh htail
  let d : OutgoingTail.TailData := ⟨core, h, hh, htail⟩
  obtain ⟨r⟩ := hreset d hreset'
  let F : Profile := ⟨d, K, r⟩
  have b : ScheduleBounds F := {
    coefficient_pos := hK
    lambda_small := hsmall.le
    wait_eq := rfl
    scale_small := hrate lam hlam hdelta' }
  exact ⟨F, rfl, rfl, rfl, b, b.specification⟩

/-- A scalar-parameter form of the same construction, with the reset bound
retained as an explicit preceding existential. -/
theorem exists_scheduled_profile_below (P m : ℝ) (hP : 0 < P) (hm : 0 < m)
    (cap : ℝ → ℝ) (hcap : ∀ K : ℝ, 0 < K → 0 < cap K) :
    ∃ K lam B : ℝ,
      0 < K ∧ 0 < lam ∧ lam < cap K ∧ lam < 1 / 120 ∧ 0 < B ∧
      ∀ h : ℝ, 0 < h → 2 * h < lam →
        ∃ F : Profile, F.data.core.P = P ∧ F.data.core.m = m ∧
          F.data.core.lam = lam ∧ F.data.h = h ∧ F.coefficientBound = K ∧
          ScheduleBounds F ∧ OutgoingProfile.Specification F B := by
  obtain ⟨K, B, core, hK, hB, hcP, hcm, _hwait, hcaller, hsmall, hf⟩ :=
    exists_scheduled_core_below P m hP hm cap hcap
  refine ⟨K, core.lam, B, hK, core.lam_pos, hcaller, hsmall, hB, ?_⟩
  intro h hh ht
  obtain ⟨F, hcore, hh', hK', hb, hF⟩ := hf h hh ht
  refine ⟨F, ?_, ?_, ?_, hh', hK', hb, hF⟩
  · rw [hcore, hcP]
  · rw [hcore, hcm]
  · rw [hcore]

/-- This number depends on the already fixed core and an additional caller
height bound. It is chosen before the terminal exponent h. -/
noncomputable def heightCap (core : OutgoingSchedule.Parameters) (extra : ℝ) : ℝ :=
  min (core.lam / 4)
    (min extra (min (1 / 1000) (min (1 / 4) (1 / (1 + TerminalCone.releaseBudget core)))))

theorem heightCap_pos (core : OutgoingSchedule.Parameters) {extra : ℝ} (he : 0 < extra) :
    0 < heightCap core extra := by
  have hb := TerminalCone.releaseBudget_nonneg core
  exact lt_min (div_pos core.lam_pos (by norm_num))
    (lt_min he (lt_min (by norm_num) (lt_min (by norm_num) (by positivity))))

theorem heightCap_bounds (core : OutgoingSchedule.Parameters) (extra : ℝ) :
    2 * heightCap core extra < core.lam ∧ heightCap core extra ≤ extra ∧
      heightCap core extra ≤ 1 / 1000 ∧ heightCap core extra ≤ 1 / 4 ∧
      heightCap core extra ≤ 1 / (1 + TerminalCone.releaseBudget core) := by
  have hl : heightCap core extra ≤ core.lam / 4 := min_le_left _ _
  have hr : heightCap core extra ≤
      min extra (min (1 / 1000) (min (1 / 4) (1 / (1 + TerminalCone.releaseBudget core)))) :=
          min_le_right _ _
  have hrest := hr.trans (min_le_right _ _)
  have hlast := hrest.trans (min_le_right _ _)
  exact ⟨by linarith [core.lam_pos], hr.trans (min_le_left _ _),
    hrest.trans (min_le_left _ _), hlast.trans (min_le_left _ _), hlast.trans (min_le_right _ _)⟩

/-- The common lambda and all height caps are fixed before h and before the
actual reset/Profile. The additional cap may impose the outgoing-cone height
bound; the built-in caps also give the axis and terminal requirements. -/
theorem exists_scheduled_family_below (P m : ℝ) (hP : 0 < P) (hm : 0 < m)
    (cap : ℝ → ℝ) (hcap : ∀ K : ℝ, 0 < K → 0 < cap K)
    (extraHeight : OutgoingSchedule.Parameters → ℝ)
    (hextra : ∀ core : OutgoingSchedule.Parameters, 0 < extraHeight core) :
    ∃ (K B H : ℝ) (core : OutgoingSchedule.Parameters),
      0 < K ∧ 0 < B ∧ 0 < H ∧ core.P = P ∧ core.m = m ∧
      core.wait = 60 * Real.log (1 / core.lam) ∧
      core.lam < cap K ∧ core.lam < 1 / 120 ∧
      2 * H < core.lam ∧ H ≤ extraHeight core ∧ H ≤ 1 / 1000 ∧
      ∀ h : ℝ, 0 < h → h ≤ H →
        ∃ F : Profile, F.data.core = core ∧ F.data.h = h ∧ F.coefficientBound = K ∧
          ScheduleBounds F ∧ OutgoingProfile.Specification F B ∧ TerminalCone.SmallTail F.data := by
  obtain ⟨K, B, core, hK, hB, hcP, hcm, hwait, hcaller, hsmall, hf⟩ :=
    exists_scheduled_core_below P m hP hm cap hcap
  have hb := heightCap_bounds core (extraHeight core)
  refine ⟨K, B, heightCap core (extraHeight core), core, hK, hB,
    heightCap_pos core (hextra core), hcP, hcm, hwait, hcaller, hsmall,
    hb.1, hb.2.1, hb.2.2.1, ?_⟩
  intro h hh hH
  have ht : 2 * h < core.lam := (mul_le_mul_of_nonneg_left hH (by norm_num)).trans_lt hb.1
  obtain ⟨F, hcore, hh', hK', hs, hF⟩ := hf h hh ht
  refine ⟨F, hcore, hh', hK', hs, hF, ?_⟩
  unfold TerminalCone.SmallTail
  rw [hcore, hh']
  exact ⟨hH.trans hb.2.2.2.1, hH.trans hb.2.2.2.2⟩

end NavierStokes.ScheduledProfileChoice

end
end

end

section

/-!
# One prepared outgoing profile and arbitrarily late nominal matching

The reset bound precedes the outgoing exponent, the height bounds precede
the actual height, and the natural-axis choices use this same profile.
The clean cone below belongs to the unedited outgoing profile. Identification
with the complete edited nominal stress is a separate construction.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.PreparedOutgoing

open Set Filter OutgoingProfile

/-- Data obtained from the actual schedule construction, with a clean cone
available at all sufficiently late matching radii. -/
structure PreparedProfile where
  /-- Profile of `PreparedProfile`, of type `Profile`. -/
  profile : Profile
  /-- Bound of `PreparedProfile`, of type `ℝ`. -/
  bound : ℝ
  bound_pos : 0 < bound
  specification : Specification profile bound
  schedule : ExtendedHeatedOutgoing.ScheduleBounds profile
  terminal : TerminalCone.SmallTail profile.data
  amplitude_lower : 2 ≤ profile.data.core.P
  height_upper : profile.data.h ≤ 1 / 1000
  clean : ∀ left : ℝ, left ≤ 0 →
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ R : ℝ, R0 < R → OutgoingCone.ProfileCleanCone profile R left

/-- Select the reset bound and exponent together, respecting the clean-cone
cap before constructing the profile. No existing exponent is changed later. -/
theorem exists_prepared : Nonempty PreparedProfile := by
  classical
  obtain ⟨M, hM, hcone⟩ := OutgoingCone.exists_ordered_profile_cone
  let P : ℝ := max 2 (OutgoingEntranceCone.amplitudeThreshold M)
  have hP2 : 2 ≤ P := le_max_left _ _
  have hPpos : 0 < P := lt_of_lt_of_le (by norm_num) hP2
  have hPamp : OutgoingEntranceCone.amplitudeThreshold M ≤ P := le_max_right _ _
  let caps := hcone M le_rfl P hPamp
  let cap : ℝ → ℝ := fun K =>
    if hK : 0 < K then Classical.choose (caps K hK) else 1
  have hcap : ∀ K : ℝ, 0 < K → 0 < cap K := by
    intro K hK
    dsimp only [cap]
    rw [dite_eq_left hK]
    exact (Classical.choose_spec (caps K hK)).1
  obtain ⟨K, B, H, core, hK, hB, hH, hcP, hcm, hwait, hlam, _hsmall,
      _h2H, hheight, hHsmall, hfamily⟩ :=
    ScheduledProfileChoice.exists_scheduled_family_below P M hPpos hM cap hcap
      (fun core => OutgoingCone.heightThreshold M core.lam)
      (fun core => OutgoingCone.heightThreshold_pos M core.lam_pos)
  obtain ⟨F, hcore, hh, hFK, hschedule, hspec, hterminal⟩ := hfamily H hH le_rfl
  have hFP : F.data.core.P = P := by rw [hcore, hcP]
  have hFm : F.data.core.m = M := by rw [hcore, hcm]
  have hFwait : F.data.core.wait = 60 * Real.log (1 / F.data.core.lam) := by
    rw [hcore]
    exact hwait
  have hFlam : F.data.core.lam < Classical.choose (caps K hK) := by
    rw [hcore]
    simpa only [cap, dite_eq_left hK] using hlam
  have hFheight : F.data.h ≤ OutgoingCone.heightThreshold M F.data.core.lam := by
    rw [hh, hcore]
    exact hheight
  have hclean := (Classical.choose_spec (caps K hK)).2 F hFP hFm hFK hFwait hFlam hFheight
  exact ⟨{
    profile := F
    bound := B
    bound_pos := hB
    specification := hspec
    schedule := hschedule
    terminal := hterminal
    amplitude_lower := by rw [hFP]; exact hP2
    height_upper := by rw [hh]; exact hHsmall
    clean := hclean }⟩

/-- The actual nominal matching radius can exceed any prescribed bound while
the outgoing profile and all its schedule choices remain fixed. -/
theorem PreparedProfile.large_nominal (d : PreparedProfile) (floor left : ℝ)
    (hleft : left ≤ 0) :
    ∃ W : NominalProfile.Witness d.profile,
      floor < W.controls.radius ∧
      OutgoingCone.ProfileCleanCone d.profile W.controls.radius left := by
  obtain ⟨R0, _hR0, hclean⟩ := d.clean left hleft
  have hrho : 0 < NominalProfile.resetSolver.radius / 2 :=
    div_pos NominalProfile.resetSolver.radius_pos (by norm_num)
  have hradius : NominalProfile.resetSolver.radius / 2 ≤ NominalProfile.resetSolver.radius := by
    linarith [NominalProfile.resetSolver.radius_pos]
  obtain ⟨eps, heps, _heps1, hordered⟩ :=
    MatchingDebtBounds.exists_ordered_nominal_witness d.specification d.amplitude_lower
      0 hrho hradius
  let j : ℝ := min (eps / 2) (1 / 2000)
  have hj : 0 < j := lt_min (by positivity) (by norm_num)
  have hjbound : |j| ≤ eps := by
    rw [abs_of_pos hj]
    exact (min_le_left _ _).trans (by linarith)
  have hsmall : NaturalAxisData.SmallParameters d.profile.data.h j :=
    ⟨d.profile.data.h_pos, d.height_upper, hj,
      (min_le_right _ _).trans (by norm_num)⟩
  obtain ⟨L0, hL0, hscale⟩ := hordered j hjbound hsmall
  obtain ⟨T, _hT, C0, _hC0, hnorm⟩ := hscale L0 (zero_lt_one.trans_le hL0) le_rfl
  obtain ⟨C, _hCpos, hC0, hR, _hsep⟩ :=
    (NominalProfile.eventually_matching_geometry d.profile T (max floor R0) C0).exists
  obtain ⟨W, _hjW, _hLW, hCW, _hTW, _hmatch⟩ := hnorm C hC0
  have hrad : W.controls.radius = NominalProfile.matchingRadius d.profile C := by
    change NominalProfile.matchingRadius d.profile W.axis.normalization = _
    rw [hCW]
  refine ⟨W, ?_, ?_⟩
  · rw [hrad]
    exact (le_max_left _ _).trans_lt hR
  · apply hclean
    rw [hrad]
    exact (le_max_right _ _).trans_lt hR

/-- An actual fixed prepared profile, obtained from the proved existence. -/
noncomputable def prepared : PreparedProfile := Classical.choice exists_prepared

theorem exists_matched_nominal (floor left : ℝ) (hleft : left ≤ 0) :
    ∃ (d : PreparedProfile) (W : NominalProfile.Witness d.profile),
      floor < W.controls.radius ∧
      OutgoingCone.ProfileCleanCone d.profile W.controls.radius left := by
  obtain ⟨W, hW⟩ := prepared.large_nominal floor left hleft
  exact ⟨prepared, W, hW⟩

end NavierStokes.PreparedOutgoing

end
end

end

@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff
open NavierStokes.ProfileHistories
open NavierStokes.OutgoingProfile
open NavierStokes.NominalProfile (AxisStage Controls SmallDebt)
open NavierStokes.StressActivation

namespace NavierStokes.NominalConeAssembly

/-- Is true, constructed using `ActivationContinuation.IsRelaxed`. -/
noncomputable def IsTrue {D : RadialDomain} (P : Profiles D) (h : ℝ) (p : Point) : Prop :=
  ActivationContinuation.IsRelaxed P h p ∧
    2 < ActivationContinuation.shearSize
      (ActivationContinuation.shearA P p) (ActivationContinuation.shearB P p)

theorem isTrue_iff_loop {D : RadialDomain} (P : Profiles D) (h : ℝ) (p : Point) :
    IsTrue P h p ↔ TrueConeLoop.InTrueCone (ReferenceBounds.p1 P h p)
      (ReferenceBounds.p2 P h p) (ActivationContinuation.shearA P p)
      (ActivationContinuation.shearB P p) := by
  constructor
  · rintro ⟨hc, hv⟩
    exact ⟨hc.first_positive, hv, hc.projection_positive, hc.cone⟩
  · rintro ⟨ha, hv, hp, hc⟩
    exact ⟨⟨ha, hp, hc⟩, hv⟩

theorem p1_eq_stock {D : RadialDomain} (P : Profiles D) (h : ℝ) (p : Point) :
    ReferenceBounds.p1 P h p = ActivationStocks.profileStockOne P h p := rfl

theorem p2_eq_stock {D : RadialDomain} (P : Profiles D) (h : ℝ) (p : Point) :
    ReferenceBounds.p2 P h p = ActivationStocks.profileStockTwo P h p := by
  unfold ReferenceBounds.p2 ReferenceBounds.ns ActivationStocks.profileStockTwo
  ring

/-! ## Local smooth coordinates for the modulation annulus -/

/-- Tilt, given by `ActivationContinuation.shearB P p / ActivationContinuation.shearA P p`. -/
noncomputable def tilt {D : RadialDomain} (P : Profiles D) (p : Point) : ℝ :=
  ActivationContinuation.shearB P p / ActivationContinuation.shearA P p

theorem physicalE_smoothAt {D : RadialDomain} (P : Profiles D) {p : Point}
    (hp : p ∈ D.carrier) (hX : 0 < p.1) : ContDiffAt ℝ ∞ P.E p :=
  ((contDiffAt_const.mul contDiffAt_fst).sqrt (by positivity)).mul
    (P.f_smooth.contDiffAt (D.isOpen.mem_nhds hp))

theorem shears_smoothAt {D : RadialDomain} (P : Profiles D) {p : Point}
    (hp : p ∈ D.carrier) (hX : 0 < p.1) (hf : P.f p ≠ 0) :
    ContDiffAt ℝ ∞ (ActivationContinuation.shearA P) p ∧
      ContDiffAt ℝ ∞ (ActivationContinuation.shearB P) p := by
  have hpf := P.f_smooth.contDiffAt (D.isOpen.mem_nhds hp)
  have hdf := (radialPartial_smooth D P.f_smooth).contDiffAt (D.isOpen.mem_nhds hp)
  have hdu := (radialPartial_smooth D P.U_smooth).contDiffAt (D.isOpen.mem_nhds hp)
  exact ⟨((contDiffAt_const.mul contDiffAt_fst).mul hdf).div hpf hf,
    ((contDiffAt_const.mul contDiffAt_fst).mul hdu).div
      (physicalE_smoothAt P hp hX) (P.E_ne_zero hX hf)⟩

theorem stocks_smoothAt {D : RadialDomain} (P : Profiles D) (h : ℝ) {p : Point}
    (hp : p ∈ D.carrier) (hX : 0 < p.1) (hf : P.f p ≠ 0)
    (hL : NaturalAxisData.L h p.2 ≠ 0) :
    ContDiffAt ℝ ∞ (ReferenceBounds.p1 P h) p ∧
      ContDiffAt ℝ ∞ (ReferenceBounds.p2 P h) p := by
  have hLc : ContDiffAt ℝ ∞ (fun q : Point => NaturalAxisData.L h q.2) p :=
    contDiffAt_const.sub ((contDiffAt_const.mul contDiffAt_const).mul (contDiffAt_snd.pow 2))
  exact ⟨(contDiffAt_fst.mul (P.angularLag_smoothAt h hp hX.ne' (P.H_ne_zero hX.ne' hf))).div hLc
      hL,
    (contDiffAt_fst.mul ((P.axialLag_smoothAt h hp hX.ne').div hLc hL)).div
      (physicalE_smoothAt P hp hX) (P.E_ne_zero hX hf)⟩

theorem cone_coordinates_smoothAt {D : RadialDomain} (P : Profiles D) (h : ℝ) {p : Point}
    (hp : p ∈ D.carrier) (hX : 0 < p.1) (hf : P.f p ≠ 0)
    (ha : ActivationContinuation.shearA P p ≠ 0) (hL : NaturalAxisData.L h p.2 ≠ 0) :
    ContDiffAt ℝ ∞ (ActivationContinuation.shearA P) p ∧
      ContDiffAt ℝ ∞ (tilt P) p ∧
      ContDiffAt ℝ ∞ (ReferenceBounds.p1 P h) p ∧
      ContDiffAt ℝ ∞ (ReferenceBounds.p2 P h) p := by
  have hs := shears_smoothAt P hp hX hf
  exact ⟨hs.1, hs.2.div hs.1 ha, stocks_smoothAt P h hp hX hf hL⟩

/-- Equality of an actual prefix propagates to every history, before any
derivative or stock comparison is made. -/
theorem history_of_prefix {D D' : RadialDomain} (P : Profiles D) (Q : Profiles D')
    {J : Set ℝ} {R : ℝ} (h0 : P.pressure0 = Q.pressure0)
    (hf : ∀ p : Point, p.2 ∈ J → p.1 ≤ R → P.f p = Q.f p)
    (hu : ∀ p : Point, p.2 ∈ J → p.1 ≤ R → P.U p = Q.U p)
    (r : HistoryRow) {X eta : ℝ} (hX : 0 ≤ X) (hR : X ≤ R) (heta : eta ∈ J) :
    profileHistory P r (X, eta) = profileHistory Q r (X, eta) := by
  apply ActivationStocks.profileHistory_congr_across P Q r hX
  · cases r <;> simp only [profileInitial, h0]
  · intro x hx
    exact hf (x, eta) heta (hx.2.trans hR)
  · intro x hx
    exact hu (x, eta) heta (hx.2.trans hR)

/-- The endpoint is included: equality on the left determines the radial
derivative because both fields are genuinely differentiable there. -/
theorem radialPartial_of_left {D D' : RadialDomain} {F G : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) (hG : ContDiffOn ℝ ∞ G D'.carrier)
    {R : ℝ} {p : Point} (hp : p ∈ D.carrier) (hq : p ∈ D'.carrier)
    (hR : p.1 ≤ R) (he : ∀ x ≤ R, F (x, p.2) = G (x, p.2)) :
    radialPartial F p = radialPartial G p := by
  exact (uniqueDiffOn_Iic R p.1 hR).eq_deriv _
    (radialPartial_hasDerivAt D hF hp).hasDerivWithinAt
    ((radialPartial_hasDerivAt D' hG hq).hasDerivWithinAt.congr_of_mem he hR)

theorem coordinates_of_prefix {D D' : RadialDomain} (P : Profiles D) (Q : Profiles D')
    (h : ℝ) {J : Set ℝ} (hJ : IsOpen J) {R : ℝ}
    (h0 : P.pressure0 = Q.pressure0)
    (hf : ∀ p : Point, p.2 ∈ J → p.1 ≤ R → P.f p = Q.f p)
    (hu : ∀ p : Point, p.2 ∈ J → p.1 ≤ R → P.U p = Q.U p)
    {p : Point} (hp : p ∈ D.carrier) (hq : p ∈ D'.carrier)
    (hX : 0 < p.1) (hR : p.1 ≤ R) (heta : p.2 ∈ J) (hfne : Q.f p ≠ 0) :
    ActivationContinuation.shearA P p = ActivationContinuation.shearA Q p ∧
      ActivationContinuation.shearB P p = ActivationContinuation.shearB Q p ∧
      ReferenceBounds.p1 P h p = ReferenceBounds.p1 Q h p ∧
      ReferenceBounds.p2 P h p = ReferenceBounds.p2 Q h p := by
  have hfv := hf p heta hR
  have huv := hu p heta hR
  have hfd := radialPartial_of_left P.f_smooth Q.f_smooth hp hq hR
    (fun x hx => hf (x, p.2) heta hx)
  have hud := radialPartial_of_left P.U_smooth Q.U_smooth hp hq hR
    (fun x hx => hu (x, p.2) heta hx)
  have hE : P.E p = Q.E p := by simp only [Profiles.E, hfv]
  have hs := ActivationStocks.profiles_stocks_congr P Q h hJ heta hp hq hX hfv hfne huv
    (fun r eta he => history_of_prefix P Q h0 hf hu r hX.le hR he)
  refine ⟨?_, ?_, hs.1, ?_⟩
  · simp only [ActivationContinuation.shearA, hfd, hfv]
  · simp only [ActivationContinuation.shearB, hud, hE]
  · simpa only [p2_eq_stock] using hs.2

theorem relaxed_of_coordinates {D D' : RadialDomain} (P : Profiles D) (Q : Profiles D')
    {h : ℝ} {p : Point}
    (he : ActivationContinuation.shearA P p = ActivationContinuation.shearA Q p ∧
      ActivationContinuation.shearB P p = ActivationContinuation.shearB Q p ∧
      ReferenceBounds.p1 P h p = ReferenceBounds.p1 Q h p ∧
      ReferenceBounds.p2 P h p = ReferenceBounds.p2 Q h p)
    (hc : ActivationContinuation.IsRelaxed Q h p) : ActivationContinuation.IsRelaxed P h p := by
  unfold ActivationContinuation.IsRelaxed at *
  rwa [he.1, he.2.1, he.2.2.1, he.2.2.2]

theorem controls_seed_coordinates {F : Profile} {A : AxisStage F} (c : Controls A)
    (hsep : c.separation ≤ Real.exp (-8)) {p : Point}
    (hsmall : SmallDebt F c.debt p.2) (hX : 0 < p.1) (hXi : p.1 ≤ NominalProfile.Xi)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    ActivationContinuation.shearA (c.profiles hsep) p = ActivationContinuation.shearA
        c.seedProfiles p ∧
      ActivationContinuation.shearB (c.profiles hsep) p = ActivationContinuation.shearB
          c.seedProfiles p ∧
      ReferenceBounds.p1 (c.profiles hsep) F.data.h p = ReferenceBounds.p1 c.seedProfiles F.data.h
          p ∧
      ReferenceBounds.p2 (c.profiles hsep) F.data.h p = ReferenceBounds.p2 c.seedProfiles F.data.h
          p := by
  apply coordinates_of_prefix (c.profiles hsep) c.seedProfiles F.data.h isOpen_univ rfl
    (fun q _ hq => c.f_before_Xi hq) (fun q _ hq => (c.physical_before_Xi hsep hq).1)
    (c.admissible_nonnegative hX.le (NominalProfile.physical_band_in_parameterInterval heta) hsmall)
    _ hX hXi (mem_univ _)
  · exact (c.seedF_positive (NominalProfile.physical_band_in_parameterInterval heta) hX.le).ne'
  · exact ⟨lt_of_lt_of_le (by norm_num) (mul_nonneg A.scale_pos.le hX.le),
      NominalProfile.physical_band_in_parameterInterval heta⟩

theorem continuation_first_at_Xi {F : Profile} {A : AxisStage F} {N : ℕ} {eps T : ℝ}
    (w : ActivationContinuation.ContinuationWitness A.natural A.scale_pos A.small
      F.axisDatum_contDiff N eps) (hT : 0 < T)
    (hsep : (Controls.ofContinuation A w T hT).separation ≤ Real.exp (-8)) {eta : ℝ}
    (hsmall : SmallDebt F (Controls.ofContinuation A w T hT).debt eta)
    (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    2 < ReferenceBounds.p1 ((Controls.ofContinuation A w T hT).profiles hsep)
      F.data.h (NominalProfile.Xi, eta) := by
  rw [(controls_seed_coordinates (Controls.ofContinuation A w T hT) hsep (p := (NominalProfile.Xi,
      eta)) hsmall
    NominalProfile.Xi_pos le_rfl heta).2.2.1]
  exact w.final_first 110 ⟨w.parameters.hold_lt_final.le, le_rfl⟩ eta heta

/-- History index as an element of `Fin 5`. -/
noncomputable def historyIndex (r : HistoryRow) : Fin 5 := by
  classical
  exact if r = .mass then 0 else if r = .angular then 1 else
    if r = .transport then 2 else if r = .energy then 3 else 4

@[simp] theorem historyIndex_mass : historyIndex .mass = 0 := by simp [historyIndex]
@[simp] theorem historyIndex_angular : historyIndex .angular = 1 := by simp [historyIndex]
@[simp] theorem historyIndex_transport : historyIndex .transport = 2 := by simp [historyIndex]
@[simp] theorem historyIndex_energy : historyIndex .energy = 3 := by simp [historyIndex]
@[simp] theorem historyIndex_pressure : historyIndex .pressure = 4 := by simp [historyIndex]

theorem profileDensity_eq_regular {D : RadialDomain} (P : Profiles D) (r : HistoryRow) (p : Point) :
    profileDensity P r p = NominalProfile.regularDensity P p (historyIndex r) := by
  cases r <;> simp only [historyIndex_mass, historyIndex_angular, historyIndex_transport,
    historyIndex_energy, historyIndex_pressure] <;> rfl

theorem history_eq_moment {D : RadialDomain} (P : Profiles D) (r : HistoryRow)
    {X eta : ℝ} (hX : 0 ≤ X) :
    profileHistory P r (X, eta) = profileInitial P r eta +
      NominalProfile.moments P.U P.E X eta (historyIndex r) := by
  rw [profileHistory_eq_initial_add_primitive]
  congr 1
  rw [primitive, intervalIntegral.integral_of_le hX]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  change profileDensity P r (x, eta) =
    NominalProfile.density (fun t => P.U (t, eta)) (fun t => P.E (t, eta)) x (historyIndex r)
  rw [profileDensity_eq_regular]
  exact congrArg (fun q : NominalProfile.Debt => q (historyIndex r))
    (NominalProfile.regularDensity_eq P hx.1 eta).symm

namespace Witness

variable {F : Profile} (W : NominalProfile.Witness F)

theorem f_positive {p : Point} (hX : 0 < p.1) (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    0 < W.profiles.f p := by
  have he := W.E_positive hX heta
  rw [W.E_eq_sqrt_f hX] at he
  exact pos_of_mul_pos_right he (Real.sqrt_nonneg _)

theorem prefix_f {p : Point} (hp : p.1 ≤ W.controls.heatJoin) :
    W.profiles.f p = (W.controls.profiles W.separated).f p := by
  change W.controls.extendedf W.heat.coefficients p = W.controls.f p
  by_cases hXi : p.1 ≤ NominalProfile.Xi
  · simp only [Controls.extendedf, ite_eq_left hXi]
  · rw [Controls.extendedf, ite_eq_right hXi,
      W.controls.extendedE_before W.heat.coefficients hp, Controls.f, ite_eq_right hXi]

theorem prefix_histories (r : HistoryRow) {X eta : ℝ} (hX : 0 ≤ X)
    (hR : X ≤ W.controls.heatJoin) :
    profileHistory W.profiles r (X, eta) =
      profileHistory (W.controls.profiles W.separated) r (X, eta) :=
  history_of_prefix W.profiles (W.controls.profiles W.separated) (J := univ) rfl
    (fun _ _ hq => prefix_f W hq) (fun _ _ _ => rfl) r hX hR (mem_univ _)

theorem prefix_coordinates {p : Point} (hp : p ∈ W.domain.carrier)
    (hX : 0 < p.1) (hR : p.1 ≤ W.controls.heatJoin)
    (hf : W.controls.f p ≠ 0) :
    ActivationContinuation.shearA W.profiles p =
        ActivationContinuation.shearA (W.controls.profiles W.separated) p ∧
      ActivationContinuation.shearB W.profiles p =
        ActivationContinuation.shearB (W.controls.profiles W.separated) p ∧
      ReferenceBounds.p1 W.profiles F.data.h p =
        ReferenceBounds.p1 (W.controls.profiles W.separated) F.data.h p ∧
      ReferenceBounds.p2 W.profiles F.data.h p =
        ReferenceBounds.p2 (W.controls.profiles W.separated) F.data.h p :=
  coordinates_of_prefix W.profiles (W.controls.profiles W.separated) F.data.h isOpen_univ rfl
    (fun _ _ hq => prefix_f W hq) (fun _ _ _ => rfl) hp hp.1 hX hR (mem_univ _) hf

theorem prefix_relaxed {p : Point} (hX : 0 < p.1) (hR : p.1 ≤ W.controls.heatJoin)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain)
    (hc : ActivationContinuation.IsRelaxed (W.controls.profiles W.separated) F.data.h p) :
    ActivationContinuation.IsRelaxed W.profiles F.data.h p := by
  have hf : W.controls.f p ≠ 0 := by
    change (W.controls.profiles W.separated).f p ≠ 0
    rw [← prefix_f W hR]
    exact (f_positive W hX heta).ne'
  exact relaxed_of_coordinates W.profiles (W.controls.profiles W.separated)
    (prefix_coordinates W (W.domain_contains hX.le heta) hX hR hf) hc

theorem seed_coordinates {p : Point} (hX : 0 < p.1) (hXi : p.1 ≤ NominalProfile.Xi)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    ActivationContinuation.shearA W.profiles p = ActivationContinuation.shearA
        W.controls.seedProfiles p ∧
      ActivationContinuation.shearB W.profiles p = ActivationContinuation.shearB
          W.controls.seedProfiles p ∧
      ReferenceBounds.p1 W.profiles F.data.h p = ReferenceBounds.p1 W.controls.seedProfiles
          F.data.h p ∧
      ReferenceBounds.p2 W.profiles F.data.h p = ReferenceBounds.p2 W.controls.seedProfiles
          F.data.h p := by
  apply coordinates_of_prefix W.profiles W.controls.seedProfiles F.data.h isOpen_univ rfl
    (fun q _ hq => (W.controls.extended_seed_fields W.heat.coefficients W.separated hq).1)
    (fun q _ hq => (W.controls.extended_seed_fields W.heat.coefficients W.separated hq).2)
    (W.domain_contains hX.le heta) _ hX hXi (mem_univ _)
  · exact (W.controls.seedF_positive (NominalProfile.physical_band_in_parameterInterval heta)
      hX.le).ne'
  · exact ⟨lt_of_lt_of_le (by norm_num) (mul_nonneg W.axis.scale_pos.le hX.le),
      NominalProfile.physical_band_in_parameterInterval heta⟩

theorem seed_relaxed {p : Point} (hX : 0 < p.1) (hXi : p.1 ≤ NominalProfile.Xi)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain)
    (hc : ActivationContinuation.IsRelaxed W.controls.seedProfiles F.data.h p) :
    ActivationContinuation.IsRelaxed W.profiles F.data.h p :=
  relaxed_of_coordinates W.profiles W.controls.seedProfiles (seed_coordinates W hX hXi heta) hc

theorem seed_true {p : Point} (hX : 0 < p.1) (hXi : p.1 ≤ NominalProfile.Xi)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain)
    (hc : IsTrue W.controls.seedProfiles F.data.h p) : IsTrue W.profiles F.data.h p := by
  refine ⟨seed_relaxed W hX hXi heta hc.1, ?_⟩
  rw [(seed_coordinates W hX hXi heta).1, (seed_coordinates W hX hXi heta).2.1]
  exact hc.2

theorem continuation_relaxed {N : ℕ} {eps T : ℝ}
    (w : ActivationContinuation.ContinuationWitness W.axis.natural W.axis.scale_pos W.axis.small
      F.axisDatum_contDiff N eps) (hT : 0 < T)
    (hc : W.controls = Controls.ofContinuation W.axis w T hT)
    {p : Point} (heta : p.2 ∈ HeatedOutgoing.parameterDomain)
    (hX : p.1 ∈ Icc w.parameters.startRadius (110 : ℝ)) :
    ActivationContinuation.IsRelaxed W.profiles F.data.h p := by
  apply seed_relaxed W (w.parameters.startRadius_pos.trans_le hX.1) hX.2 heta
  have he : W.controls.seedProfiles = w.parameters.profiles := by rw [hc]; rfl
  rw [he]
  exact w.relaxed p heta hX

theorem moments_eq_profile_moments (X eta : ℝ) :
    NominalProfile.moments W.profiles.U W.profiles.E X eta =
      NominalProfile.moments W.U W.E X eta := by
  ext i
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  have he : W.profiles.E (x, eta) = W.E (x, eta) := (W.E_eq_sqrt_f hx.1).symm
  simp only [NominalProfile.density, he]
  rfl

theorem history_after (r : HistoryRow) {X eta : ℝ}
    (hX : W.controls.heatJoin ≤ X) (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    profileHistory W.profiles r (X, eta) = profileInitial W.profiles r eta +
      NominalProfile.moments (HeatedOutgoing.U F W.controls.radius)
        (HeatedOutgoing.E F W.controls.radius W.heat.physical.coefficients) X eta (historyIndex r)
            := by
  rw [history_eq_moment W.profiles r (W.controls.heatJoin_pos.le.trans hX),
    moments_eq_profile_moments W, W.moments_after hX heta]

end Witness

/-! ## Literal physical moments in the logarithmic chart -/

/-- Chart, given by `(XR * Real.exp p.1, p.2)`. -/
noncomputable def chart (XR : ℝ) (p : Point) : Point := (XR * Real.exp p.1, p.2)

theorem chart_positive {XR : ℝ} (hXR : 0 < XR) (p : Point) : 0 < (chart XR p).1 :=
  mul_pos hXR (Real.exp_pos _)

theorem integral_log_chart (f : ℝ → ℝ) {XR : ℝ} (hXR : 0 < XR) (y : ℝ) :
    (∫ x in Ioc 0 (XR * Real.exp y), f x) =
      XR * ∫ t in Iic y, Real.exp t * f (XR * Real.exp t) := by
  calc
    _ = ∫ x in Ioc 0 (XR * Real.exp y), (fun v => f (XR * v)) (x / XR) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x _
      dsimp only
      rw [mul_div_cancel₀ x hXR.ne']
    _ = XR * ∫ v in Ioc 0 (Real.exp y), f (XR * v) := by
      simpa only [mul_div_cancel_left₀ _ hXR.ne'] using
        OutgoingDilation.integral_dilate_Ioc (fun v => f (XR * v)) XR (XR * Real.exp y) hXR
    _ = _ := by
      rw [← ReleaseMoments.image_exp_Iic,
        integral_image_eq_integral_abs_deriv_smul measurableSet_Iic
          (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn]
      simp only [abs_of_pos (Real.exp_pos _), smul_eq_mul]

theorem sqrt_chart {XR : ℝ} (hXR : 0 < XR) (y : ℝ) :
    Real.sqrt (2 * (XR * Real.exp y)) = Real.sqrt (2 * XR) * Real.exp (y / 2) := by
  rw [← mul_assoc, Real.sqrt_mul (by positivity : 0 ≤ 2 * XR)]
  congr 1
  exact (Real.exp_half y).symm

theorem outgoing_U_chart (F : Profile) {XR : ℝ} (hXR : 0 < XR) (p : Point) :
    OutgoingDilation.U F XR (chart XR p) = F.logU p := by
  simp only [chart, OutgoingDilation.U, OutgoingProfile.Profile.U,
    mul_div_cancel_left₀ _ hXR.ne', Real.log_exp, Prod.eta]

theorem outgoing_E_chart (F : Profile) {XR : ℝ} (hXR : 0 < XR) (p : Point) :
    OutgoingDilation.E F XR (chart XR p) = F.logE p := by
  simp only [chart, OutgoingDilation.E, OutgoingProfile.Profile.E,
    mul_div_cancel_left₀ _ hXR.ne', Real.log_exp, Prod.eta]

theorem outgoing_M_chart (F : Profile) {XR : ℝ} (hXR : 0 < XR) (y eta : ℝ) :
    OutgoingDilation.M F XR eta (XR * Real.exp y) =
      XR * OutgoingHistories.M F.data F.amp (y, eta) := by
  unfold OutgoingDilation.M
  rw [integral_log_chart _ hXR, OutgoingHistories.M_eq_integral F.data F.amp_contDiff]
  congr 1
  apply setIntegral_congr_fun measurableSet_Iic
  intro t _
  change Real.exp t * OutgoingDilation.U F XR (chart XR (t, eta)) = _
  rw [outgoing_U_chart F hXR]
  rfl

theorem outgoing_J_chart (F : Profile) {XR : ℝ} (hXR : 0 < XR) (y eta : ℝ) :
    OutgoingDilation.J F XR eta (XR * Real.exp y) =
      (XR * Real.sqrt (2 * XR)) * OutgoingHistories.J F.reset F.amp (y, eta) := by
  unfold OutgoingDilation.J
  rw [integral_log_chart _ hXR, OutgoingHistories.J_eq_integral F.reset F.amp_contDiff]
  rw [mul_assoc]
  congr 1
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Iic
  intro t _
  change Real.exp t * (OutgoingDilation.H F XR (chart XR (t, eta)) *
    OutgoingDilation.U F XR (chart XR (t, eta))) = _
  rw [outgoing_U_chart F hXR]
  unfold OutgoingDilation.H
  rw [outgoing_E_chart F hXR]
  change Real.exp t * ((Real.sqrt (2 * (XR * Real.exp t)) * F.logE (t, eta)) * F.logU (t, eta)) = _
  dsimp only
  rw [sqrt_chart hXR, show 3 * t / 2 = t + t / 2 by ring, Real.exp_add]
  dsimp only [OutgoingProfile.Profile.logE, OutgoingProfile.Profile.logU,
    OutgoingHistories.E, OutgoingHistories.U]
  ring

theorem heated_I_chart (F : Profile) {XR : ℝ} (hXR : 0 < XR)
    (coef : ℝ → HeatedOutgoing.Coeff) {eta : ℝ} (heta : eta ∈ HeatedOutgoing.parameterDomain)
    (y : ℝ) :
    NominalProfile.moments (HeatedOutgoing.U F XR) (HeatedOutgoing.E F XR coef)
      (XR * Real.exp y) eta 1 =
      (XR * Real.sqrt (2 * XR)) * HeatSwitchCone.logI F XR coef (y, eta) := by
  change (∫ x in Ioc 0 (XR * Real.exp y), Real.sqrt (2 * x) * HeatedOutgoing.E F XR coef (x, eta))
      = _
  rw [integral_log_chart _ hXR, (HeatSwitchCone.logI_eq_past_integral F hXR coef heta y).2,
    mul_assoc]
  congr 1
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Iic
  intro t _
  change Real.exp t * (Real.sqrt (2 * (XR * Real.exp t)) * HeatedOutgoing.E F XR coef (XR *
      Real.exp t, eta)) = _
  dsimp only
  rw [sqrt_chart hXR, show 3 * t / 2 = t + t / 2 by ring, Real.exp_add]
  unfold HeatSwitchCone.logE
  ring

theorem heated_S_chart (F : Profile) {XR : ℝ} (hXR : 0 < XR)
    (coef : ℝ → HeatedOutgoing.Coeff) {eta : ℝ} (heta : eta ∈ HeatedOutgoing.parameterDomain)
    (y : ℝ) :
    NominalProfile.moments (HeatedOutgoing.U F XR) (HeatedOutgoing.E F XR coef)
      (XR * Real.exp y) eta 3 = XR * HeatSwitchCone.logS F XR coef (y, eta) := by
  change (∫ x in Ioc 0 (XR * Real.exp y), HeatedOutgoing.U F XR (x, eta) ^ 2 -
    HeatedOutgoing.E F XR coef (x, eta) ^ 2 / 2) = _
  rw [integral_log_chart _ hXR, (HeatSwitchCone.logS_eq_past_integral F hXR coef heta y).2]
  congr 1
  apply setIntegral_congr_fun measurableSet_Iic
  intro t _
  change Real.exp t * (OutgoingDilation.U F XR (chart XR (t, eta)) ^ 2 -
    HeatSwitchCone.logE F XR coef (t, eta) ^ 2 / 2) = _
  rw [outgoing_U_chart F hXR]

theorem heated_J_chart (F : Profile) {XR : ℝ} (hXR : 0 < XR)
    (coef : ℝ → HeatedOutgoing.Coeff) (y eta : ℝ) :
    NominalProfile.moments (HeatedOutgoing.U F XR) (HeatedOutgoing.E F XR coef)
      (XR * Real.exp y) eta 2 =
      (XR * Real.sqrt (2 * XR)) * OutgoingHistories.J F.reset F.amp (y, eta) := by
  have he : NominalProfile.moments (HeatedOutgoing.U F XR) (HeatedOutgoing.E F XR coef)
      (XR * Real.exp y) eta 2 = HeatedOutgoing.J F XR coef eta (XR * Real.exp y) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x _
    change HeatedOutgoing.U F XR (x, eta) * Real.sqrt (2 * x) * HeatedOutgoing.E F XR coef (x, eta)
        = _
    unfold HeatedOutgoing.H
    ring
  rw [he, HeatedOutgoing.J_unchanged F XR coef eta _ hXR, outgoing_J_chart F hXR]

namespace Witness

variable {F : Profile} (W : NominalProfile.Witness F)

theorem log_histories {p : Point} (hp : W.controls.heatJoin ≤ (chart W.controls.radius p).1)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    W.profiles.M (chart W.controls.radius p) = W.controls.radius * OutgoingHistories.M F.data F.amp
        p ∧
    W.profiles.I (chart W.controls.radius p) = (W.controls.radius * Real.sqrt (2 *
        W.controls.radius)) *
      HeatSwitchCone.logI F W.controls.radius W.heat.coefficients p ∧
    W.profiles.J (chart W.controls.radius p) = (W.controls.radius * Real.sqrt (2 *
        W.controls.radius)) *
      OutgoingHistories.J F.reset F.amp p ∧
    W.profiles.S (chart W.controls.radius p) = W.controls.radius *
      HeatSwitchCone.logS F W.controls.radius W.heat.coefficients p := by
  have hm := history_after W .mass hp heta
  have hi := history_after W .angular hp heta
  have hj := history_after W .transport hp heta
  have hs := history_after W .energy hp heta
  simp only [profileHistory, profileInitial, historyIndex_mass, historyIndex_angular,
    historyIndex_transport, historyIndex_energy, zero_add] at hm hi hj hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hm.trans (outgoing_M_chart F W.controls.radius_pos p.1 p.2)
  · exact hi.trans (heated_I_chart F W.controls.radius_pos W.heat.coefficients heta p.1)
  · exact hj.trans (heated_J_chart F W.controls.radius_pos W.heat.coefficients p.1 p.2)
  · exact hs.trans (heated_S_chart F W.controls.radius_pos W.heat.coefficients heta p.1)

theorem log_pressure {p : Point} (hp : W.controls.heatJoin < (chart W.controls.radius p).1)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    W.profiles.pressure (chart W.controls.radius p) =
      HeatSwitchCone.logPi F W.controls.radius W.heat.coefficients p := by
  exact (W.heat_agreement hp heta).2.2.trans
    (HeatSwitchCone.logPi_eq_canonical F W.heat.physical p heta).symm

end Witness

theorem parameterPartial_eq_scaled_within {D : RadialDomain} {f g : Field}
    (hf : ContDiffOn ℝ ∞ f D.carrier) {X y eta k : ℝ} (hp : (X, eta) ∈ D.carrier)
    (heta : eta ∈ HeatedOutgoing.parameterDomain) (hk : k ≠ 0)
    (he : ∀ xi ∈ HeatedOutgoing.parameterDomain, f (X, xi) = k * g (y, xi)) :
    parameterPartial f (X, eta) = k *
      derivWithin (fun xi => g (y, xi)) HeatedOutgoing.parameterDomain eta := by
  have hd := (parameterPartial_hasDerivAt D hf hp).div_const k
  have hg : HasDerivWithinAt (fun xi => g (y, xi)) (parameterPartial f (X, eta) / k)
      HeatedOutgoing.parameterDomain eta := by
    apply hd.hasDerivWithinAt.congr_of_mem _ heta
    intro xi hxi
    apply (eq_div_iff hk).mpr
    calc
      g (y, xi) * k = k * g (y, xi) := mul_comm _ _
      _ = f (X, xi) := (he xi hxi).symm
  rw [hg.derivWithin (uniqueDiffOn_Icc (by norm_num) eta heta)]
  field_simp

theorem smooth_parameterWithin_eq_dEta {g : Field} (hg : ContDiff ℝ ∞ g)
    {p : Point} (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    derivWithin (fun xi => g (p.1, xi)) HeatedOutgoing.parameterDomain p.2 =
      OutgoingHistories.dEta g p :=
  (OutgoingHistories.dEta_hasDerivAt hg p).hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Icc (by norm_num) p.2 heta)

theorem angular_scaled_quotient {R r : ℝ} (hR : R ≠ 0) (hr : r ≠ 0)
    (a b c k I Ieta J Jeta x z e : ℝ) :
    (a * (R * r * I) - b * (R * r * Ieta) - c * (R * r * Jeta) + k * (R * r * J)) /
        (R * x * (r * z * e)) =
      (a * I - b * Ieta - c * Jeta + k * J) / (x * z * e) := by
  rw [show a * (R * r * I) - b * (R * r * Ieta) - c * (R * r * Jeta) + k * (R * r * J) =
    (R * r) * (a * I - b * Ieta - c * Jeta + k * J) by ring,
    show R * x * (r * z * e) = (R * r) * (x * z * e) by ring,
    mul_div_mul_left _ _ (mul_ne_zero hR hr)]

theorem scaled_difference_quotient {R : ℝ} (hR : R ≠ 0) (a eta u v x : ℝ) :
    a * (R * u - eta * (R * v)) / (R * x) = a * (u - eta * v) / x := by
  rw [show a * (R * u - eta * (R * v)) = R * (a * (u - eta * v)) by ring,
    mul_div_mul_left _ _ hR]

theorem scaled_affine_quotient {R : ℝ} (hR : R ≠ 0) (a b u v x : ℝ) :
    (a * (R * u) - b * (R * v)) / (R * x) = (a * u - b * v) / x := by
  rw [show a * (R * u) - b * (R * v) = R * (a * u - b * v) by ring,
    mul_div_mul_left _ _ hR]

theorem shear_dilation_cancel {r z f : ℝ} (hr : r ≠ 0) (hz : z ≠ 0) (hf : f ≠ 0)
    (X df : ℝ) :
    -2 * X * df / f = 1 - 2 * (r * (z * (1 / 2)) * f + r * z * (df * X)) / (r * z * f) := by
  rw [show (2 : ℝ) * (r * (z * (1 / 2)) * f + r * z * (df * X)) =
    (r * z) * (f + 2 * df * X) by ring,
    mul_div_mul_left _ _ (mul_ne_zero hr hz)]
  field_simp [hf]; ring

/-- The logarithmic radial chart changes actual derivatives, not independent
formal jets. This statement is also valid for the matching profile before
the heat splice. -/
theorem physical_log_shears {D : RadialDomain} (P : Profiles D) {R : ℝ}
    (hR : 0 < R) (p : Point) (hp : chart R p ∈ D.carrier)
    (hf : P.f (chart R p) ≠ 0) :
    ActivationContinuation.shearA P (chart R p) =
        1 - 2 * deriv (fun y => P.E (R * Real.exp y, p.2)) p.1 / P.E (chart R p) ∧
      ActivationContinuation.shearB P (chart R p) =
        -2 * deriv (fun y => P.U (R * Real.exp y, p.2)) p.1 / P.E (chart R p) := by
  have hc := (Real.hasDerivAt_exp p.1).const_mul R
  have hfd := (radialPartial_hasDerivAt D P.f_smooth hp).comp p.1 hc
  have hud := (radialPartial_hasDerivAt D P.U_smooth hp).comp p.1 hc
  have hr := (((hasDerivAt_id p.1).div_const 2).exp).const_mul (Real.sqrt (2 * R))
  dsimp only [chart, Function.comp_def, id_eq] at hfd hud hr
  have he : (fun y => P.E (R * Real.exp y, p.2)) =
      (fun y => (Real.sqrt (2 * R) * Real.exp (y / 2)) * P.f (R * Real.exp y, p.2)) := by
    funext y
    exact congrArg (fun t => t * P.f (R * Real.exp y, p.2)) (sqrt_chart hR y)
  constructor
  · rw [he, (hr.fun_mul hfd).deriv]
    change -2 * (R * Real.exp p.1) * radialPartial P.f (chart R p) / P.f (chart R p) = _
    rw [show P.E (chart R p) = (Real.sqrt (2 * R) * Real.exp (p.1 / 2)) * P.f (chart R p) from
      congrArg (fun t => t * P.f (chart R p)) (sqrt_chart hR p.1)]
    exact shear_dilation_cancel (Real.sqrt_pos.2 (by positivity)).ne'
      (Real.exp_ne_zero _) hf _ _
  · rw [hud.deriv]
    unfold ActivationContinuation.shearB
    dsimp only [chart]
    ring

theorem physical_shear_cancel {r f X : ℝ} (hr : r ≠ 0) (hf : f ≠ 0)
    (hsq : r ^ 2 = 2 * X) (df : ℝ) :
    1 - 2 * X * (1 / (2 * r) * (2 * 1) * f + r * df) / (r * f) = -2 * X * df / f := by
  have hx : X = r ^ 2 / 2 := by linarith
  rw [hx]
  field_simp; ring

theorem modulated_shears_eq {D : RadialDomain} (P : Profiles D) {p : Point}
    (hp : p ∈ D.carrier) (hX : 0 < p.1) (hf : P.f p ≠ 0) :
    ModulatedCone.angularShear P.E p = ActivationContinuation.shearA P p ∧
      ModulatedCone.signedAxialShear P.E P.U p = ActivationContinuation.shearB P p := by
  have hr : Real.sqrt (2 * p.1) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have hr2 := Real.sq_sqrt (show 0 ≤ 2 * p.1 by positivity)
  have hd := ((Real.hasDerivAt_sqrt (show 2 * p.1 ≠ 0 by positivity)).comp p.1
    ((hasDerivAt_id p.1).const_mul 2)).fun_mul (radialPartial_hasDerivAt D P.f_smooth hp)
  dsimp only [Function.comp_def, id_eq] at hd
  constructor
  · unfold ModulatedCone.angularShear ActivationContinuation.shearA
    change 1 - 2 * p.1 * deriv (fun x => Real.sqrt (2 * x) * P.f (x, p.2)) p.1 /
      (Real.sqrt (2 * p.1) * P.f p) = _
    rw [hd.deriv]
    exact physical_shear_cancel hr hf hr2 _
  · unfold ModulatedCone.signedAxialShear ActivationContinuation.shearB
    rw [(radialPartial_hasDerivAt D P.U_smooth hp).deriv]
    ring

namespace Witness

variable {F : Profile} (W : NominalProfile.Witness F)

theorem log_history_parameters {p : Point}
    (hp : W.controls.heatJoin < (chart W.controls.radius p).1)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    parameterPartial W.profiles.M (chart W.controls.radius p) = W.controls.radius *
        OutgoingHistories.dEta (OutgoingHistories.M F.data F.amp) p ∧
    parameterPartial W.profiles.I (chart W.controls.radius p) =
      (W.controls.radius * Real.sqrt (2 * W.controls.radius)) *
        derivWithin (fun eta => HeatSwitchCone.logI F W.controls.radius W.heat.coefficients (p.1,
            eta))
          HeatedOutgoing.parameterDomain p.2 ∧
    parameterPartial W.profiles.J (chart W.controls.radius p) =
      (W.controls.radius * Real.sqrt (2 * W.controls.radius)) *
        OutgoingHistories.dEta (OutgoingHistories.J F.reset F.amp) p ∧
    parameterPartial W.profiles.S (chart W.controls.radius p) = W.controls.radius *
        derivWithin (fun eta => HeatSwitchCone.logS F W.controls.radius W.heat.coefficients (p.1,
            eta))
          HeatedOutgoing.parameterDomain p.2 ∧
    parameterPartial W.profiles.pressure (chart W.controls.radius p) =
        derivWithin (fun eta => HeatSwitchCone.logPi F W.controls.radius W.heat.coefficients (p.1,
            eta))
          HeatedOutgoing.parameterDomain p.2 := by
  have hmem := W.domain_contains (chart_positive W.controls.radius_pos p).le heta
  have hroot : W.controls.radius * Real.sqrt (2 * W.controls.radius) ≠ 0 :=
    mul_ne_zero W.controls.radius_pos.ne'
      (Real.sqrt_pos.2 (mul_pos (by norm_num) W.controls.radius_pos)).ne'
  have hm := parameterPartial_eq_scaled_within W.profiles.M_smooth hmem heta
      W.controls.radius_pos.ne'
    (fun eta he => (log_histories W (p := (p.1, eta)) hp.le he).1)
  have hi := parameterPartial_eq_scaled_within W.profiles.I_smooth hmem heta hroot
    (fun eta he => (log_histories W (p := (p.1, eta)) hp.le he).2.1)
  have hj := parameterPartial_eq_scaled_within W.profiles.J_smooth hmem heta hroot
    (fun eta he => (log_histories W (p := (p.1, eta)) hp.le he).2.2.1)
  have hs := parameterPartial_eq_scaled_within W.profiles.S_smooth hmem heta
      W.controls.radius_pos.ne'
    (fun eta he => (log_histories W (p := (p.1, eta)) hp.le he).2.2.2)
  have hP := parameterPartial_eq_scaled_within W.profiles.pressure_smooth hmem heta
    (show (1 : ℝ) ≠ 0 by norm_num) (fun eta he => by
      simp only [one_mul]
      exact log_pressure W (p := (p.1, eta)) hp he)
  rw [smooth_parameterWithin_eq_dEta (OutgoingHistories.M_smooth F.data F.amp_contDiff) heta] at hm
  rw [smooth_parameterWithin_eq_dEta (OutgoingHistories.J_smooth F.reset F.amp_contDiff) heta] at hj
  simp only [one_mul] at hP
  exact ⟨hm, hi, hj, hs, hP⟩

theorem log_fields {p : Point} (hp : W.controls.heatJoin < (chart W.controls.radius p).1)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    W.profiles.U (chart W.controls.radius p) = F.logU p ∧
    W.profiles.E (chart W.controls.radius p) = HeatSwitchCone.logE F W.controls.radius
        W.heat.coefficients p ∧
    W.profiles.H (chart W.controls.radius p) = Real.sqrt (2 * W.controls.radius) * Real.exp (p.1 /
        2) *
      HeatSwitchCone.logE F W.controls.radius W.heat.coefficients p := by
  have hx := chart_positive W.controls.radius_pos p
  have he : W.profiles.E (chart W.controls.radius p) =
      HeatSwitchCone.logE F W.controls.radius W.heat.coefficients p :=
    (W.E_eq_sqrt_f hx).symm.trans (W.heat_agreement hp heta).2.1
  refine ⟨(W.U_outgoing hp).trans (outgoing_U_chart F W.controls.radius_pos p), he, ?_⟩
  have hH : W.profiles.H (chart W.controls.radius p) =
      Real.sqrt (2 * (chart W.controls.radius p).1) * W.profiles.E (chart W.controls.radius p) := by
    dsimp only [Profiles.H, Profiles.E]
    rw [← mul_assoc, Real.mul_self_sqrt (mul_nonneg (by norm_num) hx.le)]
  rw [hH, he]
  exact congrArg (fun z => z * HeatSwitchCone.logE F W.controls.radius W.heat.coefficients p)
    (sqrt_chart W.controls.radius_pos p.1)

theorem log_transport {p : Point} (hp : W.controls.heatJoin < (chart W.controls.radius p).1)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    W.profiles.W F.data.h (chart W.controls.radius p) = OutgoingHistories.W F.data F.amp p := by
  have hmem := W.domain_contains (chart_positive W.controls.radius_pos p).le heta
  have hv := (log_histories W hp.le heta).1
  have hd := (log_history_parameters W hp heta).1
  have hf := ActivationStocks.profile_massFlux W.profiles F.data.h hmem
  rw [hv, hd] at hf
  unfold OutgoingHistories.W OutgoingHistories.X
  apply (eq_div_iff (Real.exp_ne_zero p.1)).mpr
  apply mul_left_cancel₀ W.controls.radius_pos.ne'
  convert! hf using 1 <;>
    dsimp only [chart, ActivationStocks.massFlux, OutgoingHistories.XW, OutgoingHistories.X,
      NaturalAxisData.D, NaturalAxisData.d, StressAlgebra.axialExponent,
          StressAlgebra.coordinateFactor] <;> ring

theorem log_lags {p : Point} (hp : W.controls.heatJoin < (chart W.controls.radius p).1)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    W.profiles.angularLag F.data.h (chart W.controls.radius p) =
        HeatSwitchCone.Qs F W.controls.radius W.heat.coefficients p ∧
    W.profiles.axialLag F.data.h (chart W.controls.radius p) =
        HeatSwitchCone.Ns F W.controls.radius W.heat.coefficients p := by
  have hx := chart_positive W.controls.radius_pos p
  have hmem := W.domain_contains hx.le heta
  have hf := f_positive W hx heta
  have hv := log_histories W hp.le heta
  have hd := log_history_parameters W hp heta
  have he := log_fields W hp heta
  have hroot : Real.sqrt (2 * W.controls.radius) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos (by norm_num) W.controls.radius_pos)).ne'
  have hE : HeatSwitchCone.logE F W.controls.radius W.heat.coefficients p ≠ 0 := by
    rw [← he.2.1]
    exact W.profiles.E_ne_zero hx hf.ne'
  constructor
  · rw [W.profiles.angularLag_integrated F.data.h hmem hx.ne' (W.profiles.H_ne_zero hx.ne' hf.ne'),
      log_transport W hp heta, hv.2.1, hv.2.2.1, hd.2.1, hd.2.2.1, he.2.2]
    unfold HeatSwitchCone.Qs
    simp only [chart]
    rw [show 3 * p.1 / 2 = p.1 + p.1 / 2 by ring, Real.exp_add]
    congr 1
    exact angular_scaled_quotient W.controls.radius_pos.ne' hroot _ _ _ _ _ _ _ _ _ _ _
  · rw [W.profiles.axialLag_integrated F.data.h hmem hx, log_transport W hp heta,
      he.1, hv.1, hv.2.2.2, hd.1, hd.2.2.2.1, hd.2.2.2.2, log_pressure W hp heta]
    unfold HeatSwitchCone.Ns
    simp only [chart]
    rw [scaled_difference_quotient W.controls.radius_pos.ne',
      scaled_affine_quotient W.controls.radius_pos.ne']

theorem log_stocks {p : Point} (hp : W.controls.heatJoin < (chart W.controls.radius p).1)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    ReferenceBounds.p1 W.profiles F.data.h (chart W.controls.radius p) =
        HeatSwitchCone.stressScale F W.controls.radius W.heat.coefficients p ∧
    ReferenceBounds.p2 W.profiles F.data.h (chart W.controls.radius p) =
        W.controls.radius * Real.exp p.1 * HeatSwitchCone.Ns F W.controls.radius
            W.heat.coefficients p /
          (NaturalAxisData.L F.data.h p.2 * HeatSwitchCone.logE F W.controls.radius
              W.heat.coefficients p) := by
  have hh := log_lags W hp heta
  constructor
  · rw [ReferenceBounds.p1, hh.1]
    rfl
  · rw [ReferenceBounds.p2, ReferenceBounds.ns, hh.2, (log_fields W hp heta).2.1]
    simp only [chart]
    ring

/-- Both radial shears are derivatives of the actual fields. The signed
axial convention is explicitly the negative of the outgoing convention. -/
theorem log_shears {p : Point} (hp : W.controls.heatJoin < (chart W.controls.radius p).1)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    ActivationContinuation.shearA W.profiles (chart W.controls.radius p) =
        HeatSwitchCone.radialA F W.controls.radius W.heat.coefficients p ∧
    ActivationContinuation.shearB W.profiles (chart W.controls.radius p) =
        -HeatSwitchCone.radialB F W.controls.radius W.heat.coefficients p := by
  have hx := chart_positive W.controls.radius_pos p
  have hmem := W.domain_contains hx.le heta
  have hf := f_positive W hx heta
  have hr : Real.sqrt (2 * W.controls.radius) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos (by norm_num) W.controls.radius_pos)).ne'
  have hnear : ∀ᶠ y in 𝓝 p.1, W.controls.heatJoin < W.controls.radius * Real.exp y :=
    (continuous_const.mul Real.continuous_exp).continuousAt.eventually (Ioi_mem_nhds hp)
  have hchart := (Real.hasDerivAt_exp p.1).const_mul W.controls.radius
  have hfp := (radialPartial_hasDerivAt W.domain W.profiles.f_smooth hmem).comp p.1 hchart
  have hup := (radialPartial_hasDerivAt W.domain W.profiles.U_smooth hmem).comp p.1 hchart
  have hroot := (((hasDerivAt_id p.1).div_const 2).exp).const_mul (Real.sqrt (2 *
      W.controls.radius))
  have heq : (fun y => HeatSwitchCone.logE F W.controls.radius W.heat.coefficients (y, p.2)) =ᶠ[𝓝
      p.1]
      (fun y => (Real.sqrt (2 * W.controls.radius) * Real.exp (y / 2)) *
        W.profiles.f (W.controls.radius * Real.exp y, p.2)) := by
    filter_upwards [hnear] with y hy
    rw [← (log_fields W (p := (y, p.2)) hy heta).2.1]
    change Real.sqrt (2 * (W.controls.radius * Real.exp y)) *
      W.profiles.f (W.controls.radius * Real.exp y, p.2) = _
    rw [sqrt_chart W.controls.radius_pos]
  have hEder := (hroot.mul hfp).congr_of_eventuallyEq heq
  have hueq : (fun y => F.logU (y, p.2)) =ᶠ[𝓝 p.1]
      (fun y => W.profiles.U (W.controls.radius * Real.exp y, p.2)) := by
    filter_upwards [hnear] with y hy
    exact (log_fields W (p := (y, p.2)) hy heta).1.symm
  have hUder := hup.congr_of_eventuallyEq hueq
  constructor
  · rw [HeatSwitchCone.radialA, hEder.deriv, heq.eq_of_nhds]
    unfold ActivationContinuation.shearA
    simp only [chart, id_eq, Function.comp_apply]
    exact shear_dilation_cancel hr (Real.exp_ne_zero _) hf.ne' _ _
  · rw [HeatSwitchCone.radialB, OutgoingHistories.dY_eq_deriv F.logU_contDiff, hUder.deriv]
    unfold ActivationContinuation.shearB
    rw [(log_fields W hp heta).2.1]
    simp only [chart]
    ring

end Witness

theorem stock_ratio_identity (x q n L e : ℝ) (hq : q ≠ 0) :
    x * n / (L * e) = (x * q / L) * (n / (e * q)) := by
  by_cases hL : L = 0
  · simp [hL]
  by_cases he : e = 0
  · simp [he]
  field_simp

theorem relaxed_scaled_coordinates {a b s r : ℝ} (ha : 0 < a)
    (hp : 2 < s * (1 - b * r / a))
    (hc : a * (1 + (b / a) ^ 2) <
      ConeAlgebra.coneBound (s * (1 - b * r / a)) (s * (r + b / a))) :
    ActivationContinuation.Relaxed a (-b) s (s * r) := by
  have hP : ActivationContinuation.projection s (s * r) a (-b) = s * (1 - b * r / a) := by
    unfold ActivationContinuation.projection
    ring
  have hJ : ActivationContinuation.transverse s (s * r) a (-b) = s * (r + b / a) := by
    unfold ActivationContinuation.transverse
    ring
  have hV : ActivationContinuation.shearSize a (-b) = a * (1 + (b / a) ^ 2) := by
    simp only [ActivationContinuation.shearSize, neg_div, neg_sq]
  exact ⟨ha, hP ▸ hp, by rwa [hV, hP, hJ]⟩

/-- Heat relaxed at, constructed using `0`. -/
noncomputable def HeatRelaxedAt (F : Profile) (XR : ℝ) (coef : ℝ → HeatedOutgoing.Coeff)
    (p : Point) : Prop :=
  0 < HeatSwitchCone.Qs F XR coef p ∧ 0 < HeatSwitchCone.radialA F XR coef p ∧
    2 < HeatSwitchCone.normalP F XR coef p ∧
    HeatSwitchCone.normalV F XR coef p <
      ConeAlgebra.coneBound (HeatSwitchCone.normalP F XR coef p) (HeatSwitchCone.normalJ F XR coef
          p)

/-- The pressure cancellation and all preceding histories are retained
before the first compensation patch, for every parameter. -/
theorem heated_histories_before_patch (F : Profile) {R : ℝ} (hR : 0 < R)
    (coef : ℝ → HeatedOutgoing.Coeff) {p : Point} (hp : p.1 ≤ OutgoingDilation.patchClock F) :
    HeatSwitchCone.logI F R coef p = OutgoingHistories.I F.reset p ∧
      HeatSwitchCone.logS F R coef p = OutgoingHistories.S F.reset F.amp p ∧
      HeatSwitchCone.logPi F R coef p = OutgoingHistories.Pi F.reset p := by
  have hdiff (t : ℝ) (ht : t ∈ uIcc (OutgoingDilation.patchClock F) p.1) :
      HeatSwitchCone.logE F R coef (t, p.2) = F.logE (t, p.2) :=
    HeatSwitchCone.logE_before_patch F hR coef (ht.2.trans (max_le le_rfl hp))
  have hi : (∫ t in OutgoingDilation.patchClock F..p.1,
      Real.exp (3 * t / 2) * (HeatSwitchCone.logE F R coef (t, p.2) - F.logE (t, p.2))) = 0 := by
    calc
      _ = ∫ _t in OutgoingDilation.patchClock F..p.1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [hdiff t ht, sub_self, mul_zero]
      _ = 0 := by simp
  have hs : (∫ t in OutgoingDilation.patchClock F..p.1,
      Real.exp t * (HeatSwitchCone.logE F R coef (t, p.2) ^ 2 - F.logE (t, p.2) ^ 2)) = 0 := by
    calc
      _ = ∫ _t in OutgoingDilation.patchClock F..p.1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [hdiff t ht, sub_self, mul_zero]
      _ = 0 := by simp
  have hpi : (∫ t in OutgoingDilation.patchClock F..p.1,
      HeatSwitchCone.logE F R coef (t, p.2) ^ 2 - F.logE (t, p.2) ^ 2) = 0 := by
    calc
      _ = ∫ _t in OutgoingDilation.patchClock F..p.1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [hdiff t ht, sub_self]
      _ = 0 := by simp
  simp only [HeatSwitchCone.logI, HeatSwitchCone.logS, HeatSwitchCone.logPi, hi, hs, hpi,
    mul_zero, add_zero, sub_zero, and_self]

theorem heated_lags_before_patch (F : Profile) {R : ℝ} (hR : 0 < R)
    (coef : ℝ → HeatedOutgoing.Coeff) {p : Point} (hp : p.1 ≤ OutgoingDilation.patchClock F)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    HeatSwitchCone.Qs F R coef p = OutgoingHistories.Qs F.reset F.amp p ∧
      HeatSwitchCone.Ns F R coef p = OutgoingHistories.Ns F.reset F.amp p := by
  have hi : (fun eta => HeatSwitchCone.logI F R coef (p.1, eta)) =
      (fun eta => OutgoingHistories.I F.reset (p.1, eta)) :=
    funext (fun eta => (heated_histories_before_patch F hR coef (p := (p.1, eta)) hp).1)
  have hs : (fun eta => HeatSwitchCone.logS F R coef (p.1, eta)) =
      (fun eta => OutgoingHistories.S F.reset F.amp (p.1, eta)) :=
    funext (fun eta => (heated_histories_before_patch F hR coef (p := (p.1, eta)) hp).2.1)
  have hpi : (fun eta => HeatSwitchCone.logPi F R coef (p.1, eta)) =
      (fun eta => OutgoingHistories.Pi F.reset (p.1, eta)) :=
    funext (fun eta => (heated_histories_before_patch F hR coef (p := (p.1, eta)) hp).2.2)
  have hv := heated_histories_before_patch F hR coef hp
  constructor
  · rw [HeatSwitchCone.Qs, OutgoingHistories.Qs_integrated, hv.1, hi,
      smooth_parameterWithin_eq_dEta (OutgoingHistories.I_smooth F.reset) heta,
      HeatSwitchCone.logE_before_patch F hR coef hp,
      show OutgoingHistories.X p * OutgoingHistories.H F.reset p =
        Real.exp (3 * p.1 / 2) * F.logE p from OutgoingHistories.angularWeight_eq F.reset p]
  · rw [HeatSwitchCone.Ns, OutgoingHistories.Ns_integrated, hv.2.1, hv.2.2, hs, hpi,
      smooth_parameterWithin_eq_dEta (OutgoingHistories.S_smooth F.reset F.amp_contDiff) heta,
      smooth_parameterWithin_eq_dEta (OutgoingHistories.Pi_smooth F.reset) heta]
    rfl

theorem heated_shears_before_patch (F : Profile) {R : ℝ} (hR : 0 < R)
    (coef : ℝ → HeatedOutgoing.Coeff) {p : Point} (hp : p.1 < OutgoingDilation.patchClock F) :
    HeatSwitchCone.radialA F R coef p = OutgoingEntranceCone.coneA F.reset p ∧
      HeatSwitchCone.radialB F R coef p = OutgoingEntranceCone.coneB F.reset F.amp p := by
  have he : (fun y => HeatSwitchCone.logE F R coef (y, p.2)) =ᶠ[𝓝 p.1]
      (fun y => F.logE (y, p.2)) := by
    filter_upwards [Iio_mem_nhds hp] with y hy
    exact HeatSwitchCone.logE_before_patch F hR coef hy.le
  constructor
  · rw [HeatSwitchCone.radialA, he.deriv_eq, HeatSwitchCone.logE_before_patch F hR coef hp.le,
      OutgoingEntranceCone.coneA_eq_E_derivative,
      OutgoingHistories.dY_eq_deriv (OutgoingHistories.E_smooth F.reset)]
    rfl
  · rw [HeatSwitchCone.radialB, HeatSwitchCone.logE_before_patch F hR coef hp.le]
    rfl

theorem heated_relaxed_before_patch (F : Profile) {R : ℝ} (hR : 0 < R)
    (coef : ℝ → HeatedOutgoing.Coeff) {p : Point} (hp : p.1 < OutgoingDilation.patchClock F)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain)
    (hc : OutgoingCone.RelaxedAt F.reset F.amp R p) : HeatRelaxedAt F R coef p := by
  have hl := heated_lags_before_patch F hR coef hp.le heta
  have ha := heated_shears_before_patch F hR coef hp
  have hr : HeatSwitchCone.ratio F R coef p = OutgoingEntranceCone.coneRatio F.reset F.amp p := by
    simp only [HeatSwitchCone.ratio, hl.1, hl.2, HeatSwitchCone.logE_before_patch F hR coef hp.le]
    rfl
  have hs : HeatSwitchCone.stressScale F R coef p = OutgoingHistories.p1 R F.reset F.amp p := by
    rw [HeatSwitchCone.stressScale, hl.1]
    rfl
  refine ⟨hl.1 ▸ hc.angular_positive, ha.1 ▸ hc.radial_positive, ?_, ?_⟩
  · simp only [HeatSwitchCone.normalP, HeatSwitchCone.sourceC, hs, ha.1, ha.2, hr]
    exact hc.stress_gt_two
  · simp only [HeatSwitchCone.normalP, HeatSwitchCone.normalJ, HeatSwitchCone.normalV,
      HeatSwitchCone.sourceC, HeatSwitchCone.sourceJ, hs, ha.1, ha.2, hr]
    exact hc.root_strict

namespace Witness

variable {F : Profile} (W : NominalProfile.Witness F)

theorem log_second_stock {p : Point} (hp : W.controls.heatJoin < (chart W.controls.radius p).1)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain)
    (hq : HeatSwitchCone.Qs F W.controls.radius W.heat.coefficients p ≠ 0) :
    ReferenceBounds.p2 W.profiles F.data.h (chart W.controls.radius p) =
      HeatSwitchCone.stressScale F W.controls.radius W.heat.coefficients p *
        HeatSwitchCone.ratio F W.controls.radius W.heat.coefficients p := by
  rw [(log_stocks W hp heta).2]
  exact stock_ratio_identity _ _ _ _ _ hq

theorem heat_relaxed {p : Point} (hp : W.controls.heatJoin < (chart W.controls.radius p).1)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain)
    (hc : HeatRelaxedAt F W.controls.radius W.heat.coefficients p) :
    ActivationContinuation.IsRelaxed W.profiles F.data.h (chart W.controls.radius p) := by
  have hs := log_shears W hp heta
  unfold ActivationContinuation.IsRelaxed
  rw [hs.1, hs.2, (log_stocks W hp heta).1, log_second_stock W hp heta hc.1.ne']
  exact relaxed_scaled_coordinates hc.2.1 hc.2.2.1 hc.2.2.2

theorem heat_true {p : Point} (hp : W.controls.heatJoin < (chart W.controls.radius p).1)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain)
    (hc : HeatSwitchCone.TrueAt F W.controls.radius W.heat.coefficients p) :
    IsTrue W.profiles F.data.h (chart W.controls.radius p) := by
  refine ⟨heat_relaxed W hp heta ⟨hc.1, hc.2.1, hc.2.2.2.1, hc.2.2.2.2⟩, ?_⟩
  rw [(log_shears W hp heta).1, (log_shears W hp heta).2]
  simp only [ActivationContinuation.shearSize, neg_div, neg_sq]
  exact hc.2.2.1

theorem chart_after_match {p : Point} (hp : 0 ≤ p.1) :
    W.controls.heatJoin < (chart W.controls.radius p).1 := by
  exact W.controls.heatJoin_lt_radius.trans_le
    (le_mul_of_one_le_right W.controls.radius_pos.le (Real.one_le_exp hp))

theorem chart_after_matching {p : Point} (hp : (-5 : ℝ) < p.1) :
    W.controls.heatJoin < (chart W.controls.radius p).1 :=
  mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hp) W.controls.radius_pos

theorem clean_relaxed_before_hold
    (hc : OutgoingCone.ProfileCleanCone F W.controls.radius (-5)) {p : Point}
    (hy : (-5 : ℝ) < p.1) (hhold : p.1 ≤ F.data.core.holdStart)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    ActivationContinuation.IsRelaxed W.profiles F.data.h (chart W.controls.radius p) := by
  have hend : F.data.core.holdStart ≤ OutgoingCone.cleanEnd F.data :=
    (OutgoingTail.coreEndpoint_ge_hold F.data).trans
      (TerminalHistoryBridge.terminalStart_after_endpoint F).le
  exact heat_relaxed W (chart_after_matching W hy) heta
    (heated_relaxed_before_patch F W.controls.radius_pos W.heat.coefficients
      (hhold.trans_lt (OutgoingDilation.patchClock_after_hold F)) heta
      (hc.relaxed p ⟨⟨hy.le, hhold.trans hend⟩, heta⟩))

theorem terminal_true {y eta : ℝ} (hsmall : TerminalCone.SmallTail F.data)
    (hXR : TerminalCone.radiusThreshold F ≤ W.controls.radius)
    (hy : TerminalCone.terminalStart F.data ≤ y) (hy' : y < OutgoingTail.tailEnd F.data)
    (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    IsTrue W.profiles F.data.h (chart W.controls.radius (y, eta)) := by
  have hy0 : 0 ≤ y := (SchedulePressure.endpoint_pos F.data).le.trans
    ((TerminalHistoryBridge.terminalStart_after_endpoint F).le.trans hy)
  exact heat_true W (chart_after_match W hy0) heta
    (TerminalHistoryBridge.terminal_forward_cone F W.outgoing_specification W.heat.physical
      hsmall hXR hy hy' heta).1

end Witness

/-! ## A compensation bound chosen before the entrance radius -/

/-- Compensated family data, collecting `bound`, `bound_pos`, `radiusFloor`, `radiusFloor_pos`,
`branches`, `true_from_hold`. -/
structure CompensatedFamily (F : Profile) where
  /-- Bound of `CompensatedFamily`, of type `ℝ`. -/
  bound : ℝ
  bound_pos : 0 < bound
  /-- Radius floor of `CompensatedFamily`, of type `ℝ`. -/
  radiusFloor : ℝ
  radiusFloor_pos : 0 < radiusFloor
  branches : ∀ XR : ℝ, radiusFloor ≤ XR → Nonempty (ExtendedHeatedOutgoing.Witness F XR bound)
  true_from_hold : ∀ XR : ℝ, radiusFloor ≤ XR →
    ∀ w : ExtendedHeatedOutgoing.Witness F XR bound,
    ∀ p ∈ OutgoingCone.trueWindow F.data, HeatSwitchCone.TrueAt F XR w.coefficients p

theorem exists_compensatedFamily (F : Profile) {anchor left : ℝ}
    (hc : OutgoingCone.CleanOutgoingCone F.reset anchor left) (ha : 0 < anchor) :
    Nonempty (CompensatedFamily F) := by
  obtain ⟨R0, B, hR0, hB, hbranches⟩ := ExtendedHeatedOutgoing.exists_witness F
  obtain ⟨R1, _hR1, hcone⟩ := HeatSwitchCone.preserves_true_cone F hc ha B
  exact ⟨⟨B, hB, max R0 R1, hR0.trans_le (le_max_left _ _),
    fun XR hXR => hbranches XR ((le_max_left _ _).trans hXR),
    fun XR hXR w p hp => hcone XR ((le_max_right _ _).trans hXR) w.physical p hp⟩⟩

namespace CompensatedFamily

variable {F : Profile} (G : CompensatedFamily F)

/-- The actual heat witness and the nominal fields are constructed only after
the same physical radius has met the previously fixed bound. -/
noncomputable def assemble {D : ℝ} (hF : OutgoingProfile.Specification F D)
    (A : AxisStage F) (c : Controls A) (hr : G.radiusFloor ≤ c.radius)
    (hsep : c.separation ≤ Real.exp (-8))
    (hs : ∀ eta ∈ HeatedOutgoing.parameterDomain, SmallDebt F c.debt eta) : NominalProfile.Witness
        F :=
  ⟨A, c, D, hF, G.bound, Classical.choice (G.branches c.radius hr), hsep, hs⟩

theorem assemble_axis {D : ℝ} (hF : OutgoingProfile.Specification F D)
    (A : AxisStage F) (c : Controls A) (hr : G.radiusFloor ≤ c.radius)
    (hsep : c.separation ≤ Real.exp (-8))
    (hs : ∀ eta ∈ HeatedOutgoing.parameterDomain, SmallDebt F c.debt eta) :
    (G.assemble hF A c hr hsep hs).axis = A := rfl

theorem assemble_controls {D : ℝ} (hF : OutgoingProfile.Specification F D)
    (A : AxisStage F) (c : Controls A) (hr : G.radiusFloor ≤ c.radius)
    (hsep : c.separation ≤ Real.exp (-8))
    (hs : ∀ eta ∈ HeatedOutgoing.parameterDomain, SmallDebt F c.debt eta) :
    (G.assemble hF A c hr hsep hs).controls = c := rfl

theorem assemble_bound {D : ℝ} (hF : OutgoingProfile.Specification F D)
    (A : AxisStage F) (c : Controls A) (hr : G.radiusFloor ≤ c.radius)
    (hsep : c.separation ≤ Real.exp (-8))
    (hs : ∀ eta ∈ HeatedOutgoing.parameterDomain, SmallDebt F c.debt eta) :
    (G.assemble hF A c hr hsep hs).heatBound = G.bound := rfl

theorem assemble_true_from_hold {D : ℝ} (hF : OutgoingProfile.Specification F D)
    (A : AxisStage F) (c : Controls A) (hr : G.radiusFloor ≤ c.radius)
    (hsep : c.separation ≤ Real.exp (-8))
    (hs : ∀ eta ∈ HeatedOutgoing.parameterDomain, SmallDebt F c.debt eta)
    (p : Point) (hp : p ∈ OutgoingCone.trueWindow F.data) :
    HeatSwitchCone.TrueAt F c.radius (G.assemble hF A c hr hsep hs).heat.coefficients p :=
  G.true_from_hold c.radius hr _ p hp

theorem assemble_profile_true {D : ℝ} (hF : OutgoingProfile.Specification F D)
    (A : AxisStage F) (c : Controls A) (hr : G.radiusFloor ≤ c.radius)
    (hsep : c.separation ≤ Real.exp (-8))
    (hs : ∀ eta ∈ HeatedOutgoing.parameterDomain, SmallDebt F c.debt eta)
    (p : Point) (hp : p ∈ OutgoingCone.trueWindow F.data) :
    IsTrue (G.assemble hF A c hr hsep hs).profiles F.data.h (chart c.radius p) := by
  let W := G.assemble hF A c hr hsep hs
  have hy0 : 0 ≤ p.1 := F.data.core.holdStart_pos.le.trans hp.1.1
  exact Witness.heat_true W (Witness.chart_after_match W hy0) hp.2
    (G.assemble_true_from_hold hF A c hr hsep hs p hp)

theorem assemble_profile_true_late {D : ℝ} (hF : OutgoingProfile.Specification F D)
    (A : AxisStage F) (c : Controls A) (hr : G.radiusFloor ≤ c.radius)
    (hsep : c.separation ≤ Real.exp (-8))
    (hs : ∀ eta ∈ HeatedOutgoing.parameterDomain, SmallDebt F c.debt eta)
    (hsmall : TerminalCone.SmallTail F.data) (hXR : TerminalCone.radiusThreshold F ≤ c.radius)
    {p : Point} (hp : F.data.core.holdStart ≤ p.1) (hend : p.1 < OutgoingTail.tailEnd F.data)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    IsTrue (G.assemble hF A c hr hsep hs).profiles F.data.h (chart c.radius p) := by
  by_cases hy : p.1 ≤ OutgoingCone.cleanEnd F.data
  · exact G.assemble_profile_true hF A c hr hsep hs p ⟨⟨hp, hy⟩, heta⟩
  · exact Witness.terminal_true (G.assemble hF A c hr hsep hs) hsmall hXR
      (le_of_not_ge hy) hend heta

theorem assemble_profile_relaxed_outer {D : ℝ} (hF : OutgoingProfile.Specification F D)
    (A : AxisStage F) (c : Controls A) (hr : G.radiusFloor ≤ c.radius)
    (hsep : c.separation ≤ Real.exp (-8))
    (hs : ∀ eta ∈ HeatedOutgoing.parameterDomain, SmallDebt F c.debt eta)
    (hsmall : TerminalCone.SmallTail F.data) (hXR : TerminalCone.radiusThreshold F ≤ c.radius)
    (hclean : OutgoingCone.ProfileCleanCone F c.radius (-5))
    {p : Point} (hp : (-5 : ℝ) < p.1) (hend : p.1 < OutgoingTail.tailEnd F.data)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    ActivationContinuation.IsRelaxed (G.assemble hF A c hr hsep hs).profiles F.data.h
      (chart c.radius p) := by
  by_cases hy : p.1 ≤ F.data.core.holdStart
  · exact Witness.clean_relaxed_before_hold (G.assemble hF A c hr hsep hs) hclean hp hy heta
  · exact (G.assemble_profile_true_late hF A c hr hsep hs hsmall hXR (le_of_not_ge hy) hend heta).1

/-- The already selected axis stage and continuation are used literally in
the final fields; only the compensation branch is selected here. -/
noncomputable def assemblePrepared {D : ℝ} (hF : OutgoingProfile.Specification F D)
    {N : ℕ} {delta radiusFloor : ℝ}
    (M : MatchingConeBounds.PreparedWitness F N delta radiusFloor)
    (hr : G.radiusFloor ≤ radiusFloor) : NominalProfile.Witness F :=
  G.assemble hF M.axis M.controls (hr.trans M.bounds.radius_large)
    M.bounds.matching.separation.le (fun _eta heta => M.bounds.matching.smallDebt
        M.bounds.debt_radius heta)

theorem prepared_continuation_relaxed {D : ℝ} (hF : OutgoingProfile.Specification F D)
    {N : ℕ} {delta radiusFloor : ℝ}
    (M : MatchingConeBounds.PreparedWitness F N delta radiusFloor)
    (hr : G.radiusFloor ≤ radiusFloor) {p : Point}
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain)
    (hp : p.1 ∈ Icc M.continuation.parameters.startRadius (110 : ℝ)) :
    ActivationContinuation.IsRelaxed (G.assemblePrepared hF M hr).profiles F.data.h p :=
  Witness.continuation_relaxed (G.assemblePrepared hF M hr) M.continuation M.shapeTime_pos rfl heta
      hp

theorem prepared_shape_relaxed {D : ℝ} (hF : OutgoingProfile.Specification F D)
    {N : ℕ} {delta radiusFloor : ℝ}
    (M : MatchingConeBounds.PreparedWitness F N delta radiusFloor)
    (hr : G.radiusFloor ≤ radiusFloor) {X eta : ℝ}
    (hX : NominalProfile.Xi ≤ X) (hR : X ≤ M.controls.radius * Real.exp (-8))
    (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    ActivationContinuation.IsRelaxed (G.assemblePrepared hF M hr).profiles F.data.h (X, eta) := by
  let W := G.assemblePrepared hF M hr
  have hsmall := M.bounds.matching.smallDebt M.bounds.debt_radius heta
  have hinit := continuation_first_at_Xi M.continuation M.shapeTime_pos
    M.bounds.matching.separation.le hsmall heta
  have hc := M.bounds.shape_relaxed hX hR heta hinit
  apply Witness.prefix_relaxed W (NominalProfile.Xi_pos.trans_le hX) _ heta hc
  exact hR.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by norm_num : (-8 : ℝ) ≤ -5)) M.controls.radius_pos.le)

end CompensatedFamily

namespace Initial

open NaturalAxisCoefficients

/-- Exact physical shears on the initial natural collar. -/
theorem physical_initial_shears {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
    (E : NaturalEntrance.EntranceProfile d Λ C) {hΛ : 0 < Λ}
    {hsmall : NaturalAxisData.SmallParameters h j} {hP0 : ContDiff ℝ ∞ P0}
    (r : ActivationContinuation.RampParameters E.profile.family hΛ hsmall hP0)
    {y η : ℝ} (hy : y ≤ r.refTime) (hη : η ∈ ReferencePath.parameterInterval) :
    let N := ReferencePath.Input.ofNatural hΛ E.profile.family
    let L := StressActivation.FromReference.refLog N r.refTime
    let U := StressActivation.FromReference.refAxial N r.refTime
    let z : Point := (radius N.endpoint y, η)
    ActivationContinuation.shearA r.profiles z = actualP1 r.actTime r.kappa L (y, η) ∧
      ActivationContinuation.shearB r.profiles z = actualP2 r.actTime r.kappa N.endpoint L U (y, η)
          := by
  let N := ReferencePath.Input.ofNatural hΛ E.profile.family
  let L := StressActivation.FromReference.refLog N r.refTime
  let U := StressActivation.FromReference.refAxial N r.refTime
  let z : Point := (radius N.endpoint y, η)
  let R := r.reference
  let P := r.profiles
  have hx : 0 < z.1 := mul_pos N.endpoint_pos (Real.exp_pos y)
  have hlog : R.logPoint z = (y, η) := by
    change (R.logTime (radius R.radius0 y), η) = (y, η)
    rw [R.logTime_chart]
  have hd := TransitionRamp.physical_radial_equations E.profile.family hΛ hsmall
    r.refTime_pos r.refTime_bound hP0 (κ := r.kappa) r.actTime_pos r.before_big
      r.widthU_pos r.widthA_pos hη hx
  change (z.1 * radialPartial P.f z / P.f z =
      TransitionRamp.angularSlope r.actTime r.kappa R.bigTime r.widthU r.widthA R.angularStock
          (R.logPoint z)) ∧
    (z.1 * radialPartial P.U z =
      TransitionRamp.axialSlope r.actTime r.kappa R.bigTime r.widthU R.axialStock (R.logPoint z))
          at hd
  rw [hlog] at hd
  have hs := TransitionRamp.ofNatural_stock_slopes E.profile.family hΛ hsmall
    r.refTime_pos r.refTime_bound hP0 y hy hη
  change R.angularStock (y, η) = -2 * radialPartial L (y, η) ∧
    R.axialStock (y, η) = -2 * radialPartial U (y, η) at hs
  have hb : y ≤ R.bigTime := hy.trans r.before_big
  have hb' : y ≤ R.bigTime + r.widthU := by linarith [r.widthU_pos]
  have hR : z.1 ≤ N.endpoint * Real.exp r.refTime :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hy) N.endpoint_pos.le
  have hf : P.f z = activatedAngular r.actTime r.kappa L (y, η) :=
    (r.initial_fields hη hR).1.trans
      (StressActivation.FromReference.f_logPullback N r.actTime_pos r.refTime_pos r.refTime_bound
          r.kappa y hη)
  have hE : P.E z = velocity N.endpoint (activatedAngular r.actTime r.kappa L) (y, η) := by
    change Real.sqrt (2 * z.1) * P.f z = _
    rw [hf]
    rfl
  have hL := StressActivation.FromReference.refLog_smooth N r.refTime_pos r.refTime_bound
  have hU := StressActivation.FromReference.refAxial_smooth N r.refTime_pos r.refTime_bound
  constructor
  · change ActivationContinuation.shearA P z = _
    calc
      _ = -2 * (z.1 * radialPartial P.f z / P.f z) := by unfold ActivationContinuation.shearA; ring
      _ = -2 * TransitionRamp.baseSlope r.actTime r.kappa R.angularStock (y, η) := by
        rw [hd.1, TransitionRamp.angularSlope_before r.widthA_pos R.angularStock hb']
      _ = damping r.actTime r.kappa y * referenceP1 L (y, η) := by
        unfold TransitionRamp.baseSlope
        rw [hs.1]
        unfold referenceP1
        ring
      _ = _ := (actualP1_eq r.actTime r.kappa ReferencePath.parameterInterval_open hL y hη).symm
  · change ActivationContinuation.shearB P z = _
    calc
      _ = -2 * (z.1 * radialPartial P.U z) / P.E z := by unfold ActivationContinuation.shearB; ring
      _ = -2 * TransitionRamp.baseSlope r.actTime r.kappa R.axialStock (y, η) /
          velocity N.endpoint (activatedAngular r.actTime r.kappa L) (y, η) := by
        rw [hd.2, TransitionRamp.axialSlope_before r.widthU_pos R.axialStock hb, hE]
      _ = -2 * (damping r.actTime r.kappa y * radialPartial U (y, η)) /
          velocity N.endpoint (activatedAngular r.actTime r.kappa L) (y, η) := by
        unfold TransitionRamp.baseSlope
        rw [hs.2]
        ring
      _ = _ := by
        unfold actualP2
        rw [(controlled_hasDerivAt r.actTime r.kappa ReferencePath.parameterInterval_open hU y
            hη).deriv]

/-- Positivity from this same constructed entrance profile. -/
theorem referenceP1_positive_initial {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
    (E : NaturalEntrance.EntranceProfile d Λ C) {hΛ : 0 < Λ}
    {hsmall : NaturalAxisData.SmallParameters h j} {hP0 : ContDiff ℝ ∞ P0}
    (r : ActivationContinuation.RampParameters E.profile.family hΛ hsmall hP0)
    {y η : ℝ} (hy : y ≤ r.refTime) (hη : η ∈ Icc (-1 : ℝ) 1) :
    0 < referenceP1 (StressActivation.FromReference.refLog
      (ReferencePath.Input.ofNatural hΛ E.profile.family) r.refTime) (y, η) := by
  let N := ReferencePath.Input.ofNatural hΛ E.profile.family
  rw [ActivationCone.referenceP1_natural N r.refTime_pos r.refTime_bound hy
      (original_interval_interior hη)]
  apply E.slope_positive
  · change (Λ * (N.fromLog (y, η)).1, η) ∈ NaturalEntrance.entranceSet
    have hyT : y < ReferencePath.rampLimit := by linarith [r.refTime_pos, r.refTime_bound]
    have he : Real.exp y < 41 / 40 := by
      simpa only [ReferencePath.rampLimit, Real.exp_log (by norm_num : (0 : ℝ) < 41 / 40)]
        using Real.exp_lt_exp.mpr hyT
    have hid : Λ * (N.fromLog (y, η)).1 = 4 * Real.exp y := N.fromLog_scaled (y, η)
    exact ⟨⟨by rw [hid]; positivity, by rw [hid]; linarith⟩, hη⟩
  · exact mul_pos N.endpoint_pos (Real.exp_pos y)

theorem shearSize_eq_initial (a b : ℝ) (ha : a ≠ 0) :
    ActivationContinuation.shearSize a b = a + b ^ 2 / a := by
  unfold ActivationContinuation.shearSize
  field_simp

theorem projection_eq_initial (h X0 T κ : ℝ) (I : HistoryRow → ℝ → ℝ)
    (L U : ProfileHistories.Field) (p : Point) :
    ActivationContinuation.projection (ActivationCone.activatedStockOne h X0 I L U T κ p)
      (ActivationCone.activatedStockTwo h X0 I L U T κ p)
      (actualP1 T κ L p) (actualP2 T κ X0 L U p) =
        ActivationCone.activatedProjection h X0 I L U T κ p := rfl

theorem transverse_eq_initial (h X0 T κ : ℝ) (I : HistoryRow → ℝ → ℝ)
    (L U : ProfileHistories.Field) (p : Point) :
    ActivationContinuation.transverse (ActivationCone.activatedStockOne h X0 I L U T κ p)
      (ActivationCone.activatedStockTwo h X0 I L U T κ p)
      (actualP1 T κ L p) (actualP2 T κ X0 L U p) =
        ActivationCone.activatedCross h X0 I L U T κ p := rfl

/-- The actual ACT histories of the same continuation witness give the
logarithmic stock coordinates in its initial activation certificate. -/
theorem physical_initial_stocks {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (E : NaturalEntrance.EntranceProfile d Λ C)
    {hΛ : 0 < Λ} {hsmall : NaturalAxisData.SmallParameters h j}
    {hP0 : ContDiff ℝ ∞ P0}
    (r : ActivationContinuation.RampParameters E.profile.family hΛ hsmall hP0)
    {y η : ℝ} (hy : y ≤ r.refTime) (hη : η ∈ ReferencePath.parameterInterval) :
    let N := ReferencePath.Input.ofNatural hΛ E.profile.family
    let L := StressActivation.FromReference.refLog N r.refTime
    let U := StressActivation.FromReference.refAxial N r.refTime
    let I := ActivationStocks.FromReference.initial N r.refTime_pos r.refTime_bound P0 hP0
    let z : Point := (radius N.endpoint y, η)
    ReferenceBounds.p1 r.profiles h z =
      ActivationCone.activatedStockOne h N.endpoint I L U r.actTime r.kappa (y, η) ∧
    ReferenceBounds.p2 r.profiles h z =
      ActivationCone.activatedStockTwo h N.endpoint I L U r.actTime r.kappa (y, η) := by
  let N := ReferencePath.Input.ofNatural hΛ E.profile.family
  let z : Point := (radius N.endpoint y, η)
  let Q := StressActivation.FromReference.histories N r.actTime_pos r.refTime_pos
    r.refTime_bound r.kappa P0 hP0
  have hz : z ∈ N.radialDomain.carrier := StressActivation.FromReference.log_radius_mem N y hη
  have hX : 0 < z.1 := mul_pos N.endpoint_pos (Real.exp_pos y)
  have hR : z.1 ≤ N.endpoint * Real.exp r.refTime :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hy) N.endpoint_pos.le
  have hf : Q.f z ≠ 0 :=
    (StressActivation.FromReference.f_pos N r.actTime r.kappa r.refTime hz hX.le).ne'
  have hc := NominalConeAssembly.coordinates_of_prefix r.profiles Q h
    ReferencePath.parameterInterval_open (R := N.endpoint * Real.exp r.refTime) rfl
    (fun p hp hpR => (r.initial_fields hp hpR).1)
    (fun p hp hpR => (r.initial_fields hp hpR).2)
    (p := z) hz hz hX hR hη hf
  have h1 := ActivationStocks.FromReference.actual_stockOne_logView N r.actTime_pos
    r.refTime_pos r.refTime_bound r.kappa h P0 hP0 y hη
  have h2 := ActivationStocks.FromReference.actual_stockTwo_logView N r.actTime_pos
    r.refTime_pos r.refTime_bound r.kappa h P0 hP0 y hη
  refine ⟨hc.2.2.1.trans ?_, hc.2.2.2.trans ?_⟩
  · exact (NominalConeAssembly.p1_eq_stock Q h z).trans h1
  · exact (NominalConeAssembly.p2_eq_stock Q h z).trans h2

theorem activation_cone {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (E : NaturalEntrance.EntranceProfile d Λ C)
    {hΛ : 0 < Λ} {hsmall : NaturalAxisData.SmallParameters h j}
    {hP0 : ContDiff ℝ ∞ P0} {order : ℕ} {eps : ℝ}
    (w : ActivationContinuation.ContinuationWitness E hΛ hsmall hP0 order eps) :
    let N := ReferencePath.Input.ofNatural hΛ E.profile.family
    (∀ y eta : ℝ, 0 < y → y ≤ w.parameters.actTime → eta ∈ Icc (-1 : ℝ) 1 →
      ActivationContinuation.IsRelaxed w.parameters.profiles h (radius N.endpoint y, eta)) ∧
    ∃ t : ℝ, 0 < t ∧ t ≤ w.parameters.actTime ∧
      ∀ y eta : ℝ, 0 < y → y ≤ t → eta ∈ Icc (-1 : ℝ) 1 →
        IsTrue w.parameters.profiles h (radius N.endpoint y, eta) := by
  let r := w.parameters
  let N := ReferencePath.Input.ofNatural hΛ E.profile.family
  let L := StressActivation.FromReference.refLog N r.refTime
  let U := StressActivation.FromReference.refAxial N r.refTime
  let I := ActivationStocks.FromReference.initial N r.refTime_pos r.refTime_bound P0 hP0
  obtain ⟨theta, htheta, htheta1, hcert⟩ := w.initial_activation
  have hpositive (y eta : ℝ) (hy : y ≤ r.actTime) (heta : eta ∈ Icc (-1 : ℝ) 1) :
      0 < actualP1 r.actTime r.kappa L (y, eta) := by
    exact actualP1_pos r.actTime ⟨r.kappa_pos, r.kappa_lt_one.le⟩
      ReferencePath.parameterInterval_open
      (StressActivation.FromReference.refLog_smooth N r.refTime_pos r.refTime_bound) y
      (original_interval_interior heta) (referenceP1_positive_initial E r (hy.trans r.actTime_le)
          heta)
  have hsize (y eta : ℝ) (hy : y ≤ r.actTime) (heta : eta ∈ Icc (-1 : ℝ) 1) :
      ActivationContinuation.shearSize
        (ActivationContinuation.shearA r.profiles (radius N.endpoint y, eta))
        (ActivationContinuation.shearB r.profiles (radius N.endpoint y, eta)) =
          StressActivation.shearSize r.actTime r.kappa N.endpoint L U (y, eta) := by
    have hs := physical_initial_shears E r (hy.trans r.actTime_le) (original_interval_interior heta)
    rw [hs.1, hs.2, shearSize_eq_initial _ _ (hpositive y eta hy heta).ne']
    rfl
  have hproj (y eta : ℝ) (hy : y ≤ r.actTime) (heta : eta ∈ Icc (-1 : ℝ) 1) :
      ActivationContinuation.projection
        (ReferenceBounds.p1 r.profiles h (radius N.endpoint y, eta))
        (ReferenceBounds.p2 r.profiles h (radius N.endpoint y, eta))
        (ActivationContinuation.shearA r.profiles (radius N.endpoint y, eta))
        (ActivationContinuation.shearB r.profiles (radius N.endpoint y, eta)) =
          ActivationCone.activatedProjection h N.endpoint I L U r.actTime r.kappa (y, eta) := by
    have hs := physical_initial_shears E r (hy.trans r.actTime_le) (original_interval_interior heta)
    have hp := physical_initial_stocks E r (hy.trans r.actTime_le) (original_interval_interior heta)
    rw [hs.1, hs.2, hp.1, hp.2]
    rfl
  have hcross (y eta : ℝ) (hy : y ≤ r.actTime) (heta : eta ∈ Icc (-1 : ℝ) 1) :
      ActivationContinuation.transverse
        (ReferenceBounds.p1 r.profiles h (radius N.endpoint y, eta))
        (ReferenceBounds.p2 r.profiles h (radius N.endpoint y, eta))
        (ActivationContinuation.shearA r.profiles (radius N.endpoint y, eta))
        (ActivationContinuation.shearB r.profiles (radius N.endpoint y, eta)) =
          ActivationCone.activatedCross h N.endpoint I L U r.actTime r.kappa (y, eta) := by
    have hs := physical_initial_shears E r (hy.trans r.actTime_le) (original_interval_interior heta)
    have hp := physical_initial_stocks E r (hy.trans r.actTime_le) (original_interval_interior heta)
    rw [hs.1, hs.2, hp.1, hp.2]
    rfl
  have hrelaxed (y eta : ℝ) (hy0 : 0 < y) (hy : y ≤ r.actTime) (heta : eta ∈ Icc (-1 : ℝ) 1) :
      ActivationContinuation.IsRelaxed r.profiles h (radius N.endpoint y, eta) := by
    have hc := hcert y ⟨hy0, hy⟩ eta heta
    have hs := physical_initial_shears E r (hy.trans r.actTime_le) (original_interval_interior heta)
    refine ⟨?_, ?_, ?_⟩
    · rw [hs.1]
      exact hpositive y eta hy heta
    · rw [hproj y eta hy heta]
      exact lt_trans (by norm_num : (2 : ℝ) < 2 + 1 / 32) hc.2.1
    · rw [hsize y eta hy heta, hproj y eta hy heta, hcross y eta hy heta]
      exact hc.2.2.2.1
  refine ⟨hrelaxed, theta * r.actTime, mul_pos htheta r.actTime_pos, ?_, ?_⟩
  · nlinarith [r.actTime_pos]
  · intro y eta hy0 hy heta
    have hyT : y ≤ r.actTime := hy.trans (by nlinarith [r.actTime_pos])
    refine ⟨hrelaxed y eta hy0 hyT heta, ?_⟩
    rw [hsize y eta hyT heta]
    exact lt_trans (by norm_num : (2 : ℝ) < 2 + 1 / 16) ((hcert y ⟨hy0, hyT⟩ eta heta).2.2.2.2 hy)

end Initial

/-! ## The active annulus and one common ordered choice -/

/-- Active left, given by `4 / W.axis.scale`. -/
noncomputable def activeLeft {F : Profile} (W : NominalProfile.Witness F) : ℝ := 4 / W.axis.scale

/-- Active right, given by `W.controls.radius * Real.exp (OutgoingTail.tailEnd F.data)`. -/
noncomputable def activeRight {F : Profile} (W : NominalProfile.Witness F) : ℝ :=
  W.controls.radius * Real.exp (OutgoingTail.tailEnd F.data)

theorem activeLeft_pos {F : Profile} (W : NominalProfile.Witness F) : 0 < activeLeft W :=
  div_pos (by norm_num) W.axis.scale_pos

theorem activeLeft_lt_Xi {F : Profile} (W : NominalProfile.Witness F) :
    activeLeft W < NominalProfile.Xi := by
  have he := Real.one_lt_exp_iff.mpr W.controls.referenceWidth_pos
  have hmul : activeLeft W < activeLeft W * Real.exp W.controls.referenceWidth := by
    nlinarith [activeLeft_pos W]
  exact hmul.trans_le W.controls.activation_collar_le_Xi

theorem chart_log {R : ℝ} (hR : 0 < R) {p : Point} (hp : 0 < p.1) :
    chart R (Real.log (p.1 / R), p.2) = p := by
  apply Prod.ext
  · dsimp only [chart]
    rw [Real.exp_log (div_pos hp hR), mul_div_cancel₀ _ hR.ne']
  · rfl

theorem log_chart_lt {R X y : ℝ} (hR : 0 < R) (hX : 0 < X)
    (hy : X < R * Real.exp y) : Real.log (X / R) < y := by
  have hh : X / R < Real.exp y := (div_lt_iff₀ hR).mpr (by simpa only [mul_comm] using hy)
  simpa only [Real.log_exp] using Real.log_lt_log (div_pos hX hR) hh

theorem lt_log_chart {R X y : ℝ} (hR : 0 < R)
    (hy : R * Real.exp y < X) : y < Real.log (X / R) := by
  have hh : Real.exp y < X / R := (lt_div_iff₀ hR).mpr (by simpa only [mul_comm] using hy)
  simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos y) hh

/-- Every assertion concerns the same physical fields and absolute
histories. The extra lower speed condition is asserted only on the two
regions where the pre-modulation construction proves it. -/
structure Certificate {F : Profile} (W : NominalProfile.Witness F) : Prop where
  relaxed : ∀ p : Point, activeLeft W < p.1 → p.1 < activeRight W →
    p.2 ∈ HeatedOutgoing.parameterDomain → ActivationContinuation.IsRelaxed W.profiles F.data.h p
  initial : ∃ t : ℝ, 0 < t ∧ t ≤ W.controls.activationTime ∧
    ∀ y eta : ℝ, 0 < y → y ≤ t → eta ∈ HeatedOutgoing.parameterDomain →
      IsTrue W.profiles F.data.h (chart (activeLeft W) (y, eta))
  outgoing : ∀ y eta : ℝ, F.data.core.holdStart ≤ y → y < OutgoingTail.tailEnd F.data →
    eta ∈ HeatedOutgoing.parameterDomain → IsTrue W.profiles F.data.h (chart W.controls.radius (y,
        eta))

theorem Certificate.coordinates_smoothAt {F : Profile} {W : NominalProfile.Witness F}
    (hW : Certificate W) {p : Point} (hl : activeLeft W < p.1) (hr : p.1 < activeRight W)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    ContDiffAt ℝ ∞ (ActivationContinuation.shearA W.profiles) p ∧
      ContDiffAt ℝ ∞ (tilt W.profiles) p ∧
      ContDiffAt ℝ ∞ (ReferenceBounds.p1 W.profiles F.data.h) p ∧
      ContDiffAt ℝ ∞ (ReferenceBounds.p2 W.profiles F.data.h) p := by
  have hx := (activeLeft_pos W).trans hl
  exact cone_coordinates_smoothAt W.profiles F.data.h (W.domain_contains hx.le heta) hx
    (Witness.f_positive W hx heta).ne' (hW.relaxed p hl hr heta).first_positive.ne'
    (NaturalAxisData.L_pos W.axis.small heta).ne'

/-- Intermediate data retain the actual continuation and its repair
coefficients. The existence theorem below constructs every cone field in
this record from the already proved estimates. -/
structure Assembly (d : PreparedOutgoing.PreparedProfile) where
  /-- Family of `Assembly`, of type `CompensatedFamily d.profile`. -/
  family : CompensatedFamily d.profile
  /-- Delta of `Assembly`, of type `ℝ`. -/
  delta : ℝ
  /-- Radius floor of `Assembly`, of type `ℝ`. -/
  radiusFloor : ℝ
  /-- Matching of `Assembly`, of type `MatchingConeBounds.PreparedWitness d.profile 1 delta
  radiusFloor`. -/
  matching : MatchingConeBounds.PreparedWitness d.profile 1 delta radiusFloor
  family_floor : family.radiusFloor ≤ radiusFloor
  terminal_floor : TerminalCone.radiusThreshold d.profile ≤ matching.controls.radius
  clean : OutgoingCone.ProfileCleanCone d.profile matching.controls.radius (-5)
  repair : ∀ p : Point,
    p.1 ∈ Icc (matching.controls.radius * Real.exp (-8)) (matching.controls.radius * Real.exp (-5))
        →
    p.2 ∈ HeatedOutgoing.parameterDomain →
    ActivationContinuation.IsRelaxed
      (matching.controls.profiles matching.bounds.matching.separation.le) d.profile.data.h p

namespace Assembly

variable {d : PreparedOutgoing.PreparedProfile} (A : Assembly d)

/-- Witness, given by `A.family.assemblePrepared d.specification A.matching A.family_floor`. -/
noncomputable def witness : NominalProfile.Witness d.profile :=
  A.family.assemblePrepared d.specification A.matching A.family_floor

theorem outgoing {y eta : ℝ} (hy : d.profile.data.core.holdStart ≤ y)
    (hend : y < OutgoingTail.tailEnd d.profile.data) (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    IsTrue A.witness.profiles d.profile.data.h (chart A.witness.controls.radius (y, eta)) :=
  A.family.assemble_profile_true_late d.specification A.matching.axis A.matching.controls
    (A.family_floor.trans A.matching.bounds.radius_large) A.matching.bounds.matching.separation.le
    _ d.terminal A.terminal_floor hy hend heta

theorem outer_relaxed {p : Point} (hXi : NominalProfile.Xi ≤ p.1)
    (hend : p.1 < activeRight A.witness) (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    ActivationContinuation.IsRelaxed A.witness.profiles d.profile.data.h p := by
  have hx := NominalProfile.Xi_pos.trans_le hXi
  by_cases hshape : p.1 ≤ A.matching.controls.radius * Real.exp (-8)
  · exact A.family.prepared_shape_relaxed d.specification A.matching A.family_floor hXi hshape heta
  by_cases hrepair : p.1 ≤ A.matching.controls.radius * Real.exp (-5)
  · exact Witness.prefix_relaxed A.witness hx hrepair heta
      (A.repair p ⟨(lt_of_not_ge hshape).le, hrepair⟩ heta)
  have hlo := lt_log_chart A.matching.controls.radius_pos (lt_of_not_ge hrepair)
  have hhi := log_chart_lt A.matching.controls.radius_pos hx hend
  have hc := A.family.assemble_profile_relaxed_outer d.specification A.matching.axis
      A.matching.controls
    (A.family_floor.trans A.matching.bounds.radius_large) A.matching.bounds.matching.separation.le
    (fun _eta hη => A.matching.bounds.matching.smallDebt A.matching.bounds.debt_radius hη)
    d.terminal A.terminal_floor A.clean (p := (Real.log (p.1 / A.matching.controls.radius), p.2))
        hlo hhi heta
  rwa [chart_log A.matching.controls.radius_pos hx] at hc

theorem initial_cones :
    (∀ y eta : ℝ, 0 < y → y ≤ A.witness.controls.activationTime →
      eta ∈ HeatedOutgoing.parameterDomain →
      ActivationContinuation.IsRelaxed A.witness.profiles d.profile.data.h
        (chart (activeLeft A.witness) (y, eta))) ∧
    ∃ t : ℝ, 0 < t ∧ t ≤ A.witness.controls.activationTime ∧
      ∀ y eta : ℝ, 0 < y → y ≤ t → eta ∈ HeatedOutgoing.parameterDomain →
        IsTrue A.witness.profiles d.profile.data.h (chart (activeLeft A.witness) (y, eta)) := by
  have hb := Initial.activation_cone A.matching.axis.natural A.matching.continuation
  have hXi (y eta : ℝ) (hy : y ≤ A.witness.controls.activationTime) :
      (chart (activeLeft A.witness) (y, eta)).1 ≤ NominalProfile.Xi := by
    exact (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (hy.trans A.witness.controls.activationTime_le))
      (activeLeft_pos A.witness).le).trans A.witness.controls.activation_collar_le_Xi
  constructor
  · intro y eta hy0 hy heta
    exact Witness.seed_relaxed A.witness (chart_positive (activeLeft_pos A.witness) (y, eta))
      (hXi y eta hy) heta (hb.1 y eta hy0 hy heta)
  · obtain ⟨t, ht, htT, htrue⟩ := hb.2
    refine ⟨t, ht, htT, ?_⟩
    intro y eta hy0 hy heta
    exact Witness.seed_true A.witness (chart_positive (activeLeft_pos A.witness) (y, eta))
      (hXi y eta (hy.trans htT)) heta (htrue y eta hy0 hy heta)

/-- The nominal profile has the relaxed cone throughout its active
annulus and the true cone in its initial collar and from the shaped hold
through the terminal region. Every component uses the stored witness. -/
theorem certificate : Certificate A.witness := by
  have hi := A.initial_cones
  refine ⟨?_, hi.2, ?_⟩
  · intro p hl hr heta
    have hx := (activeLeft_pos A.witness).trans hl
    by_cases hXi : p.1 ≤ NominalProfile.Xi
    · have hy0 : 0 < Real.log (p.1 / activeLeft A.witness) := by
        apply lt_log_chart (activeLeft_pos A.witness)
        simpa only [Real.exp_zero, mul_one] using hl
      by_cases hy : Real.log (p.1 / activeLeft A.witness) ≤ A.witness.controls.activationTime
      · have hc := hi.1 (Real.log (p.1 / activeLeft A.witness)) p.2 hy0 hy heta
        rwa [chart_log (activeLeft_pos A.witness) hx] at hc
      · have hstart : A.matching.continuation.parameters.startRadius ≤ p.1 := by
          change activeLeft A.witness * Real.exp A.witness.controls.activationTime ≤ p.1
          by_contra hn
          exact hy (log_chart_lt (activeLeft_pos A.witness) hx (lt_of_not_ge hn)).le
        exact A.family.prepared_continuation_relaxed d.specification A.matching A.family_floor
          heta ⟨hstart, hXi⟩
    · exact A.outer_relaxed (le_of_not_ge hXi) hr heta
  · intro y eta hy hend heta
    exact A.outgoing hy hend heta

end Assembly

theorem assembly_exists (d : PreparedOutgoing.PreparedProfile) : Nonempty (Assembly d) := by
  obtain ⟨cleanFloor, hcleanFloor, hclean⟩ := d.clean (-5) (by norm_num)
  have hanchor : 0 < cleanFloor + 1 := by linarith
  obtain ⟨G⟩ := exists_compensatedFamily d.profile (hclean (cleanFloor + 1) (by linarith)) hanchor
  obtain ⟨delta, repairFloor, hdelta, _hrepairFloor, hrepair⟩ :=
      RepairConeBounds.exists_repair_cone d.profile
  let floor := max G.radiusFloor (max (cleanFloor + 1) (max repairFloor
      (TerminalCone.radiusThreshold d.profile)))
  obtain ⟨M⟩ := MatchingConeBounds.preparedWitness_exists d.profile d.amplitude_lower d.height_upper
    1 le_rfl hdelta floor
  have hG : G.radiusFloor ≤ floor := le_max_left _ _
  have hC : cleanFloor + 1 ≤ floor := (le_max_left _ _).trans (le_max_right _ _)
  have hR : repairFloor ≤ floor := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hT : TerminalCone.radiusThreshold d.profile ≤ floor := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hendpoint : JetBounds.FiniteJetBound 1 (RepairConeBounds.endpointError M.controls)
      (Icc (-1 : ℝ) 1) delta := by
    intro n hn eta heta
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact M.bounds.endpoint eta heta n hn
  refine ⟨⟨G, delta, floor, M, hG, hT.trans M.bounds.radius_large,
    hclean M.controls.radius ?_, ?_⟩⟩
  · have hh := hC.trans M.bounds.radius_large
    exact lt_of_lt_of_le (by linarith : cleanFloor < cleanFloor + 1) hh
  · intro p hp heta
    exact hrepair M.axis M.controls M.bounds.matching.separation.le hendpoint M.bounds.coefficients
      (hR.trans M.bounds.radius_large) p hp heta (M.bounds.matching.smallDebt M.bounds.debt_radius
          heta)

/-- Any one prepared outgoing profile has a nominal witness with the
complete actual cone certificate. No cone or matching-debt assumption is
added to the prepared profile. -/
theorem exists_certificate (d : PreparedOutgoing.PreparedProfile) :
    ∃ W : NominalProfile.Witness d.profile, Certificate W := by
  obtain ⟨A⟩ := assembly_exists d
  exact ⟨A.witness, A.certificate⟩

theorem exists_nominal_cone :
    ∃ (F : Profile) (W : NominalProfile.Witness F), Certificate W := by
  obtain ⟨d⟩ := PreparedOutgoing.exists_prepared
  obtain ⟨W, hW⟩ := exists_certificate d
  exact ⟨d.profile, W, hW⟩

end NavierStokes.NominalConeAssembly
