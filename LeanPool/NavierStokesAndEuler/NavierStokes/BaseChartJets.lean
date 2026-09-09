/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ConstructedSlowBase
public import LeanPool.NavierStokesAndEuler.NavierStokes.PositiveRepresentatives
public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryPulseBounds
import LeanPool.NavierStokesAndEuler.NavierStokes.BasePhaseGeometry
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Actual summed base fields in normalized band charts

All coordinate derivatives are taken at strictly positive backward time.
The constants remain uniform as that time approaches zero while the
normalized positive branch stays in a fixed annulus.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.BaseChartJets

open Set Filter Function PhaseJetBounds PrimaryPulseBounds
open scoped Topology ContDiff BigOperators

/-- Slow: an abbreviation for `PhaseCalculus.Slow`. -/
abbrev Slow := PhaseCalculus.Slow
/-- Chart: an abbreviation for `SlowBorelBase.Chart`. -/
abbrev Chart := SlowBorelBase.Chart
/-- Inner: an abbreviation for `SlowBorelBase.Inner`. -/
abbrev Inner := SlowBorelBase.Inner

/-- One domain, bundling `scale`, `carrier`, `isOpen`, `one_le_scale`. -/
noncomputable def oneDomain (ι : Type*) {E : Type*} [NormedAddCommGroup E]
    (U : ι → Set E) (hU : ∀ i, IsOpen (U i)) : Domain ι E where
  scale _ := 1
  carrier := U
  isOpen := hU
  one_le_scale _ := le_rfl

theorem uniform_polynomial {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : ι → Set E} (hU : ∀ i, IsOpen (U i)) {f : ι → E → F}
    (hs : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    (hb : ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ i x, x ∈ U i → ‖iteratedFDeriv ℝ j (f i) x‖ ≤ C) :
    PolynomialJets (oneDomain ι U hU) f := by
  classical
  choose C hC hbound using hb
  refine ⟨hs, fun N => ⟨1 + ∑ j ∈ Finset.range (N + 1), C j, ?_, 0, ?_⟩⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => (hC j).le))
  · intro i j hj x hx
    have hsum := Finset.single_le_sum (fun k _ => (hC k).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    simpa only [oneDomain, pow_zero, mul_one] using (hbound j i x hx).trans (by linarith)

theorem uniform_envelope {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : ι → Set E} (hU : ∀ i, IsOpen (U i)) {f : ι → E → F} {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hs : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    (hb : ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ i x, x ∈ U i →
      ‖iteratedFDeriv ℝ j (f i) x‖ ≤ C * w i) :
    EnvelopeJets (oneDomain ι U hU) (fun i _ => w i) f := by
  classical
  choose C hC hbound using hb
  refine ⟨fun i _ _ => hw i, hs, fun N => ⟨1 + ∑ j ∈ Finset.range (N + 1), C j, ?_, 0, ?_⟩⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => (hC j).le))
  · intro i x hx j hj
    have hsum := Finset.single_le_sum (fun k _ => (hC k).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    simpa only [oneDomain, pow_zero, mul_one] using (hbound j i x hx).trans
      (mul_le_mul_of_nonneg_right (by linarith) (hw i))

/-- Sum region, given by `Ioi 0 ×ˢ (Ioi 0 ×ˢ univ)`. -/
noncomputable def sumRegion : Set Chart := Ioi 0 ×ˢ (Ioi 0 ×ˢ univ)

theorem sumRegion_open : IsOpen sumRegion := isOpen_Ioi.prod (isOpen_Ioi.prod isOpen_univ)

theorem scaleMap_norm_le {c M : ℝ} (hM : 1 ≤ M) (hc : |c| ≤ M) :
    ‖SlowBorelBase.scaleMap c‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans hM)
  intro x
  change max ‖c * x.1‖ ‖x.2‖ ≤ M * ‖x‖
  rw [norm_mul, Real.norm_eq_abs]
  exact max_le (mul_le_mul hc (norm_fst_le x) (norm_nonneg _) (zero_le_one.trans hM))
    ((norm_snd_le x).trans (le_mul_of_one_le_left (norm_nonneg x) hM))

/-- Recenter the frozen q-rescaling at the actual point `q=Q*rho`.
Only the bounded inverse of `rho`, not `Q⁻¹`, appears in this estimate. -/
theorem scaled_jet_from_blown {f : Chart → ℝ}
    (hf : ContDiffOn ℝ ∞ f sumRegion) {Q rho M : ℝ} {w : Inner}
    (hQ : 0 < Q) (hrho : 0 < rho) (hw : 0 < w.1)
    (hM : 1 ≤ M) (hi : 1 / rho ≤ M) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (f ∘ SlowBorelBase.scaleMap Q) (rho, w)‖ ≤
      ‖SlowBorelBase.blownJet j f (Q * rho, w)‖ * M ^ j := by
  have hs : ContDiffOn ℝ ∞ (f ∘ SlowBorelBase.scaleMap (Q * rho)) sumRegion :=
    hf.comp (SlowBorelBase.scaleMap (Q * rho)).contDiff.contDiffOn
      (fun y hy => ⟨mul_pos (mul_pos hQ hrho) hy.1, hy.2⟩)
  have heq : f ∘ SlowBorelBase.scaleMap Q =
      (f ∘ SlowBorelBase.scaleMap (Q * rho)) ∘ SlowBorelBase.scaleMap rho⁻¹ := by
    funext y
    change f (Q * y.1, y.2) = f (Q * rho * (rho⁻¹ * y.1), y.2)
    congr 1
    apply Prod.ext
    · change Q * y.1 = Q * rho * (rho⁻¹ * y.1)
      field_simp
    · rfl
  have hx : SlowBorelBase.scaleMap rho⁻¹ (rho, w) ∈ sumRegion := by
    have hw' : ((1 : ℝ), w) ∈ sumRegion := ⟨by norm_num, hw, mem_univ _⟩
    simpa only [SlowBorelBase.scaleMap_apply, inv_mul_cancel₀ hrho.ne'] using
      hw'
  have hb := norm_jet_comp_linear sumRegion_open hs (SlowBorelBase.scaleMap rho⁻¹) hx j
  have hnorm : ‖SlowBorelBase.scaleMap rho⁻¹‖ ≤ M :=
    scaleMap_norm_le hM (by simpa only [abs_of_pos (inv_pos.mpr hrho), one_div] using hi)
  rw [← heq] at hb
  apply hb.trans
  have hpoint : SlowBorelBase.scaleMap rho⁻¹ (rho, w) = (1, w) := by
    simp only [SlowBorelBase.scaleMap_apply, inv_mul_cancel₀ hrho.ne']
  rw [hpoint]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm j) (norm_nonneg _)

/-- Inner region, given by `Ioo qlo qhi ×ˢ (Ioo lo hi ×ˢ Ioo (-1) 1)`. -/
noncomputable def innerRegion (qlo qhi lo hi : ℝ) : Set Chart :=
  Ioo qlo qhi ×ˢ (Ioo lo hi ×ˢ Ioo (-1) 1)

theorem innerRegion_open (qlo qhi lo hi : ℝ) : IsOpen (innerRegion qlo qhi lo hi) :=
  isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_Ioo)

theorem normalized_error_envelope {ι : Type*} {h qlo qhi lo hi : ℝ}
    (hh : 0 < h) (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hsmall : ∀ i, Q i * qhi ≤ 1)
    (f : Chart → ℝ) (hf : ContDiffOn ℝ ∞ f sumRegion)
    (hb : ∀ j : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ q : ℝ, 0 < q → q ≤ 1 →
      ∀ w ∈ SlowBorelBase.innerBox lo hi,
        ‖SlowBorelBase.blownJet j f (q, w)‖ ≤ B * q ^ (2 * h)) :
    EnvelopeJets (oneDomain ι (fun _ => innerRegion qlo qhi lo hi)
      (fun _ => innerRegion_open _ _ _ _)) (fun i _ => Q i ^ (2 * h))
      (fun i => f ∘ SlowBorelBase.scaleMap (Q i)) := by
  apply uniform_envelope _ (fun i => (Real.rpow_pos_of_pos (hQ i) _).le)
  · intro i
    apply hf.comp (SlowBorelBase.scaleMap (Q i)).contDiff.contDiffOn
    intro y hy
    exact ⟨mul_pos (hQ i) (hqlo.trans hy.1.1), hlo.trans hy.2.1.1, mem_univ _⟩
  · intro j
    obtain ⟨B, hB, hb⟩ := hb j
    let K := max 1 (1 / qlo)
    have hK : 1 ≤ K := le_max_left _ _
    refine ⟨B * qhi ^ (2 * h) * K ^ j, by positivity, ?_⟩
    intro i y hy
    have hrho : 0 < y.1 := hqlo.trans hy.1.1
    have hinv : 1 / y.1 ≤ K :=
      (one_div_le_one_div_of_le hqlo hy.1.1.le).trans (le_max_right _ _)
    have hscaled := scaled_jet_from_blown hf (hQ i) hrho (hlo.trans hy.2.1.1) hK hinv j
    have hw : y.2 ∈ SlowBorelBase.innerBox lo hi :=
      ⟨⟨hy.2.1.1.le, hy.2.1.2.le⟩, hy.2.2.1.le, hy.2.2.2.le⟩
    have hs : Q i * y.1 ≤ 1 :=
      (mul_le_mul_of_nonneg_left hy.1.2.le (hQ i).le).trans (hsmall i)
    have hr : y.1 ^ (2 * h) ≤ qhi ^ (2 * h) :=
      Real.rpow_le_rpow hrho.le hy.1.2.le (by linarith)
    calc
      _ ≤ ‖SlowBorelBase.blownJet j f (Q i * y.1, y.2)‖ * K ^ j := hscaled
      _ ≤ (B * (Q i * y.1) ^ (2 * h)) * K ^ j :=
        mul_le_mul_of_nonneg_right (hb _ (mul_pos (hQ i) hrho) hs _ hw) (by positivity)
      _ = (B * Q i ^ (2 * h) * y.1 ^ (2 * h)) * K ^ j := by
        rw [Real.mul_rpow (hQ i).le hrho.le]
        ring
      _ ≤ (B * Q i ^ (2 * h) * qhi ^ (2 * h)) * K ^ j :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hr (mul_nonneg hB.le (Real.rpow_nonneg (hQ i).le _))) (by
              positivity)
      _ = _ := by ring

/-- Swirl error, given by `SlowBorelBase.normalizedSwirl a h C d y - SlowBorelBase.leadingSwirl
C d y.2`. -/
noncomputable def swirlError (a : ℕ → ℕ) (h C : ℝ) (d : SlowBorelBase.Coefficients) (y : Chart) : ℝ
    :=
  SlowBorelBase.normalizedSwirl a h C d y - SlowBorelBase.leadingSwirl C d y.2

/-- Axial error, given by `SlowBorelBase.slowSum a h d.axial y - d.axial 0 y.2`. -/
noncomputable def axialError (a : ℕ → ℕ) (h : ℝ) (d : SlowBorelBase.Coefficients) (y : Chart) : ℝ :=
  SlowBorelBase.slowSum a h d.axial y - d.axial 0 y.2

theorem errors_smooth {a : ℕ → ℕ} (ha : StrictMono a) (h C : ℝ)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d) :
    ContDiffOn ℝ ∞ (swirlError a h C d) sumRegion ∧
    ContDiffOn ℝ ∞ (axialError a h d) sumRegion := by
  constructor
  · intro y hy
    have hX : 0 < y.2.1 := hy.2.1
    have hr : ContDiffAt ℝ ∞ (fun z : Chart => Real.sqrt (2 * z.2.1) / C) y :=
      ((contDiffAt_const.mul contDiffAt_snd.fst).sqrt (by
          positivity : (2 : ℝ) * y.2.1 ≠ 0)).div_const C
    have hs := SlowBorelBase.slowSum_smoothAt ha hd.phi h hy.1
    have h0 := (hd.phi 0).contDiffAt.comp y contDiffAt_snd
    exact ((hr.mul hs).sub (hr.mul h0)).contDiffWithinAt
  · intro y hy
    exact ((SlowBorelBase.slowSum_smoothAt ha hd.axial h hy.1).sub
      ((hd.axial 0).contDiffAt.comp y contDiffAt_snd)).contDiffWithinAt

theorem actual_error_envelopes {ι : Type*} {a : ℕ → ℕ} {h C qlo qhi lo hi : ℝ}
    (hh : 0 < h) (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    (ha : SlowBorelBase.AdmissibleScales h (SlowBorelBase.coefficientBundle C d)
      (SlowBorelBase.innerBox lo hi) a)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hsmall : ∀ i, Q i * qhi ≤ 1) :
    EnvelopeJets (oneDomain ι (fun _ => innerRegion qlo qhi lo hi)
      (fun _ => innerRegion_open _ _ _ _)) (fun i _ => Q i ^ (2 * h))
      (fun i => swirlError a h C d ∘ SlowBorelBase.scaleMap (Q i)) ∧
    EnvelopeJets (oneDomain ι (fun _ => innerRegion qlo qhi lo hi)
      (fun _ => innerRegion_open _ _ _ _)) (fun i _ => Q i ^ (2 * h))
      (fun i => axialError a h d ∘ SlowBorelBase.scaleMap (Q i)) := by
  have hs := errors_smooth ha.strictMono h C hd
  constructor
  · apply normalized_error_envelope hh hqlo hqhi hlo Q hQ hsmall _ hs.1
    intro j
    obtain ⟨B, hB, hb⟩ := SlowBorelBase.normalized_tangential_bounds hh hlo hd ha j
    exact ⟨B, hB, fun q hq hq1 w hw => (hb q hq hq1 w hw).1⟩
  · apply normalized_error_envelope hh hqlo hqhi hlo Q hQ hsmall _ hs.2
    intro j
    obtain ⟨B, hB, hb⟩ := SlowBorelBase.normalized_tangential_bounds hh hlo hd ha j
    exact ⟨B, hB, fun q hq hq1 w hw => (hb q hq hq1 w hw).2⟩

/-- Physical input, given by `(1 - p.2.2, (p.1 ^ 2 / 2, p.2.1))`. -/
noncomputable def physicalInput (p : Slow) : Chart := (1 - p.2.2, (p.1 ^ 2 / 2, p.2.1))

theorem physicalInput_smooth : ContDiff ℝ ∞ physicalInput :=
  (contDiff_const.sub contDiff_snd.snd).prodMk
    (((contDiff_fst.pow 2).div_const 2).prodMk contDiff_snd.fst)

/-- Normalized coordinates, given by `SlowBorelBase.physicalChart h (physicalInput p)`. -/
noncomputable def normalizedCoordinates (h : ℝ) (p : Slow) : Chart :=
  SlowBorelBase.physicalChart h (physicalInput p)

theorem normalizedCoordinates_eq (h : ℝ) (p : Slow) :
    normalizedCoordinates h p =
      (SimilarityHomogeneity.chartQ h p,
        (SimilarityHomogeneity.chartX h p, SimilarityHomogeneity.chartEta h p)) := by
  simp only [normalizedCoordinates, physicalInput, SlowBorelBase.physicalChart,
    PhysicalCoordinateBounds.physicalQ, PhysicalCoordinateBounds.physicalX,
    PhysicalCoordinateBounds.physicalEta, PhysicalCoordinateBounds.timeShift,
    Function.comp_apply, PhysicalCoordinateBounds.qCoord, PhysicalCoordinateBounds.xCoord,
    PhysicalCoordinateBounds.etaCoord, SimilarityHomogeneity.chartQ,
    SimilarityHomogeneity.chartX, SimilarityHomogeneity.chartEta,
    SimilarityCoordinates.coordinateX, SimilarityCoordinates.coordinateEta,
    PhysicalCoordinateBounds.D]
  congr 2 <;> ring_nf

theorem normalizedCoordinates_smoothAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : Slow} (hT : 0 < p.2.2) : ContDiffAt ℝ ∞ (normalizedCoordinates h) p :=
  (SlowBorelBase.physicalChart_smoothAt hh hh1 (show (physicalInput p).1 < 1 by
    dsimp [physicalInput]; linarith)).comp p physicalInput_smooth.contDiffAt

theorem normalizedCoordinates_q_pos {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : Slow} (hT : 0 < p.2.2) : 0 < (normalizedCoordinates h p).1 :=
  SlowBorelBase.physicalChart_positive hh hh1 (show (physicalInput p).1 < 1 by
    dsimp [physicalInput]; linarith)

theorem normalizedCoordinates_eta {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : Slow} (hT : 0 < p.2.2) : |(normalizedCoordinates h p).2.2| < 1 :=
  PhysicalCoordinateBounds.physicalEta_abs_lt_one (by linarith) (by linarith)
    (show (physicalInput p).1 < 1 by dsimp [physicalInput]; linarith)

/-- These are only pointwise geometric restrictions on the actual chart,
not coordinate-derivative or base-field estimates. -/
structure GeometryBounds {ι : Type*} (D : Domain ι Slow)
    (h r M qlo qhi lo hi : ℝ) : Prop where
  time : ∀ i p, p ∈ D.carrier i → 0 < p.2.2
  radius : ∀ i p, p ∈ D.carrier i → r ≤ p.1
  bounded : ∀ i p, p ∈ D.carrier i → ‖p‖ ≤ M
  q_range : ∀ i p, p ∈ D.carrier i →
    qlo < (normalizedCoordinates h p).1 ∧ (normalizedCoordinates h p).1 < qhi
  x_range : ∀ i p, p ∈ D.carrier i →
    lo < (normalizedCoordinates h p).2.1 ∧ (normalizedCoordinates h p).2.1 < hi

/-- Unit scale, given by `oneDomain ι D.carrier D.isOpen`. -/
noncomputable def unitScale {ι E : Type*} [NormedAddCommGroup E] (D : Domain ι E) : Domain ι E :=
  oneDomain ι D.carrier D.isOpen

private theorem iteratedFDeriv_pair {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {g : E → G} {x : E} {j : ℕ}
    (hf : ContDiffAt ℝ j f x) (hg : ContDiffAt ℝ j g x) :
    iteratedFDeriv ℝ j (fun y => (f y, g y)) x =
      (iteratedFDeriv ℝ j f x).prod (iteratedFDeriv ℝ j g x) := by
  have h1 := (ContinuousLinearMap.fst ℝ F G).iteratedFDeriv_comp_left (hf.prodMk hg) le_rfl
  have h2 := (ContinuousLinearMap.snd ℝ F G).iteratedFDeriv_comp_left (hf.prodMk hg) le_rfl
  apply ContinuousMultilinearMap.ext
  intro v
  apply Prod.ext
  · exact (congrArg (fun M => M v) h1).symm
  · exact (congrArg (fun M => M v) h2).symm

/-- The actual inverse coordinate jets are bounded for any fixed upper
q bound.  The proof uses the normalized inverse-Jacobian expressions,
which are regular at the limiting forward parameters. -/
theorem physicalChart_jet_bound {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (lo hi qhi : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Chart, p.1 < 1 →
      (SlowBorelBase.physicalChart h p).1 ≤ qhi →
      (SlowBorelBase.physicalChart h p).2.1 ∈ Icc lo hi →
      ‖iteratedFDeriv ℝ j (SlowBorelBase.physicalChart h) p‖ ≤
        C * (SlowBorelBase.physicalChart h p).1 ^ (-(j : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := PhysicalCoordinateBounds.physical_coordinate_derivative_bounds
    (show 0 < 2 * h by linarith) (show 2 * h < 1 by linarith) lo hi qhi j
  refine ⟨C, hC, fun p hp hq hX => ?_⟩
  have hj : (j : WithTop ℕ∞) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl j
  have hqj := (PhysicalCoordinateBounds.physicalQ_contDiffAt
    (show 0 < 2 * h by linarith) (show 2 * h < 1 by linarith) hp).of_le hj
  have hxj := (PhysicalCoordinateBounds.physicalX_contDiffAt
    (show 0 < 2 * h by linarith) (show 2 * h < 1 by linarith) hp).of_le hj
  have hej := (PhysicalCoordinateBounds.physicalEta_contDiffAt
    (show 0 < 2 * h by linarith) (show 2 * h < 1 by linarith) hp).of_le hj
  obtain ⟨bq, be, bx⟩ := hb p hp hq hX
  change ‖iteratedFDeriv ℝ j (fun y => (PhysicalCoordinateBounds.physicalQ (2 * h) y,
    (PhysicalCoordinateBounds.physicalX (2 * h) y, PhysicalCoordinateBounds.physicalEta (2 * h)
        y))) p‖ ≤ _
  rw [iteratedFDeriv_pair hqj (hxj.prodMk hej), iteratedFDeriv_pair hxj hej,
    ContinuousMultilinearMap.opNorm_prod, ContinuousMultilinearMap.opNorm_prod]
  exact max_le bq (max_le bx be)

/-- Uniform jets of `(rho,X,eta)` on strictly positive time.  No lower
bound on time is imposed, and no derivative at time zero is used. -/
theorem normalizedCoordinates_polynomial {ι : Type*} {D : Domain ι Slow}
    {h r M qlo qhi lo hi : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (hqlo : 0 < qlo)
    (H : GeometryBounds D h r M qlo qhi lo hi) :
    PolynomialJets (unitScale D) (fun _ => normalizedCoordinates h) := by
  apply uniform_polynomial D.isOpen
  · intro i p hp
    exact (normalizedCoordinates_smoothAt hh hh1 (H.time i p hp)).contDiffWithinAt
  · intro N
    classical
    choose C hC hb using fun j => physicalChart_jet_bound hh hh1 lo hi qhi j
    obtain ⟨B, hB, hBj⟩ := compact_jet_bound isOpen_univ physicalInput_smooth.contDiffOn
      (isCompact_closedBall (0 : Slow) M) (subset_univ _) N
    let A := 1 + ∑ j ∈ Finset.range (N + 1), C j * qlo ^ (-(j : ℝ))
    have hA : 0 < A := by
      dsimp [A]
      exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun j _ =>
        mul_nonneg (hC j).le (Real.rpow_nonneg hqlo.le _)))
    refine ⟨(N.factorial : ℝ) * A * B ^ N, by positivity, ?_⟩
    intro i p hp
    have hT := H.time i p hp
    have hphys : (physicalInput p).1 < 1 := by dsimp [physicalInput]; linarith
    have hq := normalizedCoordinates_q_pos hh hh1 hT
    have houter (j : ℕ) (hj : j ≤ N) :
        ‖iteratedFDeriv ℝ j (SlowBorelBase.physicalChart h) (physicalInput p)‖ ≤ A := by
      have hhj := hb j (physicalInput p) hphys (H.q_range i p hp).2.le
        ⟨(H.x_range i p hp).1.le, (H.x_range i p hp).2.le⟩
      have hpow : (normalizedCoordinates h p).1 ^ (-(j : ℝ)) ≤ qlo ^ (-(j : ℝ)) := by
        rw [Real.rpow_neg hq.le, Real.rpow_neg hqlo.le, Real.rpow_natCast, Real.rpow_natCast]
        exact inv_anti₀ (pow_pos hqlo j) (pow_le_pow_left₀ hqlo.le (H.q_range i p hp).1.le j)
      have hsum := Finset.single_le_sum (fun j _ =>
        mul_nonneg (hC j).le (Real.rpow_nonneg hqlo.le (-(j : ℝ))))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
      exact (hhj.trans (mul_le_mul_of_nonneg_left hpow (hC j).le)).trans (by dsimp [A]; linarith)
    let U : Set Slow := {p | 0 < p.2.2}
    let V : Set Chart := Iio 1 ×ˢ univ
    have hU : IsOpen U := isOpen_lt continuous_const continuous_snd.snd
    have hV : IsOpen V := isOpen_Iio.prod isOpen_univ
    have hF : ContDiffOn ℝ ∞ (SlowBorelBase.physicalChart h) V :=
      fun q hq => (SlowBorelBase.physicalChart_smoothAt hh hh1 hq.1).contDiffWithinAt
    have hmap : MapsTo physicalInput U V := by
      intro q hq
      have ht : 0 < q.2.2 := hq
      exact ⟨by change 1 - q.2.2 < 1; linarith, mem_univ _⟩
    have hpnorm : p ∈ Metric.closedBall (0 : Slow) M := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using H.bounded i p hp
    have hchain := norm_iteratedFDerivWithin_comp_le hF physicalInput_smooth.contDiffOn
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl N) hV.uniqueDiffOn hU.uniqueDiffOn hmap hT
      (C := A) (D := B) (fun j hj => ?_) (fun j hj1 hj => ?_)
    · simp only [iteratedFDerivWithin_of_isOpen N hU hT]
        at hchain
      exact hchain
    · rw [iteratedFDerivWithin_of_isOpen j hV (hmap hT)]
      exact houter j hj
    · rw [iteratedFDerivWithin_of_isOpen j hU hT]
      exact (hBj j hj p hpnorm).trans (by simpa only [pow_one] using pow_le_pow_right₀ hB hj1)

/-- Axial factor, given by `(normalizedCoordinates h p).1 ^ (-CoordinateAlgebra.A h)`. -/
noncomputable def axialFactor (h : ℝ) (p : Slow) : ℝ :=
  (normalizedCoordinates h p).1 ^ (-CoordinateAlgebra.A h)

/-- Frequency factor, given by `axialFactor h p / p.1`. -/
noncomputable def frequencyFactor (h : ℝ) (p : Slow) : ℝ := axialFactor h p / p.1

/-- The actual `Q^A`-normalized angular velocity divided by the normalized
radius.  The factor `1/R` is retained in the definition. -/
noncomputable def frequency (a : ℕ → ℕ) (h C : ℝ) (d : SlowBorelBase.Coefficients)
    (Q : ℝ) (p : Slow) : ℝ :=
  frequencyFactor h p * SlowBorelBase.normalizedSwirl a h C d
    (SlowBorelBase.scaleMap Q (normalizedCoordinates h p))

/-- Axial, given by `axialFactor h p * SlowBorelBase.slowSum a h d.axial (SlowBorelBase.scaleMap
Q (normalizedCoordinates h p))`. -/
noncomputable def axial (a : ℕ → ℕ) (h : ℝ) (d : SlowBorelBase.Coefficients)
    (Q : ℝ) (p : Slow) : ℝ :=
  axialFactor h p * SlowBorelBase.slowSum a h d.axial
    (SlowBorelBase.scaleMap Q (normalizedCoordinates h p))

/-- Leading frequency, given by `frequencyFactor h p * SlowBorelBase.leadingSwirl C d
(normalizedCoordinates h p).2`. -/
noncomputable def leadingFrequency (h C : ℝ) (d : SlowBorelBase.Coefficients) (p : Slow) : ℝ :=
  frequencyFactor h p * SlowBorelBase.leadingSwirl C d (normalizedCoordinates h p).2

/-- Leading axial, given by `axialFactor h p * d.axial 0 (normalizedCoordinates h p).2`. -/
noncomputable def leadingAxial (h : ℝ) (d : SlowBorelBase.Coefficients) (p : Slow) : ℝ :=
  axialFactor h p * d.axial 0 (normalizedCoordinates h p).2

theorem geometry_factors_polynomial {ι : Type*} {D : Domain ι Slow}
    {h r M qlo qhi lo hi : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hr : 0 < r) (hM : 1 ≤ M) (hqlo : 0 < qlo)
    (H : GeometryBounds D h r M qlo qhi lo hi) :
    PolynomialJets (unitScale D) (fun _ => frequencyFactor h) ∧
    PolynomialJets (unitScale D) (fun _ => axialFactor h) := by
  have hc := normalizedCoordinates_polynomial hh hh1 hqlo H
  have hq := hc.clm (ContinuousLinearMap.fst ℝ ℝ Inner)
  have hp : PolynomialJets (unitScale D) (fun _ => axialFactor h) := by
    apply hq.compact_comp isOpen_Ioi
      (show ContDiffOn ℝ ∞ (fun x : ℝ => x ^ (-CoordinateAlgebra.A h)) (Ioi 0) from
        fun x hx => (contDiffAt_id.rpow_const_of_ne hx.ne').contDiffWithinAt)
      isCompact_Icc (fun x hx => hqlo.trans_le hx.1)
    · intro i p hp
      exact ⟨(H.q_range i p hp).1.le, (H.q_range i p hp).2.le⟩
  have hR : PolynomialJets (unitScale D) (fun _ p => p.1) := by
    have hrange (i : ι) (p : Slow) (hp : p ∈ (unitScale D).carrier i) : |p.1| ≤ M := by
      simpa only [Real.norm_eq_abs] using (norm_fst_le p).trans (H.bounded i p hp)
    simpa only [ContinuousLinearMap.coe_fst', add_zero, pow_zero, mul_one] using
      (PolynomialJets.affine (D := unitScale D) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))
        (fun _ => 0) (m := 0) hM (by
          simpa only [ContinuousLinearMap.coe_fst', add_zero, pow_zero, mul_one, Real.norm_eq_abs]
              using hrange))
  have hRi := hR.inv hr (fun i p hp => by
      rw [abs_of_pos (hr.trans_le (H.radius i p hp))]
      exact H.radius i p hp)
    (fun i p hp => by
      simpa only [Real.norm_eq_abs] using (norm_fst_le p).trans (H.bounded i p hp))
  refine ⟨?_, hp⟩
  have he := hp.mul hRi
  exact he

theorem leading_fields_polynomial {ι : Type*} {D : Domain ι Slow}
    {h r M qlo qhi lo hi C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hr : 0 < r) (hM : 1 ≤ M) (hqlo : 0 < qlo) (hlo : 0 < lo)
    (H : GeometryBounds D h r M qlo qhi lo hi)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d) :
    PolynomialJets (unitScale D) (fun _ => leadingFrequency h C d) ∧
    PolynomialJets (unitScale D) (fun _ => leadingAxial h d) := by
  have hc := normalizedCoordinates_polynomial hh hh1 hqlo H
  have hcinner := hc.clm (ContinuousLinearMap.snd ℝ ℝ Inner)
  have hmap (i : ι) (p : Slow) (hp : p ∈ (unitScale D).carrier i) : (normalizedCoordinates h p).2 ∈
      SlowBorelBase.innerBox lo hi := by
    have he := normalizedCoordinates_eta hh hh1 (H.time i p hp)
    exact ⟨⟨(H.x_range i p hp).1.le, (H.x_range i p hp).2.le⟩,
      (abs_lt.mp he).1.le, (abs_lt.mp he).2.le⟩
  have hs : ContDiffOn ℝ ∞ (SlowBorelBase.leadingSwirl C d) {w : Inner | 0 < w.1} := by
    intro w hw
    have hX : 0 < w.1 := hw
    exact ((((contDiffAt_const.mul contDiffAt_fst).sqrt
      (by positivity : (2 : ℝ) * w.1 ≠ 0)).div_const C).mul (hd.phi 0).contDiffAt).contDiffWithinAt
  have hv := hcinner.compact_comp (isOpen_lt continuous_const continuous_fst) hs
    (SlowBorelBase.innerBox_isCompact lo hi) (fun _ hx => hlo.trans_le hx.1.1) hmap
  have hg := hcinner.compact_comp isOpen_univ (hd.axial 0).contDiffOn
    (SlowBorelBase.innerBox_isCompact lo hi) (subset_univ _) hmap
  have hf := geometry_factors_polynomial hh hh1 hr hM hqlo H
  exact ⟨hf.1.mul hv, hf.2.mul hg⟩

/-- All quantities in this conclusion are literal summed-field formulas. -/
structure Estimates {ι : Type*} (D : Domain ι Slow) (Q : ι → ℝ)
    (a : ℕ → ℕ) (h C : ℝ) (d : SlowBorelBase.Coefficients) : Prop where
  frequency_error : EnvelopeJets (unitScale D) (fun i _ => Q i ^ (2 * h))
    (fun i p => frequency a h C d (Q i) p - leadingFrequency h C d p)
  axial_error : EnvelopeJets (unitScale D) (fun i _ => Q i ^ (2 * h))
    (fun i p => axial a h d (Q i) p - leadingAxial h d p)
  leading_frequency : PolynomialJets (unitScale D) (fun _ => leadingFrequency h C d)
  leading_axial : PolynomialJets (unitScale D) (fun _ => leadingAxial h d)
  frequency_jets : PolynomialJets (unitScale D) (fun i => frequency a h C d (Q i))
  axial_jets : PolynomialJets (unitScale D) (fun i => axial a h d (Q i))

theorem actual_estimates {ι : Type*} {D : Domain ι Slow}
    {a : ℕ → ℕ} {h C r M qlo qhi lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hr : 0 < r) (hM : 1 ≤ M)
    (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (H : GeometryBounds D h r M qlo qhi lo hi)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    (ha : SlowBorelBase.AdmissibleScales h (SlowBorelBase.coefficientBundle C d)
      (SlowBorelBase.innerBox lo hi) a)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1)
    (hsmall : ∀ i, Q i * qhi ≤ 1) : Estimates D Q a h C d := by
  have he := actual_error_envelopes hh hqlo hqhi hlo hd ha Q hQ hsmall
  have hc := normalizedCoordinates_polynomial hh hh1 hqlo H
  have hmap (i : ι) (p : Slow) (hp : p ∈ (unitScale D).carrier i) : normalizedCoordinates h p ∈
      innerRegion qlo qhi lo hi := by
    have heta := abs_lt.mp (normalizedCoordinates_eta hh hh1 (H.time i p hp))
    exact ⟨H.q_range i p hp, H.x_range i p hp, heta⟩
  have hev := he.1.comp hc (fun _ => rfl) hmap
  have heg := he.2.comp hc (fun _ => rfl) hmap
  have hf := geometry_factors_polynomial hh hh1 hr hM hqlo H
  have h0 := leading_fields_polynomial (C := C) hh hh1 hr hM hqlo hlo H hd
  have hF : EnvelopeJets (unitScale D) (fun i _ => Q i ^ (2 * h))
      (fun i p => frequency a h C d (Q i) p - leadingFrequency h C d p) := by
    apply (hev.polynomial_smul hf.1).congr
    intro i p _
    simp only [frequency, leadingFrequency, swirlError, Function.comp_apply, smul_eq_mul, mul_sub,
        SlowBorelBase.scaleMap_apply]
  have hG : EnvelopeJets (unitScale D) (fun i _ => Q i ^ (2 * h))
      (fun i p => axial a h d (Q i) p - leadingAxial h d p) := by
    apply (heg.polynomial_smul hf.2).congr
    intro i p _
    simp only [axial, leadingAxial, axialError, Function.comp_apply, smul_eq_mul, mul_sub,
        SlowBorelBase.scaleMap_apply]
  have hw i p (_hp : p ∈ (unitScale D).carrier i) : Q i ^ (2 * h) ≤ 1 :=
    Real.rpow_le_one (hQ i).le (hQ1 i) (by linarith)
  refine ⟨hF, hG, h0.1, h0.2, ?_, ?_⟩
  · exact ((hF.to_polynomial hw).add h0.1).congr (fun _ _ _ => sub_add_cancel _ _)
  · exact ((hG.to_polynomial hw).add h0.2).congr (fun _ _ _ => sub_add_cancel _ _)

/-- With unit bookkeeping scale, polynomial bounds are uniform bounds. -/
theorem polynomial_unit_bound {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {D : Domain ι E} {f : ι → E → F}
    (hf : PolynomialJets (unitScale D) f) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i j, j ≤ N → ∀ x ∈ D.carrier i,
      ‖iteratedFDeriv ℝ j (f i) x‖ ≤ C := by
  obtain ⟨C, hC, m, hm⟩ := hf.bound N
  exact ⟨C, hC, fun i j hj x hx => by
      simpa only [unitScale, oneDomain, one_pow, mul_one] using hm i j hj x hx⟩

theorem envelope_unit_bound {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {D : Domain ι E} {f : ι → E → F} {w : ι → E → ℝ}
    (hf : EnvelopeJets (unitScale D) w f) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i x, x ∈ D.carrier i → ∀ j, j ≤ N →
      ‖iteratedFDeriv ℝ j (f i) x‖ ≤ C * w i x := by
  obtain ⟨C, hC, m, hm⟩ := hf.bound N
  exact ⟨C, hC, fun i x hx j hj => by
      simpa only [unitScale, oneDomain, one_pow, mul_one] using hm i x hx j hj⟩

theorem polynomial_of_unit {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {D : Domain ι E} {f : ι → E → F}
    (hf : PolynomialJets (unitScale D) f) : PolynomialJets D f := by
  refine ⟨hf.smooth, fun N => ?_⟩
  obtain ⟨C, hC, hb⟩ := polynomial_unit_bound hf N
  exact ⟨C, hC, 0, fun i j hj x hx => by simpa only [pow_zero, mul_one] using hb i j hj x hx⟩

theorem norm_fderiv_eq_jet_one {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x : E) :
    ‖fderiv ℝ f x‖ = ‖iteratedFDeriv ℝ 1 f x‖ := by
  simpa only [norm_iteratedFDeriv_zero, Nat.zero_add] using
    (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := x) (n := 0))

theorem norm_second_fderiv_eq_jet_two {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x : E) :
    ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
  rw [norm_fderiv_eq_jet_one, norm_iteratedFDeriv_fderiv]

theorem Estimates.polynomial_fields {ι : Type*} {D : Domain ι Slow} {Q : ι → ℝ}
    {a : ℕ → ℕ} {h C : ℝ} {d : SlowBorelBase.Coefficients} (H : Estimates D Q a h C d) :
    PolynomialJets D (fun i => frequency a h C d (Q i)) ∧
    PolynomialJets D (fun i => axial a h d (Q i)) :=
  ⟨polynomial_of_unit H.frequency_jets, polynomial_of_unit H.axial_jets⟩

/-- The actual all-order error estimates supply the precise C1/C2 input
of `BasePhaseGeometry`. The constant is chosen before the band or label. -/
theorem Estimates.localBaseBounds {ι : Type*} {D : Domain ι Slow} {Q : ι → ℝ}
    {a : ℕ → ℕ} {h C : ℝ} {d : SlowBorelBase.Coefficients}
    (H : Estimates D Q a h C d) (hh : 0 ≤ h)
    (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1)
    (hconvex : ∀ i, Convex ℝ (D.carrier i)) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i,
      PhaseEstimates.LocalBaseBounds (frequency a h C d (Q i)) (axial a h d (Q i))
        (leadingFrequency h C d) (leadingAxial h d) (D.carrier i) B (Q i ^ h) := by
  obtain ⟨CF, hCF, hEF⟩ := envelope_unit_bound H.frequency_error 1
  obtain ⟨CG, hCG, hEG⟩ := envelope_unit_bound H.axial_error 1
  obtain ⟨BF, hBF, hBFj⟩ := polynomial_unit_bound H.leading_frequency 2
  obtain ⟨BG, hBG, hBGj⟩ := polynomial_unit_bound H.leading_axial 2
  let K := CF + CG + BF + BG + 1
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hCFK : CF ≤ K := by dsimp [K]; linarith
  have hCGK : CG ≤ K := by dsimp [K]; linarith
  have hBFK : BF ≤ K := by dsimp [K]; linarith
  have hBGK : BG ≤ K := by dsimp [K]; linarith
  refine ⟨2 * K, by linarith, fun i => ?_⟩
  have hsquare : (Q i ^ h) ^ 2 = Q i ^ (2 * h) := by
    rw [← Real.rpow_mul_natCast (hQ i).le]
    congr 1
    ring
  have hsmall : (Q i ^ h) ^ 2 ≤ 1 := by
    rw [hsquare]
    exact Real.rpow_le_one (hQ i).le (hQ1 i) (mul_nonneg (by norm_num) hh)
  have hF (x : Slow) (hx : x ∈ D.carrier i) :=
    (H.frequency_jets.smooth i).contDiffAt ((D.isOpen i).mem_nhds hx)
  have hG (x : Slow) (hx : x ∈ D.carrier i) :=
    (H.axial_jets.smooth i).contDiffAt ((D.isOpen i).mem_nhds hx)
  have hF0 (x : Slow) (hx : x ∈ D.carrier i) :=
    (H.leading_frequency.smooth i).contDiffAt ((D.isOpen i).mem_nhds hx)
  have hG0 (x : Slow) (hx : x ∈ D.carrier i) :=
    (H.leading_axial.smooth i).contDiffAt ((D.isOpen i).mem_nhds hx)
  apply BasePhaseGeometry.localBase_of_normalized_error (zero_le_one.trans hK) hsmall (hconvex i)
    (fun x hx => (hF x hx).differentiableAt (by simp))
    (fun x hx => (hG x hx).differentiableAt (by simp))
    (fun x hx => (hF0 x hx).differentiableAt (by simp))
    (fun x hx => (hG0 x hx).differentiableAt (by simp))
    (fun x hx => ((hF0 x hx).fderiv_right (show (∞ : WithTop ℕ∞) + 1 ≤ ∞ by
        simp)).differentiableAt (by simp))
    (fun x hx => ((hG0 x hx).fderiv_right (show (∞ : WithTop ℕ∞) + 1 ≤ ∞ by
        simp)).differentiableAt (by simp))
  · intro x hx
    rw [norm_fderiv_eq_jet_one]
    exact (hBFj i 1 (by norm_num) x hx).trans hBFK
  · intro x hx
    rw [norm_fderiv_eq_jet_one]
    exact (hBGj i 1 (by norm_num) x hx).trans hBGK
  · intro x hx
    rw [norm_second_fderiv_eq_jet_two]
    exact (hBFj i 2 le_rfl x hx).trans hBFK
  · intro x hx
    rw [norm_second_fderiv_eq_jet_two]
    exact (hBGj i 2 le_rfl x hx).trans hBGK
  · intro x hx
    have he := hEF i x hx 0 (by norm_num)
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at he
    rw [hsquare]
    exact he.trans (mul_le_mul_of_nonneg_right hCFK (Real.rpow_nonneg (hQ i).le _))
  · intro x hx
    have he := hEF i x hx 1 le_rfl
    rw [← norm_fderiv_eq_jet_one, fderiv_fun_sub ((hF x hx).differentiableAt (by simp))
      ((hF0 x hx).differentiableAt (by simp))] at he
    rw [hsquare]
    exact he.trans (mul_le_mul_of_nonneg_right hCFK (Real.rpow_nonneg (hQ i).le _))
  · intro x hx
    have he := hEG i x hx 1 le_rfl
    rw [← norm_fderiv_eq_jet_one, fderiv_fun_sub ((hG x hx).differentiableAt (by simp))
      ((hG0 x hx).differentiableAt (by simp))] at he
    rw [hsquare]
    exact he.trans (mul_le_mul_of_nonneg_right hCGK (Real.rpow_nonneg (hQ i).le _))

/-- Primitive summed-coefficient hypotheses, not supplied base estimates,
produce both interfaces needed by the actual phase construction. -/
theorem actual_localBase_and_polynomial {ι : Type*} {D : Domain ι Slow}
    {a : ℕ → ℕ} {h C r M qlo qhi lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hr : 0 < r) (hM : 1 ≤ M)
    (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (H : GeometryBounds D h r M qlo qhi lo hi)
    (hconvex : ∀ i, Convex ℝ (D.carrier i))
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    (ha : SlowBorelBase.AdmissibleScales h (SlowBorelBase.coefficientBundle C d)
      (SlowBorelBase.innerBox lo hi) a)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1)
    (hsmall : ∀ i, Q i * qhi ≤ 1) :
    PolynomialJets D (fun i => frequency a h C d (Q i)) ∧
    PolynomialJets D (fun i => axial a h d (Q i)) ∧
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i,
      PhaseEstimates.LocalBaseBounds (frequency a h C d (Q i)) (axial a h d (Q i))
        (leadingFrequency h C d) (leadingAxial h d) (D.carrier i) B (Q i ^ h) := by
  have he := actual_estimates hh hh1 hr hM hqlo hqhi hlo H hd ha Q hQ hQ1 hsmall
  exact ⟨he.polynomial_fields.1, he.polynomial_fields.2,
    he.localBaseBounds hh.le hQ hQ1 hconvex⟩

/-- Exact homogeneity of the actual inverse chart under the physical band
rescaling. The frozen summation variable is `Q*rho`. -/
theorem physicalChart_band {h Q : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) {p : Slow} (hT : 0 < p.2.2) :
    SlowBorelBase.physicalChart h
      (SimilarityHomogeneity.physicalScale h Q (physicalInput p)) =
      SlowBorelBase.scaleMap Q (normalizedCoordinates h p) := by
  have hp : (physicalInput p).1 < 1 := by dsimp [physicalInput]; linarith
  simp only [SlowBorelBase.physicalChart_eq, SimilarityHomogeneity.q_physicalScale hh hh1 hQ hp,
    SimilarityHomogeneity.inner_physicalScale hh hh1 hQ hp,
    SlowBorelBase.scaleMap_apply, normalizedCoordinates]

/-- Cancelling the physical `Q^A` normalization leaves precisely `rho^(-A)`. -/
theorem normalized_power {Q rho A : ℝ} (hQ : 0 < Q) (hrho : 0 < rho) :
    Q ^ A * (Q * rho) ^ (-A) = rho ^ (-A) := by
  rw [Real.mul_rpow hQ.le hrho.le, ← mul_assoc, ← Real.rpow_add hQ]
  simp

/-- The leading angular frequency retains the `1/R` factor; simplifying it
uses the actual relation `X=R²/(2*rho)`. -/
theorem leadingFrequency_eq {h C : ℝ} {d : SlowBorelBase.Coefficients}
    (hh : 0 < h) (hh1 : h < 1 / 2) {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    leadingFrequency h C d p =
      (normalizedCoordinates h p).1 ^ (-CoordinateAlgebra.A h - 1 / 2) / C *
        d.phi 0 (normalizedCoordinates h p).2 := by
  have hrho := normalizedCoordinates_q_pos hh hh1 hT
  have hX : 2 * (normalizedCoordinates h p).2.1 =
      p.1 ^ 2 / (normalizedCoordinates h p).1 := by
    rw [normalizedCoordinates_eq]
    simp only [SimilarityHomogeneity.chartX, SimilarityCoordinates.coordinateX,
      SimilarityHomogeneity.chartQ]
    ring
  unfold leadingFrequency frequencyFactor axialFactor SlowBorelBase.leadingSwirl
  rw [hX, Real.sqrt_div (sq_nonneg p.1), Real.sqrt_sq hR.le,
    Real.sqrt_eq_rpow, Real.rpow_sub hrho]
  calc
    _ = (p.1 / p.1) * (((normalizedCoordinates h p).1 ^ (-CoordinateAlgebra.A h) /
        (normalizedCoordinates h p).1 ^ (1 / 2 : ℝ)) / C * d.phi 0 (normalizedCoordinates h p).2)
            := by
            ring
    _ = _ := by rw [div_self hR.ne', one_mul]

/-- Band point, given by `(1 - Q * p.2.2, !₂[Real.sqrt Q * p.1, 0, Q ^ CoordinateAlgebra.D h *
p.2.1])`. -/
noncomputable def bandPoint (h Q : ℝ) (p : Slow) : ProblemStatement.SpaceTime :=
  (1 - Q * p.2.2, !₂[Real.sqrt Q * p.1, 0, Q ^ CoordinateAlgebra.D h * p.2.1])

theorem bandPoint_time {h Q : ℝ} (hQ : 0 < Q) {p : Slow} (hT : 0 < p.2.2) :
    (bandPoint h Q p).1 < 1 := by
  change 1 - Q * p.2.2 < 1
  linarith [mul_pos hQ hT]

theorem bandPoint_profile {h Q : ℝ} (hQ : 0 ≤ Q) (p : Slow) :
    AxisymmetricFields.profilePoint (bandPoint h Q p).1 (bandPoint h Q p).2 =
      SimilarityHomogeneity.physicalScale h Q (physicalInput p) := by
  apply Prod.ext
  · change 1 - Q * p.2.2 = 1 - Q * (1 - (1 - p.2.2))
    ring
  · apply Prod.ext
    · change ((Real.sqrt Q * p.1) ^ 2 + 0 ^ 2) / 2 = Q * (p.1 ^ 2 / 2)
      rw [mul_pow, Real.sq_sqrt hQ]
      ring
    · rfl

theorem bandPoint_chart {h Q : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) {p : Slow} (hT : 0 < p.2.2) :
    SlowBorelBase.cartesianChart h (bandPoint h Q p) =
      SlowBorelBase.scaleMap Q (normalizedCoordinates h p) := by
  unfold SlowBorelBase.cartesianChart
  rw [bandPoint_profile hQ.le, physicalChart_band hh hh1 hQ hT]

/-- Literal equality with the axial component of the constructed curl base. -/
theorem axial_eq_normalized_velocity {a : ℕ → ℕ} (ha : StrictMono a) {h C Q : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hQ : 0 < Q)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    {p : Slow} (hT : 0 < p.2.2) :
    axial a h d Q p = Q ^ CoordinateAlgebra.A h *
      SlowBorelBase.baseVelocity a h C d (bandPoint h Q p) 2 := by
  rw [SlowBorelBase.baseVelocity_axial ha hh hh1 hd C (bandPoint_time (h := h) hQ hT)]
  unfold SlowBorelBase.physicalProfile
  rw [bandPoint_profile hQ.le, physicalChart_band hh hh1 hQ hT]
  simp only [SlowBorelBase.scaleMap_apply, smul_eq_mul]
  rw [← mul_assoc, normalized_power hQ (normalizedCoordinates_q_pos hh hh1 hT)]
  rfl

/-- Literal equality with `Q^A` times the constructed angular velocity,
divided by the normalized radius. -/
theorem frequency_eq_normalized_velocity {a : ℕ → ℕ} (ha : StrictMono a) {h C Q : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hQ : 0 < Q)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    frequency a h C d Q p = Q ^ CoordinateAlgebra.A h *
      SlowBorelBase.baseVelocity a h C d (bandPoint h Q p) 1 / p.1 := by
  have hm := SlowBorelBase.angularMoment_eq_normalizedSwirl ha hh hh1 hd C
    (bandPoint_time (h := h) hQ hT) (bandPoint h Q p).2
  have hr : 0 < Real.sqrt Q * p.1 := mul_pos (Real.sqrt_pos.2 hQ) hR
  have hsqrt : Real.sqrt (2 * AxisymmetricFields.radialEnergy (bandPoint h Q p).2) =
      Real.sqrt Q * p.1 := by
    change Real.sqrt (2 * (((Real.sqrt Q * p.1) ^ 2 + 0 ^ 2) / 2)) = _
    rw [show 2 * (((Real.sqrt Q * p.1) ^ 2 + 0 ^ 2) / 2) = (Real.sqrt Q * p.1) ^ 2 by ring,
      Real.sqrt_sq hr.le]
  rw [hsqrt, bandPoint_chart hh hh1 hQ hT] at hm
  change -0 * _ + (Real.sqrt Q * p.1) * _ = _ at hm
  simp only [neg_zero, zero_mul, zero_add] at hm
  have hv : SlowBorelBase.baseVelocity a h C d (bandPoint h Q p) 1 =
      (SlowBorelBase.scaleMap Q (normalizedCoordinates h p)).1 ^ (-CoordinateAlgebra.A h) *
        SlowBorelBase.normalizedSwirl a h C d (SlowBorelBase.scaleMap Q (normalizedCoordinates h
            p)) := by
    apply mul_left_cancel₀ hr.ne'
    simpa only [mul_assoc] using hm
  rw [hv]
  unfold frequency frequencyFactor axialFactor
  simp only [SlowBorelBase.scaleMap_apply]
  rw [← mul_assoc, normalized_power hQ (normalizedCoordinates_q_pos hh hh1 hT)]
  ring

/-- The physical scale restriction is chosen after the fixed chart bounds
and before any band, label, or derivative order. -/
theorem exists_dyadic_cutoff {qhi : ℝ} (hqhi : 0 < qhi) (N0 : ℕ) :
    ∃ N : ℕ, N0 ≤ N ∧ ∀ n ≥ N, ChartScales.Q n * qhi ≤ 1 := by
  obtain ⟨N, hN⟩ := ChartScales.exists_slow_power_epsilon_cutoff 1 (by norm_num)
    0 1 (1 / qhi) (by norm_num) (by positivity)
  refine ⟨max N0 N, le_max_left _ _, fun n hn => ?_⟩
  have hb := hN n ((le_max_right N0 N).trans hn)
  simp only [ChartScales.epsilon, Real.rpow_zero, Real.rpow_one, one_mul] at hb
  exact ((lt_div_iff₀ hqhi).mp hb).le

/-- Actual dyadic input interface. Indices may include every active label
of every band above the one fixed cutoff. -/
theorem dyadic_actual_bounds {ι : Type*} {D : Domain ι Slow}
    {a : ℕ → ℕ} {h C r M qlo qhi lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hr : 0 < r) (hM : 1 ≤ M)
    (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (H : GeometryBounds D h r M qlo qhi lo hi)
    (hconvex : ∀ i, Convex ℝ (D.carrier i))
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    (ha : SlowBorelBase.AdmissibleScales h (SlowBorelBase.coefficientBundle C d)
      (SlowBorelBase.innerBox lo hi) a)
    (band : ι → ℕ) {N : ℕ} (hN : ∀ n ≥ N, ChartScales.Q n * qhi ≤ 1)
    (hband : ∀ i, N ≤ band i) :
    PolynomialJets D (fun i => frequency a h C d (ChartScales.Q (band i))) ∧
    PolynomialJets D (fun i => axial a h d (ChartScales.Q (band i))) ∧
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i,
      PhaseEstimates.LocalBaseBounds
        (frequency a h C d (ChartScales.Q (band i)))
        (axial a h d (ChartScales.Q (band i)))
        (leadingFrequency h C d) (leadingAxial h d) (D.carrier i) B
        (ChartScales.epsilon h (band i)) :=
  actual_localBase_and_polynomial hh hh1 hr hM hqlo hqhi hlo H hconvex hd ha
    (fun i => ChartScales.Q (band i)) (fun i => ChartScales.Q_pos (band i))
    (fun i => ChartScales.Q_le_one (band i)) (fun i => hN (band i) (hband i))

/-- The already selected enlarged-bundle schedule of the nominal base
instantiates the chart theorem without any additional schedule choice. -/
theorem nominal_estimates {ι : Type*} {D : Domain ι Slow}
    {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ)
    {r M qlo qhi lo hi : ℝ}
    (hr : 0 < r) (hM : 1 ≤ M) (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (hhi : hi ≤ ConstructedSlowBase.scaleUpper W upper)
    (H : GeometryBounds D F.data.h r M qlo qhi lo hi)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1)
    (hsmall : ∀ i, Q i * qhi ≤ 1) :
    Estimates D Q (ConstructedSlowBase.nominalScales W c hc upper B)
      F.data.h W.axis.normalization (AssembledSlowBase.nominalCoefficients W) :=
  actual_estimates (ConstructedSlowBase.height_pos W) (ConstructedSlowBase.height_lt_half W)
    hr hM hqlo hqhi hlo H (AssembledSlowBase.nominalCoefficients_smooth W)
    (ConstructedSlowBase.nominalScales_admissible_on W c hc upper B hlo.le hhi)
    Q hQ hQ1 hsmall

/-- The same conclusion for the actual solved finite modulation and its
single common weighted/ordinary Borel schedule. -/
theorem modulated_estimates {ι : Type*} {D : Domain ι Slow}
    {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    {ld : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness ld)
    (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ)
    {r M qlo qhi lo hi : ℝ}
    (hr : 0 < r) (hM : 1 ≤ M) (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (hhi : hi ≤ ConstructedSlowBase.scaleUpper W upper)
    (H : GeometryBounds D F.data.h r M qlo qhi lo hi)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1)
    (hsmall : ∀ i, Q i * qhi ≤ 1) :
    Estimates D Q (ConstructedSlowBase.Modulated.scales v c hc upper B)
      F.data.h W.axis.normalization (ConstructedSlowBase.Modulated.coefficients v) := by
  have ha := ConstructedSlowBase.admissibleScales_mono
    (ConstructedSlowBase.Modulated.scales_admissible v c hc upper B)
    (show SlowBorelBase.innerBox lo hi ⊆
      SlowBorelBase.innerBox 0 (ConstructedSlowBase.scaleUpper W upper) from
        fun w hw => ⟨⟨hlo.le.trans hw.1.1, hw.1.2.trans hhi⟩, hw.2⟩)
  exact actual_estimates (ConstructedSlowBase.height_pos W) (ConstructedSlowBase.height_lt_half W)
    hr hM hqlo hqhi hlo H (ConstructedSlowBase.Modulated.coefficients_smooth v) ha Q hQ hQ1 hsmall

/-- A direct paired all-jet form, with constants uniform over every index
of the chart family. -/
theorem Estimates.uniform_errors {ι : Type*} {D : Domain ι Slow} {Q : ι → ℝ}
    {a : ℕ → ℕ} {h C : ℝ} {d : SlowBorelBase.Coefficients}
    (H : Estimates D Q a h C d) (N : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ i x, x ∈ D.carrier i → ∀ j, j ≤ N →
      ‖iteratedFDeriv ℝ j (fun p => frequency a h C d (Q i) p - leadingFrequency h C d p) x‖ ≤
        K * Q i ^ (2 * h) ∧
      ‖iteratedFDeriv ℝ j (fun p => axial a h d (Q i) p - leadingAxial h d p) x‖ ≤
        K * Q i ^ (2 * h) := by
  obtain ⟨CF, hCF, hF⟩ := envelope_unit_bound H.frequency_error N
  obtain ⟨CG, hCG, hG⟩ := envelope_unit_bound H.axial_error N
  refine ⟨max CF CG, hCF.trans (le_max_left _ _), fun i x hx j hj => ?_⟩
  have hw := H.frequency_error.nonneg i x hx
  exact ⟨(hF i x hx j hj).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hw),
    (hG i x hx j hj).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hw)⟩

/-- Every actual positive active label above a single fixed band. -/
noncomputable def CellIndex (h lo hi : ℝ) (N : ℕ) :=
  {L : PositiveRepresentatives.ActiveLabel (PrimaryRepresentatives.referenceCompact h lo hi) //
    N ≤ L.val.1}

/-- Cell band, given by `L.val.val.1`. -/
noncomputable def cellBand {h lo hi : ℝ} {N : ℕ} (L : CellIndex h lo hi N) : ℕ := L.val.val.1

/-- The actual convex positive-time three-mesh cells. The slow scale is
precisely the manuscript's `S_n`; it is not a replacement coordinate. -/
noncomputable def positiveCellDomain (h lo hi : ℝ) (N : ℕ) : Domain (CellIndex h lo hi N) Slow where
  scale L := ChartScales.S (cellBand L)
  carrier L := PositiveRepresentatives.positiveCell L.val.val.1 L.val.val.2
  isOpen L := PositiveRepresentatives.positiveCell_open _ _
  one_le_scale L := by
    have hn : (1 : ℝ) ≤ L.val.val.1 := by exact_mod_cast L.val.property.1
    change 1 ≤ (L.val.val.1 : ℝ) ^ 2
    nlinarith

theorem positiveCellDomain_convex (h lo hi : ℝ) (N : ℕ) (L : CellIndex h lo hi N) :
    Convex ℝ ((positiveCellDomain h lo hi N).carrier L) :=
  PositiveRepresentatives.positiveCell_convex _ _

theorem positiveCellDomain_representative (h lo hi : ℝ) (N : ℕ) (L : CellIndex h lo hi N) :
    PositiveRepresentatives.representative (PrimaryRepresentatives.referenceCompact h lo hi) L.val ∈
      (positiveCellDomain h lo hi N).carrier L :=
  PositiveRepresentatives.representative_mem_cell _ L.val

theorem positiveCellDomain_covers (h lo hi : ℝ) (N : ℕ) (L : CellIndex h lo hi N) :
    PrimaryRepresentatives.gridBox L.val.val.1 L.val.val.2 2 ∩ PositiveRepresentatives.positiveTime
        ⊆
      (positiveCellDomain h lo hi N).carrier L :=
  PositiveRepresentatives.enlarged_positive_subset_cell L.val.property.1 _

/-- Full actual-input conclusion. The fixed annular profile and one
admissible Borel schedule give all-order estimates and a single local-base
constant on every actual enlarged positive-time cell above one band.
No representative proximity, inverse-coordinate jets, or local-base
estimates are hypotheses of this theorem. -/
theorem exists_actual_positive_charts {a : ℕ → ℕ} {h C lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hlo : 0 < lo) (hhi : lo ≤ hi)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    (ha : SlowBorelBase.AdmissibleScales h (SlowBorelBase.coefficientBundle C d)
      (SlowBorelBase.innerBox (lo / 2) (2 * hi)) a) (N0 : ℕ) :
    ∃ N : ℕ, N0 ≤ N ∧
      Estimates (positiveCellDomain h lo hi N) (fun L => ChartScales.Q (cellBand L)) a h C d ∧
      ∃ B : ℝ, 1 ≤ B ∧ ∀ L : CellIndex h lo hi N,
        PhaseEstimates.LocalBaseBounds
          (frequency a h C d (ChartScales.Q (cellBand L)))
          (axial a h d (ChartScales.Q (cellBand L)))
          (leadingFrequency h C d) (leadingAxial h d)
          ((positiveCellDomain h lo hi N).carrier L) B (ChartScales.epsilon h (cellBand L)) := by
  obtain ⟨Nc, hNc⟩ := PositiveRepresentatives.exists_positive_reference_charts hh hh1 hlo hhi
  obtain ⟨N, hN, hs⟩ := exists_dyadic_cutoff (qhi := 4) (by norm_num) (max N0 Nc)
  have hNNc : Nc ≤ N := (le_max_right _ _).trans hN
  have hb (L : CellIndex h lo hi N) : N ≤ cellBand L := L.property
  have hc (L : CellIndex h lo hi N) (p : Slow)
      (hp : p ∈ (positiveCellDomain h lo hi N).carrier L) :=
    (hNc L.val (hNNc.trans L.property)).2.2.2.2 p hp
  have hgeom : GeometryBounds (positiveCellDomain h lo hi N) h (Real.sqrt lo / 2)
      (PositiveRepresentatives.cellBound hi) (1 / 4) 4 (lo / 2) (2 * hi) := by
    refine ⟨fun L p hp => (hc L p hp).2.2.2.1,
      fun L p hp => (hc L p hp).2.1,
      fun L p hp => (hc L p hp).2.2.1, ?_, ?_⟩
    · intro L p hp
      simp only [normalizedCoordinates_eq]
      exact (hc L p hp).2.2.2.2.1
    · intro L p hp
      simp only [normalizedCoordinates_eq]
      exact (hc L p hp).2.2.2.2.2
  have hM : 1 ≤ PositiveRepresentatives.cellBound hi :=
    (show (1 : ℝ) ≤ 3 by norm_num).trans (le_max_right _ _)
  have he := actual_estimates hh hh1 (half_pos (Real.sqrt_pos.mpr hlo)) hM
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (0 : ℝ) < 4) (half_pos hlo)
    hgeom hd ha (fun L => ChartScales.Q (cellBand L))
    (fun L => ChartScales.Q_pos (cellBand L)) (fun L => ChartScales.Q_le_one (cellBand L))
    (fun L => hs _ (hb L))
  refine ⟨N, (le_max_left _ _).trans hN, he, ?_⟩
  exact he.localBaseBounds hh.le (fun L => ChartScales.Q_pos (cellBand L))
    (fun L => ChartScales.Q_le_one (cellBand L)) (positiveCellDomain_convex h lo hi N)

/-- Actual modulated base, actual common schedule, and actual positive
active cells, combined in one theorem. The only annular restriction is
that the selected schedule controls the enlarged fixed inner box. -/
theorem exists_modulated_positive_charts
    {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    {ld : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness ld)
    (c : ℝ) (hc : 0 < c) (upper : ℝ) (B0 : ℕ)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : lo ≤ hi)
    (hbox : 2 * hi ≤ ConstructedSlowBase.scaleUpper W upper) (N0 : ℕ) :
    let a := ConstructedSlowBase.Modulated.scales v c hc upper B0
    let d := ConstructedSlowBase.Modulated.coefficients v
    ∃ N : ℕ, N0 ≤ N ∧
      Estimates (positiveCellDomain F.data.h lo hi N)
        (fun L => ChartScales.Q (cellBand L)) a F.data.h W.axis.normalization d ∧
      ∃ B : ℝ, 1 ≤ B ∧ ∀ L : CellIndex F.data.h lo hi N,
        PhaseEstimates.LocalBaseBounds
          (frequency a F.data.h W.axis.normalization d (ChartScales.Q (cellBand L)))
          (axial a F.data.h d (ChartScales.Q (cellBand L)))
          (leadingFrequency F.data.h W.axis.normalization d) (leadingAxial F.data.h d)
          ((positiveCellDomain F.data.h lo hi N).carrier L) B
          (ChartScales.epsilon F.data.h (cellBand L)) := by
  dsimp only
  have ha := ConstructedSlowBase.admissibleScales_mono
    (ConstructedSlowBase.Modulated.scales_admissible v c hc upper B0)
    (show SlowBorelBase.innerBox (lo / 2) (2 * hi) ⊆
      SlowBorelBase.innerBox 0 (ConstructedSlowBase.scaleUpper W upper) from
      fun w hw => ⟨⟨(half_pos hlo).le.trans hw.1.1, hw.1.2.trans hbox⟩, hw.2⟩)
  exact exists_actual_positive_charts (ConstructedSlowBase.height_pos W)
    (ConstructedSlowBase.height_lt_half W) hlo hhi
    (ConstructedSlowBase.Modulated.coefficients_smooth v) ha N0

end NavierStokes.BaseChartJets
