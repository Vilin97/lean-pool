/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.DegreeBookkeeping

/-! # ProductAnnulusCircle -/



open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Hermite1DimdLEAN

/-!
# ProductAnnulusCircle

Orbitwise circle inequalities lifted to a fixed product annulus.
Scaffolding notes: `ScaffoldingNotes/Circle/product_annulus_circle.md`.
-/

/-- Reverse-triangle comparison for modulus defects. -/
theorem rhoPointwise
    (a u v : ℂ) :
    rho a u ≤ rho a v + ‖u - v‖ := by
  unfold rho
  let A : ℝ := ‖a + u‖ - ‖a‖
  let B : ℝ := ‖a + v‖ - ‖a‖
  have hAB : |A - B| ≤ ‖u - v‖ := by
    calc
      |A - B| = |‖a + u‖ - ‖a + v‖| := by simp [A, B]
      _ ≤ ‖(a + u) - (a + v)‖ := abs_norm_sub_norm_le (a + u) (a + v)
      _ = ‖u - v‖ := by
        rw [sub_eq_add_neg, sub_eq_add_neg]
        ring_nf
  calc
    |A| = |(A - B) + B| := by ring_nf
    _ ≤ |A - B| + |B| := abs_add_le _ _
    _ ≤ ‖u - v‖ + |B| := by gcongr
    _ = rho a v + ‖u - v‖ := by simp [rho, B, add_comm]

/-- Quadratic defect comparison derived from `rhoPointwise`. -/
theorem rhoPointwiseSq
    (a u v : ℂ) :
    rho a u ^ 2 ≤ 2 * rho a v ^ 2 + 2 * ‖u - v‖ ^ 2 := by
  have h := rhoPointwise a u v
  have hsq : (rho a u) ^ 2 ≤ (rho a v + ‖u - v‖) ^ 2 := by
    have hnonneg : 0 ≤ rho a u := abs_nonneg _
    have hneg0 : -(rho a v + ‖u - v‖) ≤ 0 := by
      nlinarith [abs_nonneg (rho a v), norm_nonneg (u - v)]
    have hneg : -(rho a v + ‖u - v‖) ≤ rho a u := le_trans hneg0 hnonneg
    exact sq_le_sq' hneg h
  have hsum : (rho a v + ‖u - v‖) ^ 2 ≤ 2 * rho a v ^ 2 + 2 * ‖u - v‖ ^ 2 := by
    nlinarith [two_mul_le_add_sq (rho a v) ‖u - v‖]
  exact le_trans hsq hsum

/-- The local support and the local degree set carry the same total-degree image. -/
private theorem localPart_support_image_totalDegree
    {d : ℕ} (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    (localPart j M G).support.image totalDegree = localDegreeSet j M G := by
  rcases explicitLocalAndFarSupport (j := j) (M := M) (G := G) with
    ⟨_, _, hsupport, _⟩
  rw [hsupport]
  rfl

/-- Orthogonality to `ν_κ` turns the local degree window into a genuinely positive set. -/
private theorem localDegreeSet_pos
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d)
    (horth : hermiteInnerNu κ G = 0) :
    ∀ n ∈ localDegreeSet j M G, 0 < n := by
  intro n hn
  have hzero : 0 ∉ localDegreeSet j M G := zeroFrequencyAbsent κ j M G horth
  exact Nat.pos_of_ne_zero (by
    intro hn0
    exact hzero (hn0 ▸ hn))

/-- Local degree support has the exact cardinality bound needed in the low-frequency branch. -/
private theorem localDegreeSet_card_le_degreeWidth
    {d : ℕ} (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    (localDegreeSet j M G).card ≤ degreeWidth j M :=
  (localDegreeInterval j M G).2

/-- Fourier modes on `Circle` agree with complex exponentials on representatives in `ℝ`. -/
private lemma fourier_mk_eq_exp
    (n : ℤ) (θ : ℝ) :
    (fourier n (QuotientAddGroup.mk θ : Circle) : ℂ) =
      Complex.exp (Complex.I * (n : ℂ) * θ) := by
  rw [fourier_coe_apply]
  congr 1
  simp only [T, HermiteLEAN.T]
  push_cast
  field_simp

/-- The phase law rewritten in the `Circle`/`fourier` normal form used by the circle inputs. -/
private theorem productBasisPhaseLawCircle
    {d : ℕ} (κ α : MultiIndex d) (t : Circle) (z : CSpace d) :
    PhiKappaAlpha κ α (fun q => (fourier (1 : ℤ) t : ℂ) * z q) =
      (fourier (((totalDegree α : ℤ) - (totalDegree κ : ℤ)) : ℤ) t : ℂ) *
        PhiKappaAlpha κ α z := by
  induction t using Quotient.inductionOn with
  | h θ =>
    have hrot :
        (fun q => (fourier (1 : ℤ) (QuotientAddGroup.mk θ : Circle) : ℂ) * z q) =
          fun q => Complex.exp (Complex.I * θ) * z q := by
      funext q
      rw [fourier_mk_eq_exp]
      congr 1
      ring_nf
    rw [hrot, productBasisPhaseLaw, fourier_mk_eq_exp]
    apply congrArg₂ (· * ·)
    · congr 1
      push_cast
      ring
    · rfl

/-- Orbitwise coefficient grouped by total degree. -/
private def orbitCoeff
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (M : ℕ)
    (G : FiniteHermiteSum d) (z : CSpace d) (n : ℕ) : ℂ :=
  ∑ α ∈ (localPart j M G).support.filter (fun α => totalDegree α = n),
    (localPart j M G).coeff α * PhiKappaAlpha κ α z

/-- The phase-corrected local orbit is a positive-frequency polynomial on the local degree set. -/
private theorem localOrbit_eq_positiveFrequencyPolynomial
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d)
    (z : CSpace d) :
    (fun t : Circle =>
      (fourier (totalDegree κ : ℤ) t : ℂ) *
        evalHermiteSum κ (localPart j M G)
          (fun q => (fourier (1 : ℤ) t : ℂ) * z q)) =
      positiveFrequencyPolynomial (localDegreeSet j M G) (orbitCoeff κ j M G z) := by
  funext t
  classical
  let s : Finset (MultiIndex d) := (localPart j M G).support
  have hs : s.image totalDegree = localDegreeSet j M G := by
    simp [s, localPart_support_image_totalDegree (j := j) (M := M) (G := G)]
  have hgroup :=
    Finset.sum_image' (s := s) (g := totalDegree)
      (f := fun n : ℕ => orbitCoeff κ j M G z n * fourier (n : ℤ) t)
      (h := fun α : MultiIndex d =>
        ((localPart j M G).coeff α * PhiKappaAlpha κ α z) * fourier (totalDegree α : ℤ) t)
      (eq := by
        intro α hα
        unfold orbitCoeff
        change
          (∑ β ∈ (localPart j M G).support.filter (fun β => totalDegree β = totalDegree α),
              (localPart j M G).coeff β * PhiKappaAlpha κ β z) *
            fourier (totalDegree α : ℤ) t =
            ∑ j_1 ∈ s with totalDegree j_1 = totalDegree α,
              ((localPart j M G).coeff j_1 * PhiKappaAlpha κ j_1 z) *
                fourier (totalDegree j_1 : ℤ) t
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro β hβ
        by_cases hdeg : totalDegree β = totalDegree α
        · simp [hdeg, mul_left_comm, mul_comm]
        · exfalso
          exact hdeg ((Finset.mem_filter.mp hβ).2))
  calc
    (fourier (totalDegree κ : ℤ) t : ℂ) *
        evalHermiteSum κ (localPart j M G) (fun q => (fourier (1 : ℤ) t : ℂ) * z q)
      = ∑ α ∈ s,
          ((localPart j M G).coeff α * PhiKappaAlpha κ α z) * fourier (totalDegree α : ℤ) t := by
            unfold evalHermiteSum
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro α hα
            rw [productBasisPhaseLawCircle]
            have hadd :
                ((totalDegree κ : ℤ) + ((totalDegree α : ℤ) - (totalDegree κ : ℤ))) =
                  (totalDegree α : ℤ) := by omega
            calc
              (fourier (totalDegree κ : ℤ) t : ℂ) *
                  ((localPart j M G).coeff α *
                    ((fourier (((totalDegree α : ℤ) - (totalDegree κ : ℤ)) : ℤ) t : ℂ) *
                      PhiKappaAlpha κ α z))
                  = ((localPart j M G).coeff α * PhiKappaAlpha κ α z) *
                      ((fourier (totalDegree κ : ℤ) t : ℂ) *
                        (fourier (((totalDegree α : ℤ) - (totalDegree κ : ℤ)) : ℤ) t : ℂ)) := by
                          ring
              _ = ((localPart j M G).coeff α * PhiKappaAlpha κ α z) *
                    (fourier (totalDegree α : ℤ) t : ℂ) := by
                      rw [← fourier_add]
                      simp [hadd]
    _ = ∑ n ∈ s.image totalDegree, orbitCoeff κ j M G z n * fourier (n : ℤ) t := by
          simpa [s] using hgroup.symm
    _ = ∑ n ∈ localDegreeSet j M G, orbitCoeff κ j M G z n * fourier (n : ℤ) t := by rw [hs]
    _ = positiveFrequencyPolynomial (localDegreeSet j M G) (orbitCoeff κ j M G z) t := by
          simp [positiveFrequencyPolynomial]

/-- Support packaging for the low-frequency circle input. -/
private theorem localOrbit_hasPositiveFrequencySupport
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d)
    (z : CSpace d) :
    HasPositiveFrequencySupport
      (fun t : Circle =>
        (fourier (totalDegree κ : ℤ) t : ℂ) *
          evalHermiteSum κ (localPart j M G)
            (fun q => (fourier (1 : ℤ) t : ℂ) * z q))
      (localDegreeSet j M G) :=
  ⟨orbitCoeff κ j M G z, localOrbit_eq_positiveFrequencyPolynomial (κ := κ)
    (j := j) (M := M) (G := G) z⟩

/-- Support packaging for the high-frequency band input after zero-padding. -/
private theorem localOrbit_hasBandlimitedSupport
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d)
    (z : CSpace d) :
    HasBandlimitedSupport
      (fun t : Circle =>
        (fourier (totalDegree κ : ℤ) t : ℂ) *
          evalHermiteSum κ (localPart j M G)
            (fun q => (fourier (1 : ℤ) t : ℂ) * z q))
      (degreeIntervalLower j M) (degreeWidth j M) := by
  obtain ⟨c, hc⟩ := zeroPaddingBand
    (N := degreeIntervalLower j M) (L := degreeWidth j M)
    (E := localDegreeSet j M G) (b := orbitCoeff κ j M G z)
    (hE := by
      intro n hn
      rcases (localDegreeInterval j M G).1 n hn with ⟨hlo, hhi⟩
      constructor
      · exact hlo
      · dsimp [degreeWidth]
        omega)
  refine ⟨c, ?_⟩
  rw [localOrbit_eq_positiveFrequencyPolynomial (κ := κ) (j := j) (M := M) (G := G) z]
  exact hc

private lemma measurableSet_productAnnulus
    {d : ℕ} (j : MultiIndex d) :
    MeasurableSet (productAnnulus j) := by
  classical
  have h :
      MeasurableSet (⋂ q : Fin d, {z : CSpace d | (j q : ℝ) ≤ ‖z q‖ ∧ ‖z q‖ < (j q : ℝ) + 1}) := by
    refine MeasurableSet.iInter (f := fun q : Fin d =>
      {z : CSpace d | (j q : ℝ) ≤ ‖z q‖ ∧ ‖z q‖ < (j q : ℝ) + 1}) ?_
    intro q
    have hge : MeasurableSet {z : CSpace d | (j q : ℝ) ≤ ‖z q‖} :=
      measurableSet_le measurable_const (measurable_norm.comp (continuous_apply q).measurable)
    have hlt : MeasurableSet {z : CSpace d | ‖z q‖ < (j q : ℝ) + 1} :=
      measurableSet_lt (measurable_norm.comp (continuous_apply q).measurable) measurable_const
    simpa [Set.setOf_and] using hge.inter hlt
  simpa [productAnnulus, Set.setOf_forall] using h

private lemma continuous_PhiKappaAlpha
    {d : ℕ} (κ α : MultiIndex d) :
    Continuous (PhiKappaAlpha κ α) := by
  unfold PhiKappaAlpha oneDimPhi
  continuity

private lemma continuous_evalHermiteSum
    {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) :
    Continuous (evalHermiteSum κ G) := by
  unfold evalHermiteSum
  refine continuous_finsetSum _ ?_
  intro α hα
  exact continuous_const.mul (continuous_PhiKappaAlpha (κ := κ) (α := α))

private lemma continuous_nuKappa
    {d : ℕ} (κ : MultiIndex d) :
    Continuous (nuKappa κ) := by
  simpa [nuKappa] using continuous_PhiKappaAlpha (κ := κ) (α := (0 : MultiIndex d))

private lemma continuous_rho_localPart_sq
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    Continuous (fun z : CSpace d =>
      rho (nuKappa κ z) (evalHermiteSum κ (localPart j M G) z) ^ 2) := by
  unfold rho
  exact ((continuous_nuKappa (κ := κ)).add (continuous_evalHermiteSum (κ := κ)
    (localPart j M G))).norm.sub (continuous_nuKappa (κ := κ)).norm |>.abs.pow 2

private lemma rho_unit_mul (u a b : ℂ) (hu : ‖u‖ = 1) :
    rho (u * a) (u * b) = rho a b := by
  have hsum : u * a + u * b = u * (a + b) := by ring
  have h1 : ‖u * (a + b)‖ = ‖a + b‖ := by rw [norm_mul, hu, one_mul]
  have h2 : ‖u * a‖ = ‖a‖ := by rw [norm_mul, hu, one_mul]
  unfold rho
  rw [hsum, h1, h2]

/-- Phase-corrected local orbit on a fixed product annulus. -/
private def localOrbit
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (M : ℕ)
    (G : FiniteHermiteSum d) (z : CSpace d) (t : Circle) : ℂ :=
  (fourier (totalDegree κ : ℤ) t : ℂ) *
    evalHermiteSum κ (localPart j M G)
      (fun q => (fourier (1 : ℤ) t : ℂ) * z q)

/-- Multiplying by the correcting Fourier phase does not change the orbitwise mass. -/
private lemma localOrbit_norm_sq
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (M : ℕ)
    (G : FiniteHermiteSum d) (z : CSpace d) (t : Circle) :
    ‖evalHermiteSum κ (localPart j M G)
        (fun q => (fourier (1 : ℤ) t : ℂ) * z q)‖ ^ 2 =
      ‖localOrbit κ j M G z t‖ ^ 2 := by simp [localOrbit, mul_comm]

/-- The defect term is invariant under the same unit-phase correction. -/
private lemma localOrbit_defect_sq
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (M : ℕ)
    (G : FiniteHermiteSum d) (z : CSpace d) (t : Circle) :
    rho (nuKappa κ (fun q => (fourier (1 : ℤ) t : ℂ) * z q))
      (evalHermiteSum κ (localPart j M G)
        (fun q => (fourier (1 : ℤ) t : ℂ) * z q)) ^ 2 =
      rho (nuKappa κ z) (localOrbit κ j M G z t) ^ 2 := by
  have h0 : totalDegree (0 : MultiIndex d) = 0 := by simp [totalDegree]
  have hphase :=
    productBasisPhaseLawCircle (κ := κ) (α := (0 : MultiIndex d)) t z
  have hphase' :
      nuKappa κ (fun q => (fourier (1 : ℤ) t : ℂ) * z q) =
        (fourier (-(totalDegree κ : ℤ)) t : ℂ) * nuKappa κ z := by simpa [nuKappa, h0] using hphase
  have hu : ‖(fourier (totalDegree κ : ℤ) t : ℂ)‖ = 1 := by simp
  have hphaseρ :=
    rho_unit_mul
      (u := (fourier (totalDegree κ : ℤ) t : ℂ))
      (a := nuKappa κ (fun q => (fourier (1 : ℤ) t : ℂ) * z q))
      (b := evalHermiteSum κ (localPart j M G)
        (fun q => (fourier (1 : ℤ) t : ℂ) * z q))
      hu
  have hmain :
      rho (nuKappa κ (fun q => (fourier (1 : ℤ) t : ℂ) * z q))
        (evalHermiteSum κ (localPart j M G)
          (fun q => (fourier (1 : ℤ) t : ℂ) * z q)) =
      rho (nuKappa κ z) (localOrbit κ j M G z t) := by
    calc
      rho (nuKappa κ (fun q => (fourier (1 : ℤ) t : ℂ) * z q))
          (evalHermiteSum κ (localPart j M G)
            (fun q => (fourier (1 : ℤ) t : ℂ) * z q))
        = rho
            ((fourier (totalDegree κ : ℤ) t : ℂ) *
              nuKappa κ (fun q => (fourier (1 : ℤ) t : ℂ) * z q))
            ((fourier (totalDegree κ : ℤ) t : ℂ) *
              evalHermiteSum κ (localPart j M G)
                (fun q => (fourier (1 : ℤ) t : ℂ) * z q)) := by simpa using hphaseρ.symm
      _ = rho (nuKappa κ z) (localOrbit κ j M G z t) := by
            rw [hphase']
            have hcancel :
                (fourier (totalDegree κ : ℤ) t : ℂ) *
                    (fourier (-(totalDegree κ : ℤ)) t : ℂ) = 1 := by
              rw [← fourier_add]
              simp
            rw [localOrbit, ← mul_assoc, hcancel, one_mul]
  exact congrArg (fun x : ℝ => x ^ 2) hmain

/-- The orbitwise mass integrand is continuous and hence circle-integrable. -/
private lemma integrable_localOrbit_mass
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (M : ℕ)
    (G : FiniteHermiteSum d) (z : CSpace d) :
    Integrable (fun t : Circle => ‖localOrbit κ j M G z t‖ ^ 2) AddCircle.haarAddCircle := by
  have hrot : Continuous (fun t : Circle => fun q : Fin d =>
      (fourier (1 : ℤ) t : ℂ) * z q) := by continuity
  have hcont : Continuous (fun t : Circle => ‖localOrbit κ j M G z t‖ ^ 2) := by
    unfold localOrbit
    simpa [pow_two] using
      (((fourier (totalDegree κ : ℤ)).continuous.mul
        ((continuous_evalHermiteSum (κ := κ) (localPart j M G)).comp hrot)).norm.pow 2)
  simpa [MeasureTheory.integrableOn_univ] using
    (hcont.continuousOn.integrableOn_compact isCompact_univ :
      IntegrableOn (fun t : Circle => ‖localOrbit κ j M G z t‖ ^ 2) Set.univ
          AddCircle.haarAddCircle)

/-- The orbitwise defect integrand is continuous and hence circle-integrable. -/
private lemma integrable_localOrbit_defect
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (M : ℕ)
    (G : FiniteHermiteSum d) (z : CSpace d) :
    Integrable (fun t : Circle => rho (nuKappa κ z) (localOrbit κ j M G z t) ^ 2)
      AddCircle.haarAddCircle := by
  have hrot : Continuous (fun t : Circle => fun q : Fin d =>
      (fourier (1 : ℤ) t : ℂ) * z q) := by continuity
  have hloc : Continuous (fun t : Circle => localOrbit κ j M G z t) := by
    unfold localOrbit
    exact ((fourier (totalDegree κ : ℤ)).continuous.mul
      ((continuous_evalHermiteSum (κ := κ) (localPart j M G)).comp hrot))
  have hcont : Continuous (fun t : Circle => rho (nuKappa κ z) (localOrbit κ j M G z t) ^ 2) := by
    unfold rho
    simpa [pow_two] using
      (((continuous_const.add hloc).norm.sub (continuous_const).norm).abs.pow 2)
  simpa [MeasureTheory.integrableOn_univ] using
    (hcont.continuousOn.integrableOn_compact isCompact_univ :
      IntegrableOn (fun t : Circle => rho (nuKappa κ z) (localOrbit κ j M G z t) ^ 2)
        Set.univ AddCircle.haarAddCircle)

/-- Rewriting the orbitwise mass integral using the phase-corrected orbit. -/
private lemma localOrbit_mass_lintegral
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (M : ℕ)
    (G : FiniteHermiteSum d) (z : CSpace d) :
    ∫⁻ t : Circle,
        ENNReal.ofReal
          (‖evalHermiteSum κ (localPart j M G)
            (fun q => (fourier (1 : ℤ) t : ℂ) * z q)‖ ^ 2)
      ∂ AddCircle.haarAddCircle =
      ENNReal.ofReal (circleL2NormSq (localOrbit κ j M G z)) := by
  calc
    ∫⁻ t : Circle,
        ENNReal.ofReal
          (‖evalHermiteSum κ (localPart j M G)
            (fun q => (fourier (1 : ℤ) t : ℂ) * z q)‖ ^ 2)
      ∂ AddCircle.haarAddCircle
      = ∫⁻ t : Circle, ENNReal.ofReal (‖localOrbit κ j M G z t‖ ^ 2)
          ∂ AddCircle.haarAddCircle := by
            refine lintegral_congr_ae ?_
            filter_upwards with t
            exact congrArg ENNReal.ofReal
              (localOrbit_norm_sq (κ := κ) (j := j) (M := M) (G := G) z t)
    _ = ENNReal.ofReal (circleL2NormSq (localOrbit κ j M G z)) := by
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (integrable_localOrbit_mass (κ := κ) (j := j) (M := M) (G := G) z)
        (ae_of_all _ (by intro t; positivity))]
      simp [circleL2NormSq]

/-- Rewriting the orbitwise defect integral using the phase-corrected orbit. -/
private lemma localOrbit_defect_lintegral
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (M : ℕ)
    (G : FiniteHermiteSum d) (z : CSpace d) :
    ∫⁻ t : Circle,
        ENNReal.ofReal
          (rho (nuKappa κ (fun q => (fourier (1 : ℤ) t : ℂ) * z q))
            (evalHermiteSum κ (localPart j M G)
              (fun q => (fourier (1 : ℤ) t : ℂ) * z q)) ^ 2)
      ∂ AddCircle.haarAddCircle =
      ENNReal.ofReal
        (circleL2NormSq (fun t : Circle => rho (nuKappa κ z) (localOrbit κ j M G z t))) := by
  calc
    ∫⁻ t : Circle,
        ENNReal.ofReal
          (rho (nuKappa κ (fun q => (fourier (1 : ℤ) t : ℂ) * z q))
            (evalHermiteSum κ (localPart j M G)
              (fun q => (fourier (1 : ℤ) t : ℂ) * z q)) ^ 2)
      ∂ AddCircle.haarAddCircle
      = ∫⁻ t : Circle,
          ENNReal.ofReal (rho (nuKappa κ z) (localOrbit κ j M G z t) ^ 2)
        ∂ AddCircle.haarAddCircle := by
          refine lintegral_congr_ae ?_
          filter_upwards with t
          exact congrArg ENNReal.ofReal
            (localOrbit_defect_sq (κ := κ) (j := j) (M := M) (G := G) z t)
    _ = ENNReal.ofReal
        (circleL2NormSq (fun t : Circle => rho (nuKappa κ z) (localOrbit κ j M G z t))) := by
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (integrable_localOrbit_defect (κ := κ) (j := j) (M := M) (G := G) z)
        (ae_of_all _ (by intro t; positivity))]
      simp [circleL2NormSq]

/-- Integrability of the indicator mass on a product annulus. -/
private lemma indicator_mass_integrable
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    Integrable
      ((productAnnulus j).indicator
        (fun z : CSpace d => ‖evalHermiteSum κ (localPart j M G) z‖ ^ 2))
      (gaussianMeasure d) := by
  classical
  have hmass_fun_eq :
      (fun z : CSpace d => ‖indicatorMul (productAnnulus j)
          (fun w => evalHermiteSum κ (localPart j M G) w *
            conj (evalHermiteSum κ (localPart j M G) w)) z‖) =
      (productAnnulus j).indicator
        (fun z => ‖evalHermiteSum κ (localPart j M G) z‖ ^ 2) := by
    funext z
    by_cases hz : z ∈ productAnnulus j
    · have hnorm :
        |Complex.normSq (evalHermiteSum κ (localPart j M G) z)| =
          ‖evalHermiteSum κ (localPart j M G) z‖ ^ 2 := by
        have hnonneg : 0 ≤ Complex.normSq (evalHermiteSum κ (localPart j M G) z) := by
          dsimp [Complex.normSq]
          nlinarith [sq_nonneg (evalHermiteSum κ (localPart j M G) z).re,
            sq_nonneg (evalHermiteSum κ (localPart j M G) z).im]
        rw [abs_of_nonneg hnonneg, Complex.sq_norm]
      simp [indicatorMul, Set.indicator, hz, Complex.mul_conj']
    · simp [indicatorMul, Set.indicator, hz]
  rw [← hmass_fun_eq]
  simpa [indicatorMul] using
    ((annulusIntegrablePolynomial (j := j) (κ := κ)
      (G := localPart j M G) (H := localPart j M G)).norm)

/-- Rewriting annulus mass as the outer Gaussian integral of orbitwise circle mass. -/
private lemma annulusMass_localOrbit_lintegral
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (M : ℕ)
    (G : FiniteHermiteSum d) :
    ENNReal.ofReal (annulusMass j (evalHermiteSum κ (localPart j M G))) =
      ∫⁻ z : CSpace d,
        Set.indicator (productAnnulus j)
          (fun z => ENNReal.ofReal (circleL2NormSq (localOrbit κ j M G z))) z
      ∂ gaussianMeasure d := by
  classical
  have hmass_int := indicator_mass_integrable (κ := κ) (j := j) (M := M) (G := G)
  have hmass0 :
      ENNReal.ofReal (annulusMass j (evalHermiteSum κ (localPart j M G))) =
        ∫⁻ z : CSpace d,
          ENNReal.ofReal
            ((productAnnulus j).indicator
              (fun z => ‖evalHermiteSum κ (localPart j M G) z‖ ^ 2) z)
        ∂ gaussianMeasure d := by
    simpa [annulusMass, Set.indicator] using
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmass_int
        (ae_of_all _ (by
          intro z
          by_cases hz : z ∈ productAnnulus j <;> simp [hz])))
  have hFmass :
      Measurable (fun z : CSpace d => ENNReal.ofReal (‖evalHermiteSum κ (localPart j M G) z‖ ^ 2))
          := by
    have hcont : Continuous (evalHermiteSum κ (localPart j M G)) :=
      continuous_evalHermiteSum (κ := κ) (localPart j M G)
    exact (ENNReal.measurable_ofReal.comp (hcont.norm.pow 2).measurable)
  have havg :=
    annulusRotationAveraging (j := j)
      (F := fun z : CSpace d => ENNReal.ofReal (‖evalHermiteSum κ (localPart j M G) z‖ ^ 2))
      hFmass
  have hmass_indicator :
      ∫⁻ z : CSpace d,
          ENNReal.ofReal
            ((productAnnulus j).indicator
              (fun z => ‖evalHermiteSum κ (localPart j M G) z‖ ^ 2) z)
        ∂ gaussianMeasure d
        =
      ∫⁻ z : CSpace d,
          if z ∈ productAnnulus j then
            ENNReal.ofReal (‖evalHermiteSum κ (localPart j M G) z‖ ^ 2)
          else 0
        ∂ gaussianMeasure d := by
    refine lintegral_congr_ae ?_
    filter_upwards with z
    by_cases hz : z ∈ productAnnulus j <;> simp [Set.indicator, hz]
  calc
    ENNReal.ofReal (annulusMass j (evalHermiteSum κ (localPart j M G)))
      = ∫⁻ z : CSpace d,
          if z ∈ productAnnulus j then
            ∫⁻ t : Circle,
              ENNReal.ofReal
                (‖evalHermiteSum κ (localPart j M G)
                  (fun q => (fourier (1 : ℤ) t : ℂ) * z q)‖ ^ 2)
            ∂ AddCircle.haarAddCircle
          else 0
        ∂ gaussianMeasure d := by
          rw [hmass0, hmass_indicator]
          exact havg.symm
    _ = ∫⁻ z : CSpace d,
          Set.indicator (productAnnulus j)
            (fun z => ENNReal.ofReal (circleL2NormSq (localOrbit κ j M G z))) z
        ∂ gaussianMeasure d := by
          refine lintegral_congr_ae ?_
          filter_upwards with z
          by_cases hz : z ∈ productAnnulus j
          · simpa [Set.indicator, hz]
              using (localOrbit_mass_lintegral (κ := κ) (j := j) (M := M) (G := G) z)
          · simp [Set.indicator, hz]

/-- Rewriting annulus defect mass as the outer Gaussian integral of orbitwise circle defect mass. -/
private lemma defectAnnulusMass_localOrbit_lintegral
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (M : ℕ)
    (G : FiniteHermiteSum d) :
    ENNReal.ofReal (defectAnnulusMass κ j (evalHermiteSum κ (localPart j M G))) =
      ∫⁻ z : CSpace d,
        Set.indicator (productAnnulus j)
          (fun z =>
            ENNReal.ofReal
              (circleL2NormSq (fun t : Circle => rho (nuKappa κ z) (localOrbit κ j M G z t)))) z
      ∂ gaussianMeasure d := by
  classical
  have hmass_int := indicator_mass_integrable (κ := κ) (j := j) (M := M) (G := G)
  have hrho_cont := continuous_rho_localPart_sq (κ := κ) (j := j) (M := M) (G := G)
  have hdef_meas :
      AEStronglyMeasurable
        ((productAnnulus j).indicator
          (fun z : CSpace d => rho (nuKappa κ z) (evalHermiteSum κ (localPart j M G) z) ^ 2))
        (gaussianMeasure d) := by
    simpa [Set.indicator] using
      (hrho_cont.measurable.indicator (measurableSet_productAnnulus (j := j))).aestronglyMeasurable
  have hdef_le_mass :
      ∀ᵐ z ∂ gaussianMeasure d,
        ‖(productAnnulus j).indicator
            (fun z : CSpace d => rho (nuKappa κ z) (evalHermiteSum κ (localPart j M G) z) ^ 2) z‖ ≤
          ‖(productAnnulus j).indicator
            (fun z : CSpace d => ‖evalHermiteSum κ (localPart j M G) z‖ ^ 2) z‖ := by
    filter_upwards with z
    by_cases hz : z ∈ productAnnulus j
    · have hrho_le :
          rho (nuKappa κ z) (evalHermiteSum κ (localPart j M G) z) ≤
            ‖evalHermiteSum κ (localPart j M G) z‖ := by
        simpa [rho] using
          (rhoPointwise (nuKappa κ z) (evalHermiteSum κ (localPart j M G) z) 0)
      have hsq :
          rho (nuKappa κ z) (evalHermiteSum κ (localPart j M G) z) ^ 2 ≤
            ‖evalHermiteSum κ (localPart j M G) z‖ ^ 2 := sq_le_sq'
          (by
            have hnonneg : 0 ≤ rho (nuKappa κ z) (evalHermiteSum κ (localPart j M G) z) :=
              abs_nonneg _
            nlinarith)
          hrho_le
      simp [Set.indicator, hz, hsq]
    · simp [Set.indicator, hz]
  have hdef_int :
      Integrable
        ((productAnnulus j).indicator
          (fun z : CSpace d => rho (nuKappa κ z) (evalHermiteSum κ (localPart j M G) z) ^ 2))
        (gaussianMeasure d) :=
    hmass_int.mono hdef_meas hdef_le_mass
  have hdef0 :
      ENNReal.ofReal (defectAnnulusMass κ j (evalHermiteSum κ (localPart j M G))) =
        ∫⁻ z : CSpace d,
          ENNReal.ofReal
            ((productAnnulus j).indicator
              (fun z => rho (nuKappa κ z) (evalHermiteSum κ (localPart j M G) z) ^ 2) z)
        ∂ gaussianMeasure d := by
    simpa [defectAnnulusMass, Set.indicator] using
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hdef_int
        (ae_of_all _ (by
          intro z
          by_cases hz : z ∈ productAnnulus j
          · simp [hz, sq_nonneg (rho (nuKappa κ z) (evalHermiteSum κ (localPart j M G) z))]
          · simp [hz])))
  have hFdef :
      Measurable (fun z : CSpace d => ENNReal.ofReal
        (rho (nuKappa κ z) (evalHermiteSum κ (localPart j M G) z) ^ 2)) :=
    ENNReal.measurable_ofReal.comp hrho_cont.measurable
  have havg :=
    annulusRotationAveraging (j := j)
      (F := fun z : CSpace d => ENNReal.ofReal
        (rho (nuKappa κ z) (evalHermiteSum κ (localPart j M G) z) ^ 2))
      hFdef
  have hdef_indicator :
      ∫⁻ z : CSpace d,
          ENNReal.ofReal
            ((productAnnulus j).indicator
              (fun z => rho (nuKappa κ z) (evalHermiteSum κ (localPart j M G) z) ^ 2) z)
        ∂ gaussianMeasure d
        =
      ∫⁻ z : CSpace d,
          if z ∈ productAnnulus j then
            ENNReal.ofReal (rho (nuKappa κ z) (evalHermiteSum κ (localPart j M G) z) ^ 2)
          else 0
        ∂ gaussianMeasure d := by
    refine lintegral_congr_ae ?_
    filter_upwards with z
    by_cases hz : z ∈ productAnnulus j <;> simp [Set.indicator, hz]
  calc
    ENNReal.ofReal (defectAnnulusMass κ j (evalHermiteSum κ (localPart j M G)))
      = ∫⁻ z : CSpace d,
          if z ∈ productAnnulus j then
            ∫⁻ t : Circle,
              ENNReal.ofReal
                (rho (nuKappa κ (fun q => (fourier (1 : ℤ) t : ℂ) * z q))
                  (evalHermiteSum κ (localPart j M G)
                    (fun q => (fourier (1 : ℤ) t : ℂ) * z q)) ^ 2)
            ∂ AddCircle.haarAddCircle
          else 0
        ∂ gaussianMeasure d := by
          rw [hdef0, hdef_indicator]
          exact havg.symm
    _ = ∫⁻ z : CSpace d,
          Set.indicator (productAnnulus j)
            (fun z =>
              ENNReal.ofReal
                (circleL2NormSq (fun t : Circle => rho (nuKappa κ z) (localOrbit κ j M G z t)))) z
        ∂ gaussianMeasure d := by
          refine lintegral_congr_ae ?_
          filter_upwards with z
          by_cases hz : z ∈ productAnnulus j
          · simpa [Set.indicator, hz]
              using (localOrbit_defect_lintegral (κ := κ) (j := j) (M := M) (G := G) z)
          · simp [Set.indicator, hz]

private lemma productAnnulusConstantSq_nonneg
    (d M : ℕ) :
    0 ≤ productAnnulusConstantSq d M := by
  unfold productAnnulusConstantSq
  positivity

private lemma lowAnnulus_productAnnulusConstant_bound
    {d : ℕ} (hd : 1 ≤ d) (j : MultiIndex d) (M : ℕ)
    (hj : annulusRadius j < degreeThreshold d M) :
    144 * (degreeWidth j M : ℝ) ≤ productAnnulusConstantSq d M := by
  have hwidth :=
    uniformLowAnnulusWidthBound (hd := hd) (j := j) (M := M) hj
  have hwidthR :
      ((degreeWidth j M : ℕ) : ℝ) ≤ (d * (degreeThreshold d M + M) ^ 2 : ℕ) := by
    exact_mod_cast hwidth
  calc
    144 * (degreeWidth j M : ℝ)
      ≤ 144 * ((d * (degreeThreshold d M + M) ^ 2 : ℕ) : ℝ) := by gcongr
    _ = 144 * (d : ℝ) * (((degreeThreshold d M + M : ℕ) : ℝ) ^ 2) := by
          norm_num
          ring
    _ = productAnnulusConstantSq d M := by
          unfold productAnnulusConstantSq
          ring

private lemma highAnnulus_productAnnulusConstant_bound
    {d : ℕ} (hd : 1 ≤ d) (M : ℕ) :
    32 ≤ productAnnulusConstantSq d M := by
  have hd_pos : 0 < d := Nat.succ_le_iff.mp hd
  have hodd_pos : 0 < 2 * M + 1 := by omega
  have hprod_pos : 0 < 120 * d * (2 * M + 1) :=
    Nat.mul_pos (Nat.mul_pos (by decide) hd_pos) hodd_pos
  have hprod_le : 1 ≤ 120 * d * (2 * M + 1) := Nat.succ_le_iff.mpr hprod_pos
  have hdeg_nat : 1 ≤ degreeThreshold d M + M := by
    unfold degreeThreshold
    omega
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdegR : (1 : ℝ) ≤ ((degreeThreshold d M + M : ℕ) : ℝ) := by exact_mod_cast hdeg_nat
  have hsquareR : (1 : ℝ) ≤ (((degreeThreshold d M + M : ℕ) : ℝ) ^ 2) := by nlinarith
  calc
    32 ≤ 144 * (1 : ℝ) * (1 : ℝ) := by norm_num
    _ ≤ 144 * (d : ℝ) * (((degreeThreshold d M + M : ℕ) : ℝ) ^ 2) := by nlinarith
    _ = productAnnulusConstantSq d M := by
      unfold productAnnulusConstantSq
      ring

private lemma localOrbit_pointwise_estimate
    {d : ℕ} (hd : 1 ≤ d) (κ : MultiIndex d) (M : ℕ) (j : MultiIndex d)
    (G : FiniteHermiteSum d) (horth : hermiteInnerNu κ G = 0)
    (z : CSpace d) :
    circleL2NormSq (localOrbit κ j M G z) ≤
      productAnnulusConstantSq d M *
        circleL2NormSq (fun t : Circle => rho (nuKappa κ z) (localOrbit κ j M G z t)) := by
  by_cases hlow : annulusRadius j < degreeThreshold d M
  · have hbase :=
      scaledPositiveFrequencyCircleEstimate (a := nuKappa κ z)
        (E := localDegreeSet j M G)
        (P := localOrbit κ j M G z)
        (localDegreeSet_pos (κ := κ) (j := j) (M := M) (G := G) horth)
        (localOrbit_hasPositiveFrequencySupport (κ := κ) (j := j) (M := M) (G := G) z)
    have hcard :
        144 * ((localDegreeSet j M G).card : ℝ) ≤ productAnnulusConstantSq d M := by
      have hcard_le : ((localDegreeSet j M G).card : ℝ) ≤ degreeWidth j M := by
        exact_mod_cast localDegreeSet_card_le_degreeWidth (j := j) (M := M) (G := G)
      have hconst := lowAnnulus_productAnnulusConstant_bound (hd := hd) (j := j) (M := M) hlow
      nlinarith
    have hnonneg :
        0 ≤ circleL2NormSq (fun t : Circle => rho (nuKappa κ z) (localOrbit κ j M G z t)) := by
      unfold circleL2NormSq
      exact integral_nonneg fun t => sq_nonneg _
    calc
      circleL2NormSq (localOrbit κ j M G z)
        ≤ 144 * ((localDegreeSet j M G).card : ℝ) *
            circleL2NormSq (fun t : Circle => rho (nuKappa κ z) (localOrbit κ j M G z t)) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using hbase
      _ ≤ productAnnulusConstantSq d M *
            circleL2NormSq (fun t : Circle => rho (nuKappa κ z) (localOrbit κ j M G z t)) := by
              gcongr
  · have hhigh : degreeThreshold d M ≤ annulusRadius j := Nat.le_of_not_lt hlow
    have hgap := highFrequencyThreshold (hd := hd) (j := j) (M := M) hhigh
    have hbase :=
      scaledHighFrequencyBandEstimate (a := nuKappa κ z)
        (N := degreeIntervalLower j M) (L := degreeWidth j M)
        (P := localOrbit κ j M G z) hgap
        (localOrbit_hasBandlimitedSupport (κ := κ) (j := j) (M := M) (G := G) z)
    have hconst : 32 ≤ productAnnulusConstantSq d M :=
      highAnnulus_productAnnulusConstant_bound (hd := hd) (M := M)
    have hnonneg :
        0 ≤ circleL2NormSq (fun t : Circle => rho (nuKappa κ z) (localOrbit κ j M G z t)) := by
      unfold circleL2NormSq
      exact integral_nonneg fun t => sq_nonneg _
    calc
      circleL2NormSq (localOrbit κ j M G z)
        ≤ 32 * circleL2NormSq (fun t : Circle => rho (nuKappa κ z) (localOrbit κ j M G z t)) := by
            simpa using hbase
      _ ≤ productAnnulusConstantSq d M *
            circleL2NormSq (fun t : Circle => rho (nuKappa κ z) (localOrbit κ j M G z t)) := by
            gcongr

/-- Annulus-local circle estimate for the local window. -/
theorem productAnnulusEstimate
    {d : ℕ} (hd : 1 ≤ d) (κ : MultiIndex d) (M : ℕ) (j : MultiIndex d)
    (G : FiniteHermiteSum d)
    (horth : hermiteInnerNu κ G = 0) :
    annulusMass j (evalHermiteSum κ (localPart j M G)) ≤
      productAnnulusConstantSq d M *
        defectAnnulusMass κ j (evalHermiteSum κ (localPart j M G)) := by
  classical
  let fdef : CSpace d → ENNReal := fun z =>
    Set.indicator (productAnnulus j)
      (fun z =>
        ENNReal.ofReal
          (circleL2NormSq (fun t : Circle => rho (nuKappa κ z) (localOrbit κ j M G z t)))) z
  have hconst_nonneg : 0 ≤ productAnnulusConstantSq d M :=
    productAnnulusConstantSq_nonneg d M
  have hdefMass_nonneg :
      0 ≤ defectAnnulusMass κ j (evalHermiteSum κ (localPart j M G)) := by
    unfold defectAnnulusMass
    exact integral_nonneg fun z => by by_cases hz : z ∈ productAnnulus j <;> simp [hz, sq_nonneg _]
  have hmass := annulusMass_localOrbit_lintegral (κ := κ) (j := j) (M := M) (G := G)
  have hdef := defectAnnulusMass_localOrbit_lintegral (κ := κ) (j := j) (M := M) (G := G)
  have hmainENN :
      ENNReal.ofReal (annulusMass j (evalHermiteSum κ (localPart j M G))) ≤
        ENNReal.ofReal
          (productAnnulusConstantSq d M *
            defectAnnulusMass κ j (evalHermiteSum κ (localPart j M G))) := by
    calc
      ENNReal.ofReal (annulusMass j (evalHermiteSum κ (localPart j M G)))
        = ∫⁻ z : CSpace d,
            Set.indicator (productAnnulus j)
              (fun z => ENNReal.ofReal (circleL2NormSq (localOrbit κ j M G z))) z
          ∂ gaussianMeasure d := hmass
      _ ≤ ∫⁻ z : CSpace d, ENNReal.ofReal (productAnnulusConstantSq d M) * fdef z
          ∂ gaussianMeasure d := by
            refine MeasureTheory.lintegral_mono ?_
            intro z
            by_cases hz : z ∈ productAnnulus j
            · have hpoint :=
                localOrbit_pointwise_estimate
                  (hd := hd) (κ := κ) (M := M) (j := j) (G := G) horth z
              have hpointENN :
                  ENNReal.ofReal (circleL2NormSq (localOrbit κ j M G z)) ≤
                    ENNReal.ofReal (productAnnulusConstantSq d M) *
                      ENNReal.ofReal
                        (circleL2NormSq (fun t : Circle =>
                          rho (nuKappa κ z) (localOrbit κ j M G z t))) := by
                rw [← ENNReal.ofReal_mul hconst_nonneg]
                exact ENNReal.ofReal_le_ofReal hpoint
              simpa [fdef, Set.indicator, hz] using hpointENN
            · simp [fdef, Set.indicator, hz]
      _ = ENNReal.ofReal (productAnnulusConstantSq d M) *
            ∫⁻ z : CSpace d, fdef z ∂ gaussianMeasure d := by
              simpa [fdef] using
                (MeasureTheory.lintegral_const_mul'
                  (μ := gaussianMeasure d)
                  (r := ENNReal.ofReal (productAnnulusConstantSq d M))
                  (f := fdef)
                  (by simp))
      _ = ENNReal.ofReal (productAnnulusConstantSq d M) *
            ENNReal.ofReal (defectAnnulusMass κ j (evalHermiteSum κ (localPart j M G))) := by
              rw [← hdef]
      _ = ENNReal.ofReal
            (productAnnulusConstantSq d M *
              defectAnnulusMass κ j (evalHermiteSum κ (localPart j M G))) := by
              rw [ENNReal.ofReal_mul hconst_nonneg]
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hconst_nonneg hdefMass_nonneg)).mp hmainENN

end Hermite1DimdLEAN
