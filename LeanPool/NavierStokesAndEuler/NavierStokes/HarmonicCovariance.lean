/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionState
public import LeanPool.NavierStokesAndEuler.NavierStokes.WaveInteractionBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicResidual

@[expose] public section

/-!
# Covariance of actual finite real harmonic fields

Angular integration is evaluated exactly before applying the weighted product
estimates. Real projection includes both conjugate harmonics. The constants are
uniform over a fixed bound on the harmonic index.
-/

noncomputable section

namespace NavierStokes.HarmonicCovariance

open Set Filter MeasureTheory CorrectionState
open scoped BigOperators ContDiff Topology

section CoefficientCovariance

open HarmonicFields WeightedClasses

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- The zero harmonic of a genuine finite harmonic product has the sum
of its input orders. A common finite set, rather than a support cardinality
bound, makes the estimate uniform in the band. -/
theorem angularProduct_mem {s : StripData D} {P : ℕ → D → ℝ} {α β : ℝ}
    (a b : ℕ → Coefficients D) (F : Finset ℤ)
    (hF : ∀ n, (a n).support ⊆ F)
    (ha : ∀ j ∈ F, WaveClass s P α (fun n x => a n j x))
    (hb : ∀ j ∈ F, WaveClass s P β (fun n x => b n (-j) x))
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1)
    (k : ℕ → ℝ) (phase : ℕ → D → ℝ) (kp : ℕ → ℤ) (hkp : ∀ n, kp n ≠ 0) :
    MeanClass s (α + β) (fun n x => HarmonicFields.angularMean
      (fun θ => field (a n) (k n) (phase n) (kp n) (x, θ) *
        field (b n) (k n) (phase n) (kp n) (x, θ))) := by
  have hsum : MeanClass s (α + β)
      (fun n x => ∑ j ∈ F, a n j x * b n (-j) x) :=
    MemClass.sum F _ (fun _ x hx => s.zeta_nonneg x hx)
      (fun j hj => WaveInteractionBounds.wave_cmul_mean (ha j hj) (hb j hj) hP0 hP1)
  apply WaveInteractionBounds.class_congr hsum
  intro n x _
  dsimp only
  rw [angularMean_product (a n) (b n) (k n) (phase n) (hkp n) x]
  symm
  apply Finset.sum_subset (hF n)
  intro j _ hj
  rw [Finsupp.notMem_support_iff.mp hj]
  simp

end CoefficientCovariance

section RealCoefficientCovariance

open HarmonicFields WeightedClasses

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem realCoefficients_mem {s : StripData D} {P : ℕ → D → ℝ} {α : ℝ}
    (a : ℕ → Coefficients D)
    (ha : ∀ j, WaveClass s P α (fun n x => a n j x)) (j : ℤ) :
    WaveClass s P α (fun n x => HarmonicResidual.realCoefficients (a n) j x) := by
  simp only [HarmonicResidual.realCoefficients_apply]
  exact WaveInteractionBounds.class_const_cmul ((ha j).add (WaveInteractionBounds.class_conj (ha
    (-j))))
    (2 : ℂ)⁻¹

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem realAngularProduct_eq (a b : Coefficients D) (k : ℝ) (Φ : D → ℝ)
    {kp : ℤ} (hkp : kp ≠ 0) (x : D) :
    HarmonicResidual.realAngularMean (fun θ =>
      (field a k Φ kp (x, θ)).re * (field b k Φ kp (x, θ)).re) =
      (HarmonicFields.angularMean (fun θ =>
        field (HarmonicResidual.realCoefficients a) k Φ kp (x, θ) *
        field (HarmonicResidual.realCoefficients b) k Φ kp (x, θ))).re := by
  have hc := HarmonicFields.angularMean_field
    (HarmonicResidual.realCoefficients a * HarmonicResidual.realCoefficients b) k Φ hkp x
  simp only [HarmonicFields.field_mul] at hc
  rw [hc]
  simpa only [HarmonicFields.field_mul, HarmonicResidual.field_realCoefficients,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
    HarmonicResidual.realAngularMean_field
      (HarmonicResidual.realCoefficients a * HarmonicResidual.realCoefficients b) k Φ hkp x

/-- Real angular covariance is estimated from the actual conjugate-pair
coefficients. The harmonic bound is on the index, uniformly in the band. -/
theorem realAngularProduct_mem {s : StripData D} {P : ℕ → D → ℝ} {α β : ℝ}
    (a b : ℕ → Coefficients D) (N : ℕ)
    (hband : ∀ n, BandLimited (a n) N)
    (ha : ∀ j, WaveClass s P α (fun n x => a n j x))
    (hb : ∀ j, WaveClass s P β (fun n x => b n j x))
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1)
    (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ) (hkp : ∀ n, kp n ≠ 0) :
    MeanClass s (α + β) (angularAverage (fun n p =>
      (field (a n) (k n) (Φ n) (kp n) p).re *
        (field (b n) (k n) (Φ n) (kp n) p).re)) := by
  have hF : ∀ n, (HarmonicResidual.realCoefficients (a n)).support ⊆
      Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro n j hj
    have h := HarmonicResidual.band_realCoefficients (hband n) j hj
    simp only [Finset.mem_Icc]
    omega
  have hc := angularProduct_mem
    (fun n => HarmonicResidual.realCoefficients (a n))
    (fun n => HarmonicResidual.realCoefficients (b n))
    (Finset.Icc (-(N : ℤ)) (N : ℤ)) hF
    (fun j _ => realCoefficients_mem a ha j)
    (fun j _ => realCoefficients_mem b hb (-j)) hP0 hP1 k Φ kp hkp
  apply WaveInteractionBounds.class_congr (hc.map Complex.reCLM)
  intro n x _
  exact (realAngularProduct_eq (a n) (b n) (k n) (Φ n) (hkp n) x).symm

theorem blockCovariance_mem {s : StripData D} {P : ℕ → D → ℝ} {α : ℝ}
    (b : HarmonicBlock D) (N : ℕ) (hband : b.BandLimited N)
    (hcoef : ∀ i j, WaveClass s P α (fun n x => b.velocity n i j x))
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1)
    (hkp : ∀ n, b.angularFrequency n ≠ 0) (i j : Fin 3) :
    MeanClass s (α + α) (bilinearCovariance b.oscillation b.oscillation i j) :=
  realAngularProduct_mem (fun n => b.velocity n i) (fun n => b.velocity n j) N
    (fun n => hband.1 n i) (hcoef i) (hcoef j) hP0 hP1
    b.frequency b.phase b.angularFrequency hkp

theorem mixedBlockCovariance_mem {s : StripData D} {P : ℕ → D → ℝ} {α β : ℝ}
    (a b : HarmonicBlock D) (N : ℕ) (hband : a.BandLimited N)
    (hfreq : b.frequency = a.frequency) (hphase : b.phase = a.phase)
    (hangular : b.angularFrequency = a.angularFrequency)
    (ha : ∀ i j, WaveClass s P α (fun n x => a.velocity n i j x))
    (hb : ∀ i j, WaveClass s P β (fun n x => b.velocity n i j x))
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1)
    (hkp : ∀ n, a.angularFrequency n ≠ 0) (i j : Fin 3) :
    MeanClass s (α + β) (bilinearCovariance a.oscillation b.oscillation i j) := by
  simpa only [bilinearCovariance, HarmonicBlock.oscillation, hfreq, hphase, hangular] using
    realAngularProduct_mem (fun n => a.velocity n i) (fun n => b.velocity n j) N
      (fun n => hband.1 n i) (ha i) (hb j) hP0 hP1
      a.frequency a.phase a.angularFrequency hkp

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem angularAverage_add {f g : OscillatoryScalar D}
    (hf : ∀ n x, Continuous (fun θ : ℝ => f n (x, θ)))
    (hg : ∀ n x, Continuous (fun θ : ℝ => g n (x, θ))) :
    angularAverage (f + g) = angularAverage f + angularAverage g := by
  funext n x
  exact HarmonicResidual.realAngularMean_add (hf n x) (hg n x)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem angularProduct_add_error (A B C E : OscillatoryScalar D)
    (hA : ∀ n x, Continuous (fun θ : ℝ => A n (x, θ)))
    (hB : ∀ n x, Continuous (fun θ : ℝ => B n (x, θ)))
    (hC : ∀ n x, Continuous (fun θ : ℝ => C n (x, θ)))
    (hE : ∀ n x, Continuous (fun θ : ℝ => E n (x, θ))) :
    angularAverage ((A + C) * (B + E)) - angularAverage (A * B) =
      angularAverage (A * E) + angularAverage (C * B) + angularAverage (C * E) := by
  have he : (A + C) * (B + E) = A * B + (A * E + C * B + C * E) := by
    funext n p
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  rw [he, angularAverage_add
    (fun n x => (hA n x).mul (hB n x))
    (fun n x => ((hA n x).mul (hE n x)).add ((hC n x).mul (hB n x)) |>.add
      ((hC n x).mul (hE n x))),
    angularAverage_add
      (fun n x => ((hA n x).mul (hE n x)).add ((hC n x).mul (hB n x)))
      (fun n x => (hC n x).mul (hE n x)),
    angularAverage_add
      (fun n x => (hA n x).mul (hE n x))
      (fun n x => (hC n x).mul (hB n x))]
  abel

/-- The error in the actual angular covariance has order `1.5-κ`:
the two primary-curl products and the curl-curl product are all retained. -/
theorem realAngularProduct_curl_error_mem {s : StripData D} {P : ℕ → D → ℝ}
    {κ : ℝ} (hκ : κ ≤ 1 / 2)
    (a b da db : ℕ → Coefficients D) (N : ℕ)
    (hband : ∀ n, BandLimited (a n) N) (hdband : ∀ n, BandLimited (da n) N)
    (ha : ∀ j, WaveClass s P (1 / 2) (fun n x => a n j x))
    (hb : ∀ j, WaveClass s P (1 / 2) (fun n x => b n j x))
    (hda : ∀ j, WaveClass s P (1 - κ) (fun n x => da n j x))
    (hdb : ∀ j, WaveClass s P (1 - κ) (fun n x => db n j x))
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1)
    (k : ℕ → ℝ) (Φ : ℕ → D → ℝ) (kp : ℕ → ℤ) (hkp : ∀ n, kp n ≠ 0) :
    MeanClass s (3 / 2 - κ)
      (angularAverage (fun n p =>
        (field (a n + da n) (k n) (Φ n) (kp n) p).re *
        (field (b n + db n) (k n) (Φ n) (kp n) p).re) -
      angularAverage (fun n p =>
        (field (a n) (k n) (Φ n) (kp n) p).re *
        (field (b n) (k n) (Φ n) (kp n) p).re)) := by
  let A : OscillatoryScalar D := fun n p => (field (a n) (k n) (Φ n) (kp n) p).re
  let B : OscillatoryScalar D := fun n p => (field (b n) (k n) (Φ n) (kp n) p).re
  let C : OscillatoryScalar D := fun n p => (field (da n) (k n) (Φ n) (kp n) p).re
  let E : OscillatoryScalar D := fun n p => (field (db n) (k n) (Φ n) (kp n) p).re
  have hAE : MeanClass s (3 / 2 - κ) (angularAverage (A * E)) := by
    convert! realAngularProduct_mem a db N hband ha hdb hP0 hP1 k Φ kp hkp using 1
    ring
  have hCB : MeanClass s (3 / 2 - κ) (angularAverage (C * B)) := by
    convert! realAngularProduct_mem da b N hdband hda hb hP0 hP1 k Φ kp hkp using 1
    ring
  have hCE : MeanClass s (3 / 2 - κ) (angularAverage (C * E)) :=
    (realAngularProduct_mem da db N hdband hda hdb hP0 hP1 k Φ kp hkp).mono_exponent (by linarith)
  have he := angularProduct_add_error A B C E
    (fun n x => Complex.continuous_re.comp (field_angular_continuous (a n) (k n) (Φ n) (kp n) x))
    (fun n x => Complex.continuous_re.comp (field_angular_continuous (b n) (k n) (Φ n) (kp n) x))
    (fun n x => Complex.continuous_re.comp (field_angular_continuous (da n) (k n) (Φ n) (kp n) x))
    (fun n x => Complex.continuous_re.comp (field_angular_continuous (db n) (k n) (Φ n) (kp n) x))
  have herr : MeanClass s (3 / 2 - κ)
      (angularAverage ((A + C) * (B + E)) - angularAverage (A * B)) := by
    rw [he]
    exact (hAE.add hCB).add hCE
  simp only [A, B, C, E, HarmonicResidual.field_add, Complex.add_re] at herr ⊢
  exact herr

end RealCoefficientCovariance

end NavierStokes.HarmonicCovariance
