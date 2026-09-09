/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.OscillatoryCurl
public import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicCalculus
public import LeanPool.NavierStokesAndEuler.NavierStokes.WeightedClasses
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhaseJetBounds
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Weighted classes of actual cylindrical curl corrections

All differential operators act on the actual coefficient functions. The
oscillatory carrier is removed only after applying the product rule. The
radial graph derivative and every cylindrical connection are retained.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.CurlClassBounds

open Set Filter Function WeightedClasses
open scoped Topology ContDiff BigOperators InnerProductSpace


/-- Real vector: an abbreviation for `ProblemStatement.Space`. -/
abbrev RealVector := ProblemStatement.Space
/-- Complex vector: an abbreviation for `HarmonicCalculus.ComplexVector`. -/
abbrev ComplexVector := HarmonicCalculus.ComplexVector

private theorem nat_le_smooth (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

section Classes

variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {s : StripData D} {w : ℕ → D → ℝ} {α β : ℝ}

theorem class_congr {f g : ℕ → D → E} (hf : MemClass s w α f)
    (hfg : ∀ n, EqOn (f n) (g n) s.domain) : MemClass s w α g := by
  refine ⟨hf.weight_nonneg, fun n => (hf.smooth n).congr (fun x hx => (hfg n hx).symm), ?_⟩
  intro m
  obtain ⟨C, hC, p, hB⟩ := hf.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro n x hx j hj
  have he := iteratedFDerivWithin_congr (𝕜 := ℝ) (hfg n) hx j
  rw [iteratedFDerivWithin_of_isOpen j s.isOpen_domain hx,
    iteratedFDerivWithin_of_isOpen j s.isOpen_domain hx] at he
  rw [← he]
  exact hB n x hx j hj

theorem class_neg {f : ℕ → D → E} (hf : MemClass s w α f) :
    MemClass s w α (fun n x => -f n x) := by
  simpa using hf.map (-ContinuousLinearMap.id ℝ E)

theorem class_sub {f g : ℕ → D → E} (hf : MemClass s w α f) (hg : MemClass s w α g) :
    MemClass s w α (fun n x => f n x - g n x) := by
  simpa only [sub_eq_add_neg] using hf.add (class_neg hg)

theorem class_component {a : ℕ → D → ComplexVector} (ha : MemClass s w α a) (i : Fin 3) :
    MemClass s w α (fun n x => a n x i) := ha.map (ContinuousLinearMap.proj i)

theorem class_vector {a : ℕ → D → ComplexVector}
    (ha : ∀ i : Fin 3, MemClass s w α (fun n x => a n x i)) : MemClass s w α a := by
  have hsum := MemClass.sum (s := s) (w := w) (α := α) Finset.univ
    (fun i n x => (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i) (a n x i))
    (ha 0).weight_nonneg
    (fun i _ => (ha i).map (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i))
  apply class_congr hsum
  intro n x hx
  ext i
  simp

/-- A genuine directional derivative consumes the class of its vector field. -/
theorem class_along {V : ℕ → D → D} {f : ℕ → D → E}
    (hV : UnweightedClass s β V) (hf : MemClass s w α f) :
    MemClass s w (α + β) (fun n => HarmonicCalculus.along (V n) (f n)) := by
  have h := hf.fderiv.bilinear hV (ContinuousLinearMap.apply ℝ E).flip
  simp only [mul_one] at h
  exact h

theorem class_mul_real {r : ℕ → D → ℝ} {f : ℕ → D → E}
    (hr : UnweightedClass s β r) (hf : MemClass s w α f) :
    MemClass s w (β + α) (fun n x => r n x • f n x) := by
  simpa only [one_mul] using hr.smul hf

theorem class_const_complex {f : ℕ → D → ComplexVector} (hf : MemClass s w α f) (c : ℂ) :
    MemClass s w α (fun n x => c • f n x) := by
  simpa using hf.map (c • ContinuousLinearMap.id ℝ ComplexVector)

/-- The phase-jet domain corresponding to the actual strip data. -/
noncomputable def phaseDomain (s : StripData D) : PhaseJetBounds.Domain ℕ D where
  scale := s.slow
  carrier := fun _ => s.domain
  isOpen := fun _ => s.isOpen_domain
  one_le_scale := s.one_le_slow

theorem polynomialJets_unweighted {f : ℕ → D → E}
    (hf : PhaseJetBounds.PolynomialJets (phaseDomain s) f) : UnweightedClass s 0 f := by
  refine ⟨fun _ _ _ => zero_le_one, hf.smooth, ?_⟩
  intro m
  obtain ⟨C, hC, p, hB⟩ := hf.bound m
  refine ⟨C, zero_le_one.trans hC, p, ?_⟩
  intro n x hx j hj
  apply (hB n j hj x hx).trans
  simp only [majorant, Real.rpow_zero, mul_one, phaseDomain]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (zero_le_one.trans (s.one_le_slow n)) (s.slow_le_growth n x) p)
    (zero_le_one.trans hC)

end Classes

/-- Real vectors embedded coordinatewise in the complex coefficient space. -/
noncomputable def complexify : RealVector →L[ℝ] ComplexVector :=
  ContinuousLinearMap.pi (fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i))

@[simp] theorem complexify_apply (a : RealVector) (i : Fin 3) : complexify a i = (a i : ℂ) := rfl

/-- Complex cross linear as an element of `ComplexVector →L[ℝ] ComplexVector →L[ℝ]
ComplexVector`. -/
noncomputable def complexCrossLinear : ComplexVector →L[ℝ] ComplexVector →L[ℝ] ComplexVector :=
  (ContinuousLinearMap.proj 1).smulRight
      ((ContinuousLinearMap.proj 2).smulRight (Pi.single 0 (1 : ℂ))) -
  (ContinuousLinearMap.proj 2).smulRight
      ((ContinuousLinearMap.proj 1).smulRight (Pi.single 0 (1 : ℂ))) +
  (ContinuousLinearMap.proj 2).smulRight
      ((ContinuousLinearMap.proj 0).smulRight (Pi.single 1 (1 : ℂ))) -
  (ContinuousLinearMap.proj 0).smulRight
      ((ContinuousLinearMap.proj 2).smulRight (Pi.single 1 (1 : ℂ))) +
  (ContinuousLinearMap.proj 0).smulRight
      ((ContinuousLinearMap.proj 1).smulRight (Pi.single 2 (1 : ℂ))) -
  (ContinuousLinearMap.proj 1).smulRight
      ((ContinuousLinearMap.proj 0).smulRight (Pi.single 2 (1 : ℂ)))

/-- Normal cross, given by `complexCrossLinear (complexify n) a`. -/
noncomputable def normalCross (n : RealVector) (a : ComplexVector) : ComplexVector :=
  complexCrossLinear (complexify n) a

@[simp] theorem normalCross_zero (n : RealVector) (a : ComplexVector) :
    normalCross n a 0 = (n 1 : ℂ) * a 2 - (n 2 : ℂ) * a 1 := by
  simp [normalCross, complexCrossLinear]

@[simp] theorem normalCross_one (n : RealVector) (a : ComplexVector) :
    normalCross n a 1 = (n 2 : ℂ) * a 0 - (n 0 : ℂ) * a 2 := by
  simp [normalCross, complexCrossLinear]

@[simp] theorem normalCross_two (n : RealVector) (a : ComplexVector) :
    normalCross n a 2 = (n 0 : ℂ) * a 1 - (n 1 : ℂ) * a 0 := by
  simp [normalCross, complexCrossLinear]

theorem normalCross_smul (n : RealVector) (a : ComplexVector) (c : ℂ) :
    normalCross n (c • a) = c • normalCross n a := by
  ext i
  fin_cases i <;> simp [mul_sub] <;> ring

theorem normalCross_real_smul (n : RealVector) (a : ComplexVector) (c : ℝ) :
    normalCross n (c • a) = c • normalCross n a := by simp [normalCross]

theorem normalCross_triple (n : RealVector) (a : ComplexVector) :
    normalCross n (normalCross n a) =
      HarmonicCalculus.normalDot n a • complexify n - (‖n‖ ^ 2) • a := by
  have hn : ‖n‖ ^ 2 = n 0 * n 0 + n 1 * n 1 + n 2 * n 2 := by
    rw [← real_inner_self_eq_norm_sq, OscillatoryCurl.inner_coordinates]
  rw [hn]
  ext i
  fin_cases i <;>
    simp [HarmonicCalculus.normalDot, Complex.real_smul, Complex.ofReal_add,
      Complex.ofReal_mul] <;> ring

/-- The actual coefficient in the vector potential (30). -/
noncomputable def normalCoefficient (n : RealVector) (a : ComplexVector) : ComplexVector :=
  (‖n‖ ^ 2)⁻¹ • normalCross n a

theorem normalCross_normalCoefficient {n : RealVector} {a : ComplexVector}
    (hn : n ≠ 0) (ha : HarmonicCalculus.normalDot n a = 0) :
    normalCross n (normalCoefficient n a) = -a := by
  rw [normalCoefficient, normalCross_real_smul, normalCross_triple, ha, zero_smul,
    zero_sub, smul_neg, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hn)), one_smul]

section Coefficients

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}

/-- The inverse-square normalization is derived from normal jets and a
separated bounded range. It is not an assumed coefficient estimate. -/
theorem normalInverse_unweighted {N : ℕ → D → RealVector}
    (hN : PhaseJetBounds.PolynomialJets (phaseDomain s) N) {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n x, x ∈ s.domain → b ≤ ‖N n x‖)
    (hupper : ∀ n x, x ∈ s.domain → ‖N n x‖ ≤ M) :
    UnweightedClass s 0 (fun n x => (‖N n x‖ ^ 2)⁻¹) := by
  apply polynomialJets_unweighted
  apply hN.norm_sq.inv (b := b ^ 2) (M := M ^ 2) (by positivity)
  · intro n x hx
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ hb.le (norm_nonneg _)).2 (hlower n x hx)
  · intro n x hx
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (hupper n x hx))).2
      (hupper n x hx)

theorem normalCoefficient_class {N : ℕ → D → RealVector} {a : ℕ → D → ComplexVector}
    (hN : PhaseJetBounds.PolynomialJets (phaseDomain s) N) (ha : MemClass s w α a)
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n x, x ∈ s.domain → b ≤ ‖N n x‖)
    (hupper : ∀ n x, x ∈ s.domain → ‖N n x‖ ≤ M) :
    MemClass s w α (fun n x => normalCoefficient (N n x) (a n x)) := by
  have hcross : MemClass s w α (fun n x => normalCross (N n x) (a n x)) := by
    simpa only [one_mul, zero_add, normalCross] using
      ((polynomialJets_unweighted hN).map complexify).bilinear ha complexCrossLinear
  simpa only [zero_add, normalCoefficient] using
    class_mul_real (normalInverse_unweighted hN hb hlower hupper) hcross

end Coefficients

/-- Actual cylindrical curl, including the frame connection in its axial component. -/
noncomputable def cylindricalCurl {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (R : D → ℝ) (Vr Vθ Vz : D → D) (a : D → ComplexVector) (x : D) : ComplexVector :=
  ![(R x)⁻¹ • HarmonicCalculus.along Vθ (fun y => a y 2) x -
      HarmonicCalculus.along Vz (fun y => a y 1) x,
    HarmonicCalculus.along Vz (fun y => a y 0) x -
      HarmonicCalculus.along Vr (fun y => a y 2) x,
    HarmonicCalculus.along Vr (fun y => a y 1) x + (R x)⁻¹ • a x 1 -
      (R x)⁻¹ • HarmonicCalculus.along Vθ (fun y => a y 0) x]

section CurlClass

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {s : StripData D} {w : ℕ → D → ℝ} {α κ : ℝ}
  {R : D → ℝ} {Vr Vθ Vz : ℕ → D → D} {a : ℕ → D → ComplexVector}

theorem cylindricalCurl_class (ha : MemClass s w α a) (hκ : 0 ≤ κ)
    (hr : UnweightedClass s (-κ) Vr) (hθ : UnweightedClass s 0 Vθ)
    (hz : UnweightedClass s 1 Vz) (hR : UnweightedClass s 0 (fun _ x => (R x)⁻¹)) :
    MemClass s w (α - κ) (fun n => cylindricalCurl R (Vr n) (Vθ n) (Vz n) (a n)) := by
  have hDr (i : Fin 3) : MemClass s w (α - κ)
      (fun n => HarmonicCalculus.along (Vr n) (fun x => a n x i)) := by
    simpa only [sub_eq_add_neg] using class_along hr (class_component ha i)
  have hDz (i : Fin 3) : MemClass s w (α - κ)
      (fun n => HarmonicCalculus.along (Vz n) (fun x => a n x i)) :=
    (class_along hz (class_component ha i)).mono_exponent (by linarith)
  have hDθ (i : Fin 3) : MemClass s w (α - κ)
      (fun n x => (R x)⁻¹ • HarmonicCalculus.along (Vθ n) (fun y => a n y i) x) := by
    apply (class_mul_real hR (class_along hθ (class_component ha i))).mono_exponent
    linarith
  have hconn (i : Fin 3) : MemClass s w (α - κ) (fun n x => (R x)⁻¹ • a n x i) :=
    (class_mul_real hR (class_component ha i)).mono_exponent (by linarith)
  apply class_vector
  intro i
  fin_cases i
  · exact class_sub (hDθ 2) (hDz 1)
  · exact class_sub (hDz 0) (hDr 2)
  · exact class_sub ((hDr 1).add (hconn 1)) (hDθ 0)

theorem strippedDivergence_class (ha : MemClass s w α a) (hκ : 0 ≤ κ)
    (hr : UnweightedClass s (-κ) Vr) (hz : UnweightedClass s 1 Vz)
    (hR : UnweightedClass s 0 (fun _ x => (R x)⁻¹)) :
    MemClass s w (α - κ)
      (fun n => HarmonicCalculus.strippedDivergence R (Vr n) (Vz n) (a n)) := by
  have hDr : MemClass s w (α - κ)
      (fun n => HarmonicCalculus.along (Vr n) (fun x => a n x 0)) := by
    simpa only [sub_eq_add_neg] using class_along hr (class_component ha 0)
  have hDz : MemClass s w (α - κ)
      (fun n => HarmonicCalculus.along (Vz n) (fun x => a n x 2)) :=
    (class_along hz (class_component ha 2)).mono_exponent (by linarith)
  have hconn : MemClass s w (α - κ) (fun n x => (R x)⁻¹ • a n x 0) :=
    (class_mul_real hR (class_component ha 0)).mono_exponent (by linarith)
  exact (hDr.add hconn).add hDz

end CurlClass

/-- The inverse frequency is the only band factor in the stripped curl error. -/
noncomputable def curlRemainder {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (K : ℝ) (R : D → ℝ) (Vr Vθ Vz : D → D) (B : D → ComplexVector) (x : D) : ComplexVector :=
  (1 / K) • (Complex.I • cylindricalCurl R Vr Vθ Vz B x)

section RemainderClasses

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {s : StripData D} {w : ℕ → D → ℝ} {α κ : ℝ}
  {R : D → ℝ} {Vr Vθ Vz : ℕ → D → D} {K : ℕ → ℝ}

theorem curlRemainder_class {B : ℕ → D → ComplexVector} (hB : MemClass s w α B)
    (hκ : 0 ≤ κ) (hr : UnweightedClass s (-κ) Vr) (hθ : UnweightedClass s 0 Vθ)
    (hz : UnweightedClass s 1 Vz) (hR : UnweightedClass s 0 (fun _ x => (R x)⁻¹))
    (hK : BandBound s (1 / 2) (fun n => 1 / K n)) :
    MemClass s w (α + 1 / 2 - κ)
      (fun n => curlRemainder (K n) R (Vr n) (Vθ n) (Vz n) (B n)) := by
  have h := (class_const_complex (cylindricalCurl_class hB hκ hr hθ hz hR) Complex.I).band_smul hK
  have he : α - κ + 1 / 2 = α + 1 / 2 - κ := by ring
  simp only [he] at h
  exact h

/-- The all-jet estimate is derived for the actual normalized vector potential. -/
theorem normalCurlRemainder_class {N : ℕ → D → RealVector} {a : ℕ → D → ComplexVector}
    (hN : PhaseJetBounds.PolynomialJets (phaseDomain s) N) (ha : MemClass s w α a)
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n x, x ∈ s.domain → b ≤ ‖N n x‖)
    (hupper : ∀ n x, x ∈ s.domain → ‖N n x‖ ≤ M)
    (hκ : 0 ≤ κ) (hr : UnweightedClass s (-κ) Vr) (hθ : UnweightedClass s 0 Vθ)
    (hz : UnweightedClass s 1 Vz) (hR : UnweightedClass s 0 (fun _ x => (R x)⁻¹))
    (hK : BandBound s (1 / 2) (fun n => 1 / K n)) :
    MemClass s w (α + 1 / 2 - κ) (fun n =>
      curlRemainder (K n) R (Vr n) (Vθ n) (Vz n)
        (fun x => normalCoefficient (N n x) (a n x))) :=
  curlRemainder_class (normalCoefficient_class hN ha hb hlower hupper) hκ hr hθ hz hR hK

/-- Carrier frequency, given by `Scaling.carrierFrequency (s.epsilon n)`. -/
noncomputable def carrierFrequency (s : StripData D) (n : ℕ) : ℝ :=
  Scaling.carrierFrequency (s.epsilon n)

theorem carrierFrequency_pos (s : StripData D) (n : ℕ) : 0 < carrierFrequency s n :=
  Scaling.carrier_frequency_pos (s.epsilon_pos n)

/-- The rounded frequency itself supplies the half-power gain, uniformly in
any nonzero integer harmonic. -/
theorem harmonic_inverse_bandBound (s : StripData D) (j : ℕ → ℤ) (hj : ∀ n, j n ≠ 0) :
    BandBound s (1 / 2) (fun n => 1 / (carrierFrequency s n * (j n : ℝ))) := by
  refine ⟨1, zero_le_one, 0, ?_⟩
  intro n
  have hk := carrierFrequency_pos s n
  have hjabs : (1 : ℝ) ≤ |(j n : ℝ)| := by exact_mod_cast Int.one_le_abs (hj n)
  have hden : carrierFrequency s n ≤ carrierFrequency s n * |(j n : ℝ)| :=
    le_mul_of_one_le_right hk.le hjabs
  simp only [Real.norm_eq_abs, abs_div, abs_one, abs_mul, abs_of_pos hk, pow_zero, mul_one, one_mul]
  calc
    1 / (carrierFrequency s n * |(j n : ℝ)|) ≤ 1 / carrierFrequency s n :=
      div_le_div_of_nonneg_left zero_le_one hk hden
    _ ≤ Real.sqrt (s.epsilon n) :=
      (Scaling.reciprocal_frequency_bounds (s.epsilon_pos n) (s.epsilon_le_one n)).2
    _ = _ := Real.sqrt_eq_rpow _

theorem graphVector_class {ρ : D → ℝ} {M : ℕ → ℝ}
    (hρ : UnweightedClass s 0 (fun _ => ρ)) (hM : BandBound s (-κ) M) (hκ : 0 ≤ κ)
    (e v : D) :
    UnweightedClass s (-κ) (fun n x => e + M n • (ρ x • v)) := by
  have hv : UnweightedClass s 0 (fun _ x => ρ x • v) := by
    have h := hρ.smul (unweighted_const s v)
    simp only [zero_add, one_mul] at h
    exact h
  have hm : UnweightedClass s (-κ) (fun n x => M n • (ρ x • v)) := by
    have h := hv.band_smul hM
    simp only [zero_add] at h
    exact h
  exact ((unweighted_const s e).mono_exponent (by linarith)).add hm

theorem axialVector_class (s : StripData D) (z : D) :
    UnweightedClass s 1 (fun n _ => s.epsilon n • z) := by
  have h := (unweighted_const s z).band_smul (bandBound_rpow s 1)
  simp only [zero_add, Real.rpow_one] at h
  exact h

end RemainderClasses

section CurlIdentities

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem cylindricalCurl_contDiffOn {U : Set D} (hU : IsOpen U) {R : D → ℝ}
    {Vr Vθ Vz : D → D} {B : D → ComplexVector}
    (hR : ContDiffOn ℝ ∞ (fun x => (R x)⁻¹) U)
    (hr : ContDiffOn ℝ ∞ Vr U) (hθ : ContDiffOn ℝ ∞ Vθ U) (hz : ContDiffOn ℝ ∞ Vz U)
    (hB : ContDiffOn ℝ ∞ B U) : ContDiffOn ℝ ∞ (cylindricalCurl R Vr Vθ Vz B) U := by
  have hb := contDiffOn_pi.mp hB
  have hDr i := HarmonicCalculus.contDiffOn_along hU hr (hb i)
  have hDθ i := HarmonicCalculus.contDiffOn_along hU hθ (hb i)
  have hDz i := HarmonicCalculus.contDiffOn_along hU hz (hb i)
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact (hR.smul (hDθ 2)).sub (hDz 1)
  · exact (hDz 0).sub (hDr 2)
  · exact ((hDr 1).add (hR.smul (hb 1))).sub (hR.smul (hDθ 0))

/-- Every coefficient derivative and cylindrical connection survives stripping. -/
theorem cylindricalCurl_vectorMode (R : D → ℝ) (Vr Vθ Vz : D → D) (K : ℝ)
    {Φ : D → ℝ} {B : D → ComplexVector} {x : D}
    (hΦ : DifferentiableAt ℝ Φ x) (hB : ∀ i, DifferentiableAt ℝ (fun y => B y i) x) :
    cylindricalCurl R Vr Vθ Vz (HarmonicCalculus.vectorMode K Φ B) x =
      fun i => (cylindricalCurl R Vr Vθ Vz B x i + HarmonicCalculus.phaseFactor K *
        normalCross (HarmonicCalculus.phaseNormal R Vr Vθ Vz Φ x) (B x) i) *
          HarmonicCalculus.carrier K Φ x := by
  have hD (V : D → D) (i : Fin 3) :
      HarmonicCalculus.along V (fun y => B y i * HarmonicCalculus.carrier K Φ y) x =
        (HarmonicCalculus.along V (fun y => B y i) x +
          HarmonicCalculus.phaseFactor K * Complex.ofReal (HarmonicCalculus.along V Φ x) * B x i) *
            HarmonicCalculus.carrier K Φ x :=
    HarmonicCalculus.along_mode V K hΦ (hB i)
  ext i
  fin_cases i <;>
    simp [cylindricalCurl, HarmonicCalculus.vectorMode, HarmonicCalculus.mode, hD,
      HarmonicCalculus.phaseNormal, Complex.real_smul] <;> ring

theorem cylindricalCurl_const_smul (R : D → ℝ) (Vr Vθ Vz : D → D) (c : ℂ)
    {B : D → ComplexVector} {x : D} (hB : ∀ i, DifferentiableAt ℝ (fun y => B y i) x) :
    cylindricalCurl R Vr Vθ Vz (fun y => c • B y) x = c • cylindricalCurl R Vr Vθ Vz B x := by
  ext i
  fin_cases i <;>
    simp [cylindricalCurl, Pi.smul_apply, smul_eq_mul,
      HarmonicCalculus.along_const_mul _ c (hB 0),
      HarmonicCalculus.along_const_mul _ c (hB 1),
      HarmonicCalculus.along_const_mul _ c (hB 2), Complex.real_smul] <;> ring

end CurlIdentities

section Divergence

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Primitive geometric identities for genuine cylindrical graph directions.
The bracket hypotheses concern derivatives of the direction fields themselves. -/
structure CylindricalGeometry (U : Set D) (R : D → ℝ) (Vr Vθ Vz : D → D) : Prop where
  isOpen : IsOpen U
  radius_smooth : ContDiffOn ℝ ∞ R U
  radius_ne : ∀ x ∈ U, R x ≠ 0
  radial_smooth : ContDiffOn ℝ ∞ Vr U
  angular_smooth : ContDiffOn ℝ ∞ Vθ U
  axial_smooth : ContDiffOn ℝ ∞ Vz U
  radial_radius : ∀ x ∈ U, HarmonicCalculus.along Vr R x = 1
  angular_radius : ∀ x ∈ U, HarmonicCalculus.along Vθ R x = 0
  axial_radius : ∀ x ∈ U, HarmonicCalculus.along Vz R x = 0
  radial_angular : ∀ x ∈ U, fderiv ℝ Vθ x (Vr x) = fderiv ℝ Vr x (Vθ x)
  radial_axial : ∀ x ∈ U, fderiv ℝ Vz x (Vr x) = fderiv ℝ Vr x (Vz x)
  angular_axial : ∀ x ∈ U, fderiv ℝ Vz x (Vθ x) = fderiv ℝ Vθ x (Vz x)

theorem along_commute {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : D → F} {V W : D → D} {x : D} (hf : ContDiffAt ℝ ∞ f x)
    (hV : DifferentiableAt ℝ V x) (hW : DifferentiableAt ℝ W x)
    (hbracket : fderiv ℝ W x (V x) = fderiv ℝ V x (W x)) :
    HarmonicCalculus.along V (HarmonicCalculus.along W f) x =
      HarmonicCalculus.along W (HarmonicCalculus.along V f) x := by
  have hf2 : ContDiffAt ℝ 2 f x := hf.of_le (nat_le_smooth 2)
  have hDF := (hf2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold HarmonicCalculus.along
  rw [fderiv_clm_apply hDF hW, fderiv_clm_apply hDF hV]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  rw [hbracket, (hf2.isSymmSndFDerivAt (by norm_num)).eq (V x) (W x)]

theorem along_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : D → D) {f g : D → F} {x : D}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    HarmonicCalculus.along V (fun y => f y - g y) x =
      HarmonicCalculus.along V f x - HarmonicCalculus.along V g x := by
  simp only [HarmonicCalculus.along, fderiv_fun_sub hf hg, _root_.sub_apply]

theorem along_real_smul (V : D → D) {r : D → ℝ} {f : D → ℂ} {x : D}
    (hr : DifferentiableAt ℝ r x) (hf : DifferentiableAt ℝ f x) :
    HarmonicCalculus.along V (fun y => r y • f y) x =
      HarmonicCalculus.along V r x • f x + r x • HarmonicCalculus.along V f x := by
  simp only [HarmonicCalculus.along, fderiv_fun_smul hr hf, _root_.add_apply,
    _root_.smul_apply, ContinuousLinearMap.smulRight_apply]
  exact add_comm _ _

theorem along_inv (V : D → D) {R : D → ℝ} {x : D}
    (hR : DifferentiableAt ℝ R x) (hne : R x ≠ 0) :
    HarmonicCalculus.along V (fun y => (R y)⁻¹) x =
      (-(R x ^ 2)⁻¹) * HarmonicCalculus.along V R x := by
  have h := (hasDerivAt_inv hne).comp_hasFDerivAt x hR.hasFDerivAt
  dsimp only [Function.comp_def] at h
  unfold HarmonicCalculus.along
  rw [h.fderiv]
  rfl

/-- Divergence of the actual cylindrical curl is zero, including its frame term. -/
theorem divergence_curl_zero {U : Set D} {R : D → ℝ} {Vr Vθ Vz : D → D}
    (G : CylindricalGeometry U R Vr Vθ Vz) {B : D → ComplexVector}
    (hB : ContDiffOn ℝ ∞ B U) {x : D} (hx : x ∈ U) :
    HarmonicCalculus.cylindricalDivergence R Vr Vθ Vz (cylindricalCurl R Vr Vθ Vz B) x = 0 := by
  have hBi := contDiffOn_pi.mp hB
  have hDr i := HarmonicCalculus.contDiffOn_along G.isOpen G.radial_smooth (hBi i)
  have hDθ i := HarmonicCalculus.contDiffOn_along G.isOpen G.angular_smooth (hBi i)
  have hDz i := HarmonicCalculus.contDiffOn_along G.isOpen G.axial_smooth (hBi i)
  have db i := ((hBi i).contDiffAt (G.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have dr i := ((hDr i).contDiffAt (G.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have dθ i := ((hDθ i).contDiffAt (G.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have dz i := ((hDz i).contDiffAt (G.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have dinv := ((G.radius_smooth.inv G.radius_ne).contDiffAt
    (G.isOpen.mem_nhds hx)).differentiableAt (by simp)
  change DifferentiableAt ℝ (fun y => (R y)⁻¹) x at dinv
  have dR := (G.radius_smooth.contDiffAt (G.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have dVr := (G.radial_smooth.contDiffAt (G.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have dVθ := (G.angular_smooth.contDiffAt (G.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have dVz := (G.axial_smooth.contDiffAt (G.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have crθ i := along_commute ((hBi i).contDiffAt (G.isOpen.mem_nhds hx))
    dVr dVθ (G.radial_angular x hx)
  have crz i := along_commute ((hBi i).contDiffAt (G.isOpen.mem_nhds hx))
    dVr dVz (G.radial_axial x hx)
  have cθz i := along_commute ((hBi i).contDiffAt (G.isOpen.mem_nhds hx))
    dVθ dVz (G.angular_axial x hx)
  have hir : HarmonicCalculus.along Vr (fun y => (R y)⁻¹) x = -((R x)⁻¹) ^ 2 := by
    rw [along_inv Vr dR (G.radius_ne x hx), G.radial_radius x hx]
    simp
  have hiz : HarmonicCalculus.along Vz (fun y => (R y)⁻¹) x = 0 := by
    rw [along_inv Vz dR (G.radius_ne x hx), G.axial_radius x hx, mul_zero]
  simp only [HarmonicCalculus.cylindricalDivergence, cylindricalCurl,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]
  rw [along_sub Vr (dinv.fun_smul (dθ 2)) (dz 1),
    along_sub Vθ (dz 0) (dr 2),
    along_sub Vz ((dr 1).fun_add (dinv.fun_smul (db 1))) (dinv.fun_smul (dθ 0)),
    HarmonicCalculus.along_add Vz (dr 1) (dinv.fun_smul (db 1)),
    along_real_smul Vr dinv (dθ 2), along_real_smul Vz dinv (db 1),
    along_real_smul Vz dinv (dθ 0), hir, hiz, crθ 2, crz 1, cθz 0]
  simp only [zero_smul, zero_add, Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_pow]
  ring

end Divergence

section ExplicitGraph

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- Radial field, given by `(1, K x.1 • v)`. -/
noncomputable def radialField (K : ℝ → ℝ) (v : A) (x : ℝ × A) : ℝ × A :=
  (1, K x.1 • v)

theorem radialField_aux_derivative {K : ℝ → ℝ} (v w : A) {x : ℝ × A}
    (hK : DifferentiableAt ℝ K x.1) : fderiv ℝ (radialField K v) x (0, w) = 0 := by
  have hd := (hasFDerivAt_const (1 : ℝ) x).prodMk
    ((hK.hasFDerivAt.comp x hasFDerivAt_fst).smul_const v)
  dsimp only [Function.comp_def] at hd
  change fderiv ℝ (fun y : ℝ × A => (1, K y.1 • v)) x (0, w) = 0
  rw [hd.fderiv]
  simp

/-- Concrete graph directions commute because their radial coefficient only
depends on the radius. No operator commutation is assumed in this constructor. -/
theorem explicitGraph_geometry {U : Set (ℝ × A)} (hU : IsOpen U)
    {K : ℝ → ℝ} (v θ z : A)
    (hK : ∀ x ∈ U, ContDiffAt ℝ ∞ K x.1) (hR : ∀ x ∈ U, x.1 ≠ 0) :
    CylindricalGeometry U Prod.fst (radialField K v)
      (fun _ => (0, θ)) (fun _ => (0, z)) := by
  refine ⟨hU, contDiffOn_fst, hR, ?_, contDiffOn_const, contDiffOn_const,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (contDiffAt_const.prodMk (((hK x hx).comp x contDiffAt_fst).smul
      contDiffAt_const)).contDiffWithinAt
  · intro x hx
    change fderiv ℝ (ContinuousLinearMap.fst ℝ ℝ A) x (1, K x.1 • v) = 1
    rw [ContinuousLinearMap.fderiv]
    rfl
  · intro x hx
    change fderiv ℝ (ContinuousLinearMap.fst ℝ ℝ A) x (0, θ) = 0
    rw [ContinuousLinearMap.fderiv]
    rfl
  · intro x hx
    change fderiv ℝ (ContinuousLinearMap.fst ℝ ℝ A) x (0, z) = 0
    rw [ContinuousLinearMap.fderiv]
    rfl
  · intro x hx
    rw [radialField_aux_derivative v θ ((hK x hx).differentiableAt (by simp))]
    simp
  · intro x hx
    rw [radialField_aux_derivative v z ((hK x hx).differentiableAt (by simp))]
    simp
  · intro x hx
    simp

end ExplicitGraph

section Realization

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem phaseNormal_contDiffOn {U : Set D} {R : D → ℝ} {Vr Vθ Vz : D → D}
    (G : CylindricalGeometry U R Vr Vθ Vz) {Φ : D → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ U) :
    ContDiffOn ℝ ∞ (HarmonicCalculus.phaseNormal R Vr Vθ Vz Φ) U := by
  apply (contDiffOn_piLp 2).mpr
  intro i
  fin_cases i
  · exact HarmonicCalculus.contDiffOn_along G.isOpen G.radial_smooth hΦ
  · exact (HarmonicCalculus.contDiffOn_along G.isOpen G.angular_smooth hΦ).div
      G.radius_smooth G.radius_ne
  · exact HarmonicCalculus.contDiffOn_along G.isOpen G.axial_smooth hΦ

theorem normalCoefficient_contDiffOn {U : Set D} {N : D → RealVector} {a : D → ComplexVector}
    (hN : ContDiffOn ℝ ∞ N U) (ha : ContDiffOn ℝ ∞ a U) (hne : ∀ x ∈ U, N x ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => normalCoefficient (N x) (a x)) U := by
  have hnorm := (contDiff_norm_sq ℝ).comp_contDiffOn hN
  exact (hnorm.inv (fun x hx => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne x hx)))).smul
    (((hN.continuousLinearMap_comp complexify).continuousLinearMap_comp
        complexCrossLinear).clm_apply ha)

/-- Coefficient, given by `normalCoefficient (HarmonicCalculus.phaseNormal R Vr Vθ Vz Φ x) (a
x)`. -/
noncomputable def coefficient (R : D → ℝ) (Vr Vθ Vz : D → D)
    (Φ : D → ℝ) (a : D → ComplexVector) (x : D) : ComplexVector :=
  normalCoefficient (HarmonicCalculus.phaseNormal R Vr Vθ Vz Φ x) (a x)

/-- Inverse carrier, given by `Complex.I / (K : ℂ)`. -/
noncomputable def inverseCarrier (K : ℝ) : ℂ := Complex.I / (K : ℂ)

theorem inverseCarrier_phaseFactor {K : ℝ} (hK : K ≠ 0) :
    inverseCarrier K * HarmonicCalculus.phaseFactor K = -1 := by
  have hk : (K : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hK
  unfold inverseCarrier HarmonicCalculus.phaseFactor
  calc
    Complex.I / (K : ℂ) * ((K : ℂ) * Complex.I) = Complex.I * Complex.I := by
      field_simp
    _ = -1 := Complex.I_mul_I

theorem curlRemainder_eq (K : ℝ) (R : D → ℝ) (Vr Vθ Vz : D → D)
    (B : D → ComplexVector) (x : D) :
    curlRemainder K R Vr Vθ Vz B x = inverseCarrier K • cylindricalCurl R Vr Vθ Vz B x := by
  ext i
  simp [curlRemainder, inverseCarrier, Complex.real_smul, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc]

/-- Vector potential, given by `HarmonicCalculus.vectorMode K Φ (fun x => inverseCarrier K •
coefficient R Vr Vθ Vz Φ a x)`. -/
noncomputable def vectorPotential (K : ℝ) (R : D → ℝ) (Vr Vθ Vz : D → D)
    (Φ : D → ℝ) (a : D → ComplexVector) : D → ComplexVector :=
  HarmonicCalculus.vectorMode K Φ (fun x => inverseCarrier K • coefficient R Vr Vθ Vz Φ a x)

/-- Realized coefficient, given by `a x + curlRemainder K R Vr Vθ Vz (coefficient R Vr Vθ Vz Φ
a) x`. -/
noncomputable def realizedCoefficient (K : ℝ) (R : D → ℝ) (Vr Vθ Vz : D → D)
    (Φ : D → ℝ) (a : D → ComplexVector) (x : D) : ComplexVector :=
  a x + curlRemainder K R Vr Vθ Vz (coefficient R Vr Vθ Vz Φ a) x

theorem vectorPotential_contDiffOn {U : Set D} {R : D → ℝ} {Vr Vθ Vz : D → D}
    (G : CylindricalGeometry U R Vr Vθ Vz) (K : ℝ) {Φ : D → ℝ} {a : D → ComplexVector}
    (hΦ : ContDiffOn ℝ ∞ Φ U) (ha : ContDiffOn ℝ ∞ a U)
    (hn : ∀ x ∈ U, HarmonicCalculus.phaseNormal R Vr Vθ Vz Φ x ≠ 0) :
    ContDiffOn ℝ ∞ (vectorPotential K R Vr Vθ Vz Φ a) U := by
  have hB := normalCoefficient_contDiffOn (phaseNormal_contDiffOn G hΦ) ha hn
  apply contDiffOn_pi.mpr
  intro i
  exact HarmonicCalculus.contDiffOn_mode K hΦ
    ((contDiffOn_pi.mp hB i).const_smul (inverseCarrier K))

/-- Formula (30): the actual curl of the vector potential equals the tangent
harmonic plus exactly the displayed coefficient-derivative remainder. -/
theorem cylindricalCurl_vectorPotential {U : Set D} {R : D → ℝ} {Vr Vθ Vz : D → D}
    (G : CylindricalGeometry U R Vr Vθ Vz) {K : ℝ} (hK : K ≠ 0)
    {Φ : D → ℝ} {a : D → ComplexVector} (hΦ : ContDiffOn ℝ ∞ Φ U) (ha : ContDiffOn ℝ ∞ a U)
    (hn : ∀ x ∈ U, HarmonicCalculus.phaseNormal R Vr Vθ Vz Φ x ≠ 0)
    (ht : ∀ x ∈ U, HarmonicCalculus.normalDot (HarmonicCalculus.phaseNormal R Vr Vθ Vz Φ x) (a x) =
        0)
    {x : D} (hx : x ∈ U) :
    cylindricalCurl R Vr Vθ Vz (vectorPotential K R Vr Vθ Vz Φ a) x =
      HarmonicCalculus.vectorMode K Φ (realizedCoefficient K R Vr Vθ Vz Φ a) x := by
  have hB : ContDiffOn ℝ ∞ (coefficient R Vr Vθ Vz Φ a) U :=
    normalCoefficient_contDiffOn (phaseNormal_contDiffOn G hΦ) ha hn
  have db i := ((contDiffOn_pi.mp hB i).contDiffAt (G.isOpen.mem_nhds hx)).differentiableAt (by
      simp)
  have dΦ := (hΦ.contDiffAt (G.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hcross := normalCross_normalCoefficient (hn x hx) (ht x hx)
  rw [vectorPotential, cylindricalCurl_vectorMode R Vr Vθ Vz K
    (B := fun y => inverseCarrier K • coefficient R Vr Vθ Vz Φ a y) dΦ
    (fun i => (db i).const_smul (inverseCarrier K)),
    cylindricalCurl_const_smul R Vr Vθ Vz (inverseCarrier K) db,
    normalCross_smul]
  change (fun i => ((inverseCarrier K • cylindricalCurl R Vr Vθ Vz (coefficient R Vr Vθ Vz Φ a) x)
      i +
      HarmonicCalculus.phaseFactor K * (inverseCarrier K •
        normalCross (HarmonicCalculus.phaseNormal R Vr Vθ Vz Φ x)
          (normalCoefficient (HarmonicCalculus.phaseNormal R Vr Vθ Vz Φ x) (a x))) i) *
        HarmonicCalculus.carrier K Φ x) = _
  rw [hcross]
  ext i
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul, HarmonicCalculus.vectorMode,
    HarmonicCalculus.mode, realizedCoefficient, Pi.add_apply, curlRemainder_eq]
  have hc : HarmonicCalculus.phaseFactor K * inverseCarrier K = -1 := by
    rw [mul_comm, inverseCarrier_phaseFactor hK]
  calc
    _ = (inverseCarrier K * cylindricalCurl R Vr Vθ Vz (coefficient R Vr Vθ Vz Φ a) x i -
        (HarmonicCalculus.phaseFactor K * inverseCarrier K) * a x i) *
          HarmonicCalculus.carrier K Φ x := by ring
    _ = _ := by rw [hc]; ring

theorem cylindricalDivergence_congr {U : Set D} (hU : IsOpen U) (R : D → ℝ) (Vr Vθ Vz : D → D)
    {a b : D → ComplexVector} (hab : EqOn a b U) {x : D} (hx : x ∈ U) :
    HarmonicCalculus.cylindricalDivergence R Vr Vθ Vz a x =
      HarmonicCalculus.cylindricalDivergence R Vr Vθ Vz b x := by
  have hcomp i : EqOn (fun y => a y i) (fun y => b y i) U :=
    fun y hy => congrFun (hab hy) i
  unfold HarmonicCalculus.cylindricalDivergence
  rw [HarmonicCalculus.along_congr hU (hcomp 0) hx,
    HarmonicCalculus.along_congr hU (hcomp 1) hx,
    HarmonicCalculus.along_congr hU (hcomp 2) hx, hab hx]

theorem realizedCoefficient_divergence {U : Set D} {R : D → ℝ} {Vr Vθ Vz : D → D}
    (G : CylindricalGeometry U R Vr Vθ Vz) {K : ℝ} (hK : K ≠ 0)
    {Φ : D → ℝ} {a : D → ComplexVector} (hΦ : ContDiffOn ℝ ∞ Φ U) (ha : ContDiffOn ℝ ∞ a U)
    (hn : ∀ x ∈ U, HarmonicCalculus.phaseNormal R Vr Vθ Vz Φ x ≠ 0)
    (ht : ∀ x ∈ U, HarmonicCalculus.normalDot (HarmonicCalculus.phaseNormal R Vr Vθ Vz Φ x) (a x) =
        0)
    {x : D} (hx : x ∈ U) :
    HarmonicCalculus.cylindricalDivergence R Vr Vθ Vz
      (HarmonicCalculus.vectorMode K Φ (realizedCoefficient K R Vr Vθ Vz Φ a)) x = 0 := by
  rw [cylindricalDivergence_congr G.isOpen R Vr Vθ Vz
    (fun y hy => (cylindricalCurl_vectorPotential G hK hΦ ha hn ht hy).symm) hx]
  exact divergence_curl_zero G (vectorPotential_contDiffOn G K hΦ ha hn) hx

end Realization

section Longitudinal

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Solving the actual harmonic divergence identity gives the same inverse
carrier as in the curl remainder. This equality includes normal derivatives
when differentiated; there is no pointwise-only estimate here. -/
theorem longitudinal_eq_inverseCarrier (R : D → ℝ) (Vr Vθ Vz : D → D)
    {K : ℝ} (hK : K ≠ 0) {Φ : D → ℝ} {a : D → ComplexVector} {x : D}
    (hΦ : DifferentiableAt ℝ Φ x) (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) x)
    (hθ : HarmonicCalculus.along Vθ (fun y => a y 1) x = 0)
    (hdiv : HarmonicCalculus.cylindricalDivergence R Vr Vθ Vz
      (HarmonicCalculus.vectorMode K Φ a) x = 0) :
    HarmonicCalculus.normalDot (HarmonicCalculus.phaseNormal R Vr Vθ Vz Φ x) (a x) =
      inverseCarrier K * HarmonicCalculus.strippedDivergence R Vr Vz a x := by
  have h := congrArg (fun z : ℂ => inverseCarrier K * z)
    (HarmonicCalculus.longitudinal_identity R Vr Vθ Vz K hΦ ha hθ hdiv)
  rw [← mul_assoc, inverseCarrier_phaseFactor hK] at h
  simpa only [neg_one_mul, mul_neg, neg_inj] using h

variable {s : StripData D} {w : ℕ → D → ℝ} {α κ : ℝ}
  {R : D → ℝ} {Vr Vθ Vz : ℕ → D → D} {K : ℕ → ℝ}
  {Φ : ℕ → D → ℝ} {a : ℕ → D → ComplexVector}

/-- Actual all-order longitudinal contraction bounds from harmonic
solenoidality and primitive coefficient/direction classes. -/
theorem longitudinal_class (ha : MemClass s w α a) (hκ : 0 ≤ κ)
    (hr : UnweightedClass s (-κ) Vr) (hz : UnweightedClass s 1 Vz)
    (hR : UnweightedClass s 0 (fun _ x => (R x)⁻¹))
    (hK : ∀ n, K n ≠ 0) (hfreq : BandBound s (1 / 2) (fun n => 1 / K n))
    (hΦ : ∀ n, DifferentiableOn ℝ (Φ n) s.domain)
    (hθ : ∀ n x, x ∈ s.domain → HarmonicCalculus.along (Vθ n) (fun y => a n y 1) x = 0)
    (hdiv : ∀ n x, x ∈ s.domain → HarmonicCalculus.cylindricalDivergence R
      (Vr n) (Vθ n) (Vz n) (HarmonicCalculus.vectorMode (K n) (Φ n) (a n)) x = 0) :
    MemClass s w (α + 1 / 2 - κ) (fun n x => HarmonicCalculus.normalDot
      (HarmonicCalculus.phaseNormal R (Vr n) (Vθ n) (Vz n) (Φ n) x) (a n x)) := by
  have hS := strippedDivergence_class ha hκ hr hz hR
  have hI := (hS.map (Complex.I • ContinuousLinearMap.id ℝ ℂ)).band_smul hfreq
  have he : α - κ + 1 / 2 = α + 1 / 2 - κ := by ring
  rw [he] at hI
  apply class_congr hI
  intro n x hx
  dsimp only
  rw [longitudinal_eq_inverseCarrier R (Vr n) (Vθ n) (Vz n) (hK n)
    ((hΦ n x hx).differentiableAt (s.isOpen_domain.mem_nhds hx))
    (fun i => ((class_component ha i).contDiffAt n hx 1).differentiableAt (by norm_num))
    (hθ n x hx) (hdiv n x hx)]
  simp [inverseCarrier, Complex.real_smul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- The divergence premise is discharged by a genuine smooth vector
potential. Equality is required on the open strip so all derivatives transfer. -/
theorem longitudinal_from_curl_class (ha : MemClass s w α a) (hκ : 0 ≤ κ)
    (hr : UnweightedClass s (-κ) Vr) (hz : UnweightedClass s 1 Vz)
    (hR : UnweightedClass s 0 (fun _ x => (R x)⁻¹))
    (hK : ∀ n, K n ≠ 0) (hfreq : BandBound s (1 / 2) (fun n => 1 / K n))
    (hΦ : ∀ n, DifferentiableOn ℝ (Φ n) s.domain)
    (hθ : ∀ n x, x ∈ s.domain → HarmonicCalculus.along (Vθ n) (fun y => a n y 1) x = 0)
    (G : ∀ n, CylindricalGeometry s.domain R (Vr n) (Vθ n) (Vz n))
    (A : ℕ → D → ComplexVector) (hA : ∀ n, ContDiffOn ℝ ∞ (A n) s.domain)
    (hreal : ∀ n, EqOn (HarmonicCalculus.vectorMode (K n) (Φ n) (a n))
      (cylindricalCurl R (Vr n) (Vθ n) (Vz n) (A n)) s.domain) :
    MemClass s w (α + 1 / 2 - κ) (fun n x => HarmonicCalculus.normalDot
      (HarmonicCalculus.phaseNormal R (Vr n) (Vθ n) (Vz n) (Φ n) x) (a n x)) := by
  apply longitudinal_class ha hκ hr hz hR hK hfreq hΦ hθ
  intro n x hx
  rw [cylindricalDivergence_congr s.isOpen_domain R (Vr n) (Vθ n) (Vz n) (hreal n) hx]
  exact divergence_curl_zero (G n) (hA n) hx

end Longitudinal

section WaveClasses

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {s : StripData D} {P : ℕ → D → ℝ} {α κ : ℝ}
  {R : D → ℝ} {Vr Vθ Vz : ℕ → D → D} {K : ℕ → ℝ}
  {Φ : ℕ → D → ℝ} {a : ℕ → D → ComplexVector}

/-- Lemma 9.2's curl remainder, with the original wave weight unchanged. -/
theorem curlRemainder_waveClass
    (hN : PhaseJetBounds.PolynomialJets (phaseDomain s)
      (fun n => HarmonicCalculus.phaseNormal R (Vr n) (Vθ n) (Vz n) (Φ n)))
    (ha : WaveClass s P α a) {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n x, x ∈ s.domain → b ≤ ‖HarmonicCalculus.phaseNormal R (Vr n) (Vθ n) (Vz n) (Φ n)
        x‖)
    (hupper : ∀ n x, x ∈ s.domain → ‖HarmonicCalculus.phaseNormal R (Vr n) (Vθ n) (Vz n) (Φ n) x‖ ≤
        M)
    (hκ : 0 ≤ κ) (hr : UnweightedClass s (-κ) Vr) (hθ : UnweightedClass s 0 Vθ)
    (hz : UnweightedClass s 1 Vz) (hR : UnweightedClass s 0 (fun _ x => (R x)⁻¹))
    (hK : BandBound s (1 / 2) (fun n => 1 / K n)) :
    WaveClass s P (α + 1 / 2 - κ) (fun n =>
      curlRemainder (K n) R (Vr n) (Vθ n) (Vz n)
        (coefficient R (Vr n) (Vθ n) (Vz n) (Φ n) (a n))) :=
  normalCurlRemainder_class hN ha hb hlower hupper hκ hr hθ hz hR hK

theorem realizedCoefficient_waveClass
    (hN : PhaseJetBounds.PolynomialJets (phaseDomain s)
      (fun n => HarmonicCalculus.phaseNormal R (Vr n) (Vθ n) (Vz n) (Φ n)))
    (ha : WaveClass s P α a) {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n x, x ∈ s.domain → b ≤ ‖HarmonicCalculus.phaseNormal R (Vr n) (Vθ n) (Vz n) (Φ n)
        x‖)
    (hupper : ∀ n x, x ∈ s.domain → ‖HarmonicCalculus.phaseNormal R (Vr n) (Vθ n) (Vz n) (Φ n) x‖ ≤
        M)
    (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hr : UnweightedClass s (-κ) Vr) (hθ : UnweightedClass s 0 Vθ)
    (hz : UnweightedClass s 1 Vz) (hR : UnweightedClass s 0 (fun _ x => (R x)⁻¹))
    (hK : BandBound s (1 / 2) (fun n => 1 / K n)) :
    WaveClass s P α (fun n => realizedCoefficient (K n) R (Vr n) (Vθ n) (Vz n) (Φ n) (a n)) := by
  have hrem := curlRemainder_waveClass hN ha hb hlower hupper hκ hr hθ hz hR hK
  exact ha.add (hrem.mono_exponent (by linarith))

end WaveClasses

section Support

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem coefficient_tsupport_subset (R : D → ℝ) (Vr Vθ Vz : D → D)
    (Φ : D → ℝ) (a : D → ComplexVector) :
    tsupport (coefficient R Vr Vθ Vz Φ a) ⊆ tsupport a := by
  apply closure_mono
  intro x hx ha
  apply hx
  simp [coefficient, normalCoefficient, normalCross, ha]

theorem cylindricalCurl_tsupport_subset (R : D → ℝ) (Vr Vθ Vz : D → D)
    (B : D → ComplexVector) : tsupport (cylindricalCurl R Vr Vθ Vz B) ⊆ tsupport B := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  have he : B =ᶠ[𝓝 x] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hn
  have hval : B x = 0 := he.eq_of_nhds
  have hderiv (i : Fin 3) : fderiv ℝ (fun y => B y i) x = 0 := by
    have hei : (fun y => B y i) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [he] with y hy
      exact congrFun hy i
    rw [hei.fderiv_eq]
    simp
  apply hx
  ext i
  fin_cases i <;> simp [cylindricalCurl, HarmonicCalculus.along, hderiv, hval]

theorem vectorPotential_tsupport_subset (K : ℝ) (R : D → ℝ) (Vr Vθ Vz : D → D)
    (Φ : D → ℝ) (a : D → ComplexVector) :
    tsupport (vectorPotential K R Vr Vθ Vz Φ a) ⊆ tsupport a := by
  apply closure_mono
  intro x hx ha
  apply hx
  ext i
  simp [vectorPotential, HarmonicCalculus.vectorMode, HarmonicCalculus.mode,
    coefficient, normalCoefficient, normalCross, ha]

theorem realizedWave_tsupport_subset (K : ℝ) (R : D → ℝ) (Vr Vθ Vz : D → D)
    (Φ : D → ℝ) (a : D → ComplexVector) :
    tsupport (cylindricalCurl R Vr Vθ Vz (vectorPotential K R Vr Vθ Vz Φ a)) ⊆ tsupport a :=
  (cylindricalCurl_tsupport_subset R Vr Vθ Vz _).trans
    (vectorPotential_tsupport_subset K R Vr Vθ Vz Φ a)

end Support

section PhysicalCurl

open ProblemStatement

variable {s : StripData SpaceTime} {w : ℕ → SpaceTime → ℝ} {α : ℝ}
  {B : ℕ → VelocityField} {K : ℕ → ℝ}

/-- Direct compatibility with the actual Euclidean spatial curl. All input
jets here are physical spacetime jets, so no separate graph factor occurs. -/
theorem physicalCurl_class (hB : MemClass s w α B) :
    MemClass s w α (fun n => SpatialCurl.spatialCurl (B n)) := by
  apply class_congr (hB.fderiv.map
    (SpatialCurl.curlLinear.comp (ResidualStability.spaceRestriction Space)))
  intro n x hx
  change SpatialCurl.curlLinear (ResidualStability.spaceRestriction Space (fderiv ℝ (B n) x)) =
    SpatialCurl.curlLinear (fderiv ℝ (fun y => B n (x.1, y)) x.2)
  rw [ResidualStability.space_fderiv_eq_full ((hB.contDiffAt n hx 1).differentiableAt (by
      norm_num))]

theorem physical_strippedRemainder_class (hB : MemClass s w α B)
    (hK : BandBound s (1 / 2) (fun n => 1 / K n)) :
    MemClass s w (α + 1 / 2) (fun n => OscillatoryCurl.strippedRemainder (K n) (B n)) :=
  (physicalCurl_class hB).band_smul hK

theorem physical_normalCoefficient_class {N a : ℕ → VelocityField}
    (hN : PhaseJetBounds.PolynomialJets (phaseDomain s) N) (ha : MemClass s w α a)
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n x, x ∈ s.domain → b ≤ ‖N n x‖)
    (hupper : ∀ n x, x ∈ s.domain → ‖N n x‖ ≤ M) :
    MemClass s w α (fun n x => OscillatoryCurl.normalCoefficient (N n x) (a n x)) := by
  have hcross : MemClass s w α (fun n x => OscillatoryCurl.cross (N n x) (a n x)) := by
    simpa only [one_mul, zero_add, OscillatoryCurl.cross] using
      (polynomialJets_unweighted hN).bilinear ha OscillatoryCurl.crossLinear
  simpa only [zero_add, OscillatoryCurl.normalCoefficient] using
    class_mul_real (normalInverse_unweighted hN hb hlower hupper) hcross

/-- The remainder in the existing physical exact-curl theorem belongs to the
claimed class once its actual normal and amplitude jets are supplied. -/
theorem physical_actualRemainder_class {Φ : ℕ → PressureField} {a : ℕ → VelocityField}
    (hN : PhaseJetBounds.PolynomialJets (phaseDomain s) (fun n => OscillatoryCurl.phaseNormal (Φ
        n)))
    (ha : MemClass s w α a) {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n x, x ∈ s.domain → b ≤ ‖OscillatoryCurl.phaseNormal (Φ n) x‖)
    (hupper : ∀ n x, x ∈ s.domain → ‖OscillatoryCurl.phaseNormal (Φ n) x‖ ≤ M)
    (hK : BandBound s (1 / 2) (fun n => 1 / K n)) :
    MemClass s w (α + 1 / 2) (fun n =>
      OscillatoryCurl.strippedRemainder (K n) (OscillatoryCurl.coefficient (Φ n) (a n))) :=
  physical_strippedRemainder_class (physical_normalCoefficient_class hN ha hb hlower hupper) hK

end PhysicalCurl

end NavierStokes.CurlClassBounds
