/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.LabelSumBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.LinearWaveBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.SignedCovariance

/-!
# Uniform primary weights and curl estimates

A single enumeration of the joint band/label index transfers the existing
weighted analysis without losing any inverse-edge factors.  The reindexed
strip retains the same domain, edge distance, and vanishing weight.  Every
constant is chosen before both the original band and the label.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.UniformPrimaryWeights

open Set Function Filter WeightedClasses LabelSumBounds
open scoped ContDiff Topology BigOperators

variable {ι E F G : Type*} {D : Type}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Only the discrete scales are reindexed. The spatial edge geometry and
its possibly vanishing weight are exactly the original ones. -/
noncomputable def reindexedStrip (s : StripData D) (e : ℕ → ℕ × ι) : StripData D where
  domain := s.domain
  isOpen_domain := s.isOpen_domain
  epsilon k := s.epsilon (e k).1
  epsilon_pos k := s.epsilon_pos (e k).1
  epsilon_le_one k := s.epsilon_le_one (e k).1
  slow k := s.slow (e k).1
  one_le_slow k := s.one_le_slow (e k).1
  delta := s.delta
  delta_pos := s.delta_pos
  zeta := s.zeta
  zeta_smooth := s.zeta_smooth
  zeta_nonneg := s.zeta_nonneg

/-- Pull, defined pointwise by `f (e k).2 (e k).1`. -/
noncomputable def pull (e : ℕ → ℕ × ι) (f : ι → ℕ → D → E) : ℕ → D → E :=
  fun k => f (e k).2 (e k).1

@[simp] theorem reindexed_growth (s : StripData D) (e : ℕ → ℕ × ι) (k : ℕ) (x : D) :
    (reindexedStrip s e).growth k x = s.growth (e k).1 x := rfl

@[simp] theorem reindexed_majorant (s : StripData D) (e : ℕ → ℕ × ι)
    (w : ι → ℕ → D → ℝ) (α C : ℝ) (p k : ℕ) (x : D) :
    majorant (reindexedStrip s e) (pull e w) α C p k x =
      majorant s (w (e k).2) α C p (e k).1 x := rfl

theorem pull_class {s : StripData D} {w : ι → ℕ → D → ℝ} {α : ℝ}
    {f : ι → ℕ → D → E} (hf : UniformClass s w α f) (e : ℕ → ℕ × ι) :
    MemClass (reindexedStrip s e) (pull e w) α (pull e f) := by
  refine ⟨fun k => hf.weight_nonneg (e k).2 (e k).1,
    fun k => hf.smooth (e k).2 (e k).1, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  exact ⟨C, hC, p, fun k => hb (e k).2 (e k).1⟩

/-- Surjectivity is the reason the constants also control every original
label. It is never replaced by a separate bound for each label. -/
theorem uniform_of_pull {s : StripData D} {w : ι → ℕ → D → ℝ} {α : ℝ}
    {f : ι → ℕ → D → E} {e : ℕ → ℕ × ι} (he : Surjective e)
    (hf : MemClass (reindexedStrip s e) (pull e w) α (pull e f)) :
    UniformClass s w α f := by
  refine ⟨?_, ?_, ?_⟩
  · intro l n x hx
    obtain ⟨k, hk⟩ := he (n, l)
    simpa only [pull, hk] using hf.weight_nonneg k x hx
  · intro l n
    obtain ⟨k, hk⟩ := he (n, l)
    have h := hf.smooth k
    simp only [pull, hk] at h
    exact h
  · intro m
    obtain ⟨C, hC, p, hb⟩ := hf.bounds m
    refine ⟨C, hC, p, fun l n x hx j hj => ?_⟩
    obtain ⟨k, hk⟩ := he (n, l)
    simpa only [reindexed_majorant, pull, hk] using hb k x hx j hj

/-- Enumeration, given by `Classical.choose (exists_surjective_nat (ℕ × ι))`. -/
noncomputable def enumeration (ι : Type*) [Countable ι] [Nonempty ι] : ℕ → ℕ × ι :=
  Classical.choose (exists_surjective_nat (ℕ × ι))

theorem enumeration_surjective (ι : Type*) [Countable ι] [Nonempty ι] :
    Surjective (enumeration ι) := Classical.choose_spec (exists_surjective_nat (ℕ × ι))

/-- The actual slow scale on the joint index, in the `(band,label)` order
used by the phase and ODE constructions. -/
noncomputable def jointDomain (s : StripData D) : PhaseJetBounds.Domain (ℕ × ι) D where
  scale q := s.slow q.1
  carrier _ := s.domain
  isOpen _ := s.isOpen_domain
  one_le_scale q := s.one_le_slow q.1

theorem pull_polynomial {s : StripData D} {f : ι → ℕ → D → E}
    (hf : PhaseJetBounds.PolynomialJets (jointDomain s) (fun q => f q.2 q.1))
    (e : ℕ → ℕ × ι) :
    PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain (reindexedStrip s e)) (pull e f) :=
        by
  refine ⟨fun k => hf.smooth (e k), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bound m
  exact ⟨C, hC, p, fun k => hb (e k)⟩

/-- Restrict genuine joint phase/ODE jets to the common strip, allowing a
uniform polynomial change of slow scale. -/
theorem polynomial_on_joint {s : StripData D}
    {V : PhaseJetBounds.Domain (ℕ × ι) D} {f : (ℕ × ι) → D → E}
    (hf : PhaseJetBounds.PolynomialJets V f) {K : ℝ} {q : ℕ} (hK : 1 ≤ K)
    (hscale : ∀ n l, V.scale (n, l) ≤ K * s.slow n ^ q)
    (hdom : ∀ n l, s.domain ⊆ V.carrier (n, l)) :
    PhaseJetBounds.PolynomialJets (jointDomain s) f := by
  refine ⟨fun k => (hf.smooth k).mono (hdom k.1 k.2), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bound m
  refine ⟨C * K ^ p, one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hK), q * p, ?_⟩
  intro k j hj x hx
  calc
    _ ≤ C * V.scale k ^ p := hb k j hj x (hdom k.1 k.2 hx)
    _ ≤ C * (K * s.slow k.1 ^ q) ^ p := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans (V.one_le_scale k)) (hscale k.1 k.2) p)
      (zero_le_one.trans hC)
    _ = _ := by simp only [jointDomain, mul_pow, ← pow_mul]; ring

/-- This version retains the full inverse-edge polynomial in the
majorant; it is not a polynomial-in-S replacement of the weight. -/
noncomputable def UniformInverseControl (s : StripData D) (w g : ι → ℕ → D → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ l n x, x ∈ s.domain →
    w l n x / g l n x ≤ C * s.growth n x ^ p

theorem pull_inverseControl {s : StripData D} {w g : ι → ℕ → D → ℝ}
    (h : UniformInverseControl s w g) (e : ℕ → ℕ × ι) :
    SignedCovariance.InverseControl (reindexedStrip s e) (pull e w) (pull e g) := by
  obtain ⟨C, hC, p, hb⟩ := h
  exact ⟨C, hC, p, fun k => hb (e k).2 (e k).1⟩

theorem inverseControl_of_lower {s : StripData D} {w g : ι → ℕ → D → ℝ}
    (hg : ∀ l n x, x ∈ s.domain → 0 < g l n x) {c : ℝ} (hc : 0 < c) (p : ℕ)
    (hlower : ∀ l n x, x ∈ s.domain → c * w l n x / s.growth n x ^ p ≤ g l n x) :
    UniformInverseControl s w g := by
  refine ⟨c⁻¹, (inv_pos.mpr hc).le, p, fun l n x hx => ?_⟩
  have hG : 0 < s.growth n x ^ p := pow_pos (zero_lt_one.trans_le (s.one_le_growth n x)) _
  have hl := (div_le_iff₀ hG).mp (hlower l n x hx)
  apply (div_le_iff₀ (hg l n x hx)).mpr
  calc
    w l n x = c⁻¹ * (c * w l n x) := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    _ ≤ c⁻¹ * (g l n x * s.growth n x ^ p) := mul_le_mul_of_nonneg_left hl (inv_pos.mpr hc).le
    _ = _ := by ring

section WeightedOperations

variable [Countable ι] [Nonempty ι]
  {s : StripData D} {w g r : ι → ℕ → D → ℝ} {β : ℝ}

/-- Positivity is pointwise on the open strip. There is no positive
minimum of the weight, even when it vanishes at the boundary. -/
theorem sqrt_class (hw : ∀ l n x, x ∈ s.domain → 0 < w l n x)
    (hp : ∀ l n x, x ∈ s.domain → 0 < g l n x)
    (hg : UniformClass s w 0 g) (hlower : UniformInverseControl s w g) :
    UniformClass s (fun l n x => Real.sqrt (w l n x)) 0 (fun l n x => Real.sqrt (g l n x)) := by
  apply uniform_of_pull (enumeration_surjective ι)
  exact SignedCovariance.sqrt_class
    (fun k => hw (enumeration ι k).2 (enumeration ι k).1)
    (fun k => hp (enumeration ι k).2 (enumeration ι k).1)
    (pull_class hg (enumeration ι)) (pull_inverseControl hlower (enumeration ι))

theorem signed_quotient_class (hw : ∀ l n x, x ∈ s.domain → 0 < w l n x)
    (hp : ∀ l n x, x ∈ s.domain → 0 < g l n x)
    (hg : UniformClass s w 0 g) (hr : UniformClass s w β r)
    (hlower : UniformInverseControl s w g) :
    UniformClass s (fun l n x => Real.sqrt (w l n x)) β
      (fun l n x => r l n x / (2 * Real.sqrt (g l n x))) := by
  apply uniform_of_pull (enumeration_surjective ι)
  exact SignedCovariance.signed_quotient_class
    (fun k => hw (enumeration ι k).2 (enumeration ι k).1)
    (fun k => hp (enumeration ι k).2 (enumeration ι k).1)
    (pull_class hg (enumeration ι)) (pull_class hr (enumeration ι))
    (pull_inverseControl hlower (enumeration ι))

end WeightedOperations

section Calculus

variable {s : StripData D} {w v : ι → ℕ → D → ℝ} {α β : ℝ}

theorem fderiv_class {f : ι → ℕ → D → E} (hf : UniformClass s w α f) :
    UniformClass s w α (fun l n => fderiv ℝ (f l n)) := by
  refine ⟨hf.weight_nonneg, fun l n =>
    (contDiffOn_infty_iff_fderiv_of_isOpen s.isOpen_domain).mp (hf.smooth l n) |>.2, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds (m + 1)
  refine ⟨C, hC, p, fun l n x hx j hj => ?_⟩
  rw [norm_iteratedFDeriv_fderiv]
  exact hb l n x hx (j + 1) (Nat.add_le_add_right hj 1)

theorem smul_class {a : ι → ℕ → D → ℝ} {f : ι → ℕ → D → E}
    (ha : UniformClass s v β a) (hf : UniformClass s w α f) :
    UniformClass s (fun l n x => v l n x * w l n x) (β + α)
      (fun l n x => a l n x • f l n x) :=
  ha.bilinear hf (ContinuousLinearMap.lsmul ℝ ℝ)

theorem mul_class {a b : ι → ℕ → D → ℝ}
    (ha : UniformClass s w α a) (hb : UniformClass s v β b) :
    UniformClass s (fun l n x => w l n x * v l n x) (α + β)
      (fun l n x => a l n x * b l n x) := by
  simpa only [smul_eq_mul] using smul_class ha hb

theorem real_smul_class {a : ι → ℕ → D → ℝ} {f : ι → ℕ → D → E}
    (ha : UniformClass s (fun _ _ _ => 1) β a) (hf : UniformClass s w α f) :
    UniformClass s w (β + α) (fun l n x => a l n x • f l n x) := by
  simpa only [one_mul] using smul_class ha hf

theorem along_class {V : ι → ℕ → D → D} {f : ι → ℕ → D → E}
    (hV : UniformClass s (fun _ _ _ => 1) β V) (hf : UniformClass s w α f) :
    UniformClass s w (α + β) (fun l n => HarmonicCalculus.along (V l n) (f l n)) := by
  have h := (fderiv_class hf).bilinear hV (ContinuousLinearMap.apply ℝ E).flip
  simp only [mul_one] at h ⊢
  exact h

theorem class_of_single {w : ℕ → D → ℝ} {f : ℕ → D → E} (hf : MemClass s w α f) :
    UniformClass s (fun _ : ι => w) α (fun _ : ι => f) := by
  refine ⟨fun _ => hf.weight_nonneg, fun _ => hf.smooth, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  exact ⟨C, hC, p, fun _ => hb⟩

/-- Uniform band bound, given by `∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ l n, ‖a l n‖ ≤ C * s.epsilon n ^ β
* s.slow n ^ p`. -/
noncomputable def UniformBandBound (s : StripData D) (β : ℝ) (a : ι → ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ l n,
    ‖a l n‖ ≤ C * s.epsilon n ^ β * s.slow n ^ p

theorem pull_bandBound {a : ι → ℕ → ℝ} (ha : UniformBandBound s β a)
    (e : ℕ → ℕ × ι) : BandBound (reindexedStrip s e) β (fun k => a (e k).2 (e k).1) := by
  obtain ⟨C, hC, p, hb⟩ := ha
  exact ⟨C, hC, p, fun k => hb (e k).2 (e k).1⟩

theorem band_smul_class [Countable ι] [Nonempty ι]
    {a : ι → ℕ → ℝ} {f : ι → ℕ → D → E}
    (hf : UniformClass s w α f) (ha : UniformBandBound s β a) :
    UniformClass s w (α + β) (fun l n x => a l n • f l n x) := by
  apply uniform_of_pull (enumeration_surjective ι)
  exact (pull_class hf (enumeration ι)).band_smul (pull_bandBound ha (enumeration ι))

theorem polynomial_class {f : ι → ℕ → D → E}
    (hf : PhaseJetBounds.PolynomialJets (jointDomain s) (fun q => f q.2 q.1)) :
    UniformClass s (fun _ _ _ => 1) 0 f := by
  exact LabelSumBounds.uniformClass_of_polynomialJets hf (K := 1) (q := 1) le_rfl
    (fun n l => by simp [jointDomain]) (fun _ _ => subset_rfl)

end Calculus

section Covariance

variable [Countable ι] [Nonempty ι]
  {s : StripData D} {r : ι → ℕ → ℝ}
  {H : ι → ℕ → D → SmoothCovariance.Mat2}
  {T : ι → ℕ → D → SmoothCovariance.Vec2} {w : ι → ℕ → D → ℝ}

/-- The inverse matrix is differentiated after reindexing the genuine
integrated entries. The determinant gap and entry bound are common to
all labels; the target retains its full vanishing weight. -/
theorem covariance_weights_class
    (hr : PhaseJetBounds.PolynomialJets (jointDomain s) (fun q _ => r q.2 q.1))
    (hrne : ∀ l n, r l n ≠ 0)
    (hH : ∀ i j, PhaseJetBounds.PolynomialJets (jointDomain s) (fun q x => H q.2 q.1 x i j))
    (hT : ∀ i, UniformClass s w 0 (fun l n x => T l n x i))
    {b M : ℝ} (hb : 0 < b) (hM : 1 ≤ M)
    (hdet : ∀ l n x, x ∈ s.domain → b ≤ |(PrimaryPulseBounds.normalizedMatrix (r l n) (H l n
        x)).det|)
    (hentry : ∀ l n x, x ∈ s.domain → ∀ i j, |r l n * H l n x i j| ≤ M)
    (j : Fin 2) :
    UniformClass s w 0 (fun l n x => SmoothCovariance.weights (H l n x) (T l n x) j) := by
  apply uniform_of_pull (enumeration_surjective ι)
  exact PrimaryPulseBounds.covariance_weights_class
    (s := reindexedStrip s (enumeration ι))
    (r := fun k => r (enumeration ι k).2 (enumeration ι k).1)
    (H := pull (enumeration ι) H) (T := pull (enumeration ι) T) (w := pull (enumeration ι) w)
    (pull_polynomial (f := fun l n _ => r l n) hr (enumeration ι))
    (fun k => hrne (enumeration ι k).2 (enumeration ι k).1)
    (fun i j => pull_polynomial (f := fun l n x => H l n x i j) (hH i j) (enumeration ι))
    (fun i => pull_class (hT i) (enumeration ι)) hb hM
    (fun k => hdet (enumeration ι k).2 (enumeration ι k).1)
    (fun k => hentry (enumeration ι k).2 (enumeration ι k).1) j

theorem covariance_amplitudes_class
    (hr : PhaseJetBounds.PolynomialJets (jointDomain s) (fun q _ => r q.2 q.1))
    (hrne : ∀ l n, r l n ≠ 0)
    (hH : ∀ i j, PhaseJetBounds.PolynomialJets (jointDomain s) (fun q x => H q.2 q.1 x i j))
    (hT : ∀ i, UniformClass s w 0 (fun l n x => T l n x i))
    {b M c : ℝ} (hb : 0 < b) (hM : 1 ≤ M) (hc : 0 < c)
    (hdet : ∀ l n x, x ∈ s.domain → b ≤ |(PrimaryPulseBounds.normalizedMatrix (r l n) (H l n
        x)).det|)
    (hentry : ∀ l n x, x ∈ s.domain → ∀ i j, |r l n * H l n x i j| ≤ M)
    (hw : ∀ l n x, x ∈ s.domain → 0 < w l n x)
    (hlower : ∀ l n x, x ∈ s.domain → ∀ j,
      c * w l n x ≤ SmoothCovariance.weights (H l n x) (T l n x) j)
    (j : Fin 2) :
    UniformClass s (fun l n x => Real.sqrt (w l n x)) 0
      (fun l n x => SmoothCovariance.amplitudes (H l n x) (T l n x) j) := by
  apply uniform_of_pull (enumeration_surjective ι)
  exact PrimaryPulseBounds.covariance_amplitudes_class
    (s := reindexedStrip s (enumeration ι))
    (r := fun k => r (enumeration ι k).2 (enumeration ι k).1)
    (H := pull (enumeration ι) H) (T := pull (enumeration ι) T) (w := pull (enumeration ι) w)
    (pull_polynomial (f := fun l n _ => r l n) hr (enumeration ι))
    (fun k => hrne (enumeration ι k).2 (enumeration ι k).1)
    (fun i j => pull_polynomial (f := fun l n x => H l n x i j) (hH i j) (enumeration ι))
    (fun i => pull_class (hT i) (enumeration ι)) hb hM hc
    (fun k => hdet (enumeration ι k).2 (enumeration ι k).1)
    (fun k => hentry (enumeration ι k).2 (enumeration ι k).1)
    (fun k => hw (enumeration ι k).2 (enumeration ι k).1)
    (fun k => hlower (enumeration ι k).2 (enumeration ι k).1) j

end Covariance

/-- The exact normalization used by the primary covariance. -/
theorem sqrt_slow_polynomial (s : StripData D) :
    PhaseJetBounds.PolynomialJets (jointDomain (ι := ι) s) (fun q _ => Real.sqrt (s.slow q.1)) := by
  apply PhaseJetBounds.PolynomialJets.const _ (C := 1) (m := 1) le_rfl
  intro q
  have hs := s.one_le_slow q.1
  have hsq := Real.sq_sqrt (zero_le_one.trans hs)
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), one_mul, pow_one, jointDomain]
  nlinarith [Real.sqrt_nonneg (s.slow q.1)]

section Primary

variable [Countable ι] [Nonempty ι] {s : StripData D}
  {P : ι → ℕ → D → ℝ} {H : ι → ℕ → D → SmoothCovariance.Mat2}
  {T : ι → ℕ → D → SmoothCovariance.Vec2}
  {mask : ι → ℕ → D → ℝ} {v : ι → ℕ → D → ProblemStatement.Space}

theorem primaryCoefficient_waveClass
    (hH : ∀ i j, PhaseJetBounds.PolynomialJets (jointDomain s) (fun q x => H q.2 q.1 x i j))
    (hT : ∀ i, UniformMeanClass s 0 (fun l n x => T l n x i))
    (hmask : UniformClass s (fun _ _ _ => 1) 0 mask)
    (hv : UniformClass s P 0 v)
    {b M c : ℝ} (hb : 0 < b) (hM : 1 ≤ M) (hc : 0 < c)
    (hdet : ∀ l n x, x ∈ s.domain →
      b ≤ |(PrimaryPulseBounds.normalizedMatrix (Real.sqrt (s.slow n)) (H l n x)).det|)
    (hentry : ∀ l n x, x ∈ s.domain → ∀ i j, |Real.sqrt (s.slow n) * H l n x i j| ≤ M)
    (hζ : ∀ x, x ∈ s.domain → 0 < s.zeta x)
    (hlower : ∀ l n x, x ∈ s.domain → ∀ j,
      c * s.zeta x ≤ SmoothCovariance.weights (H l n x) (T l n x) j)
    (j : Fin 2) :
    UniformWaveClass s P (1 / 2)
      (fun l => PrimaryPulseBounds.primaryCoefficient s (H l) (T l) (mask l) (v l) j) := by
  have ha := covariance_amplitudes_class (sqrt_slow_polynomial s)
    (fun _ n => (Real.sqrt_pos.mpr (zero_lt_one.trans_le (s.one_le_slow n))).ne')
    hH hT hb hM hc hdet hentry (fun _ _ x hx => hζ x hx) hlower j
  have ham : UniformWaveClass s P 0 (fun l n x =>
      SmoothCovariance.amplitudes (H l n x) (T l n x) j • CurlClassBounds.complexify (v l n x)) :=
          by
    simpa only [zero_add] using smul_class ha (hv.map CurlClassBounds.complexify)
  have hm : UniformWaveClass s P 0 (fun l n x => mask l n x •
      (SmoothCovariance.amplitudes (H l n x) (T l n x) j • CurlClassBounds.complexify (v l n x)))
          := by
    simpa only [zero_add] using real_smul_class hmask ham
  have he : UniformBandBound (ι := ι) s (1 / 2) (fun _ n => Real.sqrt (s.epsilon n)) := by
    refine ⟨1, zero_le_one, 0, fun l n => ?_⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg (s.epsilon n)), Real.sqrt_eq_rpow]
    simp only [pow_zero, mul_one, one_mul, le_refl]
  apply (show UniformWaveClass s P (1 / 2) (fun l n x => Real.sqrt (s.epsilon n) •
    (mask l n x • (SmoothCovariance.amplitudes (H l n x) (T l n x) j •
      CurlClassBounds.complexify (v l n x)))) from by
          simpa only [zero_add] using band_smul_class hm he).congr
  intro l n x hx
  simp only [PrimaryPulseBounds.primaryCoefficient, PartitionedCovariance.amplitude, smul_smul]
  congr 1
  ring

end Primary

section Curl

open CurlClassBounds

variable {s : StripData D} {w : ι → ℕ → D → ℝ} {α κ : ℝ}

theorem component_class {a : ι → ℕ → D → ComplexVector}
    (ha : UniformClass s w α a) (i : Fin 3) :
    UniformClass s w α (fun l n x => a l n x i) := ha.map (ContinuousLinearMap.proj i)

theorem vector_class {a : ι → ℕ → D → ComplexVector}
    (ha : ∀ i : Fin 3, UniformClass s w α (fun l n x => a l n x i)) :
    UniformClass s w α a := by
  have hsum := UniformClass.sum Finset.univ
    (fun i l n x => (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i) (a l n x i))
    (ha 0).weight_nonneg (fun i _ => (ha i).map (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ)
        i))
  apply hsum.congr
  intro l n x hx
  ext i
  simp

/-- The normal inverse is computed from the actual jointly bounded normal,
not supplied as a separately bounded potential coefficient. -/
theorem normalCoefficient_class [Countable ι] [Nonempty ι]
    {N : ι → ℕ → D → RealVector} {a : ι → ℕ → D → ComplexVector}
    (hN : PhaseJetBounds.PolynomialJets (jointDomain s) (fun q => N q.2 q.1))
    (ha : UniformClass s w α a) {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ l n x, x ∈ s.domain → b ≤ ‖N l n x‖)
    (hupper : ∀ l n x, x ∈ s.domain → ‖N l n x‖ ≤ M) :
    UniformClass s w α (fun l n x => normalCoefficient (N l n x) (a l n x)) := by
  apply uniform_of_pull (enumeration_surjective ι)
  exact CurlClassBounds.normalCoefficient_class (s := reindexedStrip s (enumeration ι))
    (pull_polynomial hN (enumeration ι)) (pull_class ha (enumeration ι)) hb
    (fun k => hlower (enumeration ι k).2 (enumeration ι k).1)
    (fun k => hupper (enumeration ι k).2 (enumeration ι k).1)

/-- This version permits radius and direction fields to vary with both
band and label. All cylindrical connection terms are retained. -/
theorem cylindricalCurl_class
    {R : ι → ℕ → D → ℝ} {Vr Vθ Vz : ι → ℕ → D → D}
    {a : ι → ℕ → D → ComplexVector} (ha : UniformClass s w α a) (hκ : 0 ≤ κ)
    (hr : UniformClass s (fun _ _ _ => 1) (-κ) Vr)
    (hθ : UniformClass s (fun _ _ _ => 1) 0 Vθ)
    (hz : UniformClass s (fun _ _ _ => 1) 1 Vz)
    (hR : UniformClass s (fun _ _ _ => 1) 0 (fun l n x => (R l n x)⁻¹)) :
    UniformClass s w (α - κ)
      (fun l n => cylindricalCurl (R l n) (Vr l n) (Vθ l n) (Vz l n) (a l n)) := by
  have hDr (i : Fin 3) : UniformClass s w (α - κ)
      (fun l n => HarmonicCalculus.along (Vr l n) (fun x => a l n x i)) := by
    simpa only [sub_eq_add_neg] using along_class hr (component_class ha i)
  have hDz (i : Fin 3) : UniformClass s w (α - κ)
      (fun l n => HarmonicCalculus.along (Vz l n) (fun x => a l n x i)) :=
    (along_class hz (component_class ha i)).mono_exponent (by linarith)
  have hDθ (i : Fin 3) : UniformClass s w (α - κ)
      (fun l n x => (R l n x)⁻¹ • HarmonicCalculus.along (Vθ l n) (fun y => a l n y i) x) := by
    apply (real_smul_class hR (along_class hθ (component_class ha i))).mono_exponent
    linarith
  have hconn (i : Fin 3) : UniformClass s w (α - κ) (fun l n x => (R l n x)⁻¹ • a l n x i) :=
    (real_smul_class hR (component_class ha i)).mono_exponent (by linarith)
  apply vector_class
  intro i
  fin_cases i
  · exact (hDθ 2).sub (hDz 1)
  · exact (hDz 0).sub (hDr 2)
  · exact ((hDr 1).add (hconn 1)).sub (hDθ 0)

theorem curlRemainder_class [Countable ι] [Nonempty ι]
    {R : ι → ℕ → D → ℝ} {Vr Vθ Vz : ι → ℕ → D → D} {K : ι → ℕ → ℝ}
    {a : ι → ℕ → D → ComplexVector} (ha : UniformClass s w α a) (hκ : 0 ≤ κ)
    (hr : UniformClass s (fun _ _ _ => 1) (-κ) Vr)
    (hθ : UniformClass s (fun _ _ _ => 1) 0 Vθ)
    (hz : UniformClass s (fun _ _ _ => 1) 1 Vz)
    (hR : UniformClass s (fun _ _ _ => 1) 0 (fun l n x => (R l n x)⁻¹))
    (hK : UniformBandBound s (1 / 2) (fun l n => 1 / K l n)) :
    UniformClass s w (α + 1 / 2 - κ)
      (fun l n => curlRemainder (K l n) (R l n) (Vr l n) (Vθ l n) (Vz l n) (a l n)) := by
  have hc := (cylindricalCurl_class ha hκ hr hθ hz hR).map
    (Complex.I • ContinuousLinearMap.id ℝ ComplexVector)
  have hh := band_smul_class hc hK
  simp only [ _root_.smul_apply, ContinuousLinearMap.id_apply,
    show α - κ + 1 / 2 = α + 1 / 2 - κ by ring] at hh ⊢
  exact hh

theorem normalCurlRemainder_class [Countable ι] [Nonempty ι]
    {R : ι → ℕ → D → ℝ} {Vr Vθ Vz : ι → ℕ → D → D} {K : ι → ℕ → ℝ}
    {N : ι → ℕ → D → RealVector} {a : ι → ℕ → D → ComplexVector}
    (hN : PhaseJetBounds.PolynomialJets (jointDomain s) (fun q => N q.2 q.1))
    (ha : UniformClass s w α a) {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ l n x, x ∈ s.domain → b ≤ ‖N l n x‖)
    (hupper : ∀ l n x, x ∈ s.domain → ‖N l n x‖ ≤ M)
    (hκ : 0 ≤ κ)
    (hr : UniformClass s (fun _ _ _ => 1) (-κ) Vr)
    (hθ : UniformClass s (fun _ _ _ => 1) 0 Vθ)
    (hz : UniformClass s (fun _ _ _ => 1) 1 Vz)
    (hR : UniformClass s (fun _ _ _ => 1) 0 (fun l n x => (R l n x)⁻¹))
    (hK : UniformBandBound s (1 / 2) (fun l n => 1 / K l n)) :
    UniformClass s w (α + 1 / 2 - κ) (fun l n =>
      curlRemainder (K l n) (R l n) (Vr l n) (Vθ l n) (Vz l n)
        (fun x => normalCoefficient (N l n x) (a l n x))) :=
  curlRemainder_class (normalCoefficient_class hN ha hb hlower hupper) hκ hr hθ hz hR hK

/-- The half-power frequency gain is uniform even when the nonzero
integer harmonic varies with the label. -/
theorem harmonic_inverse_bandBound (s : StripData D) (j : ι → ℕ → ℤ)
    (hj : ∀ l n, j l n ≠ 0) :
    UniformBandBound s (1 / 2) (fun l n => 1 / (carrierFrequency s n * (j l n : ℝ))) := by
  refine ⟨1, zero_le_one, 0, fun l n => ?_⟩
  have hk := carrierFrequency_pos s n
  have hjabs : (1 : ℝ) ≤ |(j l n : ℝ)| := by exact_mod_cast Int.one_le_abs (hj l n)
  have hden : carrierFrequency s n ≤ carrierFrequency s n * |(j l n : ℝ)| :=
    le_mul_of_one_le_right hk.le hjabs
  simp only [Real.norm_eq_abs, abs_div, abs_one, abs_mul, abs_of_pos hk, pow_zero, mul_one, one_mul]
  calc
    1 / (carrierFrequency s n * |(j l n : ℝ)|) ≤ 1 / carrierFrequency s n :=
      div_le_div_of_nonneg_left zero_le_one hk hden
    _ ≤ Real.sqrt (s.epsilon n) :=
      (Scaling.reciprocal_frequency_bounds (s.epsilon_pos n) (s.epsilon_le_one n)).2
    _ = _ := Real.sqrt_eq_rpow _

end Curl

section ActualPhase

open PrimaryPulseBounds PhaseJetBounds

variable {U : Domain (ℕ × ι) PhaseCalculus.Slow}

/-- The same actual integrated pulse matrix, now indexed jointly by band
and label. Its entries are not independent input functions. -/
noncomputable def phaseMatrix (A : Fin 2 → PhaseConstruction U)
    (pref : Fin 2 → (ℕ × ι) → ℝ) (χ : (ℕ × ι) → D → PhaseCalculus.Slow × ℝ) :
    ι → ℕ → D → SmoothCovariance.Mat2 := fun l n x =>
  primaryCovariance pref (fun j => (A j).frame) (fun j => (A j).lam)
    (fun j => (A j).u) (fun j => (A j).L) (n, l) (χ (n, l) x).1

/-- Phase fundamental, defined pointwise by `normalizedPulse ((A j).frame (n, l)) ((A j).lam (n,
l)) ((A j).u (n, l)) ((A j).L (n, l)) (χ (n, l) x)`. -/
noncomputable def phaseFundamental (A : Fin 2 → PhaseConstruction U)
    (χ : (ℕ × ι) → D → PhaseCalculus.Slow × ℝ) (j : Fin 2) :
    ι → ℕ → D → ProblemStatement.Space := fun l n x =>
  normalizedPulse ((A j).frame (n, l)) ((A j).lam (n, l)) ((A j).u (n, l))
    ((A j).L (n, l)) (χ (n, l) x)

/-- Phase envelope, defined pointwise by `referenceP ((A j).lam (n, l)) ((A j).u (n, l)) ((A
j).L (n, l)) ((A j).L (n, l) * (χ (n, l) x).2)`. -/
noncomputable def phaseEnvelope (A : Fin 2 → PhaseConstruction U)
    (χ : (ℕ × ι) → D → PhaseCalculus.Slow × ℝ) (j : Fin 2) : ι → ℕ → D → ℝ := fun l n x =>
  referenceP ((A j).lam (n, l)) ((A j).u (n, l)) ((A j).L (n, l))
    ((A j).L (n, l) * (χ (n, l) x).2)

/-- Phase cutoff fundamental, defined pointwise by `cutoffPulse ((A j).frame (n, l)) ((A j).lam
(n, l)) ((A j).u (n, l)) ((A j).L (n, l)) (χ (n, l) x)`. -/
noncomputable def phaseCutoffFundamental (A : Fin 2 → PhaseConstruction U)
    (χ : (ℕ × ι) → D → PhaseCalculus.Slow × ℝ) (j : Fin 2) :
    ι → ℕ → D → ProblemStatement.Space := fun l n x =>
  cutoffPulse ((A j).frame (n, l)) ((A j).lam (n, l)) ((A j).u (n, l))
    ((A j).L (n, l)) (χ (n, l) x)

/-- Phase slot envelope, defined pointwise by `GaussianTailFlat.referenceSlotEnvelope ((A j).lam
(n, l)) ((A j).u (n, l)) ((A j).L (n, l)) (χ (n, l) x).2`. -/
noncomputable def phaseSlotEnvelope (A : Fin 2 → PhaseConstruction U)
    (χ : (ℕ × ι) → D → PhaseCalculus.Slow × ℝ) (j : Fin 2) : ι → ℕ → D → ℝ := fun l n x =>
  GaussianTailFlat.referenceSlotEnvelope ((A j).lam (n, l)) ((A j).u (n, l))
    ((A j).L (n, l)) (χ (n, l) x).2

/-- The matrix jets come from the actual parameter-dependent ODE and
its actual middle-cutoff covariance integral, uniformly in both indices. -/
theorem phaseMatrix_jets {s : StripData D} (A : Fin 2 → PhaseConstruction U)
    (pref : Fin 2 → (ℕ × ι) → ℝ) (χ : (ℕ × ι) → D → PhaseCalculus.Slow × ℝ)
    (hscale : ∀ q, U.scale q = s.slow q.1)
    (hχ : PolynomialJets (jointDomain s) χ)
    (hmap : ∀ q x, x ∈ s.domain → (χ q x).1 ∈ U.carrier q)
    (hpref : ∀ j, PolynomialJets U (fun q _ => pref j q)) (i j : Fin 2) :
    PolynomialJets (jointDomain s) (fun q x => phaseMatrix A pref χ q.2 q.1 x i j) := by
  apply ((EnvelopeJets.of_polynomial
    (primaryCovariance_entry_polynomial U pref (fun j => (A j).frame)
      (fun j => (A j).lam) (fun j => (A j).u) (fun j => (A j).L) hpref
      (fun j => (A j).pulse_jets) (fun j => (A j).lam_pos) (fun j => (A j).u_pos)
      (fun j => (A j).L_pos) i j)).comp
        (hχ.clm (ContinuousLinearMap.fst ℝ PhaseCalculus.Slow ℝ)) hscale hmap).to_polynomial
  intro q x hx
  rfl

theorem phaseFundamental_class {s : StripData D} (A : Fin 2 → PhaseConstruction U)
    (χ : (ℕ × ι) → D → PhaseCalculus.Slow × ℝ)
    (hscale : ∀ q, U.scale q = s.slow q.1)
    (hχ : PolynomialJets (jointDomain s) χ)
    (hmap : ∀ q x, x ∈ s.domain → χ q x ∈ U.carrier q ×ˢ Ioo (0 : ℝ) 1)
    (j : Fin 2) : UniformClass s (phaseEnvelope A χ j) 0 (phaseFundamental A χ j) := by
  have hp := (A j).pulse_jets.comp hχ hscale hmap
  apply LabelSumBounds.uniformClass_of_envelopeJets hp (K := 1) (q := 1) le_rfl
    (fun n l => by simp [jointDomain]) (fun _ _ => subset_rfl)
  · intro l n x hx
    exact hp.nonneg (n, l) x hx
  · intro l n x hx
    simp only [Real.rpow_zero, one_mul]
    rfl

/-- The actual smooth cutoff extension is controlled by the original
Gaussian slot envelope, including its zero region. -/
theorem phaseCutoffFundamental_class {s : StripData D} (A : Fin 2 → PhaseConstruction U)
    (χ : (ℕ × ι) → D → PhaseCalculus.Slow × ℝ)
    (hscale : ∀ q, U.scale q = s.slow q.1)
    (hχ : PolynomialJets (jointDomain s) χ)
    (hmap : ∀ q x, x ∈ s.domain → (χ q x).1 ∈ U.carrier q)
    (j : Fin 2) : UniformClass s (phaseSlotEnvelope A χ j) 0 (phaseCutoffFundamental A χ j) := by
  have hp := (cutoffPulse_envelope_jets U (A j).frame (A j).lam (A j).u (A j).L (A
      j).pulse_jets).comp
    hχ hscale (fun q x hx => ⟨hmap q x hx, mem_univ _⟩)
  apply LabelSumBounds.uniformClass_of_envelopeJets hp (K := 1) (q := 1) le_rfl
    (fun n l => by simp [jointDomain]) (fun _ _ => subset_rfl)
  · intro l n x hx
    exact hp.nonneg (n, l) x hx
  · intro l n x hx
    simp only [Real.rpow_zero, one_mul]
    rfl

/-- Normal derivatives and the separated range are derived from the same
joint phase data. The phase chart uses its actual unnormalized slot variable. -/
theorem phaseNormal_jets {s : StripData D} (A : PhaseConstruction U)
    (χ : (ℕ × ι) → D → PhaseCalculus.Slow × ℝ)
    (hscale : ∀ q, U.scale q = s.slow q.1)
    (hχ : PolynomialJets (jointDomain s) χ)
    (hmap : ∀ q x, x ∈ s.domain → χ q x ∈ (U.slot A.V A.openV).carrier q) :
    PolynomialJets (jointDomain s) (fun q x => A.phase.normal q (χ q x)) ∧
      (∀ q x, x ∈ s.domain → A.b ≤ ‖A.phase.normal q (χ q x)‖) ∧
      (∀ q x, x ∈ s.domain → ‖A.phase.normal q (χ q x)‖ ≤ A.M ^ 2 + 3 * A.M) := by
  refine ⟨?_, fun q x hx => A.normal_range.1 q _ (hmap q x hx),
    fun q x hx => A.normal_range.2 q _ (hmap q x hx)⟩
  apply ((EnvelopeJets.of_polynomial A.normal_jets).comp hχ hscale hmap).to_polynomial
  intro q x hx
  rfl

/-- Uniform primary class from the actual joint phase/ODE construction.
Only order-zero covariance separation and target data remain explicit. -/
theorem phase_primary_waveClass [Countable ι] [Nonempty ι] {s : StripData D}
    (A : Fin 2 → PhaseConstruction U) (pref : Fin 2 → (ℕ × ι) → ℝ)
    (χ : (ℕ × ι) → D → PhaseCalculus.Slow × ℝ)
    (T : ι → ℕ → D → SmoothCovariance.Vec2) (mask : ι → ℕ → D → ℝ)
    (hscale : ∀ q, U.scale q = s.slow q.1)
    (hχ : PolynomialJets (jointDomain s) χ)
    (hmap : ∀ q x, x ∈ s.domain → χ q x ∈ U.carrier q ×ˢ Ioo (0 : ℝ) 1)
    (hpref : ∀ j, PolynomialJets U (fun q _ => pref j q))
    (hT : ∀ i, UniformMeanClass s 0 (fun l n x => T l n x i))
    (hmask : UniformClass s (fun _ _ _ => 1) 0 mask)
    {b M c : ℝ} (hb : 0 < b) (hM : 1 ≤ M) (hc : 0 < c)
    (hdet : ∀ l n x, x ∈ s.domain →
      b ≤ |(normalizedMatrix (Real.sqrt (s.slow n)) (phaseMatrix A pref χ l n x)).det|)
    (hentry : ∀ l n x, x ∈ s.domain → ∀ i j,
      |Real.sqrt (s.slow n) * phaseMatrix A pref χ l n x i j| ≤ M)
    (hζ : ∀ x, x ∈ s.domain → 0 < s.zeta x)
    (hlower : ∀ l n x, x ∈ s.domain → ∀ j,
      c * s.zeta x ≤ SmoothCovariance.weights (phaseMatrix A pref χ l n x) (T l n x) j)
    (j : Fin 2) :
    UniformWaveClass s (phaseEnvelope A χ j) (1 / 2)
      (fun l => primaryCoefficient s (phaseMatrix A pref χ l) (T l) (mask l) (phaseFundamental A χ
          j l) j) :=
  primaryCoefficient_waveClass (phaseMatrix_jets A pref χ hscale hχ (fun q x hx => (hmap q x hx).1)
      hpref)
    hT hmask (phaseFundamental_class A χ hscale hχ hmap j) hb hM hc hdet hentry hζ hlower j

end ActualPhase

/-- Direct binding to the actual externally-cut `LinearWaveBounds`
coefficient. The cutoff occurs exactly once and every geometric class is
uniform in the label. -/
theorem cut_curl_class [Countable ι] [Nonempty ι]
    {s : StripData D} {P : ι → ℕ → D → ℝ} {α κ : ℝ}
    (a : ι → LinearWaveBounds.WaveCoefficients D)
    (d : ι → LinearWaveBounds.GraphDirections D) (ψ : ι → ℕ → D → ℝ)
    (ha : UniformWaveClass s P α (fun l => (a l).amplitude))
    (hψ : UniformClass s (fun _ _ _ => 1) 0 ψ)
    (hN : PhaseJetBounds.PolynomialJets (jointDomain s)
      (fun q => (a q.2).normal s (d q.2) q.1))
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ l n x, x ∈ s.domain → b ≤ ‖(a l).normal s (d l) n x‖)
    (hupper : ∀ l n x, x ∈ s.domain → ‖(a l).normal s (d l) n x‖ ≤ M)
    (hκ : 0 ≤ κ)
    (hr : UniformClass s (fun _ _ _ => 1) (-κ) (fun l => (d l).radialField))
    (hθ : UniformClass s (fun _ _ _ => 1) 0 (fun l _ _ => (d l).angular))
    (hz : UniformClass s (fun _ _ _ => 1) 1 (fun l => (d l).axialField s))
    (hR : UniformClass s (fun _ _ _ => 1) 0 (fun l n x => ((a l).radius n x)⁻¹))
    (hK : UniformBandBound s (1 / 2) (fun l n => 1 / (a l).frequency n)) :
    UniformWaveClass s P (α + 1 / 2 - κ)
      (fun l => ((a l).withCutoff (ψ l)).curlCorrection s (d l)) := by
  have hcut : UniformWaveClass s P α (fun l n x => ψ l n x • (a l).amplitude n x) := by
    simpa only [zero_add] using real_smul_class hψ ha
  have h := normalCurlRemainder_class hN hcut hb hlower hupper hκ hr hθ hz hR hK
  simp only [
    LinearWaveBounds.WaveCoefficients.withCutoff,
    LinearWaveBounds.WaveCoefficients.normal] at h ⊢
  exact h

section ActualCutoff

open PrimaryPulseBounds PhaseJetBounds

variable {U : Domain (ℕ × ι) PhaseCalculus.Slow}

/-- The Gaussian profile appears once in the actual coefficient. -/
theorem phase_cutoff_coefficient_eq (s : StripData D)
    (A : Fin 2 → PhaseConstruction U) (pref : Fin 2 → (ℕ × ι) → ℝ)
    (χ : (ℕ × ι) → D → PhaseCalculus.Slow × ℝ)
    (T : ι → ℕ → D → SmoothCovariance.Vec2) (mask : ι → ℕ → D → ℝ)
    (j : Fin 2) (l : ι) (n : ℕ) (x : D) :
    primaryCoefficient s (phaseMatrix A pref χ l) (T l) (mask l)
      (phaseCutoffFundamental A χ j l) j n x =
    GaussianTailFlat.profile (χ (n, l) x).2 •
      primaryCoefficient s (phaseMatrix A pref χ l) (T l) (mask l)
        (phaseFundamental A χ j l) j n x := by
  simp only [primaryCoefficient, phaseCutoffFundamental, phaseFundamental, cutoffPulse,
    map_smul, smul_smul, mul_comm]

/-- Global slot-cutoff primary estimate: the actual cutoff extension and
its Gaussian envelope both vanish outside the slot. The edge weight is
still exactly `sqrt zeta`. -/
theorem phase_cutoff_primary_waveClass [Countable ι] [Nonempty ι] {s : StripData D}
    (A : Fin 2 → PhaseConstruction U) (pref : Fin 2 → (ℕ × ι) → ℝ)
    (χ : (ℕ × ι) → D → PhaseCalculus.Slow × ℝ)
    (T : ι → ℕ → D → SmoothCovariance.Vec2) (mask : ι → ℕ → D → ℝ)
    (hscale : ∀ q, U.scale q = s.slow q.1)
    (hχ : PolynomialJets (jointDomain s) χ)
    (hmap : ∀ q x, x ∈ s.domain → (χ q x).1 ∈ U.carrier q)
    (hpref : ∀ j, PolynomialJets U (fun q _ => pref j q))
    (hT : ∀ i, UniformMeanClass s 0 (fun l n x => T l n x i))
    (hmask : UniformClass s (fun _ _ _ => 1) 0 mask)
    {b M c : ℝ} (hb : 0 < b) (hM : 1 ≤ M) (hc : 0 < c)
    (hdet : ∀ l n x, x ∈ s.domain →
      b ≤ |(normalizedMatrix (Real.sqrt (s.slow n)) (phaseMatrix A pref χ l n x)).det|)
    (hentry : ∀ l n x, x ∈ s.domain → ∀ i j,
      |Real.sqrt (s.slow n) * phaseMatrix A pref χ l n x i j| ≤ M)
    (hζ : ∀ x, x ∈ s.domain → 0 < s.zeta x)
    (hlower : ∀ l n x, x ∈ s.domain → ∀ j,
      c * s.zeta x ≤ SmoothCovariance.weights (phaseMatrix A pref χ l n x) (T l n x) j)
    (j : Fin 2) :
    UniformWaveClass s (phaseSlotEnvelope A χ j) (1 / 2)
      (fun l => primaryCoefficient s (phaseMatrix A pref χ l) (T l) (mask l)
        (phaseCutoffFundamental A χ j l) j) :=
  primaryCoefficient_waveClass (phaseMatrix_jets A pref χ hscale hχ hmap hpref)
    hT hmask (phaseCutoffFundamental_class A χ hscale hχ hmap j)
    hb hM hc hdet hentry hζ hlower j

end ActualCutoff

/-- Apply this directly to `a.withCutoff` when the stronger Gaussian
slot-envelope bound has already been derived for its actual amplitude. -/
theorem curlCorrection_class [Countable ι] [Nonempty ι]
    {s : StripData D} {P : ι → ℕ → D → ℝ} {α κ : ℝ}
    (a : ι → LinearWaveBounds.WaveCoefficients D)
    (d : ι → LinearWaveBounds.GraphDirections D)
    (ha : UniformWaveClass s P α (fun l => (a l).amplitude))
    (hN : PhaseJetBounds.PolynomialJets (jointDomain s)
      (fun q => (a q.2).normal s (d q.2) q.1))
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ l n x, x ∈ s.domain → b ≤ ‖(a l).normal s (d l) n x‖)
    (hupper : ∀ l n x, x ∈ s.domain → ‖(a l).normal s (d l) n x‖ ≤ M)
    (hκ : 0 ≤ κ)
    (hr : UniformClass s (fun _ _ _ => 1) (-κ) (fun l => (d l).radialField))
    (hθ : UniformClass s (fun _ _ _ => 1) 0 (fun l _ _ => (d l).angular))
    (hz : UniformClass s (fun _ _ _ => 1) 1 (fun l => (d l).axialField s))
    (hR : UniformClass s (fun _ _ _ => 1) 0 (fun l n x => ((a l).radius n x)⁻¹))
    (hK : UniformBandBound s (1 / 2) (fun l n => 1 / (a l).frequency n)) :
    UniformWaveClass s P (α + 1 / 2 - κ) (fun l => (a l).curlCorrection s (d l)) := by
  have h := normalCurlRemainder_class hN ha hb hlower hupper hκ hr hθ hz hR hK
  simp only [
    LinearWaveBounds.WaveCoefficients.normal] at h ⊢
  exact h

/-- The primary half-power yields the advertised `1-kappa` curl bound. -/
theorem primary_curl_exponent {s : StripData D} {P : ι → ℕ → D → ℝ} {κ : ℝ}
    {f : ι → ℕ → D → E}
    (hf : UniformWaveClass s P (1 / 2 + 1 / 2 - κ) f) :
    UniformWaveClass s P (1 - κ) f := by
  simpa only [show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num] using hf

theorem primary_curl_budget {s : StripData D} {P : ι → ℕ → D → ℝ} {κ : ℝ}
    {f : ι → ℕ → D → E} (hf : UniformWaveClass s P (1 - κ) f) (hκ : κ ≤ 8 / 25) :
    UniformWaveClass s P (17 / 25) f := hf.mono_exponent (by linarith)

end NavierStokes.UniformPrimaryWeights
