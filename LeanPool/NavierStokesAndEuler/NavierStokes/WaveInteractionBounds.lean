/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.LinearWaveResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.PartitionedCovariance
public import LeanPool.NavierStokesAndEuler.NavierStokes.CurlClassBounds

/-!
# All-jet bounds for actual nonlinear wave interactions

Only stripped coefficients are placed in the weighted classes. The carrier is
retained in the exact differential identities and is removed before estimating.
-/

@[expose] public section


namespace NavierStokes.WaveInteractionBounds

noncomputable section

open Set Filter WeightedClasses HarmonicCalculus
open scoped ContDiff Topology BigOperators

variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem class_congr {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {f g : ℕ → D → E} (hf : MemClass s w α f)
    (hfg : ∀ n, EqOn (f n) (g n) s.domain) : MemClass s w α g := by
  refine ⟨hf.weight_nonneg, fun n => (hf.smooth n).congr (fun x hx => (hfg n hx).symm), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro n x hx j hj
  have he : f n =ᶠ[𝓝[univ] x] g n := by
    rw [nhdsWithin_univ]
    exact eventually_of_mem (s.isOpen_domain.mem_nhds hx) (hfg n)
  have hjet := he.iteratedFDerivWithin_eq (𝕜 := ℝ) (hfg n hx) j
  simp only [iteratedFDerivWithin_univ] at hjet
  rw [← hjet]
  exact hb n x hx j hj

theorem class_neg {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {f : ℕ → D → E} (hf : MemClass s w α f) :
    MemClass s w α (fun n x => -f n x) := by
  simpa only [_root_.neg_apply, ContinuousLinearMap.id_apply] using
    hf.map (-(ContinuousLinearMap.id ℝ E))

theorem class_sub {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {f g : ℕ → D → E} (hf : MemClass s w α f) (hg : MemClass s w α g) :
    MemClass s w α (fun n x => f n x - g n x) := by
  simpa only [sub_eq_add_neg] using hf.add (class_neg hg)

theorem class_cmul {s : StripData D} {w v : ℕ → D → ℝ} {α β : ℝ}
    {f g : ℕ → D → ℂ} (hf : MemClass s w α f) (hg : MemClass s v β g) :
    MemClass s (fun n x => w n x * v n x) (α + β) (fun n x => f n x * g n x) :=
  hf.bilinear hg (ContinuousLinearMap.mul ℝ ℂ)

theorem class_conj {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {f : ℕ → D → ℂ} (hf : MemClass s w α f) :
    MemClass s w α (fun n x => star (f n x)) :=
  hf.map (Complex.conjCLE : ℂ →L[ℝ] ℂ)

theorem class_const_cmul {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {f : ℕ → D → ℂ} (hf : MemClass s w α f) (c : ℂ) :
    MemClass s w α (fun n x => c * f n x) :=
  hf.map (ContinuousLinearMap.mul ℝ ℂ c)

theorem unweighted_cmul {s : StripData D} {w : ℕ → D → ℝ} {α β : ℝ}
    {f g : ℕ → D → ℂ} (hf : UnweightedClass s α f) (hg : MemClass s w β g) :
    MemClass s w (α + β) (fun n x => f n x * g n x) := by
  simpa only [one_mul] using class_cmul hf hg

theorem mean_wave_cmul {s : StripData D} {P : ℕ → D → ℝ} {α β : ℝ}
    {f g : ℕ → D → ℂ} (hf : MeanClass s α f) (hg : WaveClass s P β g)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1) :
    WaveClass s P (α + β) (fun n x => f n x * g n x) :=
  hf.bilinear_wave hg hζ (ContinuousLinearMap.mul ℝ ℂ)

theorem wave_mean_cmul {s : StripData D} {P : ℕ → D → ℝ} {α β : ℝ}
    {f g : ℕ → D → ℂ} (hf : WaveClass s P α f) (hg : MeanClass s β g)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1) :
    WaveClass s P (α + β) (fun n x => f n x * g n x) := by
  simpa only [add_comm β α, mul_comm] using mean_wave_cmul hg hf hζ

theorem wave_cmul_mean {s : StripData D} {P : ℕ → D → ℝ} {α β : ℝ}
    {f g : ℕ → D → ℂ} (hf : WaveClass s P α f) (hg : WaveClass s P β g)
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) :
    MeanClass s (α + β) (fun n x => f n x * g n x) :=
  hf.bilinear_mean hg hP0 hP1 (ContinuousLinearMap.mul ℝ ℂ)

theorem wave_cmul_wave {s : StripData D} {P : ℕ → D → ℝ} {α β : ℝ}
    {f g : ℕ → D → ℂ} (hf : WaveClass s P α f) (hg : WaveClass s P β g)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1)
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) :
    WaveClass s P (α + β) (fun n x => f n x * g n x) := by
  apply (class_cmul hf hg).mono_weight hf.weight_nonneg
  intro n x hx
  have hs0 := Real.sqrt_nonneg (s.zeta x)
  have hs1 : Real.sqrt (s.zeta x) ≤ 1 := by
    nlinarith [Real.sq_sqrt (s.zeta_nonneg x hx), hζ x hx]
  have hw1 : Real.sqrt (s.zeta x) * P n x ≤ 1 :=
    (mul_le_mul hs1 (hP1 n x hx) (hP0 n x hx) (by norm_num)).trans_eq (one_mul 1)
  exact mul_le_of_le_one_right (hf.weight_nonneg n x hx) hw1

/-- Evaluation of the actual derivative field at an actual vector field. -/
theorem class_along {s : StripData D} {w : ℕ → D → ℝ} {α β : ℝ}
    {f : ℕ → D → E} {V : ℕ → D → D}
    (hf : MemClass s w α f) (hV : UnweightedClass s β V) :
    MemClass s w (α + β) (fun n => along (V n) (f n)) := by
  have h := hV.bilinear hf.fderiv (ContinuousLinearMap.apply ℝ E)
  simp only [one_mul, add_comm β α, ContinuousLinearMap.apply_apply] at h
  exact h

theorem bandBound_const (s : StripData D) (c : ℝ) : BandBound s 0 (fun _ => c) := by
  refine ⟨‖c‖, norm_nonneg c, 0, ?_⟩
  intro n
  simp

/-- Actual geometric coefficient fields, rather than assumed derivative closure. -/
structure Geometry (s : StripData D) (κ : ℝ) where
  /-- Radius of `Geometry`, of type `ℕ → D → ℝ`. -/
  radius : ℕ → D → ℝ
  /-- Radial of `Geometry`, of type `ℕ → D → D`. -/
  radial : ℕ → D → D
  /-- Angular of `Geometry`, of type `ℕ → D → D`. -/
  angular : ℕ → D → D
  /-- Axial of `Geometry`, of type `ℕ → D → D`. -/
  axial : ℕ → D → D
  radius_pos : ∀ n x, x ∈ s.domain → 0 < radius n x
  radial_class : UnweightedClass s (-κ) radial
  axial_class : UnweightedClass s 1 axial
  inverse_radius_class : UnweightedClass s 0 (fun n x => (radius n x)⁻¹)

theorem graph_vector_class {s : StripData D} {κ : ℝ} {M : ℕ → ℝ} {a : D → ℝ}
    (hκ : 0 ≤ κ) (hM : BandBound s (-κ) M)
    (ha : UnweightedClass s 0 (fun _ => a)) (e v : D) :
    UnweightedClass s (-κ) (fun n x => e + M n • (a x • v)) := by
  have he := (unweighted_const s e).mono_exponent (neg_nonpos.mpr hκ)
  have hav : UnweightedClass s 0 (fun _ x => a x • v) := by
    unfold UnweightedClass
    simpa only [one_mul, zero_add] using MemClass.smul ha (unweighted_const s v)
  have hmv : UnweightedClass s (-κ) (fun n x => M n • (a x • v)) := by
    unfold UnweightedClass
    simpa only [zero_add] using hav.band_smul hM
  exact he.add hmv

theorem axial_vector_class (s : StripData D) (v : D) :
    UnweightedClass s 1 (fun n _ => s.epsilon n • v) := by
  unfold UnweightedClass
  simpa only [zero_add, Real.rpow_one] using (unweighted_const s v).band_smul (bandBound_rpow s 1)

/-- Family: an abbreviation for `ℕ → D → ComplexVector`. -/
abbrev Family (D : Type*) := ℕ → D → ComplexVector

/-- Wave vector, given by `∀ i, WaveClass s P α (fun n x => a n x i)`. -/
def WaveVector (s : StripData D) (P : ℕ → D → ℝ) (α : ℝ) (a : Family D) : Prop :=
  ∀ i, WaveClass s P α (fun n x => a n x i)

/-- Mean vector, given by `MeanClass s (μ + 1) (fun n x => a n x 0) ∧ MeanClass s μ (fun n x =>
a n x 1) ∧ MeanClass s μ (fun n x => a n x 2)`. -/
def MeanVector (s : StripData D) (μ : ℝ) (a : Family D) : Prop :=
  MeanClass s (μ + 1) (fun n x => a n x 0) ∧
    MeanClass s μ (fun n x => a n x 1) ∧ MeanClass s μ (fun n x => a n x 2)

theorem meanVector_component {s : StripData D} {μ : ℝ} {a : Family D}
    (ha : MeanVector s μ a) (i : Fin 3) : MeanClass s μ (fun n x => a n x i) := by
  fin_cases i
  · exact ha.1.mono_exponent (by linarith)
  · exact ha.2.1
  · exact ha.2.2

/-- Angular independent, given by `∀ n i x, x ∈ s.domain → along (G.angular n) (fun y => a n y
i) x = 0`. -/
def AngularIndependent {s : StripData D} {κ : ℝ} (G : Geometry s κ) (a : Family D) : Prop :=
  ∀ n i x, x ∈ s.domain → along (G.angular n) (fun y => a n y i) x = 0

/-- Stripped transport as an element of `Family D`. -/
noncomputable def strippedTransport {s : StripData D} {κ : ℝ}
    (G : Geometry s κ) (a b : Family D) : Family D := fun n x i =>
  a n x 0 * along (G.radial n) (fun y => b n y i) x +
    (a n x 1 / (G.radius n x : ℂ)) * angularGenerator (b n x) i +
    a n x 2 * along (G.axial n) (fun y => b n y i) x

theorem transport_eq_stripped {s : StripData D} {κ : ℝ} (G : Geometry s κ)
    (a b : Family D) (hb : AngularIndependent G b) (n : ℕ) {x : D} (hx : x ∈ s.domain) :
    LinearWaveResidual.transport (G.radius n) (G.radial n) (G.angular n) (G.axial n)
      (a n) (b n) x = strippedTransport G a b n x := by
  funext i
  simp only [LinearWaveResidual.transport, hb n i x hx, zero_add, strippedTransport]

theorem generator_class {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ} {a : Family D}
    (ha : ∀ i, MemClass s w α (fun n x => a n x i)) (i : Fin 3) :
    MemClass s w α (fun n x => angularGenerator (a n x) i) := by
  fin_cases i
  · exact class_neg (ha 1)
  · exact ha 0
  · exact MemClass.zero (ha 0).weight_nonneg

theorem inverse_radius_complex {s : StripData D} {κ : ℝ} (G : Geometry s κ) :
    UnweightedClass s 0 (fun n x => ((G.radius n x : ℂ))⁻¹) := by
  unfold UnweightedClass
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_inv] using
    G.inverse_radius_class.map Complex.ofRealCLM

theorem class_div_radius {s : StripData D} {w : ℕ → D → ℝ} {α κ : ℝ}
    (G : Geometry s κ) {f : ℕ → D → ℂ} (hf : MemClass s w α f) :
    MemClass s w α (fun n x => f n x / (G.radius n x : ℂ)) := by
  simpa only [zero_add, div_eq_mul_inv, mul_comm] using
    unweighted_cmul (inverse_radius_complex G) hf

theorem strippedTransport_class {s : StripData D} {w v : ℕ → D → ℝ} {α β κ : ℝ}
    (G : Geometry s κ) (hκ : 0 ≤ κ) {a b : Family D}
    (ha : ∀ i, MemClass s w α (fun n x => a n x i))
    (hb : ∀ i, MemClass s v β (fun n x => b n x i)) (i : Fin 3) :
    MemClass s (fun n x => w n x * v n x) (α + β - κ)
      (fun n x => strippedTransport G a b n x i) := by
  have hr := class_cmul (ha 0) (class_along (hb i) G.radial_class)
  have hr' : MemClass s (fun n x => w n x * v n x) (α + β - κ)
      (fun n x => a n x 0 * along (G.radial n) (fun y => b n y i) x) := by
    convert! hr using 1
    ring
  have hc := class_cmul (class_div_radius G (ha 1)) (generator_class hb i)
  have hc' := hc.mono_exponent (show α + β - κ ≤ α + β by linarith)
  have hz := class_cmul (ha 2) (class_along (hb i) G.axial_class)
  have hz' := hz.mono_exponent (show α + β - κ ≤ α + (β + 1) by linarith)
  exact (hr'.add hc').add hz'

theorem strippedDivergence_class {s : StripData D} {w : ℕ → D → ℝ} {α κ : ℝ}
    (G : Geometry s κ) (hκ : 0 ≤ κ) {a : Family D}
    (ha : ∀ i, MemClass s w α (fun n x => a n x i)) :
    MemClass s w (α - κ)
      (fun n => strippedDivergence (G.radius n) (G.radial n) (G.axial n) (a n)) := by
  have hr : MemClass s w (α - κ)
      (fun n => along (G.radial n) (fun y => a n y 0)) := by
    simpa only [sub_eq_add_neg] using class_along (ha 0) G.radial_class
  have hc := (class_div_radius G (ha 0)).mono_exponent (show α - κ ≤ α by linarith)
  have hz := (class_along (ha 2) G.axial_class).mono_exponent
    (show α - κ ≤ α + 1 by linarith)
  apply class_congr ((hr.add hc).add hz)
  intro n x _
  simp only [strippedDivergence, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
  ring

theorem mean_wave_weight {s : StripData D} {P : ℕ → D → ℝ} {α : ℝ} {f : ℕ → D → E}
    (hf : MemClass s (fun n x => s.zeta x * (Real.sqrt (s.zeta x) * P n x)) α f)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1)
    (hP : ∀ n x, x ∈ s.domain → 0 ≤ P n x) : WaveClass s P α f := by
  apply hf.mono_weight (fun n x hx => mul_nonneg (Real.sqrt_nonneg _) (hP n x hx))
  intro n x hx
  exact mul_le_of_le_one_left (mul_nonneg (Real.sqrt_nonneg _) (hP n x hx)) (hζ x hx)

theorem wave_mean_weight {s : StripData D} {P : ℕ → D → ℝ} {α : ℝ} {f : ℕ → D → E}
    (hf : MemClass s (fun n x => (Real.sqrt (s.zeta x) * P n x) * s.zeta x) α f)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1)
    (hP : ∀ n x, x ∈ s.domain → 0 ≤ P n x) : WaveClass s P α f := by
  apply hf.mono_weight (fun n x hx => mul_nonneg (Real.sqrt_nonneg _) (hP n x hx))
  intro n x hx
  exact mul_le_of_le_one_right (mul_nonneg (Real.sqrt_nonneg _) (hP n x hx)) (hζ x hx)

theorem wave_square_weight_mean {s : StripData D} {P : ℕ → D → ℝ} {α : ℝ}
    {f : ℕ → D → E}
    (hf : MemClass s (fun n x => (Real.sqrt (s.zeta x) * P n x) *
      (Real.sqrt (s.zeta x) * P n x)) α f)
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) : MeanClass s α f := by
  apply hf.mono_weight (fun _ x hx => s.zeta_nonneg x hx)
  intro n x hx
  have hP2 : P n x * P n x ≤ 1 := by nlinarith [hP0 n x hx, hP1 n x hx]
  calc
    _ = (Real.sqrt (s.zeta x)) ^ 2 * (P n x * P n x) := by ring
    _ = s.zeta x * (P n x * P n x) := by rw [Real.sq_sqrt (s.zeta_nonneg x hx)]
    _ ≤ s.zeta x * 1 := mul_le_mul_of_nonneg_left hP2 (s.zeta_nonneg x hx)
    _ = _ := mul_one _

theorem wave_square_weight_wave {s : StripData D} {P : ℕ → D → ℝ} {α : ℝ}
    {f : ℕ → D → E}
    (hf : MemClass s (fun n x => (Real.sqrt (s.zeta x) * P n x) *
      (Real.sqrt (s.zeta x) * P n x)) α f)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1)
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) : WaveClass s P α f := by
  apply hf.mono_weight (fun n x hx => mul_nonneg (Real.sqrt_nonneg _) (hP0 n x hx))
  intro n x hx
  have hs1 : Real.sqrt (s.zeta x) ≤ 1 := by
    nlinarith [Real.sqrt_nonneg (s.zeta x), Real.sq_sqrt (s.zeta_nonneg x hx), hζ x hx]
  have hw1 : Real.sqrt (s.zeta x) * P n x ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hs1 (hP1 n x hx) (hP0 n x hx) (by norm_num : (0 : ℝ) ≤ 1)
  exact mul_le_of_le_one_right (mul_nonneg (Real.sqrt_nonneg _) (hP0 n x hx)) hw1

theorem mean_advects_stripped_wave {s : StripData D} {P : ℕ → D → ℝ} {α μ κ : ℝ}
    (G : Geometry s κ) (hκ : κ ≤ 1) {m a : Family D}
    (hm : MeanVector s μ m) (ha : WaveVector s P α a)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1) (i : Fin 3) :
    WaveClass s P (α + μ) (fun n x => strippedTransport G m a n x i) := by
  have hr := mean_wave_cmul hm.1 (class_along (ha i) G.radial_class) hζ
  have hr' := hr.mono_exponent (show α + μ ≤ μ + 1 + (α + -κ) by linarith)
  have hc := mean_wave_cmul (class_div_radius G hm.2.1) (generator_class ha i) hζ
  have hc' : WaveClass s P (α + μ)
      (fun n x => m n x 1 / (G.radius n x : ℂ) * angularGenerator (a n x) i) := by
    simpa only [add_comm μ α] using hc
  have hz := mean_wave_cmul hm.2.2 (class_along (ha i) G.axial_class) hζ
  have hz' := hz.mono_exponent (show α + μ ≤ μ + (α + 1) by linarith)
  exact (hr'.add hc').add hz'

theorem wave_advects_stripped_mean {s : StripData D} {P : ℕ → D → ℝ} {α μ κ : ℝ}
    (G : Geometry s κ) (hκ : 0 ≤ κ) {m a : Family D}
    (hm : MeanVector s μ m) (ha : WaveVector s P α a)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1)
    (hP : ∀ n x, x ∈ s.domain → 0 ≤ P n x) (i : Fin 3) :
    WaveClass s P (α + μ - κ) (fun n x => strippedTransport G a m n x i) :=
  wave_mean_weight (strippedTransport_class G hκ ha (meanVector_component hm) i) hζ hP

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem carrier_add (κ κ' : ℝ) (Φ : D → ℝ) (x : D) :
    carrier κ Φ x * carrier κ' Φ x = carrier (κ + κ') Φ x := by
  unfold carrier
  rw [← Complex.exp_add]
  congr 1
  simp only [phaseFactor, Complex.ofReal_add]
  ring

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem carrier_zero (Φ : D → ℝ) (x : D) : carrier 0 Φ x = 1 := by
  simp [carrier, phaseFactor]

theorem transport_mode_left (R : D → ℝ) (Vr Vθ Vz : D → D) (κ : ℝ)
    (Φ : D → ℝ) (a b : D → ComplexVector) (x : D) (i : Fin 3) :
    LinearWaveResidual.transport R Vr Vθ Vz (vectorMode κ Φ a) b x i =
      LinearWaveResidual.transport R Vr Vθ Vz a b x i * carrier κ Φ x := by
  simp only [LinearWaveResidual.transport, vectorMode, mode]
  ring

theorem transport_mode_right (R : D → ℝ) (Vr Vθ Vz : D → D) (κ : ℝ)
    {Φ : D → ℝ} (a : D → ComplexVector) {b : D → ComplexVector} {x : D}
    (hΦ : DifferentiableAt ℝ Φ x) (hb : ∀ i, DifferentiableAt ℝ (fun y => b y i) x)
    (i : Fin 3) :
    LinearWaveResidual.transport R Vr Vθ Vz a (vectorMode κ Φ b) x i =
      (LinearWaveResidual.transport R Vr Vθ Vz a b x i +
        phaseFactor κ * normalDot (phaseNormal R Vr Vθ Vz Φ x) (a x) * b x i) * carrier κ Φ x := by
  have hd (V : D → D) (j : Fin 3) :
      along V (fun y => vectorMode κ Φ b y j) x =
        (along V (fun y => b y j) x + phaseFactor κ * Complex.ofReal (along V Φ x) * b x j) *
          carrier κ Φ x := along_mode V κ hΦ (hb j)
  simp only [LinearWaveResidual.transport, hd]
  fin_cases i <;> simp [angularGenerator, vectorMode, mode, normalDot, phaseNormal, div_eq_mul_inv]
      <;> ring

/-- The exact phase-sum coefficient of the actual bilinear differential operator. -/
theorem transport_modes (R : D → ℝ) (Vr Vθ Vz : D → D) (κ κ' : ℝ)
    {Φ : D → ℝ} (a : D → ComplexVector) {b : D → ComplexVector} {x : D}
    (hΦ : DifferentiableAt ℝ Φ x) (hb : ∀ i, DifferentiableAt ℝ (fun y => b y i) x)
    (i : Fin 3) :
    LinearWaveResidual.transport R Vr Vθ Vz (vectorMode κ Φ a) (vectorMode κ' Φ b) x i =
      (LinearWaveResidual.transport R Vr Vθ Vz a b x i +
        phaseFactor κ' * normalDot (phaseNormal R Vr Vθ Vz Φ x) (a x) * b x i) *
          carrier (κ + κ') Φ x := by
  rw [transport_mode_left, transport_mode_right R Vr Vθ Vz κ' a hΦ hb,
    ← carrier_add]
  ring

theorem normalDot_class {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {N : ℕ → D → EuclideanSpace ℝ (Fin 3)} {a : Family D}
    (hN : ∀ i, UnweightedClass s 0 (fun n x => N n x i))
    (ha : ∀ i, MemClass s w α (fun n x => a n x i)) :
    MemClass s w α (fun n x => normalDot (N n x) (a n x)) := by
  have h i : MemClass s w α (fun n x => (N n x i : ℂ) * a n x i) := by
    simpa only [zero_add, Complex.ofRealCLM_apply] using
      unweighted_cmul ((hN i).map Complex.ofRealCLM) (ha i)
  exact ((h 0).add (h 1)).add (h 2)

theorem phaseFactor_class {s : StripData D} {w : ℕ → D → ℝ} {α β : ℝ}
    {ν : ℕ → ℝ} {f : ℕ → D → ℂ} (hf : MemClass s w α f) (hν : BandBound s β ν) :
    MemClass s w (α + β) (fun n x => phaseFactor (ν n) * f n x) := by
  apply class_congr ((class_const_cmul hf Complex.I).band_smul hν)
  intro n x _
  simp only [phaseFactor, Complex.real_smul]
  ring

/-- Wave mean coefficient as an element of `Family D`. -/
noncomputable def waveMeanCoefficient {s : StripData D} {κ : ℝ} (G : Geometry s κ)
    (Φ : ℕ → D → ℝ) (ν : ℕ → ℝ) (m a : Family D) : Family D := fun n x i =>
  strippedTransport G m a n x i + strippedTransport G a m n x i +
    phaseFactor (ν n) * normalDot
      (phaseNormal (G.radius n) (G.radial n) (G.angular n) (G.axial n) (Φ n) x) (m n x) * a n x i

/-- Both cross-advections, with the radial mean improvement explicitly used. -/
theorem wave_mean_bound {s : StripData D} {P : ℕ → D → ℝ} {α μ κ : ℝ}
    (G : Geometry s κ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1 / 2)
    {Φ : ℕ → D → ℝ} {ν : ℕ → ℝ} {m a : Family D}
    (hm : MeanVector s μ m) (ha : WaveVector s P α a)
    (hN : ∀ i, UnweightedClass s 0 (fun n x =>
      phaseNormal (G.radius n) (G.radial n) (G.angular n) (G.axial n) (Φ n) x i))
    (hν : BandBound s (-(1 / 2)) ν)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1)
    (hP : ∀ n x, x ∈ s.domain → 0 ≤ P n x) :
    WaveVector s P (α + μ - 1 / 2) (waveMeanCoefficient G Φ ν m a) := by
  intro i
  have hma := (mean_advects_stripped_wave G (by linarith) hm ha hζ i).mono_exponent
    (show α + μ - 1 / 2 ≤ α + μ by linarith)
  have ham := (wave_advects_stripped_mean G hκ0 hm ha hζ hP i).mono_exponent
    (show α + μ - 1 / 2 ≤ α + μ - κ by linarith)
  have hdot := normalDot_class hN (meanVector_component hm)
  have hfreq := phaseFactor_class hdot hν
  have hphase := mean_wave_cmul hfreq (ha i) hζ
  have hphase' : WaveClass s P (α + μ - 1 / 2) (fun n x =>
      phaseFactor (ν n) * normalDot
      (phaseNormal (G.radius n) (G.radial n) (G.angular n) (G.axial n) (Φ n) x) (m n x) * a n x i)
          := by
    convert! hphase using 1
    ring
  exact (hma.add ham).add hphase'

theorem wave_mean_identity {s : StripData D} {κ : ℝ} (G : Geometry s κ)
    (Φ : ℕ → D → ℝ) (ν : ℕ → ℝ) (m a : Family D)
    (hmθ : AngularIndependent G m) (haθ : AngularIndependent G a)
    (n : ℕ) {x : D} (hx : x ∈ s.domain) (hΦ : DifferentiableAt ℝ (Φ n) x)
    (ha : ∀ i, DifferentiableAt ℝ (fun y => a n y i) x) (i : Fin 3) :
    LinearWaveResidual.transport (G.radius n) (G.radial n) (G.angular n) (G.axial n)
      (m n) (vectorMode (ν n) (Φ n) (a n)) x i +
    LinearWaveResidual.transport (G.radius n) (G.radial n) (G.angular n) (G.axial n)
      (vectorMode (ν n) (Φ n) (a n)) (m n) x i =
        waveMeanCoefficient G Φ ν m a n x i * carrier (ν n) (Φ n) x := by
  rw [transport_mode_right _ _ _ _ _ _ hΦ ha, transport_mode_left,
    transport_eq_stripped G m a haθ n hx, transport_eq_stripped G a m hmθ n hx]
  unfold waveMeanCoefficient
  ring

theorem phaseFactor_ratio (ν ξ : ℝ) (hν : ν ≠ 0) :
    ((ξ / ν : ℝ) : ℂ) * phaseFactor ν = phaseFactor ξ := by
  have hc : (ν : ℂ) ≠ 0 := by exact_mod_cast hν
  simp only [phaseFactor, Complex.ofReal_div]
  field_simp

/-- The exact divergence cancellation, before taking any norm or any jet. -/
theorem switched_longitudinal (R : D → ℝ) (Vr Vθ Vz : D → D) (ν ξ : ℝ)
    (hν : ν ≠ 0) {Φ : D → ℝ} {a : D → ComplexVector} {x : D}
    (hΦ : DifferentiableAt ℝ Φ x) (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) x)
    (haθ : along Vθ (fun y => a y 1) x = 0)
    (hdiv : cylindricalDivergence R Vr Vθ Vz (vectorMode ν Φ a) x = 0) :
    phaseFactor ξ * normalDot (phaseNormal R Vr Vθ Vz Φ x) (a x) =
      (ξ / ν) • (-strippedDivergence R Vr Vz a x) := by
  rw [← phaseFactor_ratio ν ξ hν, mul_assoc,
    longitudinal_identity R Vr Vθ Vz ν hΦ ha haθ hdiv]
  rfl

/-- Same coefficient as an element of `Family D`. -/
noncomputable def sameCoefficient {s : StripData D} {κ : ℝ} (G : Geometry s κ)
    (Φ : ℕ → D → ℝ) (ξ : ℕ → ℝ) (a b : Family D) : Family D := fun n x i =>
  strippedTransport G a b n x i + phaseFactor (ξ n) * normalDot
    (phaseNormal (G.radius n) (G.radial n) (G.angular n) (G.axial n) (Φ n) x) (a n x) * b n x i

theorem same_label_identity {s : StripData D} {κ : ℝ} (G : Geometry s κ)
    (Φ : ℕ → D → ℝ) (ν ξ : ℕ → ℝ) (a b : Family D)
    (hbθ : AngularIndependent G b) (n : ℕ) {x : D} (hx : x ∈ s.domain)
    (hΦ : DifferentiableAt ℝ (Φ n) x)
    (hb : ∀ i, DifferentiableAt ℝ (fun y => b n y i) x) (i : Fin 3) :
    LinearWaveResidual.transport (G.radius n) (G.radial n) (G.angular n) (G.axial n)
      (vectorMode (ν n) (Φ n) (a n)) (vectorMode (ξ n) (Φ n) (b n)) x i =
        sameCoefficient G Φ ξ a b n x i * carrier (ν n + ξ n) (Φ n) x := by
  rw [transport_modes _ _ _ _ _ _ _ hΦ hb,
    transport_eq_stripped G a b hbθ n hx]
  rfl

/-- All derivatives of the longitudinal contraction are estimated through
the actual divergence identity, including derivatives of the phase normal. -/
theorem same_label_raw_bound {s : StripData D} {P : ℕ → D → ℝ} {α β κ : ℝ}
    (G : Geometry s κ) (hκ : 0 ≤ κ) {Φ : ℕ → D → ℝ} {ν ξ : ℕ → ℝ}
    {a b : Family D} (ha : WaveVector s P α a) (hb : WaveVector s P β b)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (Φ n) s.domain) (hν : ∀ n, ν n ≠ 0)
    (hratio : BandBound s 0 (fun n => ξ n / ν n))
    (haθ : AngularIndependent G a)
    (hdiv : ∀ n x, x ∈ s.domain → cylindricalDivergence
      (G.radius n) (G.radial n) (G.angular n) (G.axial n) (vectorMode (ν n) (Φ n) (a n)) x = 0)
    (i : Fin 3) :
    MemClass s (fun n x => (Real.sqrt (s.zeta x) * P n x) *
      (Real.sqrt (s.zeta x) * P n x)) (α + β - κ)
      (fun n x => sameCoefficient G Φ ξ a b n x i) := by
  have hs := strippedDivergence_class G hκ ha
  have hsw : WaveClass s P (α - κ) (fun n x =>
      (ξ n / ν n) • (-strippedDivergence (G.radius n) (G.radial n) (G.axial n) (a n) x)) := by
    unfold WaveClass
    simpa only [add_zero] using (class_neg hs).band_smul hratio
  have hprod := class_cmul hsw (hb i)
  have hprod' : MemClass s (fun n x => (Real.sqrt (s.zeta x) * P n x) *
      (Real.sqrt (s.zeta x) * P n x)) (α + β - κ) (fun n x =>
      ((ξ n / ν n) • (-strippedDivergence (G.radius n) (G.radial n) (G.axial n) (a n) x)) * b n x
          i) := by
    convert! hprod using 1
    ring
  have hp : MemClass s (fun n x => (Real.sqrt (s.zeta x) * P n x) *
      (Real.sqrt (s.zeta x) * P n x)) (α + β - κ) (fun n x =>
      phaseFactor (ξ n) * normalDot
      (phaseNormal (G.radius n) (G.radial n) (G.angular n) (G.axial n) (Φ n) x) (a n x) * b n x i)
          := by
    apply class_congr hprod'
    intro n x hx
    have hp := ((hΦ n).contDiffAt (s.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
    have hd j := (((ha j).smooth n).contDiffAt (s.isOpen_domain.mem_nhds hx)).differentiableAt (by
        simp)
    dsimp only
    rw [switched_longitudinal _ _ _ _ (ν n) (ξ n) (hν n) hp hd (haθ n 1 x hx) (hdiv n x hx)]
  exact (strippedTransport_class G hκ ha hb i).add hp

theorem same_label_wave_bound {s : StripData D} {P : ℕ → D → ℝ} {α β κ : ℝ}
    (G : Geometry s κ) (hκ : 0 ≤ κ) {Φ : ℕ → D → ℝ} {ν ξ : ℕ → ℝ}
    {a b : Family D} (ha : WaveVector s P α a) (hb : WaveVector s P β b)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (Φ n) s.domain) (hν : ∀ n, ν n ≠ 0)
    (hratio : BandBound s 0 (fun n => ξ n / ν n)) (haθ : AngularIndependent G a)
    (hdiv : ∀ n x, x ∈ s.domain → cylindricalDivergence
      (G.radius n) (G.radial n) (G.angular n) (G.axial n) (vectorMode (ν n) (Φ n) (a n)) x = 0)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1)
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) :
    WaveVector s P (α + β - κ) (sameCoefficient G Φ ξ a b) := by
  intro i
  exact wave_square_weight_wave (same_label_raw_bound G hκ ha hb hΦ hν hratio haθ hdiv i) hζ hP0 hP1

theorem same_label_mean_bound {s : StripData D} {P : ℕ → D → ℝ} {α β κ : ℝ}
    (G : Geometry s κ) (hκ : 0 ≤ κ) {Φ : ℕ → D → ℝ} {ν ξ : ℕ → ℝ}
    {a b : Family D} (ha : WaveVector s P α a) (hb : WaveVector s P β b)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (Φ n) s.domain) (hν : ∀ n, ν n ≠ 0)
    (hratio : BandBound s 0 (fun n => ξ n / ν n)) (haθ : AngularIndependent G a)
    (hdiv : ∀ n x, x ∈ s.domain → cylindricalDivergence
      (G.radius n) (G.radial n) (G.angular n) (G.axial n) (vectorMode (ν n) (Φ n) (a n)) x = 0)
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) (i : Fin 3) :
    MeanClass s (α + β - κ) (fun n x => sameCoefficient G Φ ξ a b n x i) :=
  wave_square_weight_mean (same_label_raw_bound G hκ ha hb hΦ hν hratio haθ hdiv i) hP0 hP1

theorem int_abs_cast_one_le {j : ℤ} (hj : j ≠ 0) : (1 : ℝ) ≤ |(j : ℝ)| := by
  have hpos : (0 : ℤ) < |j| := abs_pos.mpr hj
  have hone : (1 : ℤ) ≤ |j| := by omega
  exact_mod_cast hone

theorem harmonic_ratio_bound {j l : ℤ} {M : ℝ} (hj : j ≠ 0)
    (hM : 0 ≤ M) (hl : |(l : ℝ)| ≤ M) : |(l : ℝ) / (j : ℝ)| ≤ M := by
  have hj1 := int_abs_cast_one_le hj
  rw [abs_div]
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hj1)).mpr
  exact hl.trans (le_mul_of_one_le_right hM hj1)

theorem bandBound_harmonic_ratio (s : StripData D) {j l : ℕ → ℤ} {M : ℝ}
    (hj : ∀ n, j n ≠ 0) (hM : 0 ≤ M) (hl : ∀ n, |(l n : ℝ)| ≤ M) :
    BandBound s 0 (fun n => (l n : ℝ) / (j n : ℝ)) := by
  refine ⟨M, hM, 0, ?_⟩
  intro n
  simpa only [Real.norm_eq_abs, Real.rpow_zero, pow_zero, mul_one] using
    harmonic_ratio_bound (hj n) hM (hl n)

theorem frequency_ratio {k : ℝ} (hk : k ≠ 0) {j : ℤ} (hj : j ≠ 0) (l : ℤ) :
    (k * (l : ℝ)) / (k * (j : ℝ)) = (l : ℝ) / (j : ℝ) := by
  have hj' : (j : ℝ) ≠ 0 := by exact_mod_cast hj
  field_simp

theorem bandBound_frequency_ratio (s : StripData D) {k : ℕ → ℝ} {j l : ℕ → ℤ} {M : ℝ}
    (hk : ∀ n, k n ≠ 0) (hj : ∀ n, j n ≠ 0) (hM : 0 ≤ M)
    (hl : ∀ n, |(l n : ℝ)| ≤ M) :
    BandBound s 0 (fun n => (k n * (l n : ℝ)) / (k n * (j n : ℝ))) := by
  simpa only [frequency_ratio (hk _) (hj _)] using bandBound_harmonic_ratio s hj hM hl

theorem bandBound_frequency {s : StripData D} {β : ℝ} {k : ℕ → ℝ} {j : ℕ → ℤ} {M : ℝ}
    (hk : BandBound s β k) (hM : 0 ≤ M) (hj : ∀ n, |(j n : ℝ)| ≤ M) :
    BandBound s β (fun n => k n * (j n : ℝ)) := by
  obtain ⟨C, hC, p, h⟩ := hk
  refine ⟨C * M, mul_nonneg hC hM, p, ?_⟩
  intro n
  rw [norm_mul]
  have hnonneg : 0 ≤ C * s.epsilon n ^ β * s.slow n ^ p :=
    mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos (s.epsilon_pos n) β).le)
      (pow_nonneg (zero_le_one.trans (s.one_le_slow n)) p)
  calc
    _ ≤ (C * s.epsilon n ^ β * s.slow n ^ p) * M :=
      mul_le_mul (h n) (by simpa only [Real.norm_eq_abs] using hj n) (norm_nonneg _) hnonneg
    _ = _ := by ring

/-- Fixed-stage frequency growth is finite and independent of the band. -/
theorem harmonic_stage_add {j l : ℤ} {M : ℝ} (stage : ℕ)
    (hj : |(j : ℝ)| ≤ 2 ^ stage * M) (hl : |(l : ℝ)| ≤ 2 ^ stage * M) :
    |((j + l : ℤ) : ℝ)| ≤ 2 ^ (stage + 1) * M := by
  rw [Int.cast_add]
  calc
    _ ≤ |(j : ℝ)| + |(l : ℝ)| := abs_add_le _ _
    _ ≤ 2 ^ stage * M + 2 ^ stage * M := add_le_add hj hl
    _ = _ := by rw [pow_succ]; ring

theorem harmonic_stage_neg {j : ℤ} {M : ℝ} (stage : ℕ)
    (hj : |(j : ℝ)| ≤ 2 ^ stage * M) : |((-j : ℤ) : ℝ)| ≤ 2 ^ stage * M := by
  simpa only [Int.cast_neg, abs_neg] using hj

/-- Conjugate family, defined pointwise by `star (a n x i)`. -/
noncomputable def conjugateFamily (a : Family D) : Family D := fun n x i => star (a n x i)

theorem conjugate_wave {s : StripData D} {P : ℕ → D → ℝ} {α : ℝ} {a : Family D}
    (ha : WaveVector s P α a) : WaveVector s P α (conjugateFamily a) :=
  fun i => class_conj (ha i)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem carrier_neg (ν : ℝ) (Φ : D → ℝ) (x : D) : carrier (-ν) Φ x = star (carrier ν Φ x) := by
  change Complex.exp (phaseFactor (-ν) * (Φ x : ℂ)) = (starRingEnd ℂ) (Complex.exp (phaseFactor ν *
      (Φ x : ℂ)))
  rw [← Complex.exp_conj]
  congr 1
  simp only [phaseFactor, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem vectorMode_conjugate (ν : ℝ) (Φ : D → ℝ) (a : D → ComplexVector) (x : D) (i : Fin 3) :
    vectorMode (-ν) Φ (fun y j => star (a y j)) x i = star (vectorMode ν Φ a x i) := by
  simp [vectorMode, mode, carrier_neg, star_mul, mul_comm]

theorem opposite_identity {s : StripData D} {κ : ℝ} (G : Geometry s κ)
    (Φ : ℕ → D → ℝ) (ν : ℕ → ℝ) (a b : Family D)
    (hbθ : AngularIndependent G b) (n : ℕ) {x : D} (hx : x ∈ s.domain)
    (hΦ : DifferentiableAt ℝ (Φ n) x)
    (hb : ∀ i, DifferentiableAt ℝ (fun y => b n y i) x) (i : Fin 3) :
    LinearWaveResidual.transport (G.radius n) (G.radial n) (G.angular n) (G.axial n)
      (vectorMode (ν n) (Φ n) (a n)) (vectorMode (-(ν n)) (Φ n) (b n)) x i =
        sameCoefficient G Φ (fun n => -(ν n)) a b n x i := by
  rw [same_label_identity G Φ ν (fun n => -(ν n)) a b hbθ n hx hΦ hb,
    add_neg_cancel, carrier_zero, mul_one]

theorem opposite_mean_bound {s : StripData D} {P : ℕ → D → ℝ} {α β κ : ℝ}
    (G : Geometry s κ) (hκ : 0 ≤ κ) {Φ : ℕ → D → ℝ} {ν : ℕ → ℝ} {a b : Family D}
    (ha : WaveVector s P α a) (hb : WaveVector s P β b)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (Φ n) s.domain) (hν : ∀ n, ν n ≠ 0)
    (haθ : AngularIndependent G a)
    (hdiv : ∀ n x, x ∈ s.domain → cylindricalDivergence
      (G.radius n) (G.radial n) (G.angular n) (G.axial n) (vectorMode (ν n) (Φ n) (a n)) x = 0)
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) (i : Fin 3) :
    MeanClass s (α + β - κ) (fun n x => sameCoefficient G Φ (fun n => -(ν n)) a b n x i) := by
  have hr : BandBound s 0 (fun n => -(ν n) / ν n) := by
    simpa only [neg_div, div_self (hν _)] using bandBound_const s (-1)
  exact same_label_mean_bound G hκ ha hb hΦ hν hr haθ hdiv hP0 hP1 i

theorem conjugate_opposite_mean_bound {s : StripData D} {P : ℕ → D → ℝ} {α β κ : ℝ}
    (G : Geometry s κ) (hκ : 0 ≤ κ) {Φ : ℕ → D → ℝ} {ν : ℕ → ℝ} {a b : Family D}
    (ha : WaveVector s P α a) (hb : WaveVector s P β b)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (Φ n) s.domain) (hν : ∀ n, ν n ≠ 0)
    (haθ : AngularIndependent G a)
    (hdiv : ∀ n x, x ∈ s.domain → cylindricalDivergence
      (G.radius n) (G.radial n) (G.angular n) (G.axial n) (vectorMode (ν n) (Φ n) (a n)) x = 0)
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) (i : Fin 3) :
    MeanClass s (α + β - κ) (fun n x =>
      (sameCoefficient G Φ (fun n => -(ν n)) a (conjugateFamily b) n x i).re) :=
  (opposite_mean_bound G hκ ha (conjugate_wave hb) hΦ hν haθ hdiv hP0 hP1 i).map Complex.reCLM

theorem finite_wave_sum {s : StripData D} {P : ℕ → D → ℝ} {α : ℝ}
    {ι : Type*} (t : Finset ι) (a : ι → Family D)
    (hP : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (ha : ∀ j ∈ t, WaveVector s P α (a j)) :
    WaveVector s P α (fun n x i => ∑ j ∈ t, a j n x i) := by
  intro i
  exact MemClass.sum t (fun j n x => a j n x i)
    (fun n x hx => mul_nonneg (Real.sqrt_nonneg _) (hP n x hx)) (fun j hj => ha j hj i)

/-- A nonzero integer first harmonic and a bounded second harmonic give
the precise uniform ratio needed by the divergence cancellation. -/
theorem same_label_harmonic_bound {s : StripData D} {P : ℕ → D → ℝ} {α β κ M : ℝ}
    (G : Geometry s κ) (hκ : 0 ≤ κ) {Φ : ℕ → D → ℝ} {k : ℕ → ℝ} {j l : ℕ → ℤ}
    {a b : Family D} (ha : WaveVector s P α a) (hb : WaveVector s P β b)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (Φ n) s.domain) (hk : ∀ n, k n ≠ 0)
    (hj : ∀ n, j n ≠ 0) (hM : 0 ≤ M) (hl : ∀ n, |(l n : ℝ)| ≤ M)
    (haθ : AngularIndependent G a)
    (hdiv : ∀ n x, x ∈ s.domain → cylindricalDivergence
      (G.radius n) (G.radial n) (G.angular n) (G.axial n)
      (vectorMode (k n * (j n : ℝ)) (Φ n) (a n)) x = 0)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1)
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) :
    WaveVector s P (α + β - κ)
      (sameCoefficient G Φ (fun n => k n * (l n : ℝ)) a b) := by
  apply same_label_wave_bound G hκ ha hb hΦ
    (fun n => mul_ne_zero (hk n) (by exact_mod_cast hj n))
    (bandBound_frequency_ratio s hk hj hM hl) haθ hdiv hζ hP0 hP1

/-- Vanishing of a product on an open set forces the differentiated second
factor to vanish wherever the first factor is nonzero. -/
theorem mul_along_zero {U : Set D} (hU : IsOpen U) {f g : D → ℂ} {x : D}
    (hx : x ∈ U) (hf : ContinuousAt f x)
    (hfg : ∀ y ∈ U, f y * g y = 0) (V : D → D) : f x * along V g x = 0 := by
  by_cases hz : f x = 0
  · simp [hz]
  have hfnz : ∀ᶠ y in 𝓝 x, f y ≠ 0 := hf.eventually_ne hz
  have hgn : g =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [hfnz, hU.mem_nhds hx] with y hfy hy
    exact (mul_eq_zero.mp (hfg y hy)).resolve_left hfy
  unfold along
  rw [hgn.fderiv_eq]
  simp

theorem transport_zero_of_products {U : Set D} (hU : IsOpen U)
    (R : D → ℝ) (Vr Vθ Vz : D → D) {a b : D → ComplexVector}
    (ha : ∀ i, ContinuousOn (fun y => a y i) U)
    (hab : ∀ i j y, y ∈ U → a y i * b y j = 0) {x : D} (hx : x ∈ U) :
    LinearWaveResidual.transport R Vr Vθ Vz a b x = 0 := by
  funext i
  have hr := mul_along_zero hU hx ((ha 0 x hx).continuousAt (hU.mem_nhds hx)) (hab 0 i) Vr
  have hθ := mul_along_zero hU hx ((ha 1 x hx).continuousAt (hU.mem_nhds hx)) (hab 1 i) Vθ
  have hz := mul_along_zero hU hx ((ha 2 x hx).continuousAt (hU.mem_nhds hx)) (hab 2 i) Vz
  have hc : a x 1 * angularGenerator (b x) i = 0 := by
    fin_cases i
    · change a x 1 * (-b x 1) = 0
      rw [mul_neg, hab 1 1 x hx, neg_zero]
    · change a x 1 * b x 0 = 0
      exact hab 1 0 x hx
    · change a x 1 * 0 = 0
      exact mul_zero _
  change _ = (0 : ℂ)
  calc
    _ = a x 0 * along Vr (fun y => b y i) x +
        (a x 1 * along Vθ (fun y => b y i) x + a x 1 * angularGenerator (b x) i) / (R x : ℂ) +
        a x 2 * along Vz (fun y => b y i) x := by unfold LinearWaveResidual.transport; ring
    _ = 0 := by rw [hr, hθ, hc, hz]; simp

theorem cross_transport_every_class {s : StripData D} {P : ℕ → D → ℝ} {γ κ : ℝ}
    (G : Geometry s κ) {a b : Family D}
    (ha : ∀ n i, ContinuousOn (fun y => a n y i) s.domain)
    (hab : ∀ n i j x, x ∈ s.domain → a n x i * b n x j = 0)
    (hP : ∀ n x, x ∈ s.domain → 0 ≤ P n x) :
    WaveVector s P γ (fun n => LinearWaveResidual.transport
      (G.radius n) (G.radial n) (G.angular n) (G.axial n) (a n) (b n)) := by
  intro i
  apply class_congr (MemClass.zero
    (fun n x hx => mul_nonneg (Real.sqrt_nonneg (s.zeta x)) (hP n x hx)))
  intro n x hx
  have h := transport_zero_of_products s.isOpen_domain (G.radius n)
    (G.radial n) (G.angular n) (G.axial n) (ha n) (hab n) hx
  exact (congrFun h i).symm

theorem slot_complex_product_zero {d h : ℝ} {vr vt : PartitionedCovariance.Plane}
    (sys : PartitionedCovariance.SlotSystem d h vr vt)
    {L M : SlotColoring.Label} (hL : 1 ≤ L.1) (hM : 1 ≤ M.1) (hne : L ≠ M)
    {f g : PartitionedCovariance.Plane → ℝ}
    (hf : Function.support f ⊆ PartitionedCovariance.slotSet h sys.radius vr vt L)
    (hg : Function.support g ⊆ PartitionedCovariance.slotSet h sys.radius vr vt M)
    {q : ℝ} (hq : 0 < q) (x : SlotColoring.Position) (Y : PartitionedCovariance.Plane)
    (a b : ℂ) :
    (((PartitionedCovariance.physicalMask d L q x *
        PartitionedCovariance.covered (SlotColoring.nativeIndex h L.1) f Y : ℝ) : ℂ) * a) *
      (((PartitionedCovariance.physicalMask d M q x *
        PartitionedCovariance.covered (SlotColoring.nativeIndex h M.1) g Y : ℝ) : ℂ) * b) = 0 := by
  have hz := sys.cross_product_zero hL hM hne hf hg hq x Y
  have hc : ((PartitionedCovariance.physicalMask d L q x *
      PartitionedCovariance.covered (SlotColoring.nativeIndex h L.1) f Y : ℝ) : ℂ) *
      ((PartitionedCovariance.physicalMask d M q x *
      PartitionedCovariance.covered (SlotColoring.nativeIndex h M.1) g Y : ℝ) : ℂ) = 0 := by
    exact_mod_cast hz
  calc
    _ = (((PartitionedCovariance.physicalMask d L q x *
      PartitionedCovariance.covered (SlotColoring.nativeIndex h L.1) f Y : ℝ) : ℂ) *
      ((PartitionedCovariance.physicalMask d M q x *
      PartitionedCovariance.covered (SlotColoring.nativeIndex h M.1) g Y : ℝ) : ℂ)) * (a * b) := by
          ring
    _ = 0 := by rw [hc, zero_mul]

/-- The actual physical partition masks and covered native slot profiles,
with arbitrary complex component multipliers (including harmonic carriers). -/
noncomputable def slotField (d h : ℝ) (L : SlotColoring.Label)
    (q : D → ℝ) (X : D → SlotColoring.Position) (Y : D → PartitionedCovariance.Plane)
    (f : Fin 3 → PartitionedCovariance.Plane → ℝ) (a : D → ComplexVector) :
    D → ComplexVector := fun x i =>
  ((PartitionedCovariance.physicalMask d L (q x) (X x) *
    PartitionedCovariance.covered (SlotColoring.nativeIndex h L.1) (f i) (Y x) : ℝ) : ℂ) * a x i

theorem slot_transport_zero {U : Set D} (hU : IsOpen U)
    {d h : ℝ} {vr vt : PartitionedCovariance.Plane}
    (sys : PartitionedCovariance.SlotSystem d h vr vt)
    {L M : SlotColoring.Label} (hL : 1 ≤ L.1) (hM : 1 ≤ M.1) (hne : L ≠ M)
    (q : D → ℝ) (X : D → SlotColoring.Position) (Y : D → PartitionedCovariance.Plane)
    (hq : ∀ y ∈ U, 0 < q y)
    (f g : Fin 3 → PartitionedCovariance.Plane → ℝ) (a b : D → ComplexVector)
    (hf : ∀ i, Function.support (f i) ⊆ PartitionedCovariance.slotSet h sys.radius vr vt L)
    (hg : ∀ i, Function.support (g i) ⊆ PartitionedCovariance.slotSet h sys.radius vr vt M)
    (ha : ∀ i, ContinuousOn (fun y => slotField d h L q X Y f a y i) U)
    (R : D → ℝ) (Vr Vθ Vz : D → D) {x : D} (hx : x ∈ U) :
    LinearWaveResidual.transport R Vr Vθ Vz
      (slotField d h L q X Y f a) (slotField d h M q X Y g b) x = 0 := by
  apply transport_zero_of_products hU R Vr Vθ Vz ha _ hx
  intro i j y hy
  exact slot_complex_product_zero sys hL hM hne (hf i) (hg j) (hq y hy) (X y) (Y y)
    (a y i) (b y j)

/-- The complex operator restricts to the real cylindrical bilinear operator. -/
theorem transport_realLift (R : D → ℝ) (Vr Vθ Vz : D → D)
    (u : D → Fin 3 → ℝ) {v : D → Fin 3 → ℝ} {x : D}
    (hv : ∀ i, DifferentiableAt ℝ (fun y => v y i) x) (i : Fin 3) :
    LinearWaveResidual.transport R Vr Vθ Vz
      (LinearWaveResidual.realLift u) (LinearWaveResidual.realLift v) x i =
        (LinearWaveResidual.realTransport R Vr Vθ Vz u v x i : ℂ) := by
  have hd (V : D → D) (j : Fin 3) := along_ofReal V (hv j)
  fin_cases i <;>
    simp [LinearWaveResidual.transport, LinearWaveResidual.realTransport,
      LinearWaveResidual.realLift, angularGenerator, LinearWaveResidual.realAngularGenerator,
      hd, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div]

/-- Real bilinear products require both ordinary and conjugate harmonic pairs. -/
theorem transport_real_parts (R : D → ℝ) (Vr Vθ Vz : D → D)
    (u : D → ComplexVector) {v : D → ComplexVector} {x : D}
    (hv : ∀ i, DifferentiableAt ℝ (fun y => v y i) x) (i : Fin 3) :
    LinearWaveResidual.realTransport R Vr Vθ Vz
      (fun y j => (u y j).re) (fun y j => (v y j).re) x i =
        ((LinearWaveResidual.transport R Vr Vθ Vz u v x i).re +
          (LinearWaveResidual.transport R Vr Vθ Vz u (fun y j => star (v y j)) x i).re) / 2 := by
  have hd (V : D → D) (j : Fin 3) :
      along V (fun y => (v y j).re) x = (along V (fun y => v y j) x).re :=
    LinearWaveResidual.along_map Complex.reCLM V (hv j)
  have hc (V : D → D) (j : Fin 3) :
      along V (fun y => (starRingEnd ℂ) (v y j)) x = (starRingEnd ℂ) (along V (fun y => v y j) x) :=
    LinearWaveResidual.along_map (Complex.conjCLE : ℂ →L[ℝ] ℂ) V (hv j)
  fin_cases i <;>
    simp [LinearWaveResidual.transport, LinearWaveResidual.realTransport,
      angularGenerator, LinearWaveResidual.realAngularGenerator, hd, hc,
      div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re, Complex.mul_im] <;> ring

theorem conjugate_angularIndependent {s : StripData D} {P : ℕ → D → ℝ} {α κ : ℝ}
    (G : Geometry s κ) {a : Family D} (ha : WaveVector s P α a)
    (haθ : AngularIndependent G a) : AngularIndependent G (conjugateFamily a) := by
  intro n i x hx
  have hd := (((ha i).smooth n).contDiffAt (s.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  change along (G.angular n) (fun y => (Complex.conjCLE : ℂ →L[ℝ] ℂ) (a n y i)) x = 0
  rw [LinearWaveResidual.along_map _ _ hd, haθ n i x hx, map_zero]

/-- Exact real reconstruction: the two output harmonics are the sum and
difference of the two input harmonics. No angular averaging is assumed. -/
theorem real_modes_identity {s : StripData D} {P : ℕ → D → ℝ} {β κ : ℝ}
    (G : Geometry s κ) (Φ : ℕ → D → ℝ) (ν ξ : ℕ → ℝ) (a b : Family D)
    (hb : WaveVector s P β b) (hbθ : AngularIndependent G b)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (Φ n) s.domain)
    (n : ℕ) {x : D} (hx : x ∈ s.domain) (i : Fin 3) :
    LinearWaveResidual.realTransport (G.radius n) (G.radial n) (G.angular n) (G.axial n)
      (fun y j => (vectorMode (ν n) (Φ n) (a n) y j).re)
      (fun y j => (vectorMode (ξ n) (Φ n) (b n) y j).re) x i =
      ((sameCoefficient G Φ ξ a b n x i * carrier (ν n + ξ n) (Φ n) x).re +
        (sameCoefficient G Φ (fun n => -(ξ n)) a (conjugateFamily b) n x i *
          carrier (ν n - ξ n) (Φ n) x).re) / 2 := by
  have hp := ((hΦ n).contDiffAt (s.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hbd j := (((hb j).smooth n).contDiffAt (s.isOpen_domain.mem_nhds hx)).differentiableAt (by
      simp)
  have hbc := conjugate_wave hb
  have hbcd j := (((hbc j).smooth n).contDiffAt (s.isOpen_domain.mem_nhds hx)).differentiableAt (by
      simp)
  have hmode j : DifferentiableAt ℝ (fun y => vectorMode (ξ n) (Φ n) (b n) y j) x :=
    ((contDiffOn_mode (ξ n) (hΦ n) ((hb j).smooth n)).contDiffAt
      (s.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  rw [transport_real_parts _ _ _ _ _ hmode]
  have hc : (fun y j => star (vectorMode (ξ n) (Φ n) (b n) y j)) =
      vectorMode (-(ξ n)) (Φ n) (conjugateFamily b n) := by
    funext y j
    exact (vectorMode_conjugate (ξ n) (Φ n) (b n) y j).symm
  rw [hc, same_label_identity G Φ ν ξ a b hbθ n hx hp hbd,
    same_label_identity G Φ ν (fun n => -(ξ n)) a (conjugateFamily b)
      (conjugate_angularIndependent G hb hbθ) n hx hp hbcd]
  rfl

/-- Equal input frequencies have an exact doubled-frequency term and an
opposite-frequency mean term, each with its real reconstruction factor. -/
theorem real_equal_modes_identity {s : StripData D} {P : ℕ → D → ℝ} {β κ : ℝ}
    (G : Geometry s κ) (Φ : ℕ → D → ℝ) (ν : ℕ → ℝ) (a b : Family D)
    (hb : WaveVector s P β b) (hbθ : AngularIndependent G b)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (Φ n) s.domain)
    (n : ℕ) {x : D} (hx : x ∈ s.domain) (i : Fin 3) :
    LinearWaveResidual.realTransport (G.radius n) (G.radial n) (G.angular n) (G.axial n)
      (fun y j => (vectorMode (ν n) (Φ n) (a n) y j).re)
      (fun y j => (vectorMode (ν n) (Φ n) (b n) y j).re) x i =
      (sameCoefficient G Φ ν a b n x i * carrier (2 * ν n) (Φ n) x).re / 2 +
        (sameCoefficient G Φ (fun n => -(ν n)) a (conjugateFamily b) n x i).re / 2 := by
  rw [real_modes_identity G Φ ν ν a b hb hbθ hΦ n hx, sub_self, carrier_zero, mul_one]
  rw [show ν n + ν n = 2 * ν n by ring]
  ring

theorem real_mean_coefficient_bound {s : StripData D} {P : ℕ → D → ℝ} {α β κ : ℝ}
    (G : Geometry s κ) (hκ : 0 ≤ κ) {Φ : ℕ → D → ℝ} {ν : ℕ → ℝ} {a b : Family D}
    (ha : WaveVector s P α a) (hb : WaveVector s P β b)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (Φ n) s.domain) (hν : ∀ n, ν n ≠ 0)
    (haθ : AngularIndependent G a)
    (hdiv : ∀ n x, x ∈ s.domain → cylindricalDivergence
      (G.radius n) (G.radial n) (G.angular n) (G.axial n) (vectorMode (ν n) (Φ n) (a n)) x = 0)
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) (i : Fin 3) :
    MeanClass s (α + β - κ) (fun n x =>
      (sameCoefficient G Φ (fun n => -(ν n)) a (conjugateFamily b) n x i).re / 2) := by
  have h := (conjugate_opposite_mean_bound G hκ ha hb hΦ hν haθ hdiv hP0 hP1 i).map
    ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
  unfold MeanClass
  simpa only [_root_.smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, div_eq_mul_inv, one_div, one_mul, mul_comm] using h

theorem divergence_congr {U : Set D} (hU : IsOpen U)
    (R : D → ℝ) (Vr Vθ Vz : D → D) {a b : D → ComplexVector}
    (hab : EqOn a b U) {x : D} (hx : x ∈ U) :
    cylindricalDivergence R Vr Vθ Vz a x = cylindricalDivergence R Vr Vθ Vz b x := by
  have hi (i : Fin 3) : EqOn (fun y => a y i) (fun y => b y i) U :=
    fun y hy => congrFun (hab hy) i
  unfold cylindricalDivergence
  rw [along_congr hU (hi 0) hx, along_congr hU (hi 1) hx,
    along_congr hU (hi 2) hx, hab hx]

/-- Exact curl realization supplies the solenoidality used in the saved
half-power estimate. The equality is required on a neighborhood, so every
derivative of the actual field participates in the identity. -/
theorem same_label_from_curl {s : StripData D} {P : ℕ → D → ℝ} {α β κ : ℝ}
    (G : Geometry s κ) (hκ : 0 ≤ κ) {Φ : ℕ → D → ℝ} {ν ξ : ℕ → ℝ}
    {a b B : Family D} (ha : WaveVector s P α a) (hb : WaveVector s P β b)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (Φ n) s.domain) (hν : ∀ n, ν n ≠ 0)
    (hratio : BandBound s 0 (fun n => ξ n / ν n)) (haθ : AngularIndependent G a)
    (hG : ∀ n, CurlClassBounds.CylindricalGeometry s.domain
      (G.radius n) (G.radial n) (G.angular n) (G.axial n))
    (hB : ∀ n, ContDiffOn ℝ ∞ (B n) s.domain)
    (hcurl : ∀ n, EqOn (vectorMode (ν n) (Φ n) (a n))
      (CurlClassBounds.cylindricalCurl (G.radius n) (G.radial n) (G.angular n) (G.axial n) (B n))
      s.domain)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1)
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) :
    WaveVector s P (α + β - κ) (sameCoefficient G Φ ξ a b) := by
  apply same_label_wave_bound G hκ ha hb hΦ hν hratio haθ _ hζ hP0 hP1
  intro n x hx
  rw [divergence_congr s.isOpen_domain _ _ _ _ (hcurl n) hx]
  exact CurlClassBounds.divergence_curl_zero (hG n) (hB n) hx

/-- A direct specialization to the manuscript's constructed vector potential.
Its curl remainder is part of the realized coefficient on both sides. -/
theorem same_label_from_realized {s : StripData D} {P : ℕ → D → ℝ} {α β κ : ℝ}
    (G : Geometry s κ) (hκ : 0 ≤ κ) {Φ : ℕ → D → ℝ} {ν ξ : ℕ → ℝ}
    {a₀ b : Family D}
    (ha : WaveVector s P α (fun n => CurlClassBounds.realizedCoefficient (ν n)
      (G.radius n) (G.radial n) (G.angular n) (G.axial n) (Φ n) (a₀ n)))
    (hb : WaveVector s P β b)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (Φ n) s.domain) (hν : ∀ n, ν n ≠ 0)
    (hratio : BandBound s 0 (fun n => ξ n / ν n))
    (haθ : AngularIndependent G (fun n => CurlClassBounds.realizedCoefficient (ν n)
      (G.radius n) (G.radial n) (G.angular n) (G.axial n) (Φ n) (a₀ n)))
    (hG : ∀ n, CurlClassBounds.CylindricalGeometry s.domain
      (G.radius n) (G.radial n) (G.angular n) (G.axial n))
    (ha₀ : ∀ n, ContDiffOn ℝ ∞ (a₀ n) s.domain)
    (hn : ∀ n x, x ∈ s.domain →
      phaseNormal (G.radius n) (G.radial n) (G.angular n) (G.axial n) (Φ n) x ≠ 0)
    (ht : ∀ n x, x ∈ s.domain → normalDot
      (phaseNormal (G.radius n) (G.radial n) (G.angular n) (G.axial n) (Φ n) x) (a₀ n x) = 0)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1)
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) :
    WaveVector s P (α + β - κ) (sameCoefficient G Φ ξ
      (fun n => CurlClassBounds.realizedCoefficient (ν n)
        (G.radius n) (G.radial n) (G.angular n) (G.axial n) (Φ n) (a₀ n)) b) := by
  apply same_label_wave_bound G hκ ha hb hΦ hν hratio haθ _ hζ hP0 hP1
  intro n x hx
  exact CurlClassBounds.realizedCoefficient_divergence (hG n) (hν n) (hΦ n) (ha₀ n)
    (hn n) (ht n) hx

/-- Multiplying by the actual curl of the second field still vanishes on
disjoint supports; this includes every coefficient derivative and frame term. -/
theorem product_curl_zero {U : Set D} (hU : IsOpen U)
    (R : D → ℝ) (Vr Vθ Vz : D → D) {a b : D → ComplexVector}
    (ha : ∀ i, ContinuousOn (fun y => a y i) U)
    (hab : ∀ i j y, y ∈ U → a y i * b y j = 0)
    {x : D} (hx : x ∈ U) (i j : Fin 3) :
    a x i * CurlClassBounds.cylindricalCurl R Vr Vθ Vz b x j = 0 := by
  have hD (V : D → D) (k : Fin 3) :=
    mul_along_zero hU hx ((ha i x hx).continuousAt (hU.mem_nhds hx)) (hab i k) V
  fin_cases j
  · change a x i * ((R x)⁻¹ • along Vθ (fun y => b y 2) x - along Vz (fun y => b y 1) x) = 0
    rw [Complex.real_smul]
    calc
      _ = ((R x)⁻¹ : ℂ) * (a x i * along Vθ (fun y => b y 2) x) -
          a x i * along Vz (fun y => b y 1) x := by simp only [Complex.ofReal_inv]; ring
      _ = 0 := by rw [hD Vθ 2, hD Vz 1]; ring
  · change a x i * (along Vz (fun y => b y 0) x - along Vr (fun y => b y 2) x) = 0
    rw [mul_sub, hD Vz 0, hD Vr 2, sub_self]
  · change a x i * (along Vr (fun y => b y 1) x + (R x)⁻¹ • b x 1 -
      (R x)⁻¹ • along Vθ (fun y => b y 0) x) = 0
    simp only [Complex.real_smul]
    calc
      _ = a x i * along Vr (fun y => b y 1) x + ((R x)⁻¹ : ℂ) * (a x i * b x 1) -
          ((R x)⁻¹ : ℂ) * (a x i * along Vθ (fun y => b y 0) x) := by
            simp only [Complex.ofReal_inv]
            ring
      _ = 0 := by rw [hD Vr 1, hab i 1 x hx, hD Vθ 0]; ring

theorem curl_cross_products {U : Set D} {R : D → ℝ} {Vr Vθ Vz : D → D}
    (G : CurlClassBounds.CylindricalGeometry U R Vr Vθ Vz) {a b : D → ComplexVector}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hab : ∀ i j y, y ∈ U → a y i * b y j = 0)
    {x : D} (hx : x ∈ U) (i j : Fin 3) :
    CurlClassBounds.cylindricalCurl R Vr Vθ Vz a x i *
      CurlClassBounds.cylindricalCurl R Vr Vθ Vz b x j = 0 := by
  have hcb := CurlClassBounds.cylindricalCurl_contDiffOn G.isOpen
    (G.radius_smooth.inv G.radius_ne) G.radial_smooth G.angular_smooth G.axial_smooth hb
  have hac (k : Fin 3) : ContinuousOn (fun y => a y k) U := (contDiffOn_pi.mp ha k).continuousOn
  have hcbc (k : Fin 3) : ContinuousOn
      (fun y => CurlClassBounds.cylindricalCurl R Vr Vθ Vz b y k) U :=
    (contDiffOn_pi.mp hcb k).continuousOn
  have hba : ∀ k l y, y ∈ U → CurlClassBounds.cylindricalCurl R Vr Vθ Vz b y k * a y l = 0 := by
    intro k l y hy
    rw [mul_comm]
    exact product_curl_zero G.isOpen R Vr Vθ Vz hac hab hy l k
  rw [mul_comm]
  exact product_curl_zero G.isOpen R Vr Vθ Vz hcbc hba hx j i

theorem curl_transport_zero {U : Set D} {R : D → ℝ} {Vr Vθ Vz : D → D}
    (G : CurlClassBounds.CylindricalGeometry U R Vr Vθ Vz) {a b : D → ComplexVector}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hab : ∀ i j y, y ∈ U → a y i * b y j = 0) {x : D} (hx : x ∈ U) :
    LinearWaveResidual.transport R Vr Vθ Vz
      (CurlClassBounds.cylindricalCurl R Vr Vθ Vz a)
      (CurlClassBounds.cylindricalCurl R Vr Vθ Vz b) x = 0 := by
  have hca := CurlClassBounds.cylindricalCurl_contDiffOn G.isOpen
    (G.radius_smooth.inv G.radius_ne) G.radial_smooth G.angular_smooth G.axial_smooth ha
  apply transport_zero_of_products G.isOpen R Vr Vθ Vz
    (fun i => (contDiffOn_pi.mp hca i).continuousOn) _ hx
  intro i j y hy
  exact curl_cross_products G ha hb hab hy i j

theorem curl_transport_every_class {s : StripData D} {P : ℕ → D → ℝ} {γ κ : ℝ}
    (G : Geometry s κ) {a b : Family D}
    (hG : ∀ n, CurlClassBounds.CylindricalGeometry s.domain
      (G.radius n) (G.radial n) (G.angular n) (G.axial n))
    (ha : ∀ n, ContDiffOn ℝ ∞ (a n) s.domain) (hb : ∀ n, ContDiffOn ℝ ∞ (b n) s.domain)
    (hab : ∀ n i j x, x ∈ s.domain → a n x i * b n x j = 0)
    (hP : ∀ n x, x ∈ s.domain → 0 ≤ P n x) :
    WaveVector s P γ (fun n => LinearWaveResidual.transport
      (G.radius n) (G.radial n) (G.angular n) (G.axial n)
      (CurlClassBounds.cylindricalCurl (G.radius n) (G.radial n) (G.angular n) (G.axial n) (a n))
      (CurlClassBounds.cylindricalCurl (G.radius n) (G.radial n) (G.angular n) (G.axial n) (b n)))
          := by
  intro i
  apply class_congr (MemClass.zero
    (fun n x hx => mul_nonneg (Real.sqrt_nonneg (s.zeta x)) (hP n x hx)))
  intro n x hx
  exact (congrFun (curl_transport_zero (hG n) (ha n) (hb n) (hab n) hx) i).symm

/-- The separated, covered slots make the actual curl-wave interaction zero.
This remains true at the boundaries of the supports. -/
theorem slot_curl_transport_zero {U : Set D}
    {R : D → ℝ} {Vr Vθ Vz : D → D}
    (G : CurlClassBounds.CylindricalGeometry U R Vr Vθ Vz)
    {d h : ℝ} {vr vt : PartitionedCovariance.Plane}
    (sys : PartitionedCovariance.SlotSystem d h vr vt)
    {L M : SlotColoring.Label} (hL : 1 ≤ L.1) (hM : 1 ≤ M.1) (hne : L ≠ M)
    (q : D → ℝ) (X : D → SlotColoring.Position) (Y : D → PartitionedCovariance.Plane)
    (hq : ∀ y ∈ U, 0 < q y)
    (f g : Fin 3 → PartitionedCovariance.Plane → ℝ) (a b : D → ComplexVector)
    (hf : ∀ i, Function.support (f i) ⊆ PartitionedCovariance.slotSet h sys.radius vr vt L)
    (hg : ∀ i, Function.support (g i) ⊆ PartitionedCovariance.slotSet h sys.radius vr vt M)
    (ha : ContDiffOn ℝ ∞ (slotField d h L q X Y f a) U)
    (hb : ContDiffOn ℝ ∞ (slotField d h M q X Y g b) U)
    {x : D} (hx : x ∈ U) :
    LinearWaveResidual.transport R Vr Vθ Vz
      (CurlClassBounds.cylindricalCurl R Vr Vθ Vz (slotField d h L q X Y f a))
      (CurlClassBounds.cylindricalCurl R Vr Vθ Vz (slotField d h M q X Y g b)) x = 0 := by
  apply curl_transport_zero G ha hb _ hx
  intro i j y hy
  exact slot_complex_product_zero sys hL hM hne (hf i) (hg j) (hq y hy) (X y) (Y y)
    (a y i) (b y j)

open ProblemStatement in
theorem realTransport_coordinates (u : Space → Space) {v : Space → Space} {q : Space}
    (hv : DifferentiableAt ℝ v q) (i : Fin 3) :
    LinearWaveResidual.realTransport (fun y : Space => y 0)
      (fun _ => coordinateVector 0) (fun _ => coordinateVector 1) (fun _ => coordinateVector 2)
      (fun y j => u y j) (fun y j => v y j) q i =
        LinearWaveResidual.bilinearAdvection u v q i := by
  have hd (k j : Fin 3) : along (fun _ => coordinateVector k) (fun y => v y j) q =
      CylindricalResidual.dCoord k v q j :=
    CylindricalResidual.dCoord_map (AxisymmetricFields.projection j) hv k
  fin_cases i <;>
    simp [LinearWaveResidual.realTransport, LinearWaveResidual.bilinearAdvection, hd,
      LinearWaveResidual.realAngularGenerator, CylindricalResidual.connection_apply] <;> ring

open ProblemStatement in
/-- The real bilinear operator estimated above is obtained from the actual
Cartesian derivative by the cylindrical frame, on positive radius. -/
theorem cartesian_transport_components {u v : Space → Space} {q : Space}
    (hv : DifferentiableAt ℝ v (CylindricalResidual.chart q)) (hr : 0 < q 0) (i : Fin 3) :
    (CylindricalResidual.frame (-(q 1))
      (fderiv ℝ v (CylindricalResidual.chart q) (u (CylindricalResidual.chart q)))) i =
      LinearWaveResidual.realTransport (fun y : Space => y 0)
        (fun _ => coordinateVector 0) (fun _ => coordinateVector 1) (fun _ => coordinateVector 2)
        (fun y j => CylindricalResidual.components u y j)
        (fun y j => CylindricalResidual.components v y j) q i := by
  rw [LinearWaveResidual.cartesianBilinearAdvection_components hv (ne_of_gt hr),
    CylindricalResidual.frame_inverse]
  exact (realTransport_coordinates _ (CylindricalResidual.differentiableAt_components hv) i).symm

/-- Fixed geometry, bundling `radius`, `radial`, `angular`, `axial` and the required
compatibility proofs. -/
noncomputable def fixedGeometry {s : StripData D} {κ : ℝ}
    (R : D → ℝ) (Vr Vθ Vz : ℕ → D → D)
    (hR : ∀ x ∈ s.domain, 0 < R x)
    (hr : UnweightedClass s (-κ) Vr) (hz : UnweightedClass s 1 Vz)
    (hinv : UnweightedClass s 0 (fun _ x => (R x)⁻¹)) : Geometry s κ where
  radius := fun _ => R
  radial := Vr
  angular := Vθ
  axial := Vz
  radius_pos := fun _ => hR
  radial_class := hr
  axial_class := hz
  inverse_radius_class := hinv

/-- The input wave classes in the interaction estimate can themselves be
generated from seed amplitudes by the proved curl-remainder bounds. -/
theorem realized_seed_pair_bound {s : StripData D} {P : ℕ → D → ℝ} {α β κ δ M : ℝ}
    (R : D → ℝ) (Vr Vθ Vz : ℕ → D → D)
    (hR : ∀ x ∈ s.domain, 0 < R x)
    (hr : UnweightedClass s (-κ) Vr) (hθ : UnweightedClass s 0 Vθ)
    (hz : UnweightedClass s 1 Vz) (hinv : UnweightedClass s 0 (fun _ x => (R x)⁻¹))
    {Φ : ℕ → D → ℝ} {ν ξ : ℕ → ℝ} {a₀ b₀ : Family D}
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s)
      (fun n => phaseNormal R (Vr n) (Vθ n) (Vz n) (Φ n)))
    (ha₀ : WaveClass s P α a₀) (hb₀ : WaveClass s P β b₀) (hδ : 0 < δ)
    (hlower : ∀ n x, x ∈ s.domain → δ ≤ ‖phaseNormal R (Vr n) (Vθ n) (Vz n) (Φ n) x‖)
    (hupper : ∀ n x, x ∈ s.domain → ‖phaseNormal R (Vr n) (Vθ n) (Vz n) (Φ n) x‖ ≤ M)
    (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hνinv : BandBound s (1 / 2) (fun n => 1 / ν n))
    (hξinv : BandBound s (1 / 2) (fun n => 1 / ξ n))
    (hν : ∀ n, ν n ≠ 0) (hratio : BandBound s 0 (fun n => ξ n / ν n))
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (Φ n) s.domain)
    (hG : ∀ n, CurlClassBounds.CylindricalGeometry s.domain R (Vr n) (Vθ n) (Vz n))
    (ht : ∀ n x, x ∈ s.domain → normalDot (phaseNormal R (Vr n) (Vθ n) (Vz n) (Φ n) x) (a₀ n x) = 0)
    (haθ : ∀ n i x, x ∈ s.domain → along (Vθ n)
      (fun y => CurlClassBounds.realizedCoefficient (ν n) R (Vr n) (Vθ n) (Vz n) (Φ n) (a₀ n) y i)
          x = 0)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1)
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) :
    WaveVector s P (α + β - κ)
      (sameCoefficient (fixedGeometry R Vr Vθ Vz hR hr hz hinv) Φ ξ
        (fun n => CurlClassBounds.realizedCoefficient (ν n) R (Vr n) (Vθ n) (Vz n) (Φ n) (a₀ n))
        (fun n => CurlClassBounds.realizedCoefficient (ξ n) R (Vr n) (Vθ n) (Vz n) (Φ n) (b₀ n)))
            := by
  have ha := CurlClassBounds.realizedCoefficient_waveClass hN ha₀ hδ hlower hupper
    hκ hκhalf hr hθ hz hinv hνinv
  have hb := CurlClassBounds.realizedCoefficient_waveClass hN hb₀ hδ hlower hupper
    hκ hκhalf hr hθ hz hinv hξinv
  apply same_label_from_realized (fixedGeometry R Vr Vθ Vz hR hr hz hinv) hκ
    (fun i => CurlClassBounds.class_component ha i)
    (fun i => CurlClassBounds.class_component hb i)
    hΦ hν hratio haθ hG ha₀.smooth _ ht hζ hP0 hP1
  intro n x hx hn
  change phaseNormal R (Vr n) (Vθ n) (Vz n) (Φ n) x = 0 at hn
  have hh := hlower n x hx
  rw [hn, norm_zero] at hh
  linarith

/-- Finite harmonic sets generated by retention, conjugation and quadratic
interaction. The recursive definition retains zero harmonics as well. -/
noncomputable def stageHarmonics (initial : Finset ℤ) : ℕ → Finset ℤ
  | 0 => initial
  | stage + 1 =>
    let current := stageHarmonics initial stage
    current ∪ current.image (fun j => -j) ∪ (current.product current).image (fun p => p.1 + p.2)

theorem stageHarmonics_bound {initial : Finset ℤ} {M : ℝ} (hM : 0 ≤ M)
    (hinitial : ∀ j ∈ initial, |(j : ℝ)| ≤ M) (stage : ℕ) {j : ℤ}
    (hj : j ∈ stageHarmonics initial stage) : |(j : ℝ)| ≤ 2 ^ stage * M := by
  induction stage generalizing j with
  | zero => simpa only [stageHarmonics, pow_zero, one_mul] using hinitial j hj
  | succ stage ih =>
    have hgrow : 2 ^ stage * M ≤ 2 ^ (stage + 1) * M := by
      rw [pow_succ]
      have hnonneg : 0 ≤ (2 : ℝ) ^ stage * M := mul_nonneg (by positivity) hM
      linarith
    rw [stageHarmonics, Finset.mem_union, Finset.mem_union] at hj
    rcases hj with (hj | hj) | hj
    · exact (ih hj).trans hgrow
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      exact (harmonic_stage_neg stage (ih hk)).trans hgrow
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
      exact harmonic_stage_add stage (ih hp₁) (ih hp₂)

theorem stage_frequency_bound {s : StripData D} {β M : ℝ} {k : ℕ → ℝ}
    {initial : ℕ → Finset ℤ} {j : ℕ → ℤ} (hk : BandBound s β k) (hM : 0 ≤ M)
    (hinitial : ∀ n l, l ∈ initial n → |(l : ℝ)| ≤ M)
    (stage : ℕ) (hj : ∀ n, j n ∈ stageHarmonics (initial n) stage) :
    BandBound s β (fun n => k n * (j n : ℝ)) :=
  bandBound_frequency hk (mul_nonneg (by positivity) hM)
    (fun n => stageHarmonics_bound hM (hinitial n) stage (hj n))

/-- A complete ordered interaction endpoint: the coefficient is in the
claimed all-jet class and reconstructs the actual differential product. -/
theorem same_label_curl_interaction {s : StripData D} {P : ℕ → D → ℝ} {α β κ : ℝ}
    (G : Geometry s κ) (hκ : 0 ≤ κ) {Φ : ℕ → D → ℝ} {ν ξ : ℕ → ℝ}
    {a b B : Family D} (ha : WaveVector s P α a) (hb : WaveVector s P β b)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (Φ n) s.domain) (hν : ∀ n, ν n ≠ 0)
    (hratio : BandBound s 0 (fun n => ξ n / ν n))
    (haθ : AngularIndependent G a) (hbθ : AngularIndependent G b)
    (hG : ∀ n, CurlClassBounds.CylindricalGeometry s.domain
      (G.radius n) (G.radial n) (G.angular n) (G.axial n))
    (hB : ∀ n, ContDiffOn ℝ ∞ (B n) s.domain)
    (hcurl : ∀ n, EqOn (vectorMode (ν n) (Φ n) (a n))
      (CurlClassBounds.cylindricalCurl (G.radius n) (G.radial n) (G.angular n) (G.axial n) (B n))
      s.domain)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1)
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) :
    ∃ c : Family D, WaveVector s P (α + β - κ) c ∧
      ∀ n x, x ∈ s.domain → LinearWaveResidual.transport
        (G.radius n) (G.radial n) (G.angular n) (G.axial n)
        (vectorMode (ν n) (Φ n) (a n)) (vectorMode (ξ n) (Φ n) (b n)) x =
          fun i => c n x i * carrier (ν n + ξ n) (Φ n) x := by
  refine ⟨sameCoefficient G Φ ξ a b,
    same_label_from_curl G hκ ha hb hΦ hν hratio haθ hG hB hcurl hζ hP0 hP1, ?_⟩
  intro n x hx
  funext i
  exact same_label_identity G Φ ν ξ a b hbθ n hx
    (((hΦ n).contDiffAt (s.isOpen_domain.mem_nhds hx)).differentiableAt (by simp))
    (fun j => (((hb j).smooth n).contDiffAt (s.isOpen_domain.mem_nhds hx)).differentiableAt (by
        simp)) i

end

end NavierStokes.WaveInteractionBounds
