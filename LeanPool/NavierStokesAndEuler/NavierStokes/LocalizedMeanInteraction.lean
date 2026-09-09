/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalizedWaveBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicWaveInteraction

@[expose] public section

/-!
# Mean interactions from support-local phase estimates

The phase normal is estimated only on the genuine native phase patch.
Outside that patch the wave coefficients have zero germs, which force
the actual mean interaction to have a zero germ as well.
-/

noncomputable section

namespace NavierStokes.LocalizedMeanInteraction

open Set Function Filter WeightedClasses HarmonicCalculus HarmonicFields
open LocalizedWaveBounds WaveInteractionBounds HarmonicMeanInteraction
open scoped Topology ContDiff BigOperators ComplexConjugate


variable {D : Type} {I E : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev LocalMean (s : StripData D) (C : ℕ → I → Set D) (α : ℝ)
    (f : ℕ → I → D → E) : Prop := LocalClass s C (fun _ _ x => s.zeta x) α f

noncomputable def LocalMeanVector (s : StripData D) (C : ℕ → I → Set D) (H : ℝ)
    (m : ℕ → I → D → ComplexVector) : Prop :=
  LocalMean s C (H + 1) (fun n l x => m n l x 0) ∧
    LocalMean s C H (fun n l x => m n l x 1) ∧
    LocalMean s C H (fun n l x => m n l x 2)

theorem localMean_component {s : StripData D} {C : ℕ → I → Set D} {H : ℝ}
    {m : ℕ → I → D → ComplexVector} (hm : LocalMeanVector s C H m) (i : Fin 3) :
    LocalMean s C H (fun n l x => m n l x i) := by
  fin_cases i
  · exact hm.1.mono_exponent (by linarith)
  · exact hm.2.1
  · exact hm.2.2

theorem local_cmul {s : StripData D} {C : ℕ → I → Set D}
    {w v : ℕ → I → D → ℝ} {α β : ℝ} {f g : ℕ → I → D → ℂ}
    (hf : LocalClass s C w α f) (hg : LocalClass s C v β g) :
    LocalClass s C (fun n l x => w n l x * v n l x) (α + β)
      (fun n l x => f n l x * g n l x) :=
  hf.bilinear hg (ContinuousLinearMap.mul ℝ ℂ)

theorem local_mean_wave_cmul {s : StripData D} {C : ℕ → I → Set D}
    {P : ℕ → I → D → ℝ} {α β : ℝ} {f g : ℕ → I → D → ℂ}
    (hf : LocalMean s C α f) (hg : LocalWave s C P β g)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1) :
    LocalWave s C P (α + β) (fun n l x => f n l x * g n l x) := by
  apply (local_cmul hf hg).mono_weight hg.weight_nonneg
  intro n l x hx _
  exact mul_le_of_le_one_left (hg.weight_nonneg n l x hx) (hζ x hx)

theorem local_wave_mean_cmul {s : StripData D} {C : ℕ → I → Set D}
    {P : ℕ → I → D → ℝ} {α β : ℝ} {f g : ℕ → I → D → ℂ}
    (hf : LocalWave s C P α f) (hg : LocalMean s C β g)
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1) :
    LocalWave s C P (α + β) (fun n l x => f n l x * g n l x) := by
  simpa only [add_comm β α, mul_comm] using local_mean_wave_cmul hg hf hζ

theorem local_along {s : StripData D} {C : ℕ → I → Set D}
    {w : ℕ → I → D → ℝ} {α β : ℝ} {f : ℕ → I → D → E} {V : ℕ → I → D → D}
    (hf : LocalClass s C w α f) (hV : LocalUnweighted s C β V) :
    LocalClass s C w (α + β) (fun n l => along (V n l) (f n l)) := by
  have hh := hV.bilinear hf.fderiv (ContinuousLinearMap.apply ℝ E)
  simp only [one_mul, add_comm β α, ContinuousLinearMap.apply_apply] at hh ⊢
  exact hh

theorem local_div_radius {s : StripData D} {C : ℕ → I → Set D}
    {w : ℕ → I → D → ℝ} {α κ : ℝ} (G : Geometry s κ)
    {f : ℕ → I → D → ℂ} (hf : LocalClass s C w α f) :
    LocalClass s C w α (fun n l x => f n l x / (G.radius n x : ℂ)) := by
  have hi : LocalUnweighted s C 0 (fun n _ x => ((G.radius n x : ℂ))⁻¹) :=
    LocalClass.of_global (inverse_radius_complex G)
  simpa only [zero_add, one_mul, mul_one, div_eq_mul_inv, mul_comm] using local_cmul hi hf

theorem local_mean_advects_wave {s : StripData D} {C : ℕ → I → Set D}
    {P : ℕ → I → D → ℝ} {α H κ : ℝ} (G : Geometry s κ) (hκ : κ ≤ 1)
    {m a : ℕ → I → D → ComplexVector} (hm : LocalMeanVector s C H m)
    (ha : ∀ i, LocalWave s C P α (fun n l x => a n l x i))
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1) (i : Fin 3) :
    LocalWave s C P (α + H) (fun n l x =>
      strippedTransport G (fun n => m n l) (fun n => a n l) n x i) := by
  have hr := local_mean_wave_cmul hm.1
    (local_along (ha i) (LocalClass.of_global G.radial_class)) hζ
  have hr' := hr.mono_exponent (show α + H ≤ H + 1 + (α + -κ) by linarith)
  have hc := local_mean_wave_cmul (local_div_radius G hm.2.1)
    (LocalizedWaveBounds.angular_classes ha i) hζ
  have hc' : LocalWave s C P (α + H) (fun n l x =>
      m n l x 1 / (G.radius n x : ℂ) * angularGenerator (a n l x) i) := by
    simpa only [add_comm H α] using hc
  have hz := local_mean_wave_cmul hm.2.2
    (local_along (ha i) (LocalClass.of_global G.axial_class)) hζ
  have hz' := hz.mono_exponent (show α + H ≤ H + (α + 1) by linarith)
  exact (hr'.add hc').add hz'

theorem local_wave_advects_mean {s : StripData D} {C : ℕ → I → Set D}
    {P : ℕ → I → D → ℝ} {α H κ : ℝ} (G : Geometry s κ) (hκ : 0 ≤ κ)
    {m a : ℕ → I → D → ComplexVector} (hm : LocalMeanVector s C H m)
    (ha : ∀ i, LocalWave s C P α (fun n l x => a n l x i))
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1) (i : Fin 3) :
    LocalWave s C P (α + H - κ) (fun n l x =>
      strippedTransport G (fun n => a n l) (fun n => m n l) n x i) := by
  have hr := local_wave_mean_cmul (ha 0)
    (local_along (localMean_component hm i) (LocalClass.of_global G.radial_class)) hζ
  have hr' : LocalWave s C P (α + H - κ) (fun n l x =>
      a n l x 0 * along (G.radial n) (fun y => m n l y i) x) := by
    simpa only [sub_eq_add_neg, add_assoc] using hr
  have hc := local_wave_mean_cmul (local_div_radius G (ha 1))
    (LocalizedWaveBounds.angular_classes (localMean_component hm) i) hζ
  have hc' := hc.mono_exponent (show α + H - κ ≤ α + H by linarith)
  have hz := local_wave_mean_cmul (ha 2)
    (local_along (localMean_component hm i) (LocalClass.of_global G.axial_class)) hζ
  have hz' := hz.mono_exponent (show α + H - κ ≤ α + (H + 1) by linarith)
  exact (hr'.add hc').add hz'

theorem local_normalDot {s : StripData D} {C : ℕ → I → Set D}
    {w : ℕ → I → D → ℝ} {α : ℝ}
    {N : ℕ → I → D → EuclideanSpace ℝ (Fin 3)} {a : ℕ → I → D → ComplexVector}
    (hN : ∀ i, LocalUnweighted s C 0 (fun n l x => N n l x i))
    (ha : ∀ i, LocalClass s C w α (fun n l x => a n l x i)) :
    LocalClass s C w α (fun n l x => normalDot (N n l x) (a n l x)) := by
  have hh (i : Fin 3) : LocalClass s C w α
      (fun n l x => (N n l x i : ℂ) * a n l x i) := by
    simpa only [zero_add] using LocalizedWaveBounds.real_mul_complex (hN i) (ha i)
  exact ((hh 0).add (hh 1)).add (hh 2)

theorem local_waveMeanCoefficient {s : StripData D} {C : ℕ → I → Set D}
    {P : ℕ → I → D → ℝ} {α H κ : ℝ} (G : Geometry s κ)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1 / 2)
    {Φ : ℕ → I → D → ℝ} {ν : ℕ → I → ℝ} {m a : ℕ → I → D → ComplexVector}
    (hm : LocalMeanVector s C H m)
    (ha : ∀ i, LocalWave s C P α (fun n l x => a n l x i))
    (hN : ∀ i, LocalUnweighted s C 0 (fun n l x =>
      phaseNormal (G.radius n) (G.radial n) (G.angular n) (G.axial n) (Φ n l) x i))
    (hν : LocalUnweighted s C (-(1 / 2)) (fun n l _ => ν n l))
    (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1) (i : Fin 3) :
    LocalWave s C P (α + H - 1 / 2) (fun n l x =>
      waveMeanCoefficient G (fun n => Φ n l) (fun n => ν n l)
        (fun n => m n l) (fun n => a n l) n x i) := by
  have hma := (local_mean_advects_wave G (by linarith) hm ha hζ i).mono_exponent
    (show α + H - 1 / 2 ≤ α + H by linarith)
  have ham := (local_wave_advects_mean G hκ0 hm ha hζ i).mono_exponent
    (show α + H - 1 / 2 ≤ α + H - κ by linarith)
  have hphase := local_mean_wave_cmul
    (LocalizedWaveBounds.frequency_mul (local_normalDot hN (localMean_component hm)) hν) (ha i) hζ
  have hphase' : LocalWave s C P (α + H - 1 / 2) (fun n l x =>
      phaseFactor (ν n l) * normalDot
        (phaseNormal (G.radius n) (G.radial n) (G.angular n) (G.axial n) (Φ n l) x)
        (m n l x) * a n l x i) := by
    convert! hphase using 1
    ring
  exact (hma.add ham).add hphase'

theorem local_realCoefficient {s : StripData D} {C : ℕ → I → Set D}
    {P : ℕ → I → D → ℝ} {α : ℝ} (a : ℕ → I → Coefficients D) (j : ℤ)
    (ha : LocalWave s C P α (fun n l x => a n l j x))
    (han : LocalWave s C P α (fun n l x => a n l (-j) x)) :
    LocalWave s C P α (fun n l x => HarmonicResidual.realCoefficients (a n l) j x) := by
  have hh := LocalizedWaveBounds.constant_complex_mul
    (ha.add (han.map (Complex.conjCLE : ℂ →L[ℝ] ℂ))) ((2 : ℂ)⁻¹)
  apply hh.congr
  intro n l x
  exact (HarmonicResidual.realCoefficients_apply (a n l) j x).symm

theorem local_blockAmplitude {s : StripData D} {C : ℕ → I → Set D}
    {P : ℕ → I → D → ℝ} {α : ℝ} {b : I → CorrectionState.HarmonicBlock D}
    (hb : ∀ i j, j ≠ 0 → LocalWave s C P α (fun n l x => (b l).velocity n i j x))
    {j : ℤ} (hj : j ≠ 0) (i : Fin 3) :
    LocalWave s C P α (fun n l x => blockAmplitude (b l) n i j x) :=
  local_realCoefficient (fun n l => (b l).velocity n i) j (hb i j hj)
    (hb i (-j) (neg_ne_zero.mpr hj))

theorem local_frequency_mul_const {s : StripData D} {C : ℕ → I → Set D}
    {β : ℝ} {ν : ℕ → I → ℝ}
    (hν : LocalUnweighted s C β (fun n l _ => ν n l)) (r : ℝ) :
    LocalUnweighted s C β (fun n l _ => ν n l * r) := by
  apply (LocalizedWaveBounds.constant_real_mul hν r).congr
  intro n l x
  ring

theorem local_meanCross {s : StripData D} {C : ℕ → I → Set D}
    {P : ℕ → I → D → ℝ} {α H κ : ℝ}
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hκ : κ ≤ 1 / 2) (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    {h : I → MeanIncrementBounds.Triple D} {b : I → CorrectionState.HarmonicBlock D}
    (hm : LocalMeanVector s C H (fun n l => tripleField (h l) n))
    (hb : ∀ i j, j ≠ 0 → LocalWave s C P α (fun n l x => (b l).velocity n i j x))
    (hN : ∀ i, LocalUnweighted s C 0 (fun n l x => slowNormal c ho hR (b l).phase n x i))
    (hk : LocalUnweighted s C (-(1 / 2)) (fun n l _ => (b l).frequency n))
    (hkp : LocalUnweighted s C (-(1 / 2)) (fun n l _ => ((b l).angularFrequency n : ℝ)))
    {j : ℤ} (hj : j ≠ 0) (i : Fin 3) :
    LocalWave s C P (α + H - 1 / 2) (fun n l x => meanCross c (h l) (b l) n i j x) := by
  have ha := local_blockAmplitude hb hj
  have hν := local_frequency_mul_const hk (j : ℝ)
  have hs := local_waveMeanCoefficient (slowGeometry c ho hR) ho.kappa_nonneg hκ
    hm ha hN hν ho.weight_le_one i
  have hθ := local_mean_wave_cmul
    (LocalizedWaveBounds.frequency_mul (local_div_radius (slowGeometry c ho hR) hm.2.1)
      (local_frequency_mul_const hkp (j : ℝ))) (ha i) ho.weight_le_one
  have hθ' : LocalWave s C P (α + H - 1 / 2)
      (fun n l x => angularCarrierTerm c (b l) (h l) j n x i) := by
    convert! hθ using 1
    ring
  apply (hs.add hθ').congr
  intro n l x
  exact (meanCross_eq c ho hR (h l) (b l) j n x i).symm

/-! ## Zero germs and globalization -/

omit [NormedSpace ℝ D] in
theorem realCoefficient_zero_germ {a : Coefficients D} {j : ℤ} {x : D}
    (ha : a j =ᶠ[𝓝 x] fun _ => 0) (han : a (-j) =ᶠ[𝓝 x] fun _ => 0) :
    HarmonicResidual.realCoefficients a j =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [ha, han] with y hy hyn
  simp only [HarmonicResidual.realCoefficients_apply, hy, hyn, map_zero, add_zero, mul_zero]

theorem crossCoefficients_zero_germ (g : HarmonicResidual.Frame D)
    (k : ℝ) (Φ : D → ℝ) (kp : ℤ) (m : D → ComplexVector)
    (a : HarmonicResidual.VectorCoefficients D) (j : ℤ) {x : D}
    (ha : ∀ i, a i j =ᶠ[𝓝 x] fun _ => 0) (i : Fin 3) :
    crossCoefficients g k Φ kp m a i j =ᶠ[𝓝 x] fun _ => 0 := by
  have hr (r : Fin 3) : along g.radial (a r j) =ᶠ[𝓝 x] fun _ => 0 := by
    simpa only [PeriodizedWaveBounds.along_zero] using
      ParticularWaveAssembly.along_germ (ha r) g.radial
  have hz (r : Fin 3) : along g.axial (a r j) =ᶠ[𝓝 x] fun _ => 0 := by
    simpa only [PeriodizedWaveBounds.along_zero] using
      ParticularWaveAssembly.along_germ (ha r) g.axial
  filter_upwards [Filter.eventually_all.mpr ha, Filter.eventually_all.mpr hr,
    Filter.eventually_all.mpr hz] with y hay hry hzy
  have hav : (fun r => a r j y) = 0 := funext hay
  simp only [crossCoefficients, coeff_add, transport_constant_left, transport_constant_right,
    derivativeCoefficient, hry, hzy, hay]
  fin_cases i <;> simp [angularGenerator]

theorem meanCross_zero_germ (c : CorrectionState.Context D)
    (h : MeanIncrementBounds.Triple D) (b : CorrectionState.HarmonicBlock D)
    (n : ℕ) {j : ℤ} {x : D}
    (hz : ∀ i, (b.velocity n i j =ᶠ[𝓝 x] fun _ => 0) ∧
      (b.velocity n i (-j) =ᶠ[𝓝 x] fun _ => 0)) (i : Fin 3) :
    meanCross c h b n i j =ᶠ[𝓝 x] fun _ => 0 :=
  crossCoefficients_zero_germ (HarmonicResidual.contextFrame c n)
    (b.frequency n) (b.phase n) (b.angularFrequency n) (tripleField h n)
    (blockAmplitude b n) j (fun r => realCoefficient_zero_germ (hz r).1 (hz r).2) i

theorem realMeanCross_zero_germ (c : CorrectionState.Context D)
    (h : MeanIncrementBounds.Triple D) (b : CorrectionState.HarmonicBlock D)
    (n : ℕ) {j : ℤ} (hj : j ≠ 0) {x : D}
    (hz : ∀ i k, k ≠ 0 → b.velocity n i k =ᶠ[𝓝 x] fun _ => 0) (i : Fin 3) :
    HarmonicResidual.realCoefficients (meanCross c h b n i) j =ᶠ[𝓝 x] fun _ => 0 := by
  apply realCoefficient_zero_germ
  · exact meanCross_zero_germ c h b n (fun r => ⟨hz r j hj, hz r (-j) (neg_ne_zero.mpr hj)⟩) i
  · apply meanCross_zero_germ c h b n
    intro r
    exact ⟨hz r (-j) (neg_ne_zero.mpr hj), hz r (-(-j)) (by simpa using hj)⟩

theorem local_of_uniform {s : StripData D} {C : ℕ → I → Set D}
    {w : ℕ → I → D → ℝ} {α : ℝ} {f : I → ℕ → D → E}
    (hf : LabelSumBounds.UniformClass s (fun l n => w n l) α f) :
    LocalClass s C w α (fun n l => f l n) := by
  refine ⟨fun n l x hx => hf.weight_nonneg l n x hx,
    fun n l x hx _ => (hf.smooth l n).contDiffAt (s.isOpen_domain.mem_nhds hx), ?_⟩
  intro m
  obtain ⟨A, hA, p, hb⟩ := hf.bounds m
  exact ⟨A, hA, p, fun n l x hx _ j hj => hb l n x hx j hj⟩

theorem uniform_of_supported_local {s : StripData D} {C : ℕ → I → Set D}
    {w : ℕ → I → D → ℝ} {α : ℝ} {f : ℕ → I → D → E}
    (hf : LocalClass s C w α f)
    (hz : ∀ n l x, x ∈ s.domain → x ∉ C n l → f n l =ᶠ[𝓝 x] fun _ => 0) :
    LabelSumBounds.UniformClass s (fun l n => w n l) α (fun l n => f n l) := by
  have hall : LocalClass s (fun _ _ => Set.univ) w α f := hf.enlarge (by
    intro n l x hx _
    classical
    by_cases hi : x ∈ C n l
    · exact Or.inl hi
    · exact Or.inr (hz n l x hx hi))
  refine ⟨fun l n x hx => hall.weight_nonneg n l x hx,
    fun l n x hx => (hall.smooth n l x hx (Set.mem_univ x)).contDiffWithinAt, ?_⟩
  intro m
  obtain ⟨A, hA, p, hb⟩ := hall.bounds m
  exact ⟨A, hA, p, fun l n x hx j hj => hb n l x hx (Set.mem_univ x) j hj⟩

theorem uniform_constant {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {f : ℕ → D → E} (hf : MemClass s w α f) :
    LabelSumBounds.UniformClass s (fun _ : I => w) α (fun _ : I => f) := by
  refine ⟨fun _ => hf.weight_nonneg, fun _ => hf.smooth, ?_⟩
  intro m
  obtain ⟨A, hA, p, hb⟩ := hf.bounds m
  exact ⟨A, hA, p, fun _ => hb⟩

/-- A common coefficient estimated uniformly on every native copy
patch is estimated on their union with the very same constants. -/
theorem local_iUnion {J : Type*} [Nonempty J] {s : StripData D}
    {C : ℕ → I → J → Set D} {w : ℕ → I → D → ℝ} {α : ℝ}
    {f : ℕ → I → D → E}
    (hf : LocalClass s (fun (n : ℕ) (p : I × J) => C n p.1 p.2)
      (fun n p => w n p.1) α (fun n p => f n p.1)) :
    LocalClass s (fun n l => ⋃ j, C n l j) w α f := by
  classical
  refine ⟨fun n l x hx => hf.weight_nonneg n (l, Classical.arbitrary J) x hx, ?_, ?_⟩
  · intro n l x hx hi
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hi
    exact hf.smooth n (l, j) x hx hj
  · intro m
    obtain ⟨A, hA, p, hb⟩ := hf.bounds m
    refine ⟨A, hA, p, fun n l x hx hi k hk => ?_⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hi
    exact hb n (l, j) x hx hj k hk

omit [NormedSpace ℝ D] in
theorem velocity_zero_germs_of_tsupport (b : CorrectionState.HarmonicBlock D)
    {C : ℕ → Set D}
    (hs : ∀ n i j, j ≠ 0 → tsupport (b.velocity n i j) ⊆ C n)
    (n : ℕ) {x : D} (hx : x ∉ C n) (i : Fin 3) (j : ℤ) (hj : j ≠ 0) :
    b.velocity n i j =ᶠ[𝓝 x] fun _ => 0 :=
  PeriodizedWaveBounds.zero_germ_of_support isClosed_closure subset_closure
    (fun hmem => hx (hs n i j hj hmem))

/-- All constants precede the external label as well as the band.
Only the actual phase patch carries a normal estimate. -/
theorem uniform_realMeanCross_class {s : StripData D} {C : ℕ → I → Set D}
    {P : ℕ → I → D → ℝ} {α H κ : ℝ}
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hκ : κ ≤ 1 / 2) (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    {h : MeanIncrementBounds.Triple D} (hh : MeanIncrementBounds.IncrementBounds s H h)
    {b : I → CorrectionState.HarmonicBlock D}
    (hb : ∀ i j, j ≠ 0 → LabelSumBounds.UniformClass s
      (fun l n x => Real.sqrt (s.zeta x) * P n l x) α (fun l n x => (b l).velocity n i j x))
    (hN : ∀ i, LocalUnweighted s C 0 (fun n l x => slowNormal c ho hR (b l).phase n x i))
    (hk : LocalUnweighted s C (-(1 / 2)) (fun n l _ => (b l).frequency n))
    (hkp : LocalUnweighted s C (-(1 / 2)) (fun n l _ => ((b l).angularFrequency n : ℝ)))
    (hz : ∀ n l x, x ∈ s.domain → x ∉ C n l →
      ∀ i j, j ≠ 0 → (b l).velocity n i j =ᶠ[𝓝 x] fun _ => 0)
    {j : ℤ} (hj : j ≠ 0) (i : Fin 3) :
    LabelSumBounds.UniformClass s (fun l n x => Real.sqrt (s.zeta x) * P n l x)
      (α + H - 1 / 2) (fun l n x =>
        HarmonicResidual.realCoefficients (meanCross c h (b l) n i) j x) := by
  have hm : LocalMeanVector s C H (fun n (_ : I) => tripleField h n) :=
    ⟨LocalClass.of_global (tripleField_bound hh).1,
      LocalClass.of_global (tripleField_bound hh).2.1,
      LocalClass.of_global (tripleField_bound hh).2.2⟩
  have hc k (hk0 : k ≠ 0) := local_meanCross c ho hκ hR hm
    (fun i j hj => local_of_uniform (hb i j hj)) hN hk hkp hk0 i
  have hr := local_realCoefficient (fun n l => meanCross c h (b l) n i) j
    (hc j hj) (hc (-j) (neg_ne_zero.mpr hj))
  exact uniform_of_supported_local hr (fun n l x hx hC =>
    realMeanCross_zero_germ c h (b l) n hj (hz n l x hx hC) i)

/-- The single-block endpoint on the original state domain. -/
theorem realMeanCross_class {s : StripData D} {C : ℕ → Set D}
    {P : ℕ → D → ℝ} {α H κ : ℝ}
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hκ : κ ≤ 1 / 2) (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    {h : MeanIncrementBounds.Triple D} (hh : MeanIncrementBounds.IncrementBounds s H h)
    {b : CorrectionState.HarmonicBlock D} (hb : b.WaveBounds s P α)
    (hN : ∀ i, LocalUnweighted s (fun n (_ : Unit) => C n) 0
      (fun n _ x => slowNormal c ho hR b.phase n x i))
    (hk : BandBound s (-(1 / 2)) b.frequency)
    (hkp : BandBound s (-(1 / 2)) (fun n => (b.angularFrequency n : ℝ)))
    (hz : ∀ n x, x ∈ s.domain → x ∉ C n →
      ∀ i j, j ≠ 0 → b.velocity n i j =ᶠ[𝓝 x] fun _ => 0)
    {j : ℤ} (hj : j ≠ 0) (i : Fin 3) :
    WaveClass s P (α + H - 1 / 2)
      (fun n x => HarmonicResidual.realCoefficients (meanCross c h b n i) j x) := by
  have hu := uniform_realMeanCross_class (I := Unit) (P := fun n _ => P n)
    c ho hκ hR hh (b := fun _ => b) (fun i j hj => uniform_constant (hb i j hj))
    hN (LocalClass.band_const hk) (LocalClass.band_const hkp)
    (fun n _ x hx hC => hz n x hx hC) hj i
  exact hu.each ()

/-! ## The literal residual and interaction blocks -/

/-- The normal-free wave-wave estimate is combined with the newly
localized mean-wave estimate, preserving both gains and their minimum. -/
theorem interactionBlock_class {s : StripData D} {C : ℕ → Set D}
    {κ α β H : ℝ} {P : ℕ → D → ℝ}
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hκ : κ ≤ 1 / 2) (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    {u : CorrectionState.State D} (hm : MeanIncrementBounds.IncrementBounds s H u.mean)
    {a b : CorrectionState.HarmonicBlock D} {M N : ℕ}
    (ha : a.WaveBounds s P α) (hb : b.WaveBounds s P β)
    (ha0 : HarmonicWaveInteraction.ZeroMode a) (hb0 : HarmonicWaveInteraction.ZeroMode b)
    (hM : a.BandLimited M) (hN : b.BandLimited N)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (a.phase n) s.domain) (hk : ∀ n, a.frequency n ≠ 0)
    (hda : HarmonicWaveInteraction.ModeSolenoidal s c a)
    (hdb : HarmonicWaveInteraction.ModeSolenoidal s c (HarmonicWaveInteraction.withCarrier a b))
    (hNormal : ∀ i, LocalUnweighted s (fun n (_ : Unit) => C n) 0
      (fun n _ x => slowNormal c ho hR a.phase n x i))
    (hFreq : BandBound s (-(1 / 2)) a.frequency)
    (hAng : BandBound s (-(1 / 2)) (fun n => (a.angularFrequency n : ℝ)))
    (hz : ∀ n x, x ∈ s.domain → x ∉ C n →
      ∀ i j, j ≠ 0 → b.velocity n i j =ᶠ[𝓝 x] fun _ => 0)
    (hP0 : ∀ n x, x ∈ s.domain → 0 ≤ P n x)
    (hP1 : ∀ n x, x ∈ s.domain → P n x ≤ 1) :
    (HarmonicWaveInteraction.interactionBlock c u a b).WaveBounds s P
      (min (β + H - 1 / 2) (min (α + β - κ) (β + β - κ))) := by
  intro i j hj
  have hmean := realMeanCross_class c ho hκ hR hm
    (b := HarmonicWaveInteraction.withCarrier a b) hb hNormal hFreq hAng hz hj i
  have hnon m := HarmonicWaveInteraction.nonlinearCoefficients_wave_class c ho hR
    ha hb ha0 hb0 hM hN hΦ hk hda hdb hP0 hP1 m i
  have hn := realCoefficient_class
    (fun n => HarmonicWaveInteraction.nonlinearCoefficients c a b n i) j (hnon j) (hnon (-j))
  apply class_congr ((hmean.mono_exponent (min_le_left _ _)).add
    (hn.mono_exponent (min_le_right _ _)))
  intro n x _
  change _ = HarmonicResidual.nonconstant (HarmonicResidual.realCoefficients
    (meanCross c u.mean (HarmonicWaveInteraction.withCarrier a b) n i +
      HarmonicWaveInteraction.nonlinearCoefficients c a b n i)) j x
  rw [nonconstant_apply_of_ne _ hj, realCoefficients_add]
  rfl

theorem residualBlock_mean_update_class {s : StripData D} {C : ℕ → Set D}
    {κ α H : ℝ} {P : ℕ → D → ℝ}
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hκ : κ ≤ 1 / 2) (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    (s₀ s₁ : CorrectionState.State D) (h : MeanIncrementBounds.Triple D)
    (he : s₁.mean = MeanIncrementBounds.updated s₀.mean h)
    (hbase : MeanIncrementBounds.SmoothTriple s.domain c.base)
    (hmean : MeanIncrementBounds.SmoothTriple s.domain s₀.mean)
    (hh : MeanIncrementBounds.IncrementBounds s H h)
    (b : CorrectionState.HarmonicBlock D) (hb : b.WaveBounds s P α)
    (hN : ∀ i, LocalUnweighted s (fun n (_ : Unit) => C n) 0
      (fun n _ x => slowNormal c ho hR b.phase n x i))
    (hk : BandBound s (-(1 / 2)) b.frequency)
    (hkp : BandBound s (-(1 / 2)) (fun n => (b.angularFrequency n : ℝ)))
    (hz : ∀ n x, x ∈ s.domain → x ∉ C n →
      ∀ i j, j ≠ 0 → b.velocity n i j =ᶠ[𝓝 x] fun _ => 0)
    (G A₀ A₁ : HarmonicResidual.BlockCoefficients D)
    (hA : ∀ n i, BandLimited (A₁ n i - A₀ n i) 0) {j : ℤ} (hj : j ≠ 0) (i : Fin 3) :
    WaveClass s P (α + H - 1 / 2) (fun n x =>
      (HarmonicResidual.residualBlock c s₁ b G A₁).velocity n i j x -
      (HarmonicResidual.residualBlock c s₀ b G A₀).velocity n i j x) := by
  apply class_congr (realMeanCross_class c ho hκ hR hh hb hN hk hkp hz hj i)
  intro n x hx
  symm
  apply residualBlock_axisymmetric_alias_update c s₀ s₁ h he b G A₀ A₁ hA n
  · intro t
    exact ((tripleField_smooth hbase n t).contDiffAt (s.isOpen_domain.mem_nhds
      hx)).differentiableAt (by simp)
  · intro t
    exact ((tripleField_smooth hmean n t).contDiffAt (s.isOpen_domain.mem_nhds
      hx)).differentiableAt (by simp)
  · intro t
    exact ((tripleField_smooth hh.smooth n t).contDiffAt (s.isOpen_domain.mem_nhds
      hx)).differentiableAt (by simp)
  · exact hj

theorem residualDifferenceBlock_class {s : StripData D} {C : ℕ → Set D}
    {κ α H : ℝ} {P : ℕ → D → ℝ}
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hκ : κ ≤ 1 / 2) (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    (s₀ s₁ : CorrectionState.State D) (h : MeanIncrementBounds.Triple D)
    (he : s₁.mean = MeanIncrementBounds.updated s₀.mean h)
    (hbase : MeanIncrementBounds.SmoothTriple s.domain c.base)
    (hmean : MeanIncrementBounds.SmoothTriple s.domain s₀.mean)
    (hh : MeanIncrementBounds.IncrementBounds s H h)
    (b : CorrectionState.HarmonicBlock D) (hb : b.WaveBounds s P α)
    (hN : ∀ i, LocalUnweighted s (fun n (_ : Unit) => C n) 0
      (fun n _ x => slowNormal c ho hR b.phase n x i))
    (hk : BandBound s (-(1 / 2)) b.frequency)
    (hkp : BandBound s (-(1 / 2)) (fun n => (b.angularFrequency n : ℝ)))
    (hz : ∀ n x, x ∈ s.domain → x ∉ C n →
      ∀ i j, j ≠ 0 → b.velocity n i j =ᶠ[𝓝 x] fun _ => 0)
    (G A₀ A₁ : HarmonicResidual.BlockCoefficients D)
    (hA : ∀ n i, BandLimited (A₁ n i - A₀ n i) 0) :
    (residualDifferenceBlock c s₀ s₁ b G A₀ A₁).WaveBounds s P (α + H - 1 / 2) := by
  intro i j hj
  exact residualBlock_mean_update_class c ho hκ hR s₀ s₁ h he hbase hmean hh b hb hN hk hkp hz
    G A₀ A₁ hA hj i

end NavierStokes.LocalizedMeanInteraction
