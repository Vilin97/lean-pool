/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ScaledActualParticularControl
public import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicSourceSupport
public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalizedWaveBounds

/-!
# Gaussian coverage for the actual scaled particular solves

The cutoff used by the inverse is the separate Gaussian slot cutoff times
the padded native-clock cutoff.  The dyadic, radial, and slow source masks
remain in the source and amplitude.  Whole-path support, rather than a
pointwise zero of the source, supplies zero germs for the actual Volterra
solution.
-/

section

/-!
# Gaussian cutoff errors from support-local primitive estimates

The analytic phase patch may be smaller than the closed periodization
cell.  Only primitive amplitude/source/cutoff jets on that patch enter
the Gaussian estimate.  On the remainder of the cell, actual input zero
germs imply a zero germ of the two-term cutoff error.  The global source
complement is retained once, exactly as in `CopyData.globalGaussian`.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.LocalizedGaussianBounds

open Set Function Filter WeightedClasses PeriodizedWaveBounds
open HarmonicCalculus LinearWaveBounds GaussianTailFlat
open scoped Topology ContDiff BigOperators

section LocalGerms

variable {D E I : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Enlarging the set of estimated points through zero neighborhoods
preserves the actual native derivative constants. -/
theorem localJets_extend_by_zero {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    {C K : ℕ → I → Set D} {f : ℕ → I → D → E}
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x) (hf : LocalJets s w α C f)
    (hz : ∀ n i x, x ∈ s.domain → x ∈ K n i → x ∉ C n i →
      f n i =ᶠ[𝓝 x] fun _ => 0) : LocalJets s w α K f := by
  constructor
  · intro n i x hx hi
    by_cases hc : x ∈ C n i
    · exact hf.smooth n i x hx hc
    · exact contDiffAt_const.congr_of_eventuallyEq (hz n i x hx hi hc)
  · intro m
    obtain ⟨A, hA, p, hb⟩ := hf.bounds m
    refine ⟨A, hA, p, ?_⟩
    intro n i x hx hi j hj
    by_cases hc : x ∈ C n i
    · exact hb n i x hx hc j hj
    · rw [jets_eq_of_germ (hz n i x hx hi hc) j]
      simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using
        majorant_nonneg s w α hA p n x (hw n x hx)

end LocalGerms

section CopyBounds

variable {D I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable (a : CopyData D I)

/-- A zero cutoff alone leaves the source.  Both zero germs are used. -/
theorem localGaussian_zero_of_cutoff_source (d : GraphDirections D)
    {n : ℕ} {i : I} {x : D}
    (hψ : a.cutoff n i =ᶠ[𝓝 x] fun _ => 0)
    (hf : a.source n =ᶠ[𝓝 x] fun _ => 0) :
    a.localGaussian d n i =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [a.localTail_zero_germ d hψ, hf] with y hy hfy
  rw [a.localGaussian_eq, hy, hfy, smul_zero, add_zero]

theorem localGaussian_zero_of_inactive (d : GraphDirections D)
    {n : ℕ} {i : I} {x : D}
    (h : ((a.cutoff n i =ᶠ[𝓝 x] fun _ => 0) ∧ (a.source n =ᶠ[𝓝 x] fun _ => 0)) ∨
      ((a.amplitude n i =ᶠ[𝓝 x] fun _ => 0) ∧ (a.source n =ᶠ[𝓝 x] fun _ => 0))) :
    a.localGaussian d n i =ᶠ[𝓝 x] fun _ => 0 := by
  rcases h with ⟨hψ, hf⟩ | ⟨hu, hf⟩
  · exact localGaussian_zero_of_cutoff_source a d hψ hf
  · exact a.localGaussian_zero_of_fields d hu hf

/-- Gaussian and plateau hypotheses are imposed only on the analytic
patch `C`.  No raw-field derivative bound on `K \ C` is assumed. -/
theorem localGaussian_all_gains_from_supported_native
    {s : StripData D} (d : GraphDirections D) (C K : ℕ → I → Set D)
    {W : ℕ → D → ℝ} {α c : ℝ}
    (hWnonneg : ∀ n x, x ∈ s.domain → 0 ≤ W n x)
    (hψ : LocalJets s (fun _ _ => 1) 0 C a.cutoff)
    (hfast : BandBound s 0 d.fastScale)
    (hu : LocalJets s (fun n x => Real.sqrt (s.zeta x) * W n x) α C a.amplitude)
    (hf : LocalJets s (fun n x => Real.sqrt (s.zeta x) * W n x) α C (fun n _ => a.source n))
    (edges : FlatEdges s) (scales : BandScaleControl s)
    (θ : ℕ → I → D → ℝ) (L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (ell : ℝ) (hell : 0 < ell) (hLell : ∀ n, ell * ChartScales.S n ≤ L n) (hc : 0 < c)
    (hW : ∀ n i x, x ∈ s.domain → x ∈ C n i →
      W n x ≤ Real.exp (-c * (θ n i x - 1 / 2) ^ 2 * L n))
    (hcentral : ∀ n i x, x ∈ s.domain → x ∈ C n i → |θ n i x - 1 / 2| < 1 / 5 →
      (a.cutoff n i =ᶠ[𝓝 x] fun _ => 1) ∨
        ((a.amplitude n i =ᶠ[𝓝 x] fun _ => 0) ∧ (a.source n =ᶠ[𝓝 x] fun _ => 0)))
    (houtside : ∀ n i x, x ∈ s.domain → x ∈ K n i → x ∉ C n i →
      ((a.cutoff n i =ᶠ[𝓝 x] fun _ => 0) ∧ (a.source n =ᶠ[𝓝 x] fun _ => 0)) ∨
        ((a.amplitude n i =ᶠ[𝓝 x] fun _ => 0) ∧ (a.source n =ᶠ[𝓝 x] fun _ => 0)))
    (β : ℝ) : LocalJets s (fun _ _ => 1) β K (a.localGaussian d) := by
  apply localJets_extend_by_zero (fun _ _ _ => zero_le_one)
    (a.localGaussian_all_gains_from_native d hWnonneg hψ hfast hu hf edges scales θ L hL
      ell hell hLell hc hW hcentral β)
  intro n i x hx hi hn
  exact localGaussian_zero_of_inactive a d (houtside n i x hx hi hn)

/-- The source on the complement of all cells is kept and estimated
through `hcomplement`; it is not replaced by a copywise sum of sources. -/
theorem globalGaussian_all_gains_from_supported_native
    (K : Cells D I) (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    {s : StripData D} (d : GraphDirections D) (C : ℕ → I → Set D)
    {W : ℕ → D → ℝ} {α c : ℝ}
    (hWnonneg : ∀ n x, x ∈ s.domain → 0 ≤ W n x)
    (hψ : LocalJets s (fun _ _ => 1) 0 C a.cutoff)
    (hfast : BandBound s 0 d.fastScale)
    (hu : LocalJets s (fun n x => Real.sqrt (s.zeta x) * W n x) α C a.amplitude)
    (hf : LocalJets s (fun n x => Real.sqrt (s.zeta x) * W n x) α C (fun n _ => a.source n))
    (edges : FlatEdges s) (scales : BandScaleControl s)
    (θ : ℕ → I → D → ℝ) (L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (ell : ℝ) (hell : 0 < ell) (hLell : ∀ n, ell * ChartScales.S n ≤ L n) (hc : 0 < c)
    (hW : ∀ n i x, x ∈ s.domain → x ∈ C n i →
      W n x ≤ Real.exp (-c * (θ n i x - 1 / 2) ^ 2 * L n))
    (hcentral : ∀ n i x, x ∈ s.domain → x ∈ C n i → |θ n i x - 1 / 2| < 1 / 5 →
      (a.cutoff n i =ᶠ[𝓝 x] fun _ => 1) ∨
        ((a.amplitude n i =ᶠ[𝓝 x] fun _ => 0) ∧ (a.source n =ᶠ[𝓝 x] fun _ => 0)))
    (houtside : ∀ n i x, x ∈ s.domain → x ∈ K.carrier n i → x ∉ C n i →
      ((a.cutoff n i =ᶠ[𝓝 x] fun _ => 0) ∧ (a.source n =ᶠ[𝓝 x] fun _ => 0)) ∨
        ((a.amplitude n i =ᶠ[𝓝 x] fun _ => 0) ∧ (a.source n =ᶠ[𝓝 x] fun _ => 0)))
    (β : ℝ) (hcomplement : ComplementJets s (fun _ _ => 1) β K.carrier a.source) :
    UnweightedClass s β (a.globalGaussian d) :=
  a.globalGaussian_class_with_complement K hs d (fun _ _ _ => zero_le_one)
    (localGaussian_all_gains_from_supported_native a d C K.carrier hWnonneg hψ hfast hu hf
      edges scales θ L hL ell hell hLell hc hW hcentral houtside β) hcomplement

theorem source_complement_of_zero (s : StripData D) (K : Cells D I)
    (hzero : a.source = fun _ _ => 0) (β : ℝ) :
    ComplementJets s (fun _ _ => 1) β K.carrier a.source :=
  HarmonicSourceSupport.zero_complementJets_of_germs s _ β K.carrier a.source
    (fun _ _ _ _ => Filter.Eventually.of_forall (fun _ => by simp only [hzero]))

end CopyBounds

/-! ## Gaussian absorption with an arbitrary extra index -/

section IndexedEstimates

open LocalizedWaveBounds

variable {D E J : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The index may be the pair (spatial label, lattice copy).  Both the
Gaussian envelope and the native length are allowed to depend on it. -/
theorem indexed_gaussian_tail_bound {s : StripData D} {K : ℕ → J → Set D}
    {W : ℕ → J → D → ℝ} {α c : ℝ} {f : ℕ → J → D → E}
    (hf : LocalWave s K W α f) (edges : FlatEdges s) (scales : BandScaleControl s)
    (θ : ℕ → J → D → ℝ) (L : ℕ → J → ℝ) (hL : ∀ n i, 0 < L n i)
    (ell : ℝ) (hell : 0 < ell) (hLell : ∀ n i, ell * ChartScales.S n ≤ L n i) (hc : 0 < c)
    (hW : ∀ n i x, x ∈ s.domain → x ∈ K n i →
      W n i x ≤ Real.exp (-c * (θ n i x - 1 / 2) ^ 2 * L n i))
    (hzero : ∀ n i x, x ∈ s.domain → x ∈ K n i →
      |θ n i x - 1 / 2| < 1 / 5 → f n i =ᶠ[𝓝 x] fun _ => 0)
    (m : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∃ p : ℕ, ∀ n i x, x ∈ s.domain → x ∈ K n i →
      ∀ j ≤ m, ‖iteratedFDeriv ℝ j (f n i) x‖ ≤
        A * (1 + ChartScales.S n) ^ p * Real.exp (-(c * ell / 50) * ChartScales.S n) := by
  obtain ⟨A, hA, p, hb⟩ := hf.bounds m
  obtain ⟨B, hB, hweight⟩ := edges.uniform_weight p
  have hconstant := scales.constant_one_le
  have hdec : 0 < c * ell / 25 := by positivity
  obtain ⟨C, hC, hgauss⟩ := fixed_power_gaussian_bound hdec (scales.power * α)
  refine ⟨A * B * scales.boundConstant ^ p * C, by positivity, scales.degree * p, ?_⟩
  intro n i x hx hi j hj
  have hQ := ChartScales.Q_pos n
  by_cases hmid : |θ n i x - 1 / 2| < 1 / 5
  · rw [jets_eq_of_germ (hzero n i x hx hi hmid) j]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    have hS : 0 ≤ ChartScales.S n := sq_nonneg _
    positivity
  have htail : 1 / 5 ≤ |θ n i x - 1 / 2| := le_of_not_gt hmid
  have hsq : (1 / 25 : ℝ) ≤ (θ n i x - 1 / 2) ^ 2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 5) htail 2
    norm_num [sq_abs] at hh ⊢
    exact hh
  have hPg : W n i x ≤ Real.exp (-(c * ell / 25) * ChartScales.S n) := by
    apply (hW n i x hx hi).trans
    apply (Real.exp_le_exp.2 ?_).trans (gaussian_length_comparison hc.le (hLell n i))
    nlinarith [mul_le_mul_of_nonneg_left hsq (mul_nonneg hc.le (hL n i).le)]
  have hslow0 : 0 ≤ s.slow n := zero_le_one.trans (s.one_le_slow n)
  have hK0 : 0 ≤ scales.boundConstant := zero_le_one.trans scales.constant_one_le
  have hslowp : s.slow n ^ p ≤
      scales.boundConstant ^ p * (1 + ChartScales.S n) ^ (scales.degree * p) := by
    simpa only [mul_pow, ← pow_mul] using pow_le_pow_left₀ hslow0 (scales.slow_le n) p
  have hmajor : majorant s (fun n x => Real.sqrt (s.zeta x) * W n i x) α A p n x ≤
      (A * B * scales.boundConstant ^ p) * ChartScales.Q n ^ (scales.power * α) *
        ((1 + ChartScales.S n) ^ (scales.degree * p) *
          Real.exp (-(c * ell / 25) * ChartScales.S n)) := by
    rw [majorant, StripData.growth, mul_pow, scales.epsilon_eq, ← Real.rpow_mul hQ.le]
    calc
      _ = (A * ChartScales.Q n ^ (scales.power * α) * s.slow n ^ p) *
          (Real.sqrt (s.zeta x) * max 1 (s.delta x)⁻¹ ^ p) * W n i x := by ring
      _ ≤ (A * ChartScales.Q n ^ (scales.power * α) * s.slow n ^ p) *
          (Real.sqrt (s.zeta x) * max 1 (s.delta x)⁻¹ ^ p) *
            Real.exp (-(c * ell / 25) * ChartScales.S n) :=
        mul_le_mul_of_nonneg_left hPg (by positivity)
      _ ≤ (A * ChartScales.Q n ^ (scales.power * α) * s.slow n ^ p) * B *
            Real.exp (-(c * ell / 25) * ChartScales.S n) := by
        gcongr
        exact hweight x hx
      _ ≤ (A * ChartScales.Q n ^ (scales.power * α) *
          (scales.boundConstant ^ p * (1 + ChartScales.S n) ^ (scales.degree * p))) * B *
            Real.exp (-(c * ell / 25) * ChartScales.S n) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ majorant s (fun n x => Real.sqrt (s.zeta x) * W n i x) α A p n x := hb n i x hx hi j hj
    _ ≤ _ := hmajor
    _ = (A * B * scales.boundConstant ^ p) * (1 + ChartScales.S n) ^ (scales.degree * p) *
        (ChartScales.Q n ^ (scales.power * α) *
          Real.exp (-(c * ell / 25) * ChartScales.S n)) := by ring
    _ ≤ (A * B * scales.boundConstant ^ p) * (1 + ChartScales.S n) ^ (scales.degree * p) *
        (C * Real.exp (-((c * ell / 25) / 2) * ChartScales.S n)) := by
      have hS : 0 ≤ ChartScales.S n := sq_nonneg _
      exact mul_le_mul_of_nonneg_left (hgauss n) (by positivity)
    _ = _ := by
      rw [show c * ell / 25 / 2 = c * ell / 50 by ring]
      ring

theorem indexed_gaussian_all_gains {s : StripData D} {K : ℕ → J → Set D}
    {W : ℕ → J → D → ℝ} {α c : ℝ} {f : ℕ → J → D → E}
    (hf : LocalWave s K W α f) (edges : FlatEdges s) (scales : BandScaleControl s)
    (θ : ℕ → J → D → ℝ) (L : ℕ → J → ℝ) (hL : ∀ n i, 0 < L n i)
    (ell : ℝ) (hell : 0 < ell) (hLell : ∀ n i, ell * ChartScales.S n ≤ L n i) (hc : 0 < c)
    (hW : ∀ n i x, x ∈ s.domain → x ∈ K n i →
      W n i x ≤ Real.exp (-c * (θ n i x - 1 / 2) ^ 2 * L n i))
    (hzero : ∀ n i x, x ∈ s.domain → x ∈ K n i →
      |θ n i x - 1 / 2| < 1 / 5 → f n i =ᶠ[𝓝 x] fun _ => 0)
    (β : ℝ) : LocalUnweighted s K β f := by
  refine ⟨fun _ _ _ _ => zero_le_one, hf.smooth, ?_⟩
  intro m
  obtain ⟨A, hA, p, hb⟩ := indexed_gaussian_tail_bound hf edges scales θ L hL
    ell hell hLell hc hW hzero m
  obtain ⟨B, hB, hflat⟩ := gaussian_beats_Q_power (by
      positivity : 0 < c * ell / 50) p (scales.power * β)
  refine ⟨A * B, mul_nonneg hA hB.le, 0, ?_⟩
  intro n i x hx hi j hj
  have ht := (hb n i x hx hi j hj).trans
    (show A * (1 + ChartScales.S n) ^ p * Real.exp (-(c * ell / 50) * ChartScales.S n) ≤
      (A * B) * ChartScales.Q n ^ (scales.power * β) by
        calc
          _ = A * ((1 + ChartScales.S n) ^ p * Real.exp (-(c * ell / 50) * ChartScales.S n)) := by
              ring
          _ ≤ A * (B * ChartScales.Q n ^ (scales.power * β)) :=
            mul_le_mul_of_nonneg_left (hflat n) hA
          _ = _ := by ring)
  simpa only [majorant, pow_zero, mul_one, scales.epsilon_eq,
    ← Real.rpow_mul (ChartScales.Q_pos n).le] using ht

end IndexedEstimates

section UniformGluing

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {E L I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual source jets on the uncovered set, with constants chosen
before the spatial label as well as the band and point. -/
structure UniformComplementJets (s : StripData D) (w : L → ℕ → D → ℝ) (α : ℝ)
    (K : L → ℕ → I → Set D) (f : L → ℕ → D → E) : Prop where
  smooth : ∀ l n x, x ∈ s.domain → (∀ i, x ∉ K l n i) → ContDiffAt ℝ ∞ (f l n) x
  bounds : ∀ m : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∃ p : ℕ,
    ∀ l n x, x ∈ s.domain → (∀ i, x ∉ K l n i) → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (f l n) x‖ ≤ majorant s (w l) α A p n x

namespace UniformComplementJets

theorem each {s : StripData D} {w : L → ℕ → D → ℝ} {α : ℝ}
    {K : L → ℕ → I → Set D} {f : L → ℕ → D → E}
    (hf : UniformComplementJets s w α K f) (l : L) : ComplementJets s (w l) α (K l) (f l) := by
  refine ⟨hf.smooth l, ?_⟩
  intro m
  obtain ⟨A, hA, p, hb⟩ := hf.bounds m
  exact ⟨A, hA, p, hb l⟩

theorem of_zero_germs (s : StripData D) (w : L → ℕ → D → ℝ) (α : ℝ)
    (K : L → ℕ → I → Set D) (f : L → ℕ → D → E)
    (hg : ∀ l n x, x ∈ s.domain → (∀ i, x ∉ K l n i) → f l n =ᶠ[𝓝 x] fun _ => 0) :
    UniformComplementJets s w α K f := by
  constructor
  · intro l n x hx hn
    exact contDiffAt_const.congr_of_eventuallyEq (hg l n x hx hn)
  · intro m
    refine ⟨0, le_rfl, 0, ?_⟩
    intro l n x hx hn j hj
    rw [jets_eq_of_germ (hg l n x hx hn) j]
    simp [majorant]

theorem of_germs {s : StripData D} {w : L → ℕ → D → ℝ} {α : ℝ}
    {K : L → ℕ → I → Set D} {f g : L → ℕ → D → E}
    (hg : LabelSumBounds.UniformClass s w α g)
    (he : ∀ l n x, x ∈ s.domain → (∀ i, x ∉ K l n i) → f l n =ᶠ[𝓝 x] g l n) :
    UniformComplementJets s w α K f := by
  constructor
  · intro l n x hx hn
    exact ((hg.smooth l n).contDiffAt (s.isOpen_domain.mem_nhds hx)).congr_of_eventuallyEq
      (he l n x hx hn)
  · intro m
    obtain ⟨A, hA, p, hb⟩ := hg.bounds m
    refine ⟨A, hA, p, ?_⟩
    intro l n x hx hn j hj
    rw [jets_eq_of_germ (he l n x hx hn) j]
    exact hb l n x hx j hj

end UniformComplementJets

theorem uniformClass_of_local_and_complement_germs
    {s : StripData D} {w : L → ℕ → D → ℝ} {α : ℝ}
    {K : L → ℕ → I → Set D} {f : L → ℕ → I → D → E} {f₀ F : L → ℕ → D → E}
    (hw : ∀ l n x, x ∈ s.domain → 0 ≤ w l n x)
    (hlocal : UniformLocalJets s w α K f) (houtside : UniformComplementJets s w α K f₀)
    (hactive : ∀ l n i x, x ∈ s.domain → x ∈ K l n i → F l n =ᶠ[𝓝 x] f l n i)
    (hinactive : ∀ l n x, x ∈ s.domain → (∀ i, x ∉ K l n i) → F l n =ᶠ[𝓝 x] f₀ l n) :
    LabelSumBounds.UniformClass s w α F := by
  classical
  refine ⟨hw, ?_, ?_⟩
  · intro l
    exact (memClass_of_local_and_complement_germs (hw l) (hlocal.each l)
      (houtside.each l) (hactive l) (hinactive l)).smooth
  · intro m
    obtain ⟨A, hA, p, hb⟩ := hlocal.bounds m
    obtain ⟨B, hB, q, hb₀⟩ := houtside.bounds m
    refine ⟨A + B, add_nonneg hA hB, max p q, ?_⟩
    intro l n x hx j hj
    by_cases h : ∃ i, x ∈ K l n i
    · obtain ⟨i, hi⟩ := h
      rw [jets_eq_of_germ (hactive l n i x hx hi) j]
      exact (hb l n i x hx hi j hj).trans
        ((majorant_mono_degree s (w l) α hA (le_max_left _ _) n x (hw l n x hx)).trans
          (majorant_mono_constant s (w l) α (le_add_of_nonneg_right hB) _ n x (hw l n x hx)))
    · rw [jets_eq_of_germ (hinactive l n x hx (not_exists.mp h)) j]
      exact (hb₀ l n x hx (not_exists.mp h) j hj).trans
        ((majorant_mono_degree s (w l) α hB (le_max_right _ _) n x (hw l n x hx)).trans
          (majorant_mono_constant s (w l) α (le_add_of_nonneg_left hA) _ n x (hw l n x hx)))

end UniformGluing

/-! ## Primitive cutoff errors, uniformly over spatial labels -/

section UniformCopyBounds

open LocalizedWaveBounds

variable {D I L : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Indexed cutoff error, given by `d.Dfast (fun n => ψ n i) n x • u n i x + (1 - ψ n i x) • f n
i x`. -/
noncomputable def indexedCutoffError (d : GraphDirections D)
    (ψ : ℕ → I → D → ℝ) (u f : ℕ → I → D → ComplexVector)
    (n : ℕ) (i : I) (x : D) : ComplexVector :=
  d.Dfast (fun n => ψ n i) n x • u n i x + (1 - ψ n i x) • f n i x

theorem indexedCutoffError_wave_class {s : StripData D} (d : GraphDirections D)
    {K : ℕ → I → Set D} {w : ℕ → I → D → ℝ} {α : ℝ}
    {ψ : ℕ → I → D → ℝ} {u f : ℕ → I → D → ComplexVector}
    (hψ : LocalUnweighted s K 0 ψ) (hfast : BandBound s 0 d.fastScale)
    (hu : LocalClass s K w α u) (hf : LocalClass s K w α f) :
    LocalClass s K w α (indexedCutoffError d ψ u f) := by
  have hD : LocalUnweighted s K 0 (fun n i => d.Dfast (fun n => ψ n i) n) := by
    have hh : LocalUnweighted s K 0
        (fun n i x => d.fastScale n * fderiv ℝ (ψ n i) x d.fast) := by
      simpa using
      (LocalClass.band_const (K := K) hfast).smul (hψ.directional d.fast)
    convert! hh using 1
    funext n i x
    simp [GraphDirections.Dfast, GraphDirections.fastField, HarmonicCalculus.along]
  have hminus : LocalUnweighted s K 0 (fun n i x => 1 - ψ n i x) :=
    (local_const (s := s) (K := K) (1 : ℝ)).sub hψ
  have he := (unweighted_smul hD hu).add (unweighted_smul hminus hf)
  simp only [zero_add] at he
  exact he

theorem uniform_localGaussian_all_gains_from_supported_native
    (a : L → CopyData D I) {s : StripData D} (d : GraphDirections D)
    (C K : L → ℕ → I → Set D) {W : L → ℕ → D → ℝ} {α c : ℝ}
    (hWnonneg : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (hψ : UniformLocalJets s (fun _ _ _ => 1) 0 C (fun l => (a l).cutoff))
    (hfast : BandBound s 0 d.fastScale)
    (hu : UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) α C
      (fun l => (a l).amplitude))
    (hf : UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) α C
      (fun l n _ => (a l).source n))
    (edges : FlatEdges s) (scales : BandScaleControl s)
    (θ : L → ℕ → I → D → ℝ) (length : L → ℕ → ℝ)
    (hL : ∀ l n, 0 < length l n) (ell : ℝ) (hell : 0 < ell)
    (hLell : ∀ l n, ell * ChartScales.S n ≤ length l n) (hc : 0 < c)
    (hW : ∀ l n i x, x ∈ s.domain → x ∈ C l n i →
      W l n x ≤ Real.exp (-c * (θ l n i x - 1 / 2) ^ 2 * length l n))
    (hcentral : ∀ l n i x, x ∈ s.domain → x ∈ C l n i → |θ l n i x - 1 / 2| < 1 / 5 →
      ((a l).cutoff n i =ᶠ[𝓝 x] fun _ => 1) ∨
        (((a l).amplitude n i =ᶠ[𝓝 x] fun _ => 0) ∧ ((a l).source n =ᶠ[𝓝 x] fun _ => 0)))
    (houtside : ∀ l n i x, x ∈ s.domain → x ∈ K l n i → x ∉ C l n i →
      (((a l).cutoff n i =ᶠ[𝓝 x] fun _ => 0) ∧ ((a l).source n =ᶠ[𝓝 x] fun _ => 0)) ∨
        (((a l).amplitude n i =ᶠ[𝓝 x] fun _ => 0) ∧ ((a l).source n =ᶠ[𝓝 x] fun _ => 0)))
    (β : ℝ) : UniformLocalJets s (fun _ _ _ => 1) β K (fun l => (a l).localGaussian d) := by
  have hw l n x hx := mul_nonneg (Real.sqrt_nonneg (s.zeta x)) (hWnonneg l n x hx)
  have hψ' := LocalClass.of_uniformLocalJets (fun _ _ _ _ => zero_le_one) hψ
  have hu' := LocalClass.of_uniformLocalJets hw hu
  have hf' := LocalClass.of_uniformLocalJets hw hf
  have he : LocalWave s (fun n (ji : L × I) => C ji.1 n ji.2)
      (fun n ji x => W ji.1 n x) α (fun n ji => (a ji.1).localGaussian d n ji.2) :=
    indexedCutoffError_wave_class d hψ' hfast hu' hf'
  have hflat := indexed_gaussian_all_gains he edges scales
    (fun n ji => θ ji.1 n ji.2) (fun n ji => length ji.1 n)
    (fun n ji => hL ji.1 n) ell hell (fun n ji => hLell ji.1 n) hc
    (fun n ji x hx hi => hW ji.1 n ji.2 x hx hi)
    (fun n ji x hx hi hm => by
      rcases hcentral ji.1 n ji.2 x hx hi hm with hOne | ⟨hU, hF⟩
      · exact (a ji.1).localGaussian_zero_of_cutoff_one d hOne
      · exact (a ji.1).localGaussian_zero_of_fields d hU hF) β
  apply LocalClass.to_uniformLocalJets
  apply hflat.enlarge
  intro n ji x hx hi
  by_cases hC : x ∈ C ji.1 n ji.2
  · exact Or.inl hC
  · exact Or.inr (localGaussian_zero_of_inactive (a ji.1) d
      (houtside ji.1 n ji.2 x hx hi hC))

theorem uniform_globalGaussian_class_with_complement
    (a : L → CopyData D I) (K : L → Cells D I)
    (hs : ∀ l n i, support ((a l).cutoff n i) ⊆ (K l).carrier n i)
    {s : StripData D} (d : GraphDirections D) {w : L → ℕ → D → ℝ} {α : ℝ}
    (hw : ∀ l n x, x ∈ s.domain → 0 ≤ w l n x)
    (hg : UniformLocalJets s w α (fun l => (K l).carrier) (fun l => (a l).localGaussian d))
    (hf : UniformComplementJets s w α (fun l => (K l).carrier) (fun l => (a l).source)) :
    LabelSumBounds.UniformClass s w α (fun l => (a l).globalGaussian d) :=
  uniformClass_of_local_and_complement_germs hw hg hf
    (fun l n _ _ _ hx => (a l).globalGaussian_germ (K l) (hs l) d n hx)
    (fun l _ _ _ hx => (a l).globalGaussian_uncovered_germ (K l) (hs l) d hx)

/-- The constants precede every spatial label, band and native copy.
The uncovered source is included with its own equally uniform jet bound. -/
theorem uniform_globalGaussian_all_gains_from_supported_native
    (a : L → CopyData D I) (K : L → Cells D I)
    (hs : ∀ l n i, support ((a l).cutoff n i) ⊆ (K l).carrier n i)
    {s : StripData D} (d : GraphDirections D) (C : L → ℕ → I → Set D)
    {W : L → ℕ → D → ℝ} {α c : ℝ}
    (hWnonneg : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (hψ : UniformLocalJets s (fun _ _ _ => 1) 0 C (fun l => (a l).cutoff))
    (hfast : BandBound s 0 d.fastScale)
    (hu : UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) α C
      (fun l => (a l).amplitude))
    (hf : UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) α C
      (fun l n _ => (a l).source n))
    (edges : FlatEdges s) (scales : BandScaleControl s)
    (θ : L → ℕ → I → D → ℝ) (length : L → ℕ → ℝ)
    (hL : ∀ l n, 0 < length l n) (ell : ℝ) (hell : 0 < ell)
    (hLell : ∀ l n, ell * ChartScales.S n ≤ length l n) (hc : 0 < c)
    (hW : ∀ l n i x, x ∈ s.domain → x ∈ C l n i →
      W l n x ≤ Real.exp (-c * (θ l n i x - 1 / 2) ^ 2 * length l n))
    (hcentral : ∀ l n i x, x ∈ s.domain → x ∈ C l n i → |θ l n i x - 1 / 2| < 1 / 5 →
      ((a l).cutoff n i =ᶠ[𝓝 x] fun _ => 1) ∨
        (((a l).amplitude n i =ᶠ[𝓝 x] fun _ => 0) ∧ ((a l).source n =ᶠ[𝓝 x] fun _ => 0)))
    (houtside : ∀ l n i x, x ∈ s.domain → x ∈ (K l).carrier n i → x ∉ C l n i →
      (((a l).cutoff n i =ᶠ[𝓝 x] fun _ => 0) ∧ ((a l).source n =ᶠ[𝓝 x] fun _ => 0)) ∨
        (((a l).amplitude n i =ᶠ[𝓝 x] fun _ => 0) ∧ ((a l).source n =ᶠ[𝓝 x] fun _ => 0)))
    (β : ℝ)
    (hcomplement : UniformComplementJets s (fun _ _ _ => 1) β
      (fun l => (K l).carrier) (fun l => (a l).source)) :
    LabelSumBounds.UniformClass s (fun _ _ _ => 1) β (fun l => (a l).globalGaussian d) :=
  uniform_globalGaussian_class_with_complement a K hs d (fun _ _ _ _ => zero_le_one)
    (uniform_localGaussian_all_gains_from_supported_native a d C (fun l => (K l).carrier)
      hWnonneg hψ hfast hu hf edges scales θ length hL ell hell hLell hc hW hcentral houtside β)
    hcomplement

theorem uniform_source_complement_of_zero
    (a : L → CopyData D I) (s : StripData D) (K : L → Cells D I)
    (hzero : ∀ l, (a l).source = fun _ _ => 0) (β : ℝ) :
    UniformComplementJets s (fun _ _ _ => 1) β (fun l => (K l).carrier) (fun l => (a l).source) :=
  UniformComplementJets.of_zero_germs s _ β _ _
    (fun l _ _ _ _ => Filter.Eventually.of_forall (fun _ => by simp only [hzero l]))

theorem uniform_source_patch_jets_of_zero
    (a : L → CopyData D I) (s : StripData D) (C : L → ℕ → I → Set D)
    (hzero : ∀ l, (a l).source = fun _ _ => 0) (w : L → ℕ → D → ℝ) (α : ℝ) :
    UniformLocalJets s w α C (fun l n _ => (a l).source n) := by
  constructor
  · intro l n i x hx hi
    rw [hzero l]
    exact contDiffAt_const
  · intro m
    refine ⟨0, le_rfl, 0, ?_⟩
    intro l n i x hx hi j hj
    simp [hzero l, majorant]

end UniformCopyBounds

/-! ## The literal harmonic residual supplies the complement -/

section HarmonicSource

open CommonCoverSolve TorusInverse ParticularWaveAssembly HarmonicSourceSupport

variable {P L : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem source_complement_of_harmonicSupport
    (a : CopyData ((P × ℝ) × Plane) Frequency)
    (c : CorrectionState.Context (P × Plane)) (u : CorrectionState.State (P × Plane))
    (b : CorrectionState.HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane))
    (g : ℕ → Geometry) (K : ℕ → Set Plane) (hK : ∀ n, IsCompact (K n))
    {U : Set (P × Plane)} (hU : IsOpen U)
    (hs : InputSupportOn U (fun n => nativeUnion (g n) (K n)) b G A)
    (s : StripData ((P × ℝ) × Plane))
    (hdom : ∀ x, x ∈ s.domain → (x.1.1, x.2) ∈ U)
    (j : ℤ) (hsource : a.source = sourceFamily c u b G A j) (β : ℝ) :
    ComplementJets s (fun _ _ => 1) β
      (fun n => nativeCell (g n) (K n)) a.source := by
  rw [hsource]
  exact sourceFamily_zero_complementJets c u b G A g K hK hU hs s hdom j _ β

theorem uniform_source_complement_of_harmonicSupport
    (a : L → CopyData ((P × ℝ) × Plane) Frequency)
    (c : CorrectionState.Context (P × Plane)) (u : CorrectionState.State (P × Plane))
    (b : L → CorrectionState.HarmonicBlock (P × Plane))
    (G A : L → HarmonicResidual.BlockCoefficients (P × Plane))
    (g : L → ℕ → Geometry) (K : L → ℕ → Set Plane) (hK : ∀ l n, IsCompact (K l n))
    {U : Set (P × Plane)} (hU : IsOpen U)
    (hs : ∀ l, InputSupportOn U (fun n => nativeUnion (g l n) (K l n)) (b l) (G l) (A l))
    (s : StripData ((P × ℝ) × Plane))
    (hdom : ∀ x, x ∈ s.domain → (x.1.1, x.2) ∈ U)
    (j : L → ℤ) (hsource : ∀ l, (a l).source = sourceFamily c u (b l) (G l) (A l) (j l))
    (β : ℝ) : UniformComplementJets s (fun _ _ _ => 1) β
      (fun l n => nativeCell (g l n) (K l n)) (fun l => (a l).source) := by
  apply UniformComplementJets.of_zero_germs
  intro l n x hx hn
  rw [hsource l]
  exact sourceFamily_zero_germ_on c u (b l) (G l) (A l) (g l) (K l) (hK l) hU
    (hs l) (j l) n (hdom x hx) hn

/-- If an excluded harmonic tail remains outside the cells, its actual
uniform class transfers to the literal incoming source.  It is kept in
the final global Gaussian, not set to zero. -/
theorem uniform_source_complement_of_excluded_class
    (a : L → CopyData ((P × ℝ) × Plane) Frequency)
    (c : CorrectionState.Context (P × Plane)) (u : CorrectionState.State (P × Plane))
    (b : L → CorrectionState.HarmonicBlock (P × Plane))
    (G A : L → HarmonicResidual.BlockCoefficients (P × Plane))
    (g : L → ℕ → Geometry) (K : L → ℕ → Set Plane) (hK : ∀ l n, IsCompact (K l n))
    {U : Set (P × Plane)} (hU : IsOpen U)
    (hv : ∀ l n i, NonzeroSupportedOn U (nativeUnion (g l n) (K l n))
      (HarmonicResidual.realCoefficients ((b l).velocity n i)))
    (hp : ∀ l n, NonzeroSupportedOn U (nativeUnion (g l n) (K l n))
      (HarmonicResidual.realCoefficients ((b l).pressure n)))
    (s : StripData ((P × ℝ) × Plane))
    (hdom : ∀ x, x ∈ s.domain → (x.1.1, x.2) ∈ U)
    (j : L → ℤ) (hsource : ∀ l, (a l).source = sourceFamily c u (b l) (G l) (A l) (j l))
    {w : L → ℕ → (P × ℝ) × Plane → ℝ} {β : ℝ}
    (he : LabelSumBounds.UniformClass s w β
      (fun l n => angleLift (excludedSource (G l) (A l) (j l) n))) :
    UniformComplementJets s w β (fun l n => nativeCell (g l n) (K l n))
      (fun l => (a l).source) := by
  apply UniformComplementJets.of_germs he
  intro l n x hx hn
  rw [hsource l]
  have hnot : (x.1.1, x.2) ∉ nativeUnion (g l n) (K l n) := by
    simp only [nativeUnion, mem_iUnion, not_exists]
    exact hn
  have hg := residualSource_complement_germ_on c u (b l) (G l) (A l) hU
    (nativeUnion_closed (g l n) (hK l n)) n (hv l n) (hp l n) (j l) (hdom x hx) hnot
  have hc : Continuous (fun y : (P × ℝ) × Plane => (y.1.1, y.2)) :=
    continuous_fst.fst.prodMk continuous_snd
  exact hg.comp_tendsto hc.continuousAt

end HarmonicSource

end NavierStokes.LocalizedGaussianBounds

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ActualGaussianCoverage

open Set Function Filter WeightedClasses
open CommonCoverSolve TorusInverse ParticularWaveBounds PrimaryPulseBounds
open PeriodizedWaveBounds HarmonicCalculus
open scoped Topology ContDiff BigOperators

/-! ## The normalized clock and the actual envelope -/

theorem normalized_clock {L c : ℝ} (hL : L ≠ 0) (_hc : c ≠ 0) (v : ℝ) :
    c * v / L = v / (L / c) := by
  field_simp

theorem slotCutoff_clock {L c : ℝ} (hL : L ≠ 0) (hc : c ≠ 0) (v : ℝ) :
    GaussianTailFlat.slotCutoff L (c * v) = GaussianTailFlat.slotCutoff (L / c) v := by
  unfold GaussianTailFlat.slotCutoff
  rw [normalized_clock hL hc]

/-- Gaussian rate, given by `u * GaussianEnvelope.referenceMinSlope lam u / 2`. -/
noncomputable def gaussianRate (lam u : ℝ) : ℝ :=
  u * GaussianEnvelope.referenceMinSlope lam u / 2

theorem gaussianRate_pos {lam u : ℝ} (hlam : 0 < lam) (hu : 0 < u) :
    0 < gaussianRate lam u :=
  div_pos (mul_pos hu (GaussianEnvelope.referenceMinSlope_pos hlam hu)) (by norm_num)

theorem gaussianRate_mono {a b u : ℝ} (hu : 0 < u) (hab : a ≤ b) :
    gaussianRate a u ≤ gaussianRate b u := by
  unfold gaussianRate GaussianEnvelope.referenceMinSlope
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hab hu.le)
        (PulseGrowth.dampingDenominator_pos u).le) hu.le) (by norm_num)

theorem referenceP_scaled_bound {lam u L c : ℝ}
    (hlam : 0 < lam) (hu : 0 < u) (hL : 0 < L) (hc : 0 < c)
    {v : ℝ} (hv : v ∈ Icc 0 (L / c)) :
    referenceP lam u L (c * v) ≤
      Real.exp (-(gaussianRate lam u * c) * (v / (L / c) - 1 / 2) ^ 2 * (L / c)) := by
  have hcv : c * v ∈ Icc 0 L :=
    ⟨mul_nonneg hc.le hv.1, by simpa only [mul_comm] using (le_div_iff₀ hc).mp hv.2⟩
  have htheta : c * v / L ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hcv.1 hL.le, (div_le_one hL).mpr hcv.2⟩
  have hb := GaussianTailFlat.referenceSlotEnvelope_bound hlam hu hL (c * v / L)
  rw [GaussianTailFlat.referenceSlotEnvelope, ite_eq_left htheta] at hb
  have htime : L * (c * v / L) = c * v := by field_simp
  rw [htime] at hb
  change referenceP lam u L (c * v) ≤ Real.exp
    (-gaussianRate lam u * (c * v / L - 1 / 2) ^ 2 * L) at hb
  refine hb.trans_eq ?_
  congr 1
  rw [normalized_clock hL.ne' hc.ne']
  field_simp

section ScaledEnvelope

variable {Label P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : PhaseJetBounds.Domain (Label × ℕ) PhaseCalculus.Slow}
  (F : PhaseConstruction D) (clock : ActualSignedControl.PositiveScale Label)

/-- Theta, given by `clock.value l n * v / F.L (l, n)`. -/
noncomputable def theta (l : Label) (n : ℕ) (v : ℝ) : ℝ :=
  clock.value l n * v / F.L (l, n)

theorem theta_eq (l : Label) (n : ℕ) (v : ℝ) :
    theta F clock l n v = v / ScaledActualParticularControl.length F clock l n :=
  normalized_clock (F.L_pos (l, n)).ne' (clock.value_pos l n).ne' v

theorem envelope_uniform_bound {lam0 u0 : ℝ} (_hlam0 : 0 < lam0) (hu0 : 0 < u0)
    (hlam : ∀ l n, lam0 ≤ F.lam (l, n)) (hu : ∀ l n, F.u (l, n) = u0)
    (l : Label) (n : ℕ) {v : ℝ}
    (hv : v ∈ Icc 0 (ScaledActualParticularControl.length F clock l n)) :
    ScaledActualParticularControl.envelope F clock l n v ≤
      Real.exp (-(gaussianRate lam0 u0 * clock.lower) * (theta F clock l n v - 1 / 2) ^ 2 *
        ScaledActualParticularControl.length F clock l n) := by
  have hb := referenceP_scaled_bound (F.lam_pos (l, n)) (F.u_pos (l, n))
    (F.L_pos (l, n)) (clock.value_pos l n) hv
  change ScaledActualParticularControl.envelope F clock l n v ≤ _ at hb
  rw [hu l n] at hb
  change ScaledActualParticularControl.envelope F clock l n v ≤
    Real.exp (-(gaussianRate (F.lam (l,n)) u0 * clock.value l n) *
      (v / ScaledActualParticularControl.length F clock l n - 1 / 2) ^ 2 *
        ScaledActualParticularControl.length F clock l n) at hb
  rw [← theta_eq F clock] at hb
  apply hb.trans
  apply Real.exp_le_exp.mpr
  have hcoeff : gaussianRate lam0 u0 * clock.lower ≤
      gaussianRate (F.lam (l, n)) u0 * clock.value l n :=
    mul_le_mul (gaussianRate_mono hu0 (hlam l n)) (clock.bounds l n).1
      clock.lower_pos.le (gaussianRate_pos (F.lam_pos (l, n)) hu0).le
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (theta F clock l n v - 1 / 2)))
    (ScaledActualParticularControl.length_pos F clock l n).le
  nlinarith

theorem length_uniform_lower {ell : ℝ}
    (hL : ∀ l n, ell * ChartScales.S n ≤ F.L (l, n)) (l : Label) (n : ℕ) :
    (ell / clock.upper) * ChartScales.S n ≤ ScaledActualParticularControl.length F clock l n := by
  have hu : 0 < clock.upper := zero_lt_one.trans_le clock.upper_one
  have hs : 0 ≤ ChartScales.S n := sq_nonneg _
  change (ell / clock.upper) * ChartScales.S n ≤ F.L (l, n) / clock.value l n
  calc
    _ = (ell * ChartScales.S n) / clock.upper := by ring
    _ ≤ F.L (l, n) / clock.upper := div_le_div_of_nonneg_right (hL l n) hu.le
    _ ≤ F.L (l, n) / clock.value l n :=
      div_le_div_of_nonneg_left (F.L_pos (l, n)).le (clock.value_pos l n) (clock.bounds l n).2

end ScaledEnvelope

/-! ## Compact whole-path zero germs for the genuine Volterra solve -/

section PathGerms

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem whole_path_zero_germ (g : Geometry) (k : Frequency) {a b : ℝ}
    {f : P × Plane → ComplexVector} {x : P × Plane}
    (hf : ∀ v ∈ Icc a b, f =ᶠ[𝓝 (x.1, g.path k x.2 v)] fun _ => 0) :
    ∀ᶠ y in 𝓝 x, ∀ v ∈ Icc a b, f (y.1, g.path k y.2 v) = 0 := by
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro v hv
  exact (hf v hv).comp_tendsto (g.pathArgument_contDiff k).continuous.continuousAt

theorem complexCopyVelocity_zero_germ (t : TangentData P ProblemStatement.Space)
    (g : Geometry) {a b : ℝ} (hab : a ≤ b) (k : Frequency)
    {f : P × Plane → ComplexVector} {x : P × Plane}
    (hf : ∀ v ∈ Icc a b, f =ᶠ[𝓝 (x.1, g.path k x.2 v)] fun _ => 0) :
    complexCopyVelocity t f g hab k =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [whole_path_zero_germ g k hf] with y hy
  exact complexCopyVelocity_zero_of_path t f g hab k y.1 y.2 hy

end PathGerms

/-! ## The separate Gaussian cutoff and its genuine outer padding -/

/-- Padding, given by `min r L / 16`. -/
noncomputable def padding (r L : ℝ) : ℝ := min r L / 16

theorem padding_pos {r L : ℝ} (hr : 0 < r) (hL : 0 < L) : 0 < padding r L :=
  div_pos (lt_min hr hL) (by norm_num)

/-- Reference window, bundling `lower`, `upper`, `padding`, `padding_pos`. -/
noncomputable def referenceWindow (r L : ℝ) (hr : 0 < r) (hL : 0 < L) :
    PeriodicPhaseAssembly.ClockWindow where
  lower := (-r, 0)
  upper := (r, L)
  padding := padding r L
  padding_pos := padding_pos hr hL

theorem referenceWindow_core (r L : ℝ) (hr : 0 < r) (hL : 0 < L) :
    (referenceWindow r L hr hL).core = WaveEnvelopeTransport.rectangle r L := rfl

/-- This cutoff is separate from every dyadic, radial and slow source
mask.  The outer padding is transported together with the Gaussian. -/
noncomputable def nativeCutoff (r L : ℝ) (hr : 0 < r) (hL : 0 < L) (c : ℝ) : Plane → ℝ :=
  fun z => (referenceWindow r L hr hL).cutoff (CopySolveCompatibility.nativeTimeMap 0 c z) *
    GaussianTailFlat.slotCutoff L (c * z.2)

/-- Outer cell, given by `Icc (-r - 2 * padding r L) (r + 2 * padding r L) ×ˢ Icc ((-2 * padding
r L) / c) ((L + 2 * padding r L) / c)`. -/
noncomputable def outerCell (r L c : ℝ) : Set Plane :=
  Icc (-r - 2 * padding r L) (r + 2 * padding r L) ×ˢ
    Icc ((-2 * padding r L) / c) ((L + 2 * padding r L) / c)

/-- The support inherited from a Gaussian slot profile has a strict
temporal margin at both ends of the full Volterra integration interval. -/
noncomputable def sourceCell (r L c : ℝ) : Set Plane :=
  Icc (-r) r ×ˢ Icc ((L / c) / 6) (5 * (L / c) / 6)

theorem outerCell_compact (r L c : ℝ) : IsCompact (outerCell r L c) :=
  isCompact_Icc.prod isCompact_Icc

theorem sourceCell_compact (r L c : ℝ) : IsCompact (sourceCell r L c) :=
  isCompact_Icc.prod isCompact_Icc

theorem mem_outerCell {r L c : ℝ} (hr : 0 < r) (hL : 0 < L) (hc : 0 < c) (z : Plane) :
    z ∈ outerCell r L c ↔
      CopySolveCompatibility.nativeTimeMap 0 c z ∈ (referenceWindow r L hr hL).outer := by
  change (_ ∧ _) ↔ (_ ∧ _)
  simp only [ mem_Icc, CopySolveCompatibility.nativeTimeMap, referenceWindow, zero_sub, zero_add,
    div_le_iff₀ hc, le_div_iff₀ hc, mul_comm, neg_mul]

theorem sourceCell_time {r L c : ℝ} (hL : 0 < L) (hc : 0 < c) {z : Plane}
    (hz : z ∈ sourceCell r L c) : z.2 ∈ Ioo 0 (L / c) := by
  have hp := div_pos hL hc
  exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩

theorem sourceCell_subset_outer {r L c : ℝ} (hr : 0 < r) (hL : 0 < L) (hc : 0 < c) :
    sourceCell r L c ⊆ outerCell r L c := by
  intro z hz
  apply (mem_outerCell hr hL hc z).mpr
  apply (referenceWindow r L hr hL).core_subset_outer
  have ht := sourceCell_time hL hc hz
  simp only [referenceWindow, PeriodicPhaseAssembly.ClockWindow.core,
    CopySolveCompatibility.nativeTimeMap, zero_add, mem_prod]
  change z.1 ∈ Icc (-r) r ∧ c * z.2 ∈ Icc 0 L
  exact ⟨hz.1, mul_nonneg hc.le ht.1.le,
    by simpa only [mul_comm] using (le_div_iff₀ hc).mp ht.2.le⟩

theorem nativeCutoff_support {r L c : ℝ} (hr : 0 < r) (hL : 0 < L) (hc : 0 < c) :
    support (nativeCutoff r L hr hL c) ⊆ outerCell r L c := by
  intro z hz
  apply (mem_outerCell hr hL hc z).mpr
  exact (referenceWindow r L hr hL).cutoff_support (mul_ne_zero_iff.mp hz).1

theorem nativeCutoff_central_germ {r L c : ℝ} (hr : 0 < r) (hL : 0 < L) (hc : 0 < c)
    {z : Plane} (hz : z ∈ WaveEnvelopeTransport.rectangle r (L / c))
    (hcentral : |z.2 / (L / c) - 1 / 2| < 1 / 5) :
    nativeCutoff r L hr hL c =ᶠ[𝓝 z] fun _ => 1 := by
  have hm : CopySolveCompatibility.nativeTimeMap 0 c z ∈ (referenceWindow r L hr hL).core := by
    simp only [referenceWindow, PeriodicPhaseAssembly.ClockWindow.core,
      CopySolveCompatibility.nativeTimeMap, zero_add, mem_prod]
    exact ⟨hz.1, mul_nonneg hc.le hz.2.1,
      by simpa only [mul_comm] using (le_div_iff₀ hc).mp hz.2.2⟩
  have ho := ((referenceWindow r L hr hL).cutoff_germ hm).comp_tendsto
    (CopySolveCompatibility.nativeTimeMap_continuous 0 c).continuousAt
  have ht : Continuous (fun y : Plane => c * y.2 / L) :=
    (continuous_const.mul continuous_snd).div_const L
  have hg := (GaussianTailFlat.profile_eventually_one
    (by simpa only [normalized_clock hL.ne' hc.ne'] using hcentral)).comp_tendsto ht.continuousAt
  filter_upwards [ho, hg] with y hy hgy
  dsimp only [Function.comp_def] at hy hgy
  simp only [nativeCutoff, GaussianTailFlat.slotCutoff, hy, hgy, mul_one]

theorem nativeCutoff_time_zero_germ {r L c : ℝ} (hr : 0 < r) (hL : 0 < L) (hc : 0 < c)
    {z : Plane} (hz : z.2 ∉ Ioo 0 (L / c)) :
    nativeCutoff r L hr hL c =ᶠ[𝓝 z] fun _ => 0 := by
  have hlen := div_pos hL hc
  have hdist : 1 / 3 < |z.2 / (L / c) - 1 / 2| := by
    by_cases hlo : z.2 ≤ 0
    · rw [abs_of_nonpos (by linarith [div_nonpos_of_nonpos_of_nonneg hlo hlen.le])]
      linarith [div_nonpos_of_nonpos_of_nonneg hlo hlen.le]
    · have hhi : L / c ≤ z.2 := le_of_not_gt (fun h => hz ⟨lt_of_not_ge hlo, h⟩)
      have hdiv : 1 ≤ z.2 / (L / c) := (le_div_iff₀ hlen).mpr (by simpa using hhi)
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hd : 1 / 3 < |c * z.2 / L - 1 / 2| := by
    rw [normalized_clock hL.ne' hc.ne']
    exact hdist
  have ht : Continuous (fun y : Plane => c * y.2 / L) :=
    (continuous_const.mul continuous_snd).div_const L
  have hg := (GaussianTailFlat.profile_eventually_zero hd).comp_tendsto ht.continuousAt
  filter_upwards [hg] with y hy
  dsimp only [Function.comp_def] at hy
  simp only [nativeCutoff, GaussianTailFlat.slotCutoff, hy, mul_zero]

/-! ## Source support controls the entire native path -/

theorem coordinates_path_outer (g : Geometry) (k : Frequency) {Y : Plane}
    {r L c v : ℝ} (hr : 0 < r) (hL : 0 < L) (hc : 0 < c)
    (hY : g.coordinates k Y ∈ outerCell r L c) (hv : v ∈ Icc 0 (L / c)) :
    g.coordinates k (g.path k Y v) ∈ outerCell r L c := by
  rw [g.coordinates_path]
  refine ⟨hY.1, ?_, ?_⟩
  · exact (div_nonpos_of_nonpos_of_nonneg (by nlinarith [padding_pos hr hL]) hc.le).trans hv.1
  · exact hv.2.trans (div_le_div_of_nonneg_right (by linarith [padding_pos hr hL]) hc.le)

theorem other_sourceCell_excluded (g : Geometry) {r L c : ℝ}
    (hr : 0 < r) (hL : 0 < L) (hc : 0 < c)
    (hinj : InjOn TorusAverages.quotientPoint
      ((fun z => g.center + g.basis z) '' outerCell r L c))
    {k : Frequency} {Y : Plane} (hY : g.coordinates k Y ∈ outerCell r L c)
    (hn : g.coordinates k Y ∉ sourceCell r L c) :
    ∀ i, g.coordinates i Y ∉ sourceCell r L c := by
  intro i hi
  have he := ParticularWaveAssembly.native_copy_unique g hinj hY
    (sourceCell_subset_outer hr hL hc hi)
  subst i
  exact hn hi

theorem path_sourceCell_excluded (g : Geometry) {r L c : ℝ}
    (hr : 0 < r) (hL : 0 < L) (hc : 0 < c)
    (hinj : InjOn TorusAverages.quotientPoint
      ((fun z => g.center + g.basis z) '' outerCell r L c))
    {k : Frequency} {Y : Plane} (hY : g.coordinates k Y ∈ outerCell r L c)
    (hxi : (g.coordinates k Y).1 ∉ Icc (-r) r) :
    ∀ v ∈ Icc 0 (L / c), ∀ i, g.coordinates i (g.path k Y v) ∉ sourceCell r L c := by
  intro v hv
  apply other_sourceCell_excluded g hr hL hc hinj (coordinates_path_outer g k hr hL hc hY hv)
  intro hs
  rw [g.coordinates_path] at hs
  exact hxi hs.1

section ActualSource

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Source region, given by `Prod.fst ⁻¹' S ∩ HarmonicSourceSupport.nativeUnion g (sourceCell r
L rate)`. -/
noncomputable def sourceRegion (S : Set P) (g : Geometry) (r L rate : ℝ) : Set (P × Plane) :=
  Prod.fst ⁻¹' S ∩ HarmonicSourceSupport.nativeUnion g (sourceCell r L rate)

omit [NormedSpace ℝ P] in
theorem sourceRegion_closed {S : Set P} (hS : IsClosed S) (g : Geometry) (r L rate : ℝ) :
    IsClosed (sourceRegion S g r L rate) :=
  (hS.preimage continuous_fst).inter
    (HarmonicSourceSupport.nativeUnion_closed g (sourceCell_compact r L rate))

theorem sourceFamily_zero_germ
    (ctx : CorrectionState.Context (P × Plane)) (u : CorrectionState.State (P × Plane))
    (b : CorrectionState.HarmonicBlock (P × Plane))
    (G A : HarmonicResidual.BlockCoefficients (P × Plane))
    {U : Set (P × Plane)} {K : ℕ → Set (P × Plane)} (hU : IsOpen U)
    (hK : ∀ n, IsClosed (K n)) (hs : HarmonicSourceSupport.InputSupportOn U K b G A)
    (j : ℤ) (n : ℕ) {x : (P × ℝ) × Plane}
    (hx : (x.1.1, x.2) ∈ U) (hn : (x.1.1, x.2) ∉ K n) :
    ParticularWaveAssembly.sourceFamily ctx u b G A j n =ᶠ[𝓝 x] fun _ => 0 :=
  (HarmonicSourceSupport.residualSource_zero_germ_on ctx u b G A hU hK hs j n hx hn).comp_tendsto
    (continuous_fst.fst.prodMk continuous_snd).continuousAt

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem sourceSupport_mono
    {U : Set (P × Plane)} {K T : ℕ → Set (P × Plane)}
    {b : CorrectionState.HarmonicBlock (P × Plane)}
    {G A : HarmonicResidual.BlockCoefficients (P × Plane)}
    (hs : HarmonicSourceSupport.InputSupportOn U K b G A) (hKT : ∀ n, K n ⊆ T n) :
    HarmonicSourceSupport.InputSupportOn U T b G A := by
  have hm {f : HarmonicFields.Coefficients (P × Plane)} {n : ℕ}
      (hf : HarmonicSourceSupport.NonzeroSupportedOn U (K n) f) :
      HarmonicSourceSupport.NonzeroSupportedOn U (T n) f := by
    intro j hj x hx hn
    exact hf j hj x hx (fun h => hn (hKT n h))
  exact ⟨fun n i => hm (hs.velocity n i), fun n => hm (hs.pressure n),
    fun n i => hm (hs.gaussian n i), fun n i => hm (hs.aliasError n i)⟩

end ActualSource

theorem transported_outer_injective (g : Geometry) (gap : ℕ) {r L c : ℝ}
    (hr : 0 < r) (hL : 0 < L) (hc : 0 < c)
    (hinj : InjOn TorusAverages.quotientPoint
      ((fun z => g.center + g.basis z) '' (referenceWindow r L hr hL).outer)) :
    InjOn TorusAverages.quotientPoint
      ((fun z => (CopySolveCompatibility.transportGeometry g gap 0 c hc.ne').center +
        (CopySolveCompatibility.transportGeometry g gap 0 c hc.ne').basis z) '' outerCell r L c) :=
            by
  apply hinj.mono
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨CopySolveCompatibility.nativeTimeMap 0 c z, (mem_outerCell hr hL hc z).mp hz, ?_⟩
  simp only [CopySolveCompatibility.nativeTimeMap, CopySolveCompatibility.transportGeometry,
    CopySolveCompatibility.refineGeometry, CopySolveCompatibility.timeGeometry,
    CommonCoverClass.scaledBasis_apply, zero_add, Prod.mk_zero_zero, map_zero, add_zero]

theorem reference_outer_separated (g : Geometry) {r L : ℝ} (hr : 0 < r) (hL : 0 < L)
    (hinj : InjOn TorusAverages.quotientPoint
      ((fun z => g.center + g.basis z) '' (referenceWindow r L hr hL).outer)) :
    WaveEnvelopeTransport.Separated g r L := by
  apply hinj.mono
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨z, (referenceWindow r L hr hL).core_subset_outer hz, rfl⟩

/-! ## One literal family of scaled solves and cutoffs -/

section Family

variable {Label P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : PhaseJetBounds.Domain (Label × ℕ) PhaseCalculus.Slow}
  (F : PhaseConstruction D) (clock : ActualSignedControl.PositiveScale Label)
  (reference : Label → ℕ → Geometry) (gap : Label → ℕ → ℕ)
  (r : Label → ℕ → ℝ) (hr : ∀ l n, 0 < r l n)

/-- Cutoff family, given by `nativeCutoff (r l n) (F.L (l,n)) (hr l n) (F.L_pos (l,n))
(clock.value l n)`. -/
noncomputable def cutoffFamily (l : Label) (n : ℕ) : Plane → ℝ :=
  nativeCutoff (r l n) (F.L (l,n)) (hr l n) (F.L_pos (l,n)) (clock.value l n)

/-- Outer family, given by `outerCell (r l n) (F.L (l,n)) (clock.value l n)`. -/
noncomputable def outerFamily (l : Label) (n : ℕ) : Set Plane :=
  outerCell (r l n) (F.L (l,n)) (clock.value l n)

/-- Source regions, given by `sourceRegion (S l n) (ScaledActualParticularControl.geometry
reference gap clock l n) (r l n) (F.L (l,n)) (clock.value l n)`. -/
noncomputable def sourceRegions (S : Label → ℕ → Set P) (l : Label) (n : ℕ) : Set (P × Plane) :=
  sourceRegion (S l n) (ScaledActualParticularControl.geometry reference gap clock l n)
    (r l n) (F.L (l,n)) (clock.value l n)

/-- Analytic patches, constructed using `ScaledActualParticularControl.patch`. -/
noncomputable def analyticPatches (s : StripData P) (χ : P →L[ℝ] PhaseCalculus.Slow)
    (φ : (Label × ℕ) → PhaseCalculus.Slow →L[ℝ] PhaseCalculus.Slow) :
    Label → ℕ → Frequency → Set ((P × ℝ) × Plane) :=
  ScaledActualParticularControl.patch (ActualParticularControl.angleStrip s) F
    (χ.comp (ContinuousLinearMap.fst ℝ P ℝ)) φ clock
    (ScaledActualParticularControl.geometry reference gap clock) r

variable (base : Label → LinearWaveBounds.WaveCoefficients ((P × ℝ) × Plane))
  (tangent : Label → ℕ → TangentData (P × ℝ) ProblemStatement.Space)
  (ctx : CorrectionState.Context (P × Plane)) (u : CorrectionState.State (P × Plane))
  (b : Label → CorrectionState.HarmonicBlock (P × Plane))
  (G A : Label → HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ)

/-- The same actual complex solve as the correction step, with entry zero,
exit `Lref/clock`, and a single transported Gaussian-times-padding cutoff. -/
noncomputable def data (l : Label) : CopyData ((P × ℝ) × Plane) Frequency :=
  complexCopyData (base l) (tangent l)
    (ParticularWaveAssembly.sourceFamily ctx u (b l) (G l) (A l) j)
    (ScaledActualParticularControl.geometry reference gap clock l)
    (fun _ => 0) (ScaledActualParticularControl.length F clock l)
    (fun n => (ScaledActualParticularControl.length_pos F clock l n).le)
    (cutoffFamily F clock r hr l)

theorem data_cutoff_support (l : Label) (n : ℕ) (k : Frequency) :
    support ((data F clock reference gap r hr base tangent ctx u b G A j l).cutoff n k) ⊆
      nativeCell (ScaledActualParticularControl.geometry reference gap clock l n)
        (outerFamily F clock r l n) k :=
  native_cutoff_support _ (nativeCutoff_support (hr l n) (F.L_pos (l,n)) (clock.value_pos l n)) k

theorem data_central (s : StripData P) (χ : P →L[ℝ] PhaseCalculus.Slow)
    (φ : (Label × ℕ) → PhaseCalculus.Slow →L[ℝ] PhaseCalculus.Slow)
    (l : Label) (n : ℕ) (k : Frequency) {x : (P × ℝ) × Plane}
    (hx : x ∈ analyticPatches F clock reference gap r s χ φ l n k)
    (hm : |theta F clock l n
      ((ScaledActualParticularControl.geometry reference gap clock l n).coordinates k x.2).2 - 1 /
          2| < 1 / 5) :
    (data F clock reference gap r hr base tangent ctx u b G A j l).cutoff n k
      =ᶠ[𝓝 x] fun _ => 1 := by
  have hrect : (ScaledActualParticularControl.geometry reference gap clock l n).coordinates k x.2 ∈
      WaveEnvelopeTransport.rectangle (r l n) (F.L (l,n) / clock.value l n) :=
    ⟨hx.2, hx.1.2.2.1.le, hx.1.2.2.2.le⟩
  have hg := nativeCutoff_central_germ (hr l n) (F.L_pos (l,n)) (clock.value_pos l n)
    hrect (by simpa only [theta_eq, ScaledActualParticularControl.length] using hm)
  exact hg.comp_tendsto
    (((ScaledActualParticularControl.geometry reference gap clock l n).coordinates_contDiff
        k).continuous.comp
      continuous_snd).continuousAt

variable (s : StripData P) (S : Label → ℕ → Set P) (hS : ∀ l n, IsClosed (S l n))
  (hsupport : ∀ l, HarmonicSourceSupport.InputSupportOn (s.domain ×ˢ univ)
    (sourceRegions F clock reference gap r S l) (b l) (G l) (A l))

include hS hsupport

theorem data_source_zero_germ (l : Label) (n : ℕ) {x : (P × ℝ) × Plane}
    (hx : x.1.1 ∈ s.domain)
    (hn : (x.1.1, x.2) ∉ sourceRegions F clock reference gap r S l n) :
    (data F clock reference gap r hr base tangent ctx u b G A j l).source n =ᶠ[𝓝 x] fun _ => 0 :=
  sourceFamily_zero_germ ctx u (b l) (G l) (A l) (s.isOpen_domain.prod isOpen_univ)
    (fun n => sourceRegion_closed (hS l n) _ _ _ _) (hsupport l) j n ⟨hx, mem_univ _⟩ hn

theorem data_amplitude_zero_germ (l : Label) (n : ℕ) (k : Frequency) {x : (P × ℝ) × Plane}
    (hx : x.1.1 ∈ s.domain)
    (hn : ∀ v ∈ Icc 0 (ScaledActualParticularControl.length F clock l n),
      (x.1.1, (ScaledActualParticularControl.geometry reference gap clock l n).path k x.2 v) ∉
        sourceRegions F clock reference gap r S l n) :
    (data F clock reference gap r hr base tangent ctx u b G A j l).amplitude n k =ᶠ[𝓝 x] fun _ => 0
        := by
  apply complexCopyVelocity_zero_germ
  intro v hv
  exact data_source_zero_germ F clock reference gap r hr base tangent ctx u b G A j
    s S hS hsupport l n (x := (x.1, _)) hx (hn v hv)

/-- The source is supported in an actual closed slow core and in the
Gaussian support rectangle.  On the rest of a padded copy, either the
Gaussian cutoff is zero or the entire source path is zero. -/
theorem data_outside (χ : P →L[ℝ] PhaseCalculus.Slow)
    (φ : (Label × ℕ) → PhaseCalculus.Slow →L[ℝ] PhaseCalculus.Slow)
    (hinside : ∀ l n p, p ∈ s.domain → p ∈ S l n → φ (l, n) (χ p) ∈ D.carrier (l, n))
    (hinj : ∀ l n, InjOn TorusAverages.quotientPoint
      ((fun z => (reference l n).center + (reference l n).basis z) ''
        (referenceWindow (r l n) (F.L (l, n)) (hr l n) (F.L_pos (l, n))).outer))
    (l : Label) (n : ℕ) (k : Frequency) {x : (P × ℝ) × Plane}
    (hx : x ∈ (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip s)).domain)
    (hk : x ∈ nativeCell (ScaledActualParticularControl.geometry reference gap clock l n)
      (outerFamily F clock r l n) k)
    (hnot : x ∉ analyticPatches F clock reference gap r s χ φ l n k) :
    (((data F clock reference gap r hr base tangent ctx u b G A j l).cutoff n k
        =ᶠ[𝓝 x] fun _ => 0) ∧
      ((data F clock reference gap r hr base tangent ctx u b G A j l).source n
        =ᶠ[𝓝 x] fun _ => 0)) ∨
    (((data F clock reference gap r hr base tangent ctx u b G A j l).amplitude n k
        =ᶠ[𝓝 x] fun _ => 0) ∧
      ((data F clock reference gap r hr base tangent ctx u b G A j l).source n
        =ᶠ[𝓝 x] fun _ => 0)) := by
  let g := ScaledActualParticularControl.geometry reference gap clock l n
  have hi : InjOn TorusAverages.quotientPoint
      ((fun z => g.center + g.basis z) '' outerCell (r l n) (F.L (l,n)) (clock.value l n)) :=
    transported_outer_injective (reference l n) (gap l n) (hr l n) (F.L_pos (l,n))
      (clock.value_pos l n) (hinj l n)
  have hk' : g.coordinates k x.2 ∈ outerCell (r l n) (F.L (l,n)) (clock.value l n) := hk
  have hx' : x.1.1 ∈ s.domain := hx
  by_cases hp : φ (l,n) (χ x.1.1) ∈ D.carrier (l,n)
  · by_cases hxi : (g.coordinates k x.2).1 ∈ Icc (-(r l n)) (r l n)
    · have hv : (g.coordinates k x.2).2 ∉ Ioo 0 (ScaledActualParticularControl.length F clock l n)
        := by
        intro hv
        exact hnot ⟨⟨hx, hp, hv⟩, hxi⟩
      have hg := nativeCutoff_time_zero_germ (hr l n) (F.L_pos (l,n)) (clock.value_pos l n) hv
      refine Or.inl ⟨hg.comp_tendsto ((g.coordinates_contDiff k).continuous.comp
          continuous_snd).continuousAt, ?_⟩
      apply data_source_zero_germ F clock reference gap r hr base tangent ctx u b G A j s S hS
          hsupport l n hx'
      intro hs
      obtain ⟨i, hi'⟩ := mem_iUnion.mp hs.2
      exact (other_sourceCell_excluded g (hr l n) (F.L_pos (l,n)) (clock.value_pos l n) hi hk'
        (fun h => hv (sourceCell_time (F.L_pos (l,n)) (clock.value_pos l n) h)) i) hi'
    · refine Or.inr ⟨?_, ?_⟩
      · apply data_amplitude_zero_germ F clock reference gap r hr base tangent ctx u b G A j s S hS
          hsupport l n k hx'
        intro v hv hs
        obtain ⟨i, hi'⟩ := mem_iUnion.mp hs.2
        exact path_sourceCell_excluded g (hr l n) (F.L_pos (l,n)) (clock.value_pos l n) hi hk' hxi
            v hv i hi'
      · apply data_source_zero_germ F clock reference gap r hr base tangent ctx u b G A j s S hS
          hsupport l n hx'
        intro hs
        obtain ⟨i, hi'⟩ := mem_iUnion.mp hs.2
        exact (other_sourceCell_excluded g (hr l n) (F.L_pos (l,n)) (clock.value_pos l n) hi hk'
          (fun h => hxi h.1) i) hi'
  · have hp' : x.1.1 ∉ S l n := fun h => hp (hinside l n _ hx' h)
    refine Or.inr ⟨?_, ?_⟩
    · apply data_amplitude_zero_germ F clock reference gap r hr base tangent ctx u b G A j s S hS
        hsupport l n k hx'
      intro _ _ hs
      exact hp' hs.1
    · apply data_source_zero_germ F clock reference gap r hr base tangent ctx u b G A j s S hS
        hsupport l n hx'
      intro hs
      exact hp' hs.1

omit hS in
theorem data_source_complement (β : ℝ) :
    LocalizedGaussianBounds.UniformComplementJets
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip s)) (fun _ _ _ => 1) β
      (fun l n => nativeCell (ScaledActualParticularControl.geometry reference gap clock l n)
        (outerFamily F clock r l n))
      (fun l => (data F clock reference gap r hr base tangent ctx u b G A j l).source) := by
  have hlarge l : HarmonicSourceSupport.InputSupportOn (s.domain ×ˢ univ)
      (fun n => HarmonicSourceSupport.nativeUnion
        (ScaledActualParticularControl.geometry reference gap clock l n) (outerFamily F clock r l
            n))
      (b l) (G l) (A l) := by
    apply sourceSupport_mono (hsupport l)
    intro n x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx.2
    exact mem_iUnion.mpr ⟨k, sourceCell_subset_outer (hr l n) (F.L_pos (l,n)) (clock.value_pos l n)
        hk⟩
  exact LocalizedGaussianBounds.uniform_source_complement_of_harmonicSupport
    (data F clock reference gap r hr base tangent ctx u b G A j)
    ctx u b G A (ScaledActualParticularControl.geometry reference gap clock) (outerFamily F clock r)
    (fun l n => outerCell_compact _ _ _) (s.isOpen_domain.prod isOpen_univ) hlarge
    (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip s)) (fun _ hx => ⟨hx,
        mem_univ _⟩)
    (fun _ => j) (fun _ => rfl) β

end Family

/-! ## Uniform jets of the actual Gaussian clock cutoff -/

section AffineJets

variable {X Label I : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Translated native copies share the same constants: only the linear
part of their normalized clock enters the estimate. -/
theorem affine_profile_uniform_jets (s : StripData X)
    (C : Label → ℕ → I → Set X) (A : Label → ℕ → X →L[ℝ] ℝ)
    (b : Label → ℕ → I → ℝ)
    (hA : ∃ K : ℝ, 1 ≤ K ∧ ∃ p : ℕ, ∀ l n, ‖A l n‖ ≤ K * s.slow n ^ p) :
    UniformLocalJets s (fun _ _ _ => 1) 0 C
      (fun l n i x => GaussianTailFlat.profile (b l n i + A l n x)) := by
  obtain ⟨K, hK, p, hA⟩ := hA
  refine ⟨fun l n i _ _ _ =>
    (GaussianTailFlat.profile_contDiff.comp (contDiff_const.add (A l n).contDiff)).contDiffAt, ?_⟩
  intro m
  obtain ⟨B, hB, hb⟩ := GaussianTailFlat.finite_jet_bounds GaussianTailFlat.profile_jet_bounded m
  refine ⟨B * K ^ m, by positivity, p * m, ?_⟩
  intro l n i x hx hi j hj
  have hbase : 1 ≤ K * s.growth n x ^ p :=
    one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ (s.one_le_growth n x))
  have hAn : ‖A l n‖ ≤ K * s.growth n x ^ p :=
    (hA l n).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans (s.one_le_slow n)) (s.slow_le_growth n x) p)
      (zero_le_one.trans hK))
  calc
    _ ≤ ‖iteratedFDeriv ℝ j GaussianTailFlat.profile (b l n i + A l n x)‖ * ‖A l n‖ ^ j :=
      GaussianTailFlat.norm_affine_comp_jet_le GaussianTailFlat.profile_contDiff (A l n) (b l n i)
          x j
    _ ≤ B * (K * s.growth n x ^ p) ^ m :=
      mul_le_mul (hb j hj _) ((pow_le_pow_left₀ (norm_nonneg _) hAn j).trans
        (pow_le_pow_right₀ hbase hj)) (pow_nonneg (norm_nonneg _) _) hB
    _ = majorant s (fun _ _ => 1) 0 (B * K ^ m) (p * m) n x := by
      simp only [majorant, Real.rpow_zero, mul_one, mul_pow, ← pow_mul]
      ring

end AffineJets

section ClockJets

variable {P Label : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : PhaseJetBounds.Domain (Label × ℕ) PhaseCalculus.Slow}
  (F : PhaseConstruction D) (clock : ActualSignedControl.PositiveScale Label)

/-- The primitive rate bound for the selected phase family controls the
inverse transported slot length without any loss in the copy index. -/
theorem inverse_length_bound {u0 : ℝ} (hu0 : 0 < u0)
    (hu : ∀ l n, F.u (l, n) = u0) (l : Label) (n : ℕ) :
    (ScaledActualParticularControl.length F clock l n)⁻¹ ≤ clock.upper * F.M / u0 := by
  have hp : 0 ≤ u0 / F.L (l,n) := (div_pos hu0 (F.L_pos (l,n))).le
  have hb : u0 / F.L (l,n) ≤ F.M := by
    calc
      _ ≤ u0 / F.L (l,n) * D.scale (l,n) :=
        le_mul_of_one_le_right hp (D.one_le_scale (l,n))
      _ ≤ F.M := by simpa only [hu l n, abs_of_nonneg hp] using F.rate_bound (l,n)
  have hmul := mul_le_mul_of_nonneg_left hb (clock.upper_one.trans' zero_le_one)
  have hr := mul_le_mul_of_nonneg_right (clock.bounds l n).2 hp
  have hh := div_le_div_of_nonneg_right (hr.trans hmul) hu0.le
  convert! hh using 1
  dsimp only [ScaledActualParticularControl.length]
  field_simp [hu0.ne', (F.L_pos (l,n)).ne', (clock.value_pos l n).ne']

/-- Normalized linear, given by `L⁻¹ • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
(g.coordinateLinear.comp (ContinuousLinearMap.snd ℝ P Plane)))`. -/
noncomputable def normalizedLinear (g : Geometry) (L : ℝ) : (P × Plane) →L[ℝ] ℝ :=
  L⁻¹ • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    (g.coordinateLinear.comp (ContinuousLinearMap.snd ℝ P Plane)))

theorem normalizedLinear_apply (g : Geometry) (L : ℝ) (x : P × Plane) :
    normalizedLinear (P := P) g L x = (g.coordinateLinear x.2).2 / L := by
  change L⁻¹ * (g.coordinateLinear x.2).2 = (g.coordinateLinear x.2).2 / L
  ring

theorem normalized_coordinate_affine (g : Geometry) (L : ℝ) (k : Frequency) (x : P × Plane) :
    (g.coordinates k x.2).2 / L = (g.coordinates k 0).2 / L + normalizedLinear (P := P) g L x := by
  rw [g.coordinates_eq_affine, normalizedLinear_apply]
  simp only [Prod.snd_add, add_div]

theorem normalizedLinear_norm (g : Geometry) {L : ℝ} (hL : 0 < L) :
    ‖normalizedLinear (P := P) g L‖ ≤ L⁻¹ * CommonCoverClass.argumentCost g := by
  have hc : ‖g.coordinateLinear‖ ≤ CommonCoverClass.argumentCost g := by
    unfold CommonCoverClass.argumentCost
    have h : 0 ≤ ‖g.pointLinear‖ * (1 + ‖g.coordinateLinear‖) := by positivity
    linarith
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (inv_nonneg.mpr hL.le) (zero_le_one.trans (CommonCoverClass.one_le_argumentCost g)))
  intro x
  rw [normalizedLinear_apply, norm_div,
    show ‖L‖ = L by simp only [Real.norm_eq_abs, abs_of_pos hL]]
  calc
    _ ≤ ‖g.coordinateLinear x.2‖ / L := div_le_div_of_nonneg_right (norm_snd_le _) hL.le
    _ ≤ (‖g.coordinateLinear‖ * ‖x.2‖) / L :=
      div_le_div_of_nonneg_right (g.coordinateLinear.le_opNorm _) hL.le
    _ ≤ (CommonCoverClass.argumentCost g * ‖x‖) / L :=
      div_le_div_of_nonneg_right (mul_le_mul hc (norm_snd_le _) (norm_nonneg _)
        (zero_le_one.trans (CommonCoverClass.one_le_argumentCost g))) hL.le
    _ = _ := by ring

theorem gaussian_clock_uniform_jets
    (s : StripData (P × Plane)) (C : Label → ℕ → Frequency → Set (P × Plane))
    (g : Label → ℕ → Geometry) {u0 : ℝ} (hu0 : 0 < u0) (hu : ∀ l n, F.u (l, n) = u0)
    (hcost : ∃ K : ℝ, 1 ≤ K ∧ ∃ p : ℕ,
      ∀ l n, CommonCoverClass.argumentCost (g l n) ≤ K * s.slow n ^ p) :
    UniformLocalJets s (fun _ _ _ => 1) 0 C
      (fun l n k x => GaussianTailFlat.profile
        (theta F clock l n ((g l n).coordinates k x.2).2)) := by
  obtain ⟨K, hK, p, hcost⟩ := hcost
  have hc : 0 ≤ clock.upper * F.M / u0 :=
    div_nonneg (mul_nonneg (zero_le_one.trans clock.upper_one)
      (zero_le_one.trans F.one_le_M)) hu0.le
  have hA : ∃ A : ℝ, 1 ≤ A ∧ ∃ p : ℕ, ∀ l n,
      ‖normalizedLinear (P := P) (g l n) (ScaledActualParticularControl.length F clock l n)‖ ≤
        A * s.slow n ^ p := by
    refine ⟨1 + (clock.upper * F.M / u0) * K,
      le_add_of_nonneg_right (mul_nonneg hc (zero_le_one.trans hK)), p, fun l n => ?_⟩
    calc
      _ ≤ (ScaledActualParticularControl.length F clock l n)⁻¹ *
          CommonCoverClass.argumentCost (g l n) :=
        normalizedLinear_norm (g l n) (ScaledActualParticularControl.length_pos F clock l n)
      _ ≤ (clock.upper * F.M / u0) * (K * s.slow n ^ p) :=
        mul_le_mul (inverse_length_bound F clock hu0 hu l n) (hcost l n)
          (zero_le_one.trans (CommonCoverClass.one_le_argumentCost _)) hc
      _ ≤ (1 + (clock.upper * F.M / u0) * K) * s.slow n ^ p := by
        nlinarith [pow_nonneg (zero_le_one.trans (s.one_le_slow n)) p]
  have hj := affine_profile_uniform_jets s C
    (fun l n => normalizedLinear (P := P) (g l n) (ScaledActualParticularControl.length F clock l
        n))
    (fun l n k => ((g l n).coordinates k 0).2 / ScaledActualParticularControl.length F clock l n) hA
  convert! hj using 1
  funext l n k x
  rw [theta_eq, normalized_coordinate_affine]

end ClockJets

section CutoffJets

variable {Label P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : PhaseJetBounds.Domain (Label × ℕ) PhaseCalculus.Slow}
  (F : PhaseConstruction D) (clock : ActualSignedControl.PositiveScale Label)
  (reference : Label → ℕ → Geometry) (gap : Label → ℕ → ℕ)
  (r : Label → ℕ → ℝ) (hr : ∀ l n, 0 < r l n)
  (base : Label → LinearWaveBounds.WaveCoefficients ((P × ℝ) × Plane))
  (tangent : Label → ℕ → TangentData (P × ℝ) ProblemStatement.Space)
  (ctx : CorrectionState.Context (P × Plane)) (u : CorrectionState.State (P × Plane))
  (b : Label → CorrectionState.HarmonicBlock (P × Plane))
  (G A : Label → HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ)
  (s : StripData P) (χ : P →L[ℝ] PhaseCalculus.Slow)
  (φ : (Label × ℕ) → PhaseCalculus.Slow →L[ℝ] PhaseCalculus.Slow)

/-- On the analytic native cell the outer padding is identically one
nearby, leaving exactly the normalized Gaussian profile. -/
theorem data_cutoff_gaussian_germ (l : Label) (n : ℕ) (k : Frequency) {x : (P × ℝ) × Plane}
    (hx : x ∈ analyticPatches F clock reference gap r s χ φ l n k) :
    (data F clock reference gap r hr base tangent ctx u b G A j l).cutoff n k =ᶠ[𝓝 x]
      fun y => GaussianTailFlat.profile (theta F clock l n
        ((ScaledActualParticularControl.geometry reference gap clock l n).coordinates k y.2).2) :=
            by
  let g := ScaledActualParticularControl.geometry reference gap clock l n
  have hm : CopySolveCompatibility.nativeTimeMap 0 (clock.value l n) (g.coordinates k x.2) ∈
      (referenceWindow (r l n) (F.L (l,n)) (hr l n) (F.L_pos (l,n))).core := by
    change (g.coordinates k x.2).1 ∈ Icc (-(r l n)) (r l n) ∧
      0 + clock.value l n * (g.coordinates k x.2).2 ∈ Icc 0 (F.L (l,n))
    simp only [zero_add]
    exact And.intro hx.2 (ScaledActualParticularControl.clock_mem F clock
        ⟨hx.1.2.2.1.le, hx.1.2.2.2.le⟩)
  have hc : Continuous (fun y : (P × ℝ) × Plane =>
      CopySolveCompatibility.nativeTimeMap 0 (clock.value l n) (g.coordinates k y.2)) :=
    (CopySolveCompatibility.nativeTimeMap_continuous _ _).comp
      ((g.coordinates_contDiff k).continuous.comp continuous_snd)
  have he := ((referenceWindow (r l n) (F.L (l,n)) (hr l n)
    (F.L_pos (l,n))).cutoff_germ hm).comp_tendsto hc.continuousAt
  filter_upwards [he] with y hy
  dsimp only [Function.comp_def] at hy
  change (referenceWindow (r l n) (F.L (l,n)) (hr l n) (F.L_pos (l,n))).cutoff
      (CopySolveCompatibility.nativeTimeMap 0 (clock.value l n) (g.coordinates k y.2)) * _ = _
  rw [hy, one_mul]
  rfl

theorem data_cutoff_jets {u0 : ℝ} (hu0 : 0 < u0) (hu : ∀ l n, F.u (l, n) = u0)
    (hcost : ∃ K : ℝ, 1 ≤ K ∧ ∃ p : ℕ, ∀ l n,
      CommonCoverClass.argumentCost (ScaledActualParticularControl.geometry reference gap clock l
          n) ≤
        K * s.slow n ^ p) :
    UniformLocalJets (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip s))
      (fun _ _ _ => 1) 0 (analyticPatches F clock reference gap r s χ φ)
      (fun l => (data F clock reference gap r hr base tangent ctx u b G A j l).cutoff) := by
  have hj := gaussian_clock_uniform_jets F clock
    (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip s))
    (analyticPatches F clock reference gap r s χ φ)
    (ScaledActualParticularControl.geometry reference gap clock) hu0 hu hcost
  apply LocalizedWaveBounds.LocalClass.to_uniformLocalJets
  apply (LocalizedWaveBounds.LocalClass.of_uniformLocalJets (fun _ _ _ _ => zero_le_one)
      hj).congr_germ
  intro n li x hx hi
  exact (data_cutoff_gaussian_germ F clock reference gap r hr base tangent ctx u b G A j
    s χ φ li.1 n li.2 hi).symm

end CutoffJets

/-! ## The actual complex solve inherits the modal amplitude estimates -/

section ModalAmplitude

variable {P Label : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [Countable Label] [Nonempty Label]

theorem complex_amplitude_uniform_jets {s : StripData (P × Plane)} {α : ℝ}
    (t : Label → ℕ → TangentData P ProblemStatement.Space)
    (source : Label → ℕ → P × Plane → ComplexVector)
    (g : Label → ℕ → Geometry) (L : Label → ℕ → ℝ) (hL : ∀ l n, 0 < L l n)
    (envelope : Label → ℕ → ℝ → ℝ) (W : Label → ℕ → P × Plane → ℝ)
    (d : Label → ℕ → PrimaryODE.FrameData (P × ℝ)) (harmonic : ℤ)
    (C : Label → ℕ → Frequency → Set (P × Plane))
    (hr : ParticularCopyBounds.UniformModalControl s α d
      (fun l n => realData (t l n) (source l n)) harmonic g L envelope C)
    (hi : ParticularCopyBounds.UniformModalControl s α d
      (fun l n => imagData (t l n) (source l n)) harmonic g L envelope C)
    (hW : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (hcompare : ∀ l n k x, x ∈ s.domain → x ∈ C l n k →
      envelope l n ((g l n).coordinates k x.2).2 ≤ W l n x) :
    UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) α C
      (fun l n k => complexCopyVelocity (t l n) (source l n) (g l n) (hL l n).le k) := by
  have hw l n x hx := mul_nonneg (Real.sqrt_nonneg (s.zeta x)) (hW l n x hx)
  have hreal := LocalizedWaveBounds.LocalClass.of_uniformLocalJets hw (hr.localJets hL W hcompare)
  have himag := LocalizedWaveBounds.LocalClass.of_uniformLocalJets hw (hi.localJets hL W hcompare)
  exact ((hreal.map CurlClassBounds.complexify).add
    (himag.map ((complexScale Complex.I).comp CurlClassBounds.complexify))).to_uniformLocalJets

end ModalAmplitude

/-! ## The all-powers bound for the assembled, actual Gaussian error -/

section AllGains

variable {Label P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : PhaseJetBounds.Domain (Label × ℕ) PhaseCalculus.Slow}
  (F : PhaseConstruction D) (clock : ActualSignedControl.PositiveScale Label)
  (reference : Label → ℕ → Geometry) (gap : Label → ℕ → ℕ)
  (r : Label → ℕ → ℝ) (hr : ∀ l n, 0 < r l n)

/-- Field envelope, constructed using `ActualParticularControl.groupedEnvelope`. -/
noncomputable def fieldEnvelope : Label → ℕ → (P × ℝ) × Plane → ℝ :=
  ActualParticularControl.groupedEnvelope
    (ScaledActualParticularControl.geometry reference gap clock) r
    (ScaledActualParticularControl.length F clock) (ScaledActualParticularControl.envelope F clock)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem fieldEnvelope_nonneg (l : Label) (n : ℕ) (x : (P × ℝ) × Plane) :
    0 ≤ fieldEnvelope F clock reference gap r l n x :=
  WaveEnvelopeTransport.copyEnvelope_nonneg _ _ _ (fun v =>
    (referenceP_pos (F.lam (l,n)) (F.u (l,n)) (F.L (l,n)) (clock.value l n * v)).le) x.2

theorem fieldEnvelope_eq (s : StripData P) (χ : P →L[ℝ] PhaseCalculus.Slow)
    (φ : (Label × ℕ) → PhaseCalculus.Slow →L[ℝ] PhaseCalculus.Slow)
    (hinj : ∀ l n, InjOn TorusAverages.quotientPoint
      ((fun z => (reference l n).center + (reference l n).basis z) ''
        (referenceWindow (r l n) (F.L (l, n)) (hr l n) (F.L_pos (l, n))).outer))
    {l : Label} {n : ℕ} {k : Frequency} {x : (P × ℝ) × Plane}
    (hx : x ∈ analyticPatches F clock reference gap r s χ φ l n k) :
    fieldEnvelope F clock reference gap r l n x =
      ScaledActualParticularControl.envelope F clock l n
        ((ScaledActualParticularControl.geometry reference gap clock l n).coordinates k x.2).2 :=
  ScaledActualParticularControl.patch_envelope (ActualParticularControl.angleStrip s) F
    (χ.comp (ContinuousLinearMap.fst ℝ P ℝ)) φ clock reference gap r
    (fun l n => reference_outer_separated _ (hr l n) (F.L_pos (l,n)) (hinj l n)) hx

/-- Cells, constructed using `nativeCells`. -/
noncomputable def cells
    (hinj : ∀ l n, InjOn TorusAverages.quotientPoint
      ((fun z => (reference l n).center + (reference l n).basis z) ''
        (referenceWindow (r l n) (F.L (l, n)) (hr l n) (F.L_pos (l, n))).outer))
    (l : Label) : Cells ((P × ℝ) × Plane) Frequency :=
  nativeCells (ScaledActualParticularControl.geometry reference gap clock l)
    (outerFamily F clock r l) (fun _ => outerCell_compact _ _ _)
    (fun n => transported_outer_injective _ (gap l n) (hr l n) (F.L_pos (l,n))
      (clock.value_pos l n) (hinj l n))

variable [Countable Label] [Nonempty Label]
  (base : Label → LinearWaveBounds.WaveCoefficients ((P × ℝ) × Plane))
  (tangent : Label → ℕ → TangentData (P × ℝ) ProblemStatement.Space)
  (ctx : CorrectionState.Context (P × Plane)) (u : CorrectionState.State (P × Plane))
  (b : Label → CorrectionState.HarmonicBlock (P × Plane))
  (G A : Label → HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ)
  (s : StripData P) (χ : P →L[ℝ] PhaseCalculus.Slow)
  (φ : (Label × ℕ) → PhaseCalculus.Slow →L[ℝ] PhaseCalculus.Slow)

/-- Every real power is gained by the literal global Gaussian error,
including its uncovered-source term. The source support assumptions are
on the incoming harmonic coefficients; all output zero germs and all
cutoff estimates are derived. The modal controls are precisely those
constructed by `ScaledActualParticularControl`. -/
theorem globalGaussian_all_gains
    (frame : Label → ℕ → PrimaryODE.FrameData ((P × ℝ) × ℝ))
    {α lam0 u0 ell : ℝ} (hlam0 : 0 < lam0) (hu0 : 0 < u0) (hell : 0 < ell)
    (hlam : ∀ l n, lam0 ≤ F.lam (l, n)) (hu : ∀ l n, F.u (l, n) = u0)
    (hL : ∀ l n, ell * ChartScales.S n ≤ F.L (l, n))
    (hinj : ∀ l n, InjOn TorusAverages.quotientPoint
      ((fun z => (reference l n).center + (reference l n).basis z) ''
        (referenceWindow (r l n) (F.L (l, n)) (hr l n) (F.L_pos (l, n))).outer))
    (S : Label → ℕ → Set P) (hS : ∀ l n, IsClosed (S l n))
    (hsupport : ∀ l, HarmonicSourceSupport.InputSupportOn (s.domain ×ˢ univ)
      (sourceRegions F clock reference gap r S l) (b l) (G l) (A l))
    (hinside : ∀ l n p, p ∈ s.domain → p ∈ S l n → φ (l, n) (χ p) ∈ D.carrier (l, n))
    (hreal : ParticularCopyBounds.UniformModalControl
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip s)) α frame
      (fun l n => realData (tangent l n) (ParticularWaveAssembly.sourceFamily ctx u (b l) (G l) (A
          l) j n))
      j (ScaledActualParticularControl.geometry reference gap clock)
      (ScaledActualParticularControl.length F clock) (ScaledActualParticularControl.envelope F
          clock)
      (analyticPatches F clock reference gap r s χ φ))
    (himag : ParticularCopyBounds.UniformModalControl
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip s)) α frame
      (fun l n => imagData (tangent l n) (ParticularWaveAssembly.sourceFamily ctx u (b l) (G l) (A
          l) j n))
      j (ScaledActualParticularControl.geometry reference gap clock)
      (ScaledActualParticularControl.length F clock) (ScaledActualParticularControl.envelope F
          clock)
      (analyticPatches F clock reference gap r s χ φ))
    (hsource : UniformLocalJets
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip s))
      (fun l n x => Real.sqrt (s.zeta x.1.1) * fieldEnvelope F clock reference gap r l n x) α
      (analyticPatches F clock reference gap r s χ φ)
      (fun l n _ => ParticularWaveAssembly.sourceFamily ctx u (b l) (G l) (A l) j n))
    (dirs : LinearWaveBounds.GraphDirections ((P × ℝ) × Plane))
    (hfast : BandBound (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip s)) 0
        dirs.fastScale)
    (edges : GaussianTailFlat.FlatEdges (CommonCoverClass.sourceStrip
        (ActualParticularControl.angleStrip s)))
    (scales : GaussianTailFlat.BandScaleControl (CommonCoverClass.sourceStrip
        (ActualParticularControl.angleStrip s)))
    (β : ℝ) :
    LabelSumBounds.UniformClass (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip
        s))
      (fun _ _ _ => 1) β
      (fun l => (data F clock reference gap r hr base tangent ctx u b G A j l).globalGaussian dirs)
          := by
  have hw l n x (_ : x ∈ (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip
      s)).domain) :=
    fieldEnvelope_nonneg F clock reference gap r l n x
  have he l n k x (_ : x ∈ (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip
      s)).domain)
      (hx : x ∈ analyticPatches F clock reference gap r s χ φ l n k) :=
    (fieldEnvelope_eq F clock reference gap r hr s χ φ hinj hx).ge
  have hamp := complex_amplitude_uniform_jets tangent
    (fun l => ParticularWaveAssembly.sourceFamily ctx u (b l) (G l) (A l) j)
    (ScaledActualParticularControl.geometry reference gap clock)
    (ScaledActualParticularControl.length F clock) (ScaledActualParticularControl.length_pos F
        clock)
    (ScaledActualParticularControl.envelope F clock) (fieldEnvelope F clock reference gap r)
    frame j (analyticPatches F clock reference gap r s χ φ) hreal himag hw he
  apply LocalizedGaussianBounds.uniform_globalGaussian_all_gains_from_supported_native
    (data F clock reference gap r hr base tangent ctx u b G A j)
    (cells F clock reference gap r hr hinj)
    (data_cutoff_support F clock reference gap r hr base tangent ctx u b G A j)
    dirs (analyticPatches F clock reference gap r s χ φ) hw
    (data_cutoff_jets F clock reference gap r hr base tangent ctx u b G A j s χ φ hu0 hu
      ⟨hreal.boundConstant, hreal.constant_ge_one, hreal.coordinatePower, hreal.coordinate_bound⟩)
    hfast hamp hsource edges scales
    (fun l n k x => theta F clock l n
      ((ScaledActualParticularControl.geometry reference gap clock l n).coordinates k x.2).2)
    (ScaledActualParticularControl.length F clock) (ScaledActualParticularControl.length_pos F
        clock)
    (ell / clock.upper) (div_pos hell (zero_lt_one.trans_le clock.upper_one))
    (length_uniform_lower F clock hL)
    (mul_pos (gaussianRate_pos hlam0 hu0) clock.lower_pos)
    ?_ ?_ ?_ β
    (data_source_complement F clock reference gap r hr base tangent ctx u b G A j s S hsupport β)
  · intro l n k x hx hc
    rw [fieldEnvelope_eq F clock reference gap r hr s χ φ hinj hc]
    exact envelope_uniform_bound F clock hlam0 hu0 hlam hu l n ⟨hc.1.2.2.1.le, hc.1.2.2.2.le⟩
  · intro l n k x hx hc hm
    exact Or.inl (data_central F clock reference gap r hr base tangent ctx u b G A j s χ φ l n k hc
        hm)
  · intro l n k x hx hk hn
    exact data_outside F clock reference gap r hr base tangent ctx u b G A j s S hS hsupport
      χ φ hinside hinj l n k hx hk hn

end AllGains

section CurrentSourceJets

variable {Label P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : PhaseJetBounds.Domain (Label × ℕ) PhaseCalculus.Slow}

/-- The local source estimate consumed above follows from the actual
current harmonic residual classes, with the angular variable inserted
by the literal source-family definition. -/
theorem source_jets_of_residual_classes
    (F : PhaseConstruction D) (clock : ActualSignedControl.PositiveScale Label)
    (reference : Label → ℕ → Geometry) (gap : Label → ℕ → ℕ) (r : Label → ℕ → ℝ)
    (s : StripData P) (χ : P →L[ℝ] PhaseCalculus.Slow)
    (φ : (Label × ℕ) → PhaseCalculus.Slow →L[ℝ] PhaseCalculus.Slow)
    (ctx : CorrectionState.Context (P × Plane)) (u : CorrectionState.State (P × Plane))
    (b : Label → CorrectionState.HarmonicBlock (P × Plane))
    (G A : Label → HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ) (α : ℝ)
    (h : ∀ i : Fin 3, LabelSumBounds.UniformWaveClass (CommonCoverClass.sourceStrip s)
      (ActualParticularControl.groupedEnvelope
        (ScaledActualParticularControl.geometry reference gap clock) r
        (ScaledActualParticularControl.length F clock) (ScaledActualParticularControl.envelope F
            clock)) α
      (fun l n x => (HarmonicResidual.residualBlock ctx u (b l) (G l) (A l)).velocity n i j x)) :
    UniformLocalJets (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip s))
      (fun l n x => Real.sqrt (s.zeta x.1.1) * fieldEnvelope F clock reference gap r l n x) α
      (analyticPatches F clock reference gap r s χ φ)
      (fun l n _ => ParticularWaveAssembly.sourceFamily ctx u (b l) (G l) (A l) j n) := by
  have hs := ActualParticularControl.sourceFamily_uniform s
    (ScaledActualParticularControl.geometry reference gap clock) r
    (ScaledActualParticularControl.length F clock) (ScaledActualParticularControl.envelope F clock)
    α ctx u b G A (fun _ => j) h
  refine ⟨fun l n _ x hx _ => (hs.smooth l n).contDiffAt
    ((CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip s)).isOpen_domain.mem_nhds
        hx), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hs.bounds m
  exact ⟨C, hC, p, fun l n _ x hx _ k hk => hb l n x hx k hk⟩

end CurrentSourceJets

/-! ## Bindings to the selected reference window and primary family -/

/-- Reference cutoff, given by `(referenceWindow r L hr hL).cutoff z *
GaussianTailFlat.slotCutoff L z.2`. -/
noncomputable def referenceCutoff (r L : ℝ) (hr : 0 < r) (hL : 0 < L) (z : Plane) : ℝ :=
  (referenceWindow r L hr hL).cutoff z * GaussianTailFlat.slotCutoff L z.2

theorem nativeCutoff_eq_reference_transport {r L c : ℝ} (hr : 0 < r) (hL : 0 < L) :
    nativeCutoff r L hr hL c = referenceCutoff r L hr hL ∘
      CopySolveCompatibility.nativeTimeMap 0 c := by
  funext z
  simp only [nativeCutoff, referenceCutoff, Function.comp_def,
    CopySolveCompatibility.nativeTimeMap, zero_add]

theorem referenceCutoff_support {r L : ℝ} (hr : 0 < r) (hL : 0 < L) :
    support (referenceCutoff r L hr hL) ⊆ univ ×ˢ Icc 0 L := by
  intro z hz
  have hg : GaussianTailFlat.profile (z.2 / L) ≠ 0 := (mul_ne_zero_iff.mp hz).2
  have hd : |z.2 / L - 1 / 2| < 1 / 3 := by
    exact lt_of_not_ge (fun h => hg (GaussianTailFlat.profile_zero h))
  have hlo : 0 ≤ z.2 / L := by linarith [(abs_lt.mp hd).1]
  have hhi : z.2 / L ≤ 1 := by linarith [(abs_lt.mp hd).2]
  exact ⟨mem_univ _, by simpa only [zero_mul] using (le_div_iff₀ hL).mp hlo,
    (div_le_one hL).mp hhi⟩

theorem mem_sourceCell_clock {r L c : ℝ} (hc : 0 < c) (z : Plane) :
    z ∈ sourceCell r L c ↔
      CopySolveCompatibility.nativeTimeMap 0 c z ∈ sourceCell r L 1 := by
  simp only [sourceCell, mem_prod, mem_Icc, CopySolveCompatibility.nativeTimeMap, zero_add, div_one]
  have hlo : L / c / 6 = (L / 6) / c := by ring
  have hhi : 5 * (L / c) / 6 = (5 * L / 6) / c := by ring
  rw [hlo, hhi, div_le_iff₀ hc, le_div_iff₀ hc]
  simp only [mul_comm]

section ActualWindow

variable {D h : ℝ} {vr vt : Plane}
  (sys : PartitionedCovariance.SlotSystem D h vr vt)
  (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)

theorem actual_slot_length_pos (m : ℕ) : 0 < ChartScales.slotLength sys.radius h m :=
  div_pos (mul_pos (by norm_num) sys.radius_pos) (ChartScales.timeCoefficient_pos h m)

theorem referenceWindow_eq_actual (m : ℕ) :
    referenceWindow sys.radius (ChartScales.slotLength sys.radius h m) sys.radius_pos
      (actual_slot_length_pos sys m) = ActualSignedGeometry.clockWindow sys m := rfl

/-- The actual slot system supplies the geometric injectivity needed
for finite periodization cells, including their outer padding. -/
theorem actual_outer_injective (hh : 0 ≤ h) {l : SlotColoring.Label} (hl : 4 ≤ l.1)
    (gap : ℕ) :
    InjOn TorusAverages.quotientPoint
      ((fun z => (ActualSignedGeometry.slotGeometry sys hdet l gap).center +
        (ActualSignedGeometry.slotGeometry sys hdet l gap).basis z) ''
        (referenceWindow sys.radius (ChartScales.slotLength sys.radius h l.1) sys.radius_pos
          (actual_slot_length_pos sys l.1)).outer) :=
  ActualSignedGeometry.clockWindow_injective sys hdet hh hl gap

theorem actual_scaled_slot_lower (hh : 0 ≤ h) {m : ℕ} (hm : 4 ≤ m)
    {c upper : ℝ} (hc : 0 < c) (hcU : c ≤ upper) :
    (2 * sys.radius / upper) * ChartScales.S m ≤ ChartScales.slotLength sys.radius h m / c := by
  have hU := hc.trans_le hcU
  calc
    _ = (2 * sys.radius * ChartScales.S m) / upper := by ring
    _ ≤ ChartScales.slotLength sys.radius h m / upper :=
      div_le_div_of_nonneg_right (ChartScales.slotLength_bounds sys.radius h sys.radius_pos.le hh
          hm).1 hU.le
    _ ≤ _ := div_le_div_of_nonneg_left (actual_slot_length_pos sys m).le hc hcU

end ActualWindow

section ActualParametersAndMasks

variable {profile : OutgoingProfile.Profile} {W : NominalProfile.Witness profile}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)
  {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
  (a : PrimaryGeometryAssembly.Prepared H v upper B r0 N0) (hr0 : 0 < r0)

theorem prepared_lambda_lower (sign : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) :
    a.M⁻¹ ≤ (PrimaryGeometryAssembly.construction H v a hr0 sign).lam L := by
  rw [PrimaryGeometryAssembly.construction_lambda]
  exact ((a.parameters L).positive_lower a.one_le_M
    (a.radius_pos L _ (PrimaryGeometryAssembly.representative_in_carrier W L)) (a.cone L)).2.2.1

theorem prepared_gaussian_rate_pos : 0 < gaussianRate a.M⁻¹ a.u :=
  gaussianRate_pos (inv_pos.mpr (zero_lt_one.trans_le a.one_le_M)) a.u_pos

/-- The closed slow support is the actual one-mesh primary mask.
Its inclusion in the two-mesh analytic phase cell has a genuine margin. -/
noncomputable def actualSlowCore (L : PrimaryGeometryAssembly.Index W a.N) : Set PhaseCalculus.Slow
    :=
  tsupport (PrimaryRepresentatives.nativeMask (BaseChartJets.cellBand L)
    (PrimaryGeometryAssembly.label W L).2)

theorem actualSlowCore_closed (L : PrimaryGeometryAssembly.Index W a.N) :
    IsClosed (actualSlowCore H v a L) := isClosed_tsupport _

theorem actualSlowCore_inside (L : PrimaryGeometryAssembly.Index W a.N) {p : PhaseCalculus.Slow}
    (hp : p ∈ actualSlowCore H v a L) (ht : 0 < p.2.2) :
    p ∈ (PrimaryGeometryAssembly.domain W a.N).carrier L :=
  PrimaryGeometryAssembly.native_support_in_carrier W L ⟨hp, ht⟩

/-- Actual source core, given by `actualSlowCore H v a L ×ˢ sourceCell r0
(ChartScales.slotLength r0 profile.data.h (BaseChartJets.cellBand L)) 1`. -/
noncomputable def actualSourceCore (L : PrimaryGeometryAssembly.Index W a.N) : Set
    ActualSignedGeometry.Native :=
  actualSlowCore H v a L ×ˢ sourceCell r0
    (ChartScales.slotLength r0 profile.data.h (BaseChartJets.cellBand L)) 1

theorem actualSourceCore_closed (L : PrimaryGeometryAssembly.Index W a.N) :
    IsClosed (actualSourceCore H v a L) :=
  (actualSlowCore_closed H v a L).prod (sourceCell_compact _ _ _).isClosed

include hr0 in
/-- The full actual source mask retains all its factors. Its support is
contained in the closed slow core and the Gaussian support rectangle;
none of the dyadic or radial factors is asserted to equal one. -/
theorem actualMask_support (L : PrimaryGeometryAssembly.Index W a.N) :
    support (ActualSignedGeometry.nativeCutoff H v a L) ⊆ actualSourceCore H v a L := by
  intro x hx
  change ActualSignedGeometry.nativeCutoff H v a L x ≠ 0 at hx
  simp only [ActualSignedGeometry.nativeCutoff, mul_ne_zero_iff] at hx
  have hL : 0 < ChartScales.slotLength r0 profile.data.h (BaseChartJets.cellBand L) :=
    div_pos (mul_pos (by norm_num) hr0) (ChartScales.timeCoefficient_pos _ _)
  have hs : x.1 ∈ actualSlowCore H v a L := subset_closure hx.1.1.2
  have htrans : x.2.1 ∈ Ioo (-r0) r0 := by
    rw [← PartitionedCovariance.cutoff_support hr0]
    exact hx.1.2
  have hg : |x.2.2 / ChartScales.slotLength r0 profile.data.h (BaseChartJets.cellBand L) - 1 / 2| <
      1 / 3 :=
    lt_of_not_ge (fun h => hx.2 (GaussianTailFlat.profile_zero h))
  have hlow : (1 / 6 : ℝ) < x.2.2 / ChartScales.slotLength r0 profile.data.h
      (BaseChartJets.cellBand L) := by
    linarith [(abs_lt.mp hg).1]
  have hhigh : x.2.2 / ChartScales.slotLength r0 profile.data.h (BaseChartJets.cellBand L) < 5 / 6
      := by
    linarith [(abs_lt.mp hg).2]
  refine ⟨hs, ⟨htrans.1.le, htrans.2.le⟩, ?_, ?_⟩
  · change (ChartScales.slotLength r0 profile.data.h (BaseChartJets.cellBand L) / 1) / 6 ≤ x.2.2
    simpa only [div_eq_mul_inv, inv_one, mul_one, one_mul, mul_comm] using (lt_div_iff₀ hL).mp hlow
        |>.le
  · have ht := ((div_lt_iff₀ hL).mp hhigh).le
    change x.2.2 ≤ 5 * (ChartScales.slotLength r0 profile.data.h (BaseChartJets.cellBand L) / 1) / 6
    simpa only [div_eq_mul_inv, inv_one, mul_one, one_mul, mul_comm, mul_assoc, mul_left_comm]
        using ht

include hr0 in
theorem actualMask_tsupport (L : PrimaryGeometryAssembly.Index W a.N) :
    tsupport (ActualSignedGeometry.nativeCutoff H v a L) ⊆ actualSourceCore H v a L :=
  closure_minimal (actualMask_support H v a hr0 L) (actualSourceCore_closed H v a L)

include hr0 in
theorem actualMask_jet_support (L : PrimaryGeometryAssembly.Index W a.N) (m : ℕ) :
    tsupport (iteratedFDeriv ℝ m (ActualSignedGeometry.nativeCutoff H v a L)) ⊆ actualSourceCore H
        v a L :=
  (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) m).trans (actualMask_tsupport H v a hr0 L)

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

include hr0 in
/-- Clock transport of the full actual mask supplies the exact closed
source region used above. The spatial mask remains part of the source. -/
theorem actualMask_transported_support (L : PrimaryGeometryAssembly.Index W a.N)
    (χ : P →L[ℝ] PhaseCalculus.Slow) (g : Geometry) (k : Frequency) {c : ℝ} (hc : 0 < c) :
    support (fun x : P × Plane => ActualSignedGeometry.nativeCutoff H v a L
      (χ x.1, CopySolveCompatibility.nativeTimeMap 0 c (g.coordinates k x.2))) ⊆
      sourceRegion (χ ⁻¹' actualSlowCore H v a L) g r0
        (ChartScales.slotLength r0 profile.data.h (BaseChartJets.cellBand L)) c := by
  intro x hx
  have hs := actualMask_support H v a hr0 L hx
  exact ⟨hs.1, mem_iUnion.mpr ⟨k, (mem_sourceCell_clock hc _).mpr hs.2⟩⟩

include hr0 in
theorem actualMask_transported_tsupport (L : PrimaryGeometryAssembly.Index W a.N)
    (χ : P →L[ℝ] PhaseCalculus.Slow) (g : Geometry) (k : Frequency) {c : ℝ} (hc : 0 < c) :
    tsupport (fun x : P × Plane => ActualSignedGeometry.nativeCutoff H v a L
      (χ x.1, CopySolveCompatibility.nativeTimeMap 0 c (g.coordinates k x.2))) ⊆
      sourceRegion (χ ⁻¹' actualSlowCore H v a L) g r0
        (ChartScales.slotLength r0 profile.data.h (BaseChartJets.cellBand L)) c :=
  closure_minimal (actualMask_transported_support H v a hr0 L χ g k hc)
    (sourceRegion_closed ((actualSlowCore_closed H v a L).preimage χ.continuous) _ _ _ _)

include hr0 in
theorem actualMask_transported_jet_support (L : PrimaryGeometryAssembly.Index W a.N)
    (χ : P →L[ℝ] PhaseCalculus.Slow) (g : Geometry) (k : Frequency) {c : ℝ} (hc : 0 < c) (m : ℕ) :
    tsupport (iteratedFDeriv ℝ m (fun x : P × Plane => ActualSignedGeometry.nativeCutoff H v a L
      (χ x.1, CopySolveCompatibility.nativeTimeMap 0 c (g.coordinates k x.2)))) ⊆
      sourceRegion (χ ⁻¹' actualSlowCore H v a L) g r0
        (ChartScales.slotLength r0 profile.data.h (BaseChartJets.cellBand L)) c :=
  (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) m).trans
    (actualMask_transported_tsupport H v a hr0 L χ g k hc)

end ActualParametersAndMasks

/-! ## A weighted companion for physical edge estimates -/

section WeightedGaussian

open LocalizedWaveBounds GaussianTailFlat

variable {X E I Label : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Only the dyadic exponent is absorbed. The flat edge weight is retained
for the subsequent physical extension estimate. -/
theorem gaussian_epsilon_shift (s : StripData X) (scales : BandScaleControl s)
    {c : ℝ} (hc : 0 < c) (α β : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ n,
      s.epsilon n ^ α * Real.exp (-c * ChartScales.S n) ≤ B * s.epsilon n ^ β := by
  obtain ⟨B, hB, hb⟩ := gaussian_beats_Q_power hc 0 (scales.power * (β - α))
  refine ⟨B, hB, fun n => ?_⟩
  have hQ := ChartScales.Q_pos n
  have hg : Real.exp (-c * ChartScales.S n) ≤ B * ChartScales.Q n ^ (scales.power * (β - α)) := by
    simpa only [pow_zero, one_mul] using hb n
  rw [scales.epsilon_eq, ← Real.rpow_mul hQ.le, ← Real.rpow_mul hQ.le]
  calc
    _ ≤ ChartScales.Q n ^ (scales.power * α) *
        (B * ChartScales.Q n ^ (scales.power * (β - α))) :=
      mul_le_mul_of_nonneg_left hg (Real.rpow_pos_of_pos hQ _).le
    _ = B * (ChartScales.Q n ^ (scales.power * α) *
        ChartScales.Q n ^ (scales.power * (β - α))) := by ring
    _ = _ := by rw [← Real.rpow_add hQ]; congr 2; ring

/-- The Gaussian gain preserves `sqrt(zeta)` exactly. Unlike the
unweighted absorption theorem, this estimate retains its original
polynomial inverse-edge degree; the positive edge weight remains
available to absorb that degree in physical coordinates. -/
theorem indexed_gaussian_weighted_all_gains {s : StripData X} {K : ℕ → I → Set X}
    {W : ℕ → I → X → ℝ} {α c : ℝ} {f : ℕ → I → X → E}
    (hf : LocalWave s K W α f) (scales : BandScaleControl s)
    (θ : ℕ → I → X → ℝ) (L : ℕ → I → ℝ) (hL : ∀ n i, 0 < L n i)
    (ell : ℝ) (hell : 0 < ell) (hLell : ∀ n i, ell * ChartScales.S n ≤ L n i) (hc : 0 < c)
    (hW : ∀ n i x, x ∈ s.domain → x ∈ K n i →
      W n i x ≤ Real.exp (-c * (θ n i x - 1 / 2) ^ 2 * L n i))
    (hzero : ∀ n i x, x ∈ s.domain → x ∈ K n i →
      |θ n i x - 1 / 2| < 1 / 5 → f n i =ᶠ[𝓝 x] fun _ => 0)
    (β : ℝ) : LocalClass s K (fun _ _ x => Real.sqrt (s.zeta x)) β f := by
  refine ⟨fun _ _ _ _ => Real.sqrt_nonneg _, hf.smooth, ?_⟩
  intro m
  obtain ⟨A, hA, p, hb⟩ := hf.bounds m
  obtain ⟨B, hB, hshift⟩ := gaussian_epsilon_shift s scales
    (by positivity : 0 < c * ell / 25) α β
  refine ⟨A * B, mul_nonneg hA hB.le, p, ?_⟩
  intro n i x hx hi j hj
  by_cases hm : |θ n i x - 1 / 2| < 1 / 5
  · rw [jets_eq_of_germ (hzero n i x hx hi hm) j]
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using
      majorant_nonneg s (fun _ x => Real.sqrt (s.zeta x)) β (mul_nonneg hA hB.le) p n x
        (Real.sqrt_nonneg _)
  have htail : 1 / 5 ≤ |θ n i x - 1 / 2| := le_of_not_gt hm
  have hsq : (1 / 25 : ℝ) ≤ (θ n i x - 1 / 2) ^ 2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 5) htail 2
    norm_num [sq_abs] at hh ⊢
    exact hh
  have hPg : W n i x ≤ Real.exp (-(c * ell / 25) * ChartScales.S n) := by
    apply (hW n i x hx hi).trans
    apply (Real.exp_le_exp.2 ?_).trans (gaussian_length_comparison hc.le (hLell n i))
    nlinarith [mul_le_mul_of_nonneg_left hsq (mul_nonneg hc.le (hL n i).le)]
  have hweight : s.epsilon n ^ α * W n i x ≤ B * s.epsilon n ^ β :=
    (mul_le_mul_of_nonneg_left hPg (Real.rpow_pos_of_pos (s.epsilon_pos n) α).le).trans (hshift n)
  calc
    _ ≤ majorant s (fun n x => Real.sqrt (s.zeta x) * W n i x) α A p n x := hb n i x hx hi j hj
    _ = (A * s.growth n x ^ p * Real.sqrt (s.zeta x)) * (s.epsilon n ^ α * W n i x) := by
      unfold majorant; ring
    _ ≤ (A * s.growth n x ^ p * Real.sqrt (s.zeta x)) * (B * s.epsilon n ^ β) :=
      mul_le_mul_of_nonneg_left hweight
        (mul_nonneg (mul_nonneg hA (pow_nonneg (s.growth_nonneg n x) p)) (Real.sqrt_nonneg _))
    _ = majorant s (fun _ x => Real.sqrt (s.zeta x)) β (A * B) p n x := by
      unfold majorant; ring

/-- Weighted counterpart of the frozen LGB gluing theorem. The source
complement retains the same edge weight and still occurs exactly once. -/
theorem uniform_globalGaussian_weighted_from_supported_native
    (a : Label → CopyData X I) (K : Label → Cells X I)
    (hs : ∀ l n i, support ((a l).cutoff n i) ⊆ (K l).carrier n i)
    {s : StripData X} (d : LinearWaveBounds.GraphDirections X) (C : Label → ℕ → I → Set X)
    {W : Label → ℕ → X → ℝ} {α c : ℝ}
    (hWnonneg : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (hψ : UniformLocalJets s (fun _ _ _ => 1) 0 C (fun l => (a l).cutoff))
    (hfast : BandBound s 0 d.fastScale)
    (hu : UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) α C
      (fun l => (a l).amplitude))
    (hf : UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) α C
      (fun l n _ => (a l).source n))
    (scales : BandScaleControl s)
    (θ : Label → ℕ → I → X → ℝ) (length : Label → ℕ → ℝ)
    (hL : ∀ l n, 0 < length l n) (ell : ℝ) (hell : 0 < ell)
    (hLell : ∀ l n, ell * ChartScales.S n ≤ length l n) (hc : 0 < c)
    (hW : ∀ l n i x, x ∈ s.domain → x ∈ C l n i →
      W l n x ≤ Real.exp (-c * (θ l n i x - 1 / 2) ^ 2 * length l n))
    (hcentral : ∀ l n i x, x ∈ s.domain → x ∈ C l n i → |θ l n i x - 1 / 2| < 1 / 5 →
      ((a l).cutoff n i =ᶠ[𝓝 x] fun _ => 1) ∨
        (((a l).amplitude n i =ᶠ[𝓝 x] fun _ => 0) ∧ ((a l).source n =ᶠ[𝓝 x] fun _ => 0)))
    (houtside : ∀ l n i x, x ∈ s.domain → x ∈ (K l).carrier n i → x ∉ C l n i →
      (((a l).cutoff n i =ᶠ[𝓝 x] fun _ => 0) ∧ ((a l).source n =ᶠ[𝓝 x] fun _ => 0)) ∨
        (((a l).amplitude n i =ᶠ[𝓝 x] fun _ => 0) ∧ ((a l).source n =ᶠ[𝓝 x] fun _ => 0)))
    (β : ℝ)
    (hcomplement : LocalizedGaussianBounds.UniformComplementJets s
      (fun _ _ x => Real.sqrt (s.zeta x)) β (fun l => (K l).carrier) (fun l => (a l).source)) :
    LabelSumBounds.UniformClass s (fun _ _ x => Real.sqrt (s.zeta x)) β
      (fun l => (a l).globalGaussian d) := by
  have hw l n x hx := mul_nonneg (Real.sqrt_nonneg (s.zeta x)) (hWnonneg l n x hx)
  have he : LocalWave s (fun n (li : Label × I) => C li.1 n li.2)
      (fun n li x => W li.1 n x) α (fun n li => (a li.1).localGaussian d n li.2) :=
    LocalizedGaussianBounds.indexedCutoffError_wave_class d
      (LocalClass.of_uniformLocalJets (fun _ _ _ _ => zero_le_one) hψ) hfast
      (LocalClass.of_uniformLocalJets hw hu) (LocalClass.of_uniformLocalJets hw hf)
  have hflat := indexed_gaussian_weighted_all_gains he scales
    (fun n li => θ li.1 n li.2) (fun n li => length li.1 n)
    (fun n li => hL li.1 n) ell hell (fun n li => hLell li.1 n) hc
    (fun n li x hx hi => hW li.1 n li.2 x hx hi)
    (fun n li x hx hi hm => by
      rcases hcentral li.1 n li.2 x hx hi hm with ho | ⟨hu,hf⟩
      · exact (a li.1).localGaussian_zero_of_cutoff_one d ho
      · exact (a li.1).localGaussian_zero_of_fields d hu hf) β
  have hlarge : LocalClass s (fun n (li : Label × I) => (K li.1).carrier n li.2)
      (fun _ _ x => Real.sqrt (s.zeta x)) β (fun n li => (a li.1).localGaussian d n li.2) := by
    apply hflat.enlarge
    intro n li x hx hi
    by_cases hh : x ∈ C li.1 n li.2
    · exact Or.inl hh
    · exact Or.inr (LocalizedGaussianBounds.localGaussian_zero_of_inactive (a li.1) d
        (houtside li.1 n li.2 x hx hi hh))
  exact LocalizedGaussianBounds.uniform_globalGaussian_class_with_complement a K hs d
    (fun _ _ _ _ => Real.sqrt_nonneg _) hlarge.to_uniformLocalJets hcomplement

end WeightedGaussian

section ActualWeighted

variable {Label P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : PhaseJetBounds.Domain (Label × ℕ) PhaseCalculus.Slow}
  (F : PhaseConstruction D) (clock : ActualSignedControl.PositiveScale Label)
  (reference : Label → ℕ → Geometry) (gap : Label → ℕ → ℕ)
  (r : Label → ℕ → ℝ) (hr : ∀ l n, 0 < r l n)

variable [Countable Label] [Nonempty Label]
  (base : Label → LinearWaveBounds.WaveCoefficients ((P × ℝ) × Plane))
  (tangent : Label → ℕ → TangentData (P × ℝ) ProblemStatement.Space)
  (ctx : CorrectionState.Context (P × Plane)) (u : CorrectionState.State (P × Plane))
  (b : Label → CorrectionState.HarmonicBlock (P × Plane))
  (G A : Label → HarmonicResidual.BlockCoefficients (P × Plane)) (j : ℤ)
  (s : StripData P) (χ : P →L[ℝ] PhaseCalculus.Slow)
  (φ : (Label × ℕ) → PhaseCalculus.Slow →L[ℝ] PhaseCalculus.Slow)

/-- The actual Gaussian error retains precisely the flat `sqrt(zeta)`
weight at every decay exponent. This companion is suitable for the
physical local-source bounds; no completed edge extension is assumed. -/
theorem globalGaussian_weighted_all_gains
    (frame : Label → ℕ → PrimaryODE.FrameData ((P × ℝ) × ℝ))
    {α lam0 u0 ell : ℝ} (hlam0 : 0 < lam0) (hu0 : 0 < u0) (hell : 0 < ell)
    (hlam : ∀ l n, lam0 ≤ F.lam (l, n)) (hu : ∀ l n, F.u (l, n) = u0)
    (hL : ∀ l n, ell * ChartScales.S n ≤ F.L (l, n))
    (hinj : ∀ l n, InjOn TorusAverages.quotientPoint
      ((fun z => (reference l n).center + (reference l n).basis z) ''
        (referenceWindow (r l n) (F.L (l, n)) (hr l n) (F.L_pos (l, n))).outer))
    (S : Label → ℕ → Set P) (hS : ∀ l n, IsClosed (S l n))
    (hsupport : ∀ l, HarmonicSourceSupport.InputSupportOn (s.domain ×ˢ univ)
      (sourceRegions F clock reference gap r S l) (b l) (G l) (A l))
    (hinside : ∀ l n p, p ∈ s.domain → p ∈ S l n → φ (l, n) (χ p) ∈ D.carrier (l, n))
    (hreal : ParticularCopyBounds.UniformModalControl
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip s)) α frame
      (fun l n => realData (tangent l n) (ParticularWaveAssembly.sourceFamily ctx u (b l) (G l) (A
          l) j n))
      j (ScaledActualParticularControl.geometry reference gap clock)
      (ScaledActualParticularControl.length F clock) (ScaledActualParticularControl.envelope F
          clock)
      (analyticPatches F clock reference gap r s χ φ))
    (himag : ParticularCopyBounds.UniformModalControl
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip s)) α frame
      (fun l n => imagData (tangent l n) (ParticularWaveAssembly.sourceFamily ctx u (b l) (G l) (A
          l) j n))
      j (ScaledActualParticularControl.geometry reference gap clock)
      (ScaledActualParticularControl.length F clock) (ScaledActualParticularControl.envelope F
          clock)
      (analyticPatches F clock reference gap r s χ φ))
    (hsource : UniformLocalJets
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip s))
      (fun l n x => Real.sqrt (s.zeta x.1.1) * fieldEnvelope F clock reference gap r l n x) α
      (analyticPatches F clock reference gap r s χ φ)
      (fun l n _ => ParticularWaveAssembly.sourceFamily ctx u (b l) (G l) (A l) j n))
    (dirs : LinearWaveBounds.GraphDirections ((P × ℝ) × Plane))
    (hfast : BandBound (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip s)) 0
        dirs.fastScale)
    (scales : GaussianTailFlat.BandScaleControl (CommonCoverClass.sourceStrip
        (ActualParticularControl.angleStrip s)))
    (β : ℝ) :
    LabelSumBounds.UniformClass (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip
        s))
      (fun _ _ x => Real.sqrt (s.zeta x.1.1)) β
      (fun l => (data F clock reference gap r hr base tangent ctx u b G A j l).globalGaussian dirs)
          := by
  have hw l n x (_ : x ∈ (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip
      s)).domain) :=
    fieldEnvelope_nonneg F clock reference gap r l n x
  have he l n k x (_ : x ∈ (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip
      s)).domain)
      (hx : x ∈ analyticPatches F clock reference gap r s χ φ l n k) :=
    (fieldEnvelope_eq F clock reference gap r hr s χ φ hinj hx).ge
  have hamp := complex_amplitude_uniform_jets tangent
    (fun l => ParticularWaveAssembly.sourceFamily ctx u (b l) (G l) (A l) j)
    (ScaledActualParticularControl.geometry reference gap clock)
    (ScaledActualParticularControl.length F clock) (ScaledActualParticularControl.length_pos F
        clock)
    (ScaledActualParticularControl.envelope F clock) (fieldEnvelope F clock reference gap r)
    frame j (analyticPatches F clock reference gap r s χ φ) hreal himag hw he
  have hcomp : LocalizedGaussianBounds.UniformComplementJets
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip s))
      (fun _ _ x => Real.sqrt (s.zeta x.1.1)) β
      (fun l => (cells F clock reference gap r hr hinj l).carrier)
      (fun l => (data F clock reference gap r hr base tangent ctx u b G A j l).source) := by
    apply LocalizedGaussianBounds.UniformComplementJets.of_zero_germs
    intro l n x hx hn
    apply data_source_zero_germ F clock reference gap r hr base tangent ctx u b G A j
      s S hS hsupport l n hx
    intro hreg
    obtain ⟨k,hk⟩ := mem_iUnion.mp hreg.2
    exact hn k (sourceCell_subset_outer (hr l n) (F.L_pos (l,n)) (clock.value_pos l n) hk)
  apply uniform_globalGaussian_weighted_from_supported_native
    (data F clock reference gap r hr base tangent ctx u b G A j)
    (cells F clock reference gap r hr hinj)
    (data_cutoff_support F clock reference gap r hr base tangent ctx u b G A j)
    dirs (analyticPatches F clock reference gap r s χ φ) hw
    (data_cutoff_jets F clock reference gap r hr base tangent ctx u b G A j s χ φ hu0 hu
      ⟨hreal.boundConstant, hreal.constant_ge_one, hreal.coordinatePower, hreal.coordinate_bound⟩)
    hfast hamp hsource scales
    (fun l n k x => theta F clock l n
      ((ScaledActualParticularControl.geometry reference gap clock l n).coordinates k x.2).2)
    (ScaledActualParticularControl.length F clock) (ScaledActualParticularControl.length_pos F
        clock)
    (ell / clock.upper) (div_pos hell (zero_lt_one.trans_le clock.upper_one))
    (length_uniform_lower F clock hL)
    (mul_pos (gaussianRate_pos hlam0 hu0) clock.lower_pos)
    ?_ ?_ ?_ β
    hcomp
  · intro l n k x hx hc
    rw [fieldEnvelope_eq F clock reference gap r hr s χ φ hinj hc]
    exact envelope_uniform_bound F clock hlam0 hu0 hlam hu l n ⟨hc.1.2.2.1.le, hc.1.2.2.2.le⟩
  · intro l n k x hx hc hm
    exact Or.inl (data_central F clock reference gap r hr base tangent ctx u b G A j s χ φ l n k hc
        hm)
  · intro l n k x hx hk hn
    exact data_outside F clock reference gap r hr base tangent ctx u b G A j s S hS hsupport
      χ φ hinside hinj l n k hx hk hn

end ActualWeighted

end NavierStokes.ActualGaussianCoverage
