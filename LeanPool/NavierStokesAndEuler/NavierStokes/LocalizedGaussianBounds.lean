/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicSourceSupport
public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalizedWaveBounds

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
