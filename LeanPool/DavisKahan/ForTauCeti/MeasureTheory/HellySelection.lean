/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
Adapted from: Spectra (https://github.com/adambornemann-glitch/Spectra),
  `Spectra/Herglotz/Stieltjes/Hellys.lean` at commit
  `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`,
  Copyright (c) 2026 Spectra Formalization Project, `Authors: Adam Bornemann`,
  Apache 2.0.  Modified: see `## Provenance` (Apache 2.0 §4(b)); the donor's
  copyright and authorship notices are retained here and below (§4(c)).
-/
module

public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.Data.Rat.Denumerable
public import Mathlib.Topology.Sequences

/-!
# Helly's selection theorem, and the measure it produces

Helly selection for uniformly bounded monotone functions on `ℝ`, and the
Stieltjes measure attached to a monotone limit.  Mathlib has `StieltjesFunction`
and its measure but not Helly selection, so this is an addition.

Used by the spectral-measure construction: the approximating spectral
distribution functions are monotone and uniformly bounded, and Helly extracts the
convergent subsequence whose limit carries the spectral measure.

## Provenance

* **Original repository:** Spectra, commit `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`.
* **Original module:** `Spectra/Herglotz/Stieltjes/Hellys.lean`, which imports
  **only Mathlib**.
* **Original authors / copyright / licence:** Copyright (c) 2026 Spectra
  Formalization Project; `Authors: Adam Bornemann`; Apache 2.0.
* **Extraction class:** *copied, then re-homed.*  Statements and proofs are
  Spectra's, essentially verbatim.
* **Semantic differences from the donor:** none; the namespace moves from
  `Spectra.Herglotz` to `TauCeti` and the file adopts Tau Ceti's module-system
  preamble.
-/

public section

namespace TauCeti

open Filter Topology

section HellySelection

/-- **Helly selection, unanchored.** Uniformly bounded, monotone `Fₙ` admit a
subsequence converging at every rational and at every continuity point of the
limit. No value is fixed at the origin.

`_hM` is logically redundant (it follows from `h_bnd 0 0`) and unused in the proof;
it is carried explicitly only for API symmetry with `helly_selection'`, whose `hM`
is genuinely load-bearing. -/
lemma helly_selection
    (F : ℕ → ℝ → ℝ) (M : ℝ) (_hM : 0 ≤ M)
    (h_mono : ∀ N, Monotone (F N))
    (h_bnd : ∀ N x, F N x ∈ Set.Icc (0 : ℝ) M) :
    ∃ (G : ℝ → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ Monotone G ∧
      (∀ x, G x ∈ Set.Icc (0 : ℝ) M) ∧
      (∀ q : ℚ, Tendsto (fun k => F (φ k) (q : ℝ)) atTop (𝓝 (G (q : ℝ)))) ∧
      (∀ x : ℝ, ContinuousAt G x →
        Tendsto (fun k => F (φ k) x) atTop (𝓝 (G x))) := by
  have hC : IsCompact (Set.univ.pi fun _ : ℚ => Set.Icc (0 : ℝ) M) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ n, (fun q : ℚ => F n (q : ℝ)) ∈ Set.univ.pi fun _ => Set.Icc (0:ℝ) M :=
    fun n q _ => h_bnd n (q : ℝ)
  obtain ⟨g, -, φ, hφ_mono, hφ_lim⟩ := hC.isSeqCompact hmem
  have h_rat_conv : ∀ q : ℚ, Tendsto (fun k => F (φ k) (q : ℝ)) atTop (𝓝 (g q)) :=
    fun q => (tendsto_pi_nhds.mp hφ_lim) q
  have hg_bnd : ∀ q : ℚ, g q ∈ Set.Icc (0 : ℝ) M := fun q =>
    ⟨ge_of_tendsto' (h_rat_conv q) fun k => (h_bnd (φ k) _).1,
     le_of_tendsto'  (h_rat_conv q) fun k => (h_bnd (φ k) _).2⟩
  have hg_mono : ∀ {q r : ℚ}, q ≤ r → g q ≤ g r := fun {q r} hqr =>
    le_of_tendsto_of_tendsto (h_rat_conv q) (h_rat_conv r)
      (Eventually.of_forall fun k => h_mono (φ k) (by exact_mod_cast hqr))
  set S : ℝ → Set ℝ := fun x => g '' {q : ℚ | x ≤ (q : ℝ)} with _hS
  have hS_ne  : ∀ x, (S x).Nonempty := fun x => by
    obtain ⟨q, hq⟩ := exists_rat_gt x; exact ⟨g q, q, hq.le, rfl⟩
  have hS_bdd : ∀ x, BddBelow (S x) := fun x =>
    ⟨0, by rintro _ ⟨q, _, rfl⟩; exact (hg_bnd q).1⟩
  set G : ℝ → ℝ := fun x => sInf (S x) with _hG
  have hG_rat : ∀ q : ℚ, G (q : ℝ) = g q := fun q =>
  le_antisymm (csInf_le (hS_bdd _) ⟨q, Set.mem_ofPred.mpr le_rfl, rfl⟩)
    (le_csInf (hS_ne _) (by rintro _ ⟨r, hr, rfl⟩; exact hg_mono (by exact_mod_cast hr)))
  have hG_mono : Monotone G := fun x y hxy =>
    le_csInf (hS_ne _) (by
      rintro _ ⟨r, hr, rfl⟩; exact csInf_le (hS_bdd _) ⟨r, le_trans hxy hr, rfl⟩)
  have hG_bnd : ∀ x, G x ∈ Set.Icc (0 : ℝ) M := fun x =>
    ⟨le_csInf (hS_ne _) (by rintro _ ⟨r, _, rfl⟩; exact (hg_bnd r).1),
     by obtain ⟨q, hq⟩ := exists_rat_gt x
        exact le_trans (csInf_le (hS_bdd _) ⟨q, hq.le, rfl⟩) (hg_bnd q).2⟩
  refine ⟨G, φ, hφ_mono, hG_mono, hG_bnd, fun q => by rw [hG_rat q]; exact h_rat_conv q, ?_⟩
  intro x hx
  refine tendsto_order.mpr ⟨fun c hc => ?_, fun c hc => ?_⟩
  · -- hc : c < G x.  Seat a rational a < x with c < g a, then sandwich from below.
    have hnhds : ∀ᶠ y in 𝓝 x, c < G y :=
      Filter.Tendsto.eventually hx (eventually_gt_nhds hc)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp hnhds
    obtain ⟨a, ha₁, ha₂⟩ := exists_rat_btwn (show x - δ < x by linarith)
    have hca : c < g a := by
      have h := hδ' (show dist (a : ℝ) x < δ by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
      rwa [hG_rat a] at h
    filter_upwards [Filter.Tendsto.eventually (h_rat_conv a) (eventually_gt_nhds hca)]
      with k hk
    exact lt_of_lt_of_le hk (h_mono (φ k) ha₂.le)
  · -- hc : G x < c.  Seat a rational b > x with g b < c, then sandwich from above.
    have hnhds : ∀ᶠ y in 𝓝 x, G y < c :=
      Filter.Tendsto.eventually hx (eventually_lt_nhds hc)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp hnhds
    obtain ⟨b, hb₁, hb₂⟩ := exists_rat_btwn (show x < x + δ by linarith)
    have hcb : g b < c := by
      have h := hδ' (show dist (b : ℝ) x < δ by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
      rwa [hG_rat b] at h
    filter_upwards [Filter.Tendsto.eventually (h_rat_conv b) (eventually_lt_nhds hcb)]
      with k hk
    exact lt_of_le_of_lt (h_mono (φ k) hb₁.le) hk

/-- **Helly's selection lemma** for distribution functions on `[0, 2π]`.
  Given a sequence of monotone functions `F_N : ℝ → ℝ` with
  `0 ≤ F_N(x) ≤ M` for all `N, x`, there exists a subsequence converging
  pointwise at all points of a countable dense set. -/
theorem helly_selection'
    (F : ℕ → ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (h_mono : ∀ N, Monotone (F N))
    (h_bnd : ∀ N x, F N x ∈ Set.Icc (0 : ℝ) M)
    (h_zero : ∀ N, F N 0 = 0) :
    ∃ (G : ℝ → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ Monotone G ∧ G 0 = 0 ∧
      (∀ x, G x ∈ Set.Icc (0 : ℝ) M) ∧
      (∀ q : ℚ, Tendsto (fun k => F (φ k) (q : ℝ)) atTop (𝓝 (G (q : ℝ)))) ∧
      (∀ x : ℝ, ContinuousAt G x →
        Tendsto (fun k => F (φ k) x) atTop (𝓝 (G x))) := by
  obtain ⟨G, φ, hφ, hGmono, hGbnd, hGrat, hGcont⟩ := helly_selection F M hM h_mono h_bnd
  refine ⟨G, φ, hφ, hGmono, ?_, hGbnd, hGrat, hGcont⟩
  have h0 := hGrat 0
  simp only [Rat.cast_zero, h_zero] at h0
  exact tendsto_nhds_unique h0 tendsto_const_nhds

open MeasureTheory in
/-- Given the Helly limit `G` (monotone, bounded), produce a
`StieltjesFunction` and its associated measure.

The key: `Monotone.stieltjesFunction` right-regularizes `G` and
packages it as a `StieltjesFunction`. Then `.measure` gives the
Borel measure. -/
noncomputable def hellyLimitMeasure (G : ℝ → ℝ) (h_mono : Monotone G) :
    Measure ℝ :=
  (h_mono.stieltjesFunction).measure

/-- The Stieltjes measure satisfies `μ(Ioc a b) = ofReal (G⁺(b) - G⁺(a))`, where
`G⁺ = h_mono.stieltjesFunction` is the right-continuous regularization of `G`.

At a continuity point `x` of `G`, `G⁺ x = G x`, so this recovers the familiar
`μ(Ioc a b) = G(b) - G(a)` whenever `a` and `b` are both continuity points of `G`. -/
lemma hellyLimitMeasure_Ioc (G : ℝ → ℝ) (h_mono : Monotone G)
    (a b : ℝ) :
    (hellyLimitMeasure G h_mono) (Set.Ioc a b) =
    ENNReal.ofReal (h_mono.stieltjesFunction b - h_mono.stieltjesFunction a) :=
  StieltjesFunction.measure_Ioc _ a b

end HellySelection

end TauCeti
