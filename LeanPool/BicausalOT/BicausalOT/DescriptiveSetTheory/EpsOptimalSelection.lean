/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
  ε-Optimal Analytically Measurable Selection

  **Bertsekas–Shreve, Proposition 7.50 (ε-optimal half), in ℝ≥0∞.**
  For an analytic set Γ ⊆ H × E with nonempty fibers over a Polish space
  H into a Polish space E, and a lower semianalytic F : H × E → ℝ≥0∞,
  every ε > 0 admits a σ(Σ¹₁)-measurable selector φ with (h, φ h) ∈ Γ and
  F (h, φ h) ≤ inf-fiber F h + ε for every h.

  Design (BLUEPRINT.md §4, docs/design_phase4.md): Borel/analytic
  ε-optimal selection genuinely fails (Blackwell), so the σ(Σ¹₁) budget
  is spent on a countable *band partition* of the domain steered by the
  VALUE of the fiber infimum g — both sublevels (analytic) and
  superlevels (co-analytic) of the lower semianalytic g lie in σ(Σ¹₁) —
  while Jankov–von Neumann uniformization is only ever applied to the
  analytic sets Γ ∩ {F < q} at constant thresholds q, never to a set
  comparing F with g. The countably many selectors are glued with
  Mathlib's `Measurable.find` instantiated at `analyticMeasurableSpace`.
-/
module

public import LeanPool.BicausalOT.BicausalOT.DescriptiveSetTheory.Tree
public import LeanPool.BicausalOT.BicausalOT.DescriptiveSetTheory.KernelIntegral
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions


/-! ## Fiber infimum approximation -/

@[expose] public section

open MeasureTheory Set ENNReal

noncomputable section

variable {H E : Type*} [TopologicalSpace H] [TopologicalSpace E]



omit [TopologicalSpace H] [TopologicalSpace E] in
/-- Any value strictly above the fiber infimum is beaten by some element
    of the fiber. -/
theorem iInf_fiber_lt {Γ : Set (H × E)} {F : H × E → ℝ≥0∞} {h : H}
    {q : ℝ≥0∞} (hlt : (⨅ (e : E) (_ : (h, e) ∈ Γ), F (h, e)) < q) :
    ∃ e : E, (h, e) ∈ Γ ∧ F (h, e) < q := by
  rw [iInf_lt_iff] at hlt
  obtain ⟨e, he⟩ := hlt
  rw [iInf_lt_iff] at he
  obtain ⟨hm, hfc⟩ := he
  exact ⟨e, hm, hfc⟩

/-! ## The selector family: fallback and level selectors -/

/-- A σ(Σ¹₁)-measurable everywhere-feasible selector exists as soon as the
    graph is analytic, nonempty, and has nonempty fibers
    (Jankov–von Neumann). -/
theorem exists_fallback_selector [PolishSpace H]
    {Γ : Set (H × E)} (hΓ : AnalyticSet Γ) (hΓne : Γ.Nonempty)
    (hfib : ∀ h : H, ∃ e : E, (h, e) ∈ Γ) :
    ∃ φ : H → E, AnalyticallyMeasurable φ ∧ ∀ h, (h, φ h) ∈ Γ := by
  obtain ⟨φ, hφ, hsel⟩ := jankov_von_neumann Γ hΓ hΓne
  refine ⟨φ, hφ, fun h => ?_⟩
  obtain ⟨e, he⟩ := hfib h
  exact hsel h ⟨(h, e), he, rfl⟩

/-- Level selector at a constant threshold `q`: a σ(Σ¹₁)-measurable map
    that, wherever the fiber meets the strict sublevel set `{F < q}`,
    selects a feasible element below `q`; elsewhere it falls back to the
    given selector `φ'`. The selection set `Γ ∩ {F < q}` is analytic, so
    Jankov–von Neumann applies — this is the only place selection ever
    happens, and the threshold is constant by design. -/
theorem exists_level_selector [PolishSpace H] [PolishSpace E]
    {Γ : Set (H × E)} {F : H × E → ℝ≥0∞}
    (hΓ : AnalyticSet Γ) (hF : IsLowerSemianalytic (X := H × E) F)
    {φ' : H → E} (hφ' : AnalyticallyMeasurable φ') (q : ℝ≥0∞) :
    ∃ χ : H → E, AnalyticallyMeasurable χ ∧
      ∀ h : H, (∃ e, (h, e) ∈ Γ ∧ F (h, e) < q) →
        (h, χ h) ∈ Γ ∧ F (h, χ h) < q := by
  have hA : AnalyticSet (Γ ∩ {p | F p < q}) := hΓ.inter' (hF q)
  by_cases hAne : (Γ ∩ {p | F p < q}).Nonempty
  · obtain ⟨χ, hχ, hsel⟩ := jankov_von_neumann _ hA hAne
    refine ⟨χ, hχ, fun h ⟨e, heΓ, heF⟩ => ?_⟩
    exact hsel h ⟨(h, e), ⟨heΓ, heF⟩, rfl⟩
  · exact ⟨φ', hφ', fun h ⟨e, heΓ, heF⟩ => absurd ⟨(h, e), heΓ, heF⟩ hAne⟩

/-! ## The glue lemma: countable σ(Σ¹₁)-piecewise gluing -/

/-- **Countable σ(Σ¹₁)-piecewise gluing.** Steering among countably many
    analytically measurable maps through the least index satisfying
    σ(Σ¹₁)-measurable predicates yields an analytically measurable map:
    Mathlib's `Measurable.find` instantiated at
    `analyticMeasurableSpace`. -/
theorem AnalyticallyMeasurable.find
    {ψ : ℕ → H → E} (hψ : ∀ m, AnalyticallyMeasurable (ψ m))
    {p : ℕ → H → Prop} [∀ m, DecidablePred (p m)]
    (hp : ∀ m, @MeasurableSet H (analyticMeasurableSpace H) {h | p m h})
    (hex : ∀ h, ∃ m, p m h) :
    AnalyticallyMeasurable (fun h => ψ (Nat.find (hex h)) h) := by
  let : MeasurableSpace H := analyticMeasurableSpace H
  let : MeasurableSpace E := borel E
  exact Measurable.find hψ hp hex

/-! ## Band bookkeeping in ℝ≥0∞ -/

namespace EpsOptimalSelection

/-- The band predicate for the `ε'`-grid on `ℝ≥0∞`: index `0` is the
    infinite band `{v = ∞}`, index `m + 1` the sublevel band
    `{v < (m + 1) · ε'}`. Steered through `Nat.find`, the effective bands
    are `{m·ε' ≤ v < (m + 1)·ε'}` plus the infinite band. -/
def bandPred (ε' : ℝ≥0∞) : ℕ → ℝ≥0∞ → Prop
  | 0, v => v = ∞
  | m + 1, v => v < ((m + 1 : ℕ) : ℝ≥0∞) * ε'

/-- Every value lies in some band (Archimedean property of the grid). -/
theorem exists_band {ε' : ℝ≥0∞} (hε'0 : 0 < ε') (hε'top : ε' ≠ ∞)
    (v : ℝ≥0∞) : ∃ m : ℕ, bandPred ε' m v := by
  by_cases hv : v = ∞
  · exact ⟨0, hv⟩
  · obtain ⟨n, hn⟩ :=
      ENNReal.exists_nat_gt (ENNReal.div_lt_top hv hε'0.ne').ne
    have hvn : v < (n : ℝ≥0∞) * ε' :=
      (ENNReal.div_lt_iff (Or.inl hε'0.ne') (Or.inl hε'top)).mp hn
    rcases n with _ | m
    · exact absurd hvn (by simp)
    · exact ⟨m + 1, hvn⟩

/-- Failure of all band predicates below `m + 1` bounds the value from
    below by the `m`-th band's lower edge. -/
theorem band_lower_bound {ε' v : ℝ≥0∞} {m : ℕ}
    (hmin : ∀ j, j < m + 1 → ¬ bandPred ε' j v) :
    ((m : ℕ) : ℝ≥0∞) * ε' ≤ v := by
  cases m with
  | zero => simp
  | succ j => exact not_lt.mp (hmin (j + 1) (by omega))

end EpsOptimalSelection

/-! ## The main theorem: BS Proposition 7.50, ε-optimal half -/

open EpsOptimalSelection in
open scoped Classical in
/-- **ε-optimal analytically measurable selection** (Bertsekas–Shreve,
    Proposition 7.50 analogue, ε-optimal half, in `ℝ≥0∞`). If `Γ ⊆ H × E`
    is analytic with nonempty fibers (H, E Polish) and `F` is lower
    semianalytic on the product, then for every `ε > 0` there is a
    σ(Σ¹₁)-measurable selector that is everywhere feasible and everywhere
    ε-optimal for the fiber infimum.

    Proof: normalize `ε' := min ε 1`; partition the domain into the bands
    `{g = ∞}` and `{m·ε' ≤ g < (m+1)·ε'}` of the fiber infimum `g` (lower
    semianalytic by BS 7.47, so all bands are σ(Σ¹₁)); on band `m` select
    from the analytic set `Γ ∩ {F < (m+1)·ε'}` via Jankov–von Neumann; on
    the infinite band any feasible selection is ε-optimal; glue with
    `AnalyticallyMeasurable.find`. -/
theorem exists_eps_optimal_selector [PolishSpace H] [PolishSpace E]
    {Γ : Set (H × E)} {F : H × E → ℝ≥0∞}
    (hΓ : AnalyticSet Γ) (hF : IsLowerSemianalytic (X := H × E) F)
    (hfib : ∀ h : H, ∃ e : E, (h, e) ∈ Γ)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ φ : H → E, AnalyticallyMeasurable φ ∧ (∀ h, (h, φ h) ∈ Γ) ∧
      ∀ h, F (h, φ h) ≤ (⨅ (e : E) (_ : (h, e) ∈ Γ), F (h, e)) + ε := by
  rcases isEmpty_or_nonempty H with hH | hH
  · -- degenerate domain: everything is vacuous
    have := hH
    let : MeasurableSpace H := analyticMeasurableSpace H
    let : MeasurableSpace E := borel E
    exact ⟨fun h => isEmptyElim h, measurable_of_empty _,
      fun h => isEmptyElim h, fun h => isEmptyElim h⟩
  · obtain ⟨h₀⟩ := hH
    have hΓne : Γ.Nonempty := ⟨(h₀, (hfib h₀).choose), (hfib h₀).choose_spec⟩
    -- Step 1: normalized tolerance ε' = min ε 1 (positive, finite, ≤ ε)
    set ε' : ℝ≥0∞ := min ε 1 with hε'def
    have hε'0 : 0 < ε' := lt_min hε zero_lt_one
    have hε'top : ε' ≠ ∞ := ((min_le_right ε 1).trans_lt one_lt_top).ne
    have hε'ε : ε' ≤ ε := min_le_left ε 1
    -- Step 2: the fiber infimum is lower semianalytic (BS 7.47)
    set g : H → ℝ≥0∞ := fun h => ⨅ (e : E) (_ : (h, e) ∈ Γ), F (h, e)
      with hgdef
    have hg : IsLowerSemianalytic g := IsLowerSemianalytic.iInf_fiber hΓ hF
    -- Step 3: the selector family — fallback plus one selector per level
    obtain ⟨φ₀, hφ₀meas, hφ₀Γ⟩ := exists_fallback_selector hΓ hΓne hfib
    have hlevel : ∀ m : ℕ, ∃ χ : H → E, AnalyticallyMeasurable χ ∧
        ∀ h : H, (∃ e, (h, e) ∈ Γ ∧ F (h, e) < (m : ℝ≥0∞) * ε') →
          (h, χ h) ∈ Γ ∧ F (h, χ h) < (m : ℝ≥0∞) * ε' :=
      fun m => exists_level_selector hΓ hF hφ₀meas _
    choose χ hχmeas hχsel using hlevel
    set ψ : ℕ → H → E := fun m => match m with
      | 0 => φ₀
      | m + 1 => χ (m + 1) with hψdef
    have hψmeas : ∀ m, AnalyticallyMeasurable (ψ m) := by
      intro m
      cases m with
      | zero => exact hφ₀meas
      | succ m => exact hχmeas (m + 1)
    -- Step 4: the band predicate is σ(Σ¹₁)-measurable
    have hp : ∀ m, @MeasurableSet H (analyticMeasurableSpace H)
        {h | bandPred ε' m (g h)} := by
      intro m
      cases m with
      | zero =>
        have hset : {h : H | bandPred ε' 0 (g h)} = {h : H | g h < ⊤}ᶜ := by
          ext h
          change g h = ∞ ↔ ¬ g h < ⊤
          simp [lt_top_iff_ne_top]
        rw [hset]
        exact (hg ⊤).compl_mem_analyticMeasurableSpace
      | succ m =>
        have hset : {h : H | bandPred ε' (m + 1) (g h)}
            = {h : H | g h < ((m + 1 : ℕ) : ℝ≥0∞) * ε'} := rfl
        rw [hset]
        exact (hg _).mem_analyticMeasurableSpace
    have hex : ∀ h, ∃ m, bandPred ε' m (g h) := fun h =>
      exists_band hε'0 hε'top (g h)
    -- Steps 5–6: glue with Nat.find; correctness by cases on the band
    have hcorrect : ∀ h : H, (h, ψ (Nat.find (hex h)) h) ∈ Γ ∧
        F (h, ψ (Nat.find (hex h)) h) ≤ g h + ε' := by
      intro h
      rcases hfind : Nat.find (hex h) with _ | m
      · -- the infinite band: any feasible selection is trivially optimal
        have hspec : bandPred ε' 0 (g h) := by
          have hs := Nat.find_spec (hex h)
          rwa [hfind] at hs
        have hginf : g h = ∞ := hspec
        exact ⟨hφ₀Γ h, by simp [hginf]⟩
      · -- band m: select below the upper edge, bound below by the lower edge
        have hspec : bandPred ε' (m + 1) (g h) := by
          have hs := Nat.find_spec (hex h)
          rwa [hfind] at hs
        have hlt : g h < ((m + 1 : ℕ) : ℝ≥0∞) * ε' := hspec
        obtain ⟨e, heΓ, heF⟩ := iInf_fiber_lt hlt
        have hsel := hχsel (m + 1) h ⟨e, heΓ, heF⟩
        have hlow : ((m : ℕ) : ℝ≥0∞) * ε' ≤ g h :=
          band_lower_bound fun j hj =>
            Nat.find_min (hex h) (by rw [hfind]; exact hj)
        refine ⟨hsel.1, ?_⟩
        calc F (h, χ (m + 1) h)
            ≤ ((m + 1 : ℕ) : ℝ≥0∞) * ε' := le_of_lt hsel.2
          _ = ((m : ℕ) : ℝ≥0∞) * ε' + ε' := by push_cast; ring
          _ ≤ g h + ε' := add_le_add hlow le_rfl
    exact ⟨fun h => ψ (Nat.find (hex h)) h,
      AnalyticallyMeasurable.find hψmeas hp hex,
      fun h => (hcorrect h).1,
      fun h => le_trans (hcorrect h).2 (add_le_add le_rfl hε'ε)⟩

end
