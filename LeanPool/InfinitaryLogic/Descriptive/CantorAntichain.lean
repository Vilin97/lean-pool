/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Topology.MetricSpace.CantorScheme

/-!
# Cantor schemes with antichain branches

General descriptive-set-theoretic infrastructure for extracting a continuous injection
`(ℕ → Bool) → α` whose distinct image points are pairwise inequivalent for an equivalence
relation `r`, from a Cantor scheme whose sibling pieces are cross-`r`-inequivalent.

This is the reusable "perfect antichain" extraction layer of Silver-type arguments, factored
out of `silver_core_closed` (`InfinitaryLogic/Conditional/SilverBurgess.lean`).

## Main results

- `CantorScheme.exists_antichain_map`: the completeness-free core. A `Bool`-scheme with
  vanishing diameter, nonempty branch intersections, and `r`-inequivalent siblings induces a
  continuous injection of Cantor space with pairwise `r`-inequivalent images. Branch-limit
  membership in the *actual* scheme sets is a hypothesis rather than being derived from
  closure-nesting: in the eventual Gandy–Harrington argument the scheme pieces are `Σ¹₁` (not
  closed) and branch limits are supplied by strong-Choquet fusion. No closedness, disjointness,
  or completeness is assumed; injectivity follows from the antichain property and reflexivity
  of `r`.
- `CantorScheme.exists_antichain_map_of_splitting`: the splitting-predicate builder. Given a
  "largeness" predicate `P` on closed subsets of a complete space, stable under splitting into
  two small-diameter cross-`r`-inequivalent pieces, this builds the scheme by recursion and
  discharges the branch-limit hypothesis via `ClosureAntitone.map_of_vanishingDiam`.
-/

universe u

open Set

namespace CantorScheme

/-- Membership in the domain of `inducedMap` is definitionally nonemptiness of the branch
intersection. -/
theorem mem_inducedMap_fst_iff {β α : Type*} {A : List β → Set α} {x : ℕ → β} :
    x ∈ (inducedMap A).1 ↔ (⋂ n, A (PiNat.res x n)).Nonempty :=
  Iff.rfl

/-- **Cantor scheme → perfect antichain (core extraction).** A `Bool`-scheme with vanishing
diameter, nonempty branch intersections, and `r`-inequivalent siblings induces a continuous
injection `f : (ℕ → Bool) → α` whose images lie along the scheme and are pairwise
`r`-inequivalent.

No completeness, closedness, or sibling-disjointness is assumed: injectivity follows from the
antichain property together with reflexivity of `r`. The branch-limit hypothesis `hlim` is
exactly totality of `inducedMap` (see `mem_inducedMap_fst_iff`); for schemes of closed sets in
a complete space it can be discharged by `ClosureAntitone.map_of_vanishingDiam` (see
`exists_antichain_map_of_splitting`), while a Gandy–Harrington fusion argument can supply it
for non-closed pieces. -/
theorem exists_antichain_map {α : Type u} [PseudoMetricSpace α]
    (r : Setoid α) {A : List Bool → Set α}
    (hlim : ∀ x : ℕ → Bool, (⋂ n, A (PiNat.res x n)).Nonempty)
    (hdiam : VanishingDiam A)
    (hcross : ∀ l : List Bool, ∀ x ∈ A (false :: l), ∀ y ∈ A (true :: l), ¬ r.r x y) :
    ∃ f : (ℕ → Bool) → α,
      Continuous f ∧ Function.Injective f ∧
      (∀ a : ℕ → Bool, ∀ n : ℕ, f a ∈ A (PiNat.res a n)) ∧
      ∀ a b, a ≠ b → ¬ r.r (f a) (f b) := by
  classical
  have hdom : ∀ x : ℕ → Bool, x ∈ (inducedMap A).1 := fun x =>
    mem_inducedMap_fst_iff.mpr (hlim x)
  -- Symmetrize the sibling cross-inequivalence over Bool
  have hcross' : ∀ l : List Bool, ∀ a b : Bool, a ≠ b →
      ∀ x ∈ A (a :: l), ∀ y ∈ A (b :: l), ¬ r.r x y := by
    intro l a b hab
    cases a <;> cases b
    · exact absurd rfl hab
    · exact hcross l
    · exact fun x hx y hy hxy => hcross l y hy x hx (r.iseqv.symm hxy)
    · exact absurd rfl hab
  let f : (ℕ → Bool) → α := fun x => (inducedMap A).2 ⟨x, hdom x⟩
  have hmem : ∀ a n, f a ∈ A (PiNat.res a n) := fun a n => map_mem ⟨a, hdom a⟩ n
  -- Pairwise r-inequivalence via the first position where the branches differ
  have hanti : ∀ a b, a ≠ b → ¬ r.r (f a) (f b) := by
    intro s t hst
    have hdiff : ∃ n, s n ≠ t n := by
      by_contra h
      push Not at h
      exact hst (funext h)
    have hn₀ : s (Nat.find hdiff) ≠ t (Nat.find hdiff) := Nat.find_spec hdiff
    have hres_eq : PiNat.res s (Nat.find hdiff) = PiNat.res t (Nat.find hdiff) := by
      rw [PiNat.res_eq_res]
      intro i hi
      by_contra h
      exact Nat.find_min hdiff hi h
    have hfs := hmem s (Nat.find hdiff + 1)
    have hft := hmem t (Nat.find hdiff + 1)
    rw [PiNat.res_succ] at hfs hft
    rw [← hres_eq] at hft
    exact hcross' _ _ _ hn₀ (f s) hfs (f t) hft
  refine ⟨f, ?_, ?_, hmem, hanti⟩
  -- Continuity
  · exact hdiam.map_continuous.comp (by fun_prop)
  -- Injectivity from the antichain property and reflexivity of r
  · intro a b hfab
    by_contra hne
    apply hanti a b hne
    rw [hfab]

/-- **Splitting predicate → perfect antichain.** Let `P` be a "largeness" predicate on closed
subsets of a complete metric space such that every large set splits into two large pieces of
arbitrarily small diameter with no cross-`r`-equivalence. Then from any large set `E` one can
extract a continuous injection `f : (ℕ → Bool) → α` into `E` whose images are pairwise
`r`-inequivalent.

Sibling disjointness is not required of the splitting: it is never used (injectivity comes from
the antichain property and reflexivity of `r`). -/
theorem exists_antichain_map_of_splitting {α : Type u} [MetricSpace α] [CompleteSpace α]
    (r : Setoid α) (P : Set α → Prop)
    (hcl : ∀ F, P F → IsClosed F) (hne : ∀ F, P F → F.Nonempty)
    {E : Set α} (hE : P E)
    (hsplit : ∀ F, P F → ∀ ε : ENNReal, 0 < ε →
      ∃ F₀ F₁ : Set α, P F₀ ∧ P F₁ ∧ F₀ ⊆ F ∧ F₁ ⊆ F ∧
        Metric.ediam F₀ ≤ ε ∧ Metric.ediam F₁ ≤ ε ∧
        ∀ x ∈ F₀, ∀ y ∈ F₁, ¬ r.r x y) :
    ∃ f : (ℕ → Bool) → α,
      Continuous f ∧ Function.Injective f ∧ (∀ a, f a ∈ E) ∧
      ∀ a b, a ≠ b → ¬ r.r (f a) (f b) := by
  classical
  -- A positive null sequence of diameter bounds
  obtain ⟨u, -, upos', hu⟩ := exists_seq_strictAnti_tendsto' (zero_lt_one' ENNReal)
  have upos : ∀ n, 0 < u n := fun n => (upos' n).1
  choose F0 F1 hP0 hP1 hsub0 hsub1 hd0 hd1 hcr using hsplit
  -- Build the scheme recursively on List Bool, rooted at E
  let DP : List Bool → Subtype P := fun l => by
    induction l with
    | nil => exact ⟨E, hE⟩
    | cons a l ih =>
      cases a
      · exact ⟨F0 ih.1 ih.2 (u (l.length + 1)) (upos (l.length + 1)),
          hP0 ih.1 ih.2 (u (l.length + 1)) (upos (l.length + 1))⟩
      · exact ⟨F1 ih.1 ih.2 (u (l.length + 1)) (upos (l.length + 1)),
          hP1 ih.1 ih.2 (u (l.length + 1)) (upos (l.length + 1))⟩
  let A : List Bool → Set α := fun l => (DP l).1
  -- ClosureAntitone (all sets are closed, so this is just Antitone)
  have hanti : ClosureAntitone A := by
    apply CantorScheme.Antitone.closureAntitone
    · intro l a
      show (DP (a :: l)).1 ⊆ (DP l).1
      cases a
      · exact hsub0 (DP l).1 (DP l).2 _ (upos (l.length + 1))
      · exact hsub1 (DP l).1 (DP l).2 _ (upos (l.length + 1))
    · intro l
      exact hcl _ (DP l).2
  have hnonempty : ∀ l, (A l).Nonempty := fun l => hne _ (DP l).2
  -- VanishingDiam
  have hdiam : VanishingDiam A := by
    intro x
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    · simp
    rw [Filter.eventually_atTop]
    refine ⟨1, fun m hm => ?_⟩
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    show Metric.ediam (A (x n :: PiNat.res x n)) ≤ u (n + 1)
    cases x n
    · exact (hd0 (DP (PiNat.res x n)).1 (DP (PiNat.res x n)).2 _
        (upos ((PiNat.res x n).length + 1))).trans (by rw [PiNat.res_length])
    · exact (hd1 (DP (PiNat.res x n)).1 (DP (PiNat.res x n)).2 _
        (upos ((PiNat.res x n).length + 1))).trans (by rw [PiNat.res_length])
  -- Branch limits exist by completeness and closure-nesting
  have hlim : ∀ x : ℕ → Bool, (⋂ n, A (PiNat.res x n)).Nonempty := fun x =>
    mem_inducedMap_fst_iff.mp
      (by rw [hanti.map_of_vanishingDiam hdiam hnonempty]; exact Set.mem_univ x)
  -- Sibling cross-inequivalence
  have hcross : ∀ l : List Bool, ∀ x ∈ A (false :: l), ∀ y ∈ A (true :: l), ¬ r.r x y :=
    fun l => hcr (DP l).1 (DP l).2 (u (l.length + 1)) (upos (l.length + 1))
  obtain ⟨f, hcont, hinj, hmem, hanti'⟩ := exists_antichain_map r hlim hdiam hcross
  refine ⟨f, hcont, hinj, fun a => ?_, hanti'⟩
  have h0 := hmem a 0
  rwa [PiNat.res_zero] at h0

end CantorScheme
