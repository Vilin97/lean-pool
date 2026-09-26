/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Gonality.DivisorialGonality
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionIso
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.UnitSubdivisionPresentation
public import Mathlib.Tactic

/-!
# Transport of divisorial gonality, and gonality over regular subdivisions

This module supplies three ingredients for the tricycle formalization:

1. `divisorialGonality_of_laplacianEquiv` — divisorial gonality is an invariant
   of the Laplacian, so every presentation of a graph computes the same number.
2. `rank_ge_of_add_effective` and `le_divisorialGonality_of_forall` — the two
   little lemmas that turn "no positive-rank divisor of degree exactly `d`, for
   each `d < k`" into the bound `k ≤ divisorialGonality`.
3. `Spec.scale`, `Spec.regularSubdivisionGonality`, and their `CFGraph`-level
   counterparts `regularSubdivision` / `regularSubdivisionGonality` — the
   invariant `min_{k ≥ 1} dgon(σ_k(G))`.

## What the name `regularSubdivisionGonality` does and does not claim

Van Dobben de Bruyn–Smit–van der Wegen's Theorem 1.5 identifies
`min_{k ≥ 1} dgon(σ_k(G))` with the divisorial gonality of the **metric** graph
`Γ(G, 𝟙)`.  That theorem needs metric graphs, piecewise-linear rational
functions, Luo's Theorems 1.6 and 1.10, and a rational-LP lemma; none of that is
formalized here, and none of it is needed for the tricycle gap.  **So the
invariant is not called `metricGonality`.**  The identification with the metric
gonality is external and unformalized.

It is also **not** `stableGonality`, which is taken and means something strictly
smaller: Bodlaender–van der Wegen–van der Zanden (arXiv:1808.06921) define *stable
divisorial gonality* as the minimum of `dgon` over **all** subdivisions, with
independent per-edge subdivision counts, and Cornelissen–Kato–Kool's *stable
gonality* additionally allows adding leaves.  A subdivision with unequal
per-edge counts is the unit model of a *different* metric graph `Γ(G, ℓ)`, so
`sdgon(G) ≤ regularSubdivisionGonality G`, possibly strictly.

-/

@[expose] public section

namespace Utilities.Gonality

open Finset

open Utilities.Certificate

/-! ## Adding an effective divisor cannot lower the rank below one -/

/-- Adding an effective divisor preserves positive rank.  This is what upgrades
"no positive-rank divisor of degree exactly `d`" to a gonality bound without
re-running the smaller degrees. -/
theorem rank_ge_of_add_effective {G : CFGraph} {D E : CFDiv G} (hE : effective E)
    (hD : rank G D ≥ 1) : rank G (D + E) ≥ 1 := by
  rw [← rank_geq_iff]
  intro F hF
  have hwin : winnable G (D - F) := (rank_geq_iff G D 1).mpr hD F hF
  obtain ⟨A, hAeff, hAequiv⟩ := (winnable_iff_exists_effective G (D - F)).mp hwin
  refine (winnable_iff_exists_effective G (D + E - F)).mpr ⟨A + E, ?_, ?_⟩
  · intro v
    have := hAeff v
    have := hE v
    simp only [Pi.add_apply]
    omega
  · show (A + E) - (D + E - F) ∈ principalDivisors G
    have hrw : (A + E) - (D + E - F) = A - (D - F) := by ring
    rw [hrw]
    exact hAequiv

/-! ## Lower bounds on `divisorialGonality` -/

/-- Bounding the gonality from below is exactly bounding the degree of every
positive-rank effective divisor from below. -/
theorem le_divisorialGonality_of_forall {G : CFGraph} (h_conn : graphConnected G)
    {k : ℕ}
    (h : ∀ D : CFDiv G, effective D → rank G D ≥ 1 → (k : ℤ) ≤ deg D) :
    k ≤ divisorialGonality G := by
  obtain ⟨D, hEff, hDeg, hRank⟩ := exists_divisor_of_divisorialGonality h_conn
  have := h D hEff hRank
  rw [hDeg] at this
  exact_mod_cast this

/-- The form the tricycle lower bounds are actually proved in: no positive-rank
effective divisor of degree *exactly* `d` for any `d < k`.  `rank_ge_of_add_effective`
is what lets the smaller degrees be skipped. -/
theorem le_divisorialGonality_of_no_small {G : CFGraph} (h_conn : graphConnected G)
    {k : ℕ}
    (h : ∀ D : CFDiv G, effective D → deg D = ((k : ℤ) - 1) → ¬ (rank G D ≥ 1)) :
    k ≤ divisorialGonality G := by
  classical
  refine le_divisorialGonality_of_forall h_conn ?_
  intro D hEff hRank
  by_contra hlt
  push Not at hlt
  -- pad `D` up to degree `k - 1` with chips at an arbitrary vertex
  obtain ⟨v⟩ := G.instNonempty
  set m : ℕ := ((k : ℤ) - 1 - deg D).toNat with hm
  have hdegnn : 0 ≤ deg D := by
    have : effective D := hEff
    exact Finset.sum_nonneg fun x _ => this x
  have hmval : (m : ℤ) = (k : ℤ) - 1 - deg D := by
    rw [hm, Int.toNat_of_nonneg]; omega
  set E : CFDiv G := fun w => if w = v then (m : ℤ) else 0 with hE
  have hEeff : effective E := by
    intro w
    by_cases hw : w = v <;> simp [hE, hw]
  have hEdeg : deg E = (m : ℤ) := by
    show (∑ w : G.V, if w = v then (m : ℤ) else 0) = (m : ℤ)
    simp
  have hrank' : rank G (D + E) ≥ 1 := rank_ge_of_add_effective hEeff hRank
  have hdeg' : deg (D + E) = (k : ℤ) - 1 := by
    have : deg (D + E) = deg D + deg E := map_add deg D E
    rw [this, hEdeg, hmval]; ring
  have hEff' : effective (D + E) := by
    intro w
    have := hEff w
    have := hEeff w
    simp only [Pi.add_apply]
    omega
  exact h (D + E) hEff' hdeg' hrank'

/-! ## Divisorial gonality is a Laplacian invariant -/

theorem gonalitySet_eq_of_laplacianEquiv {G H : CFGraph}
    (equivalence : LaplacianEquiv G H) : gonalitySet G = gonalitySet H := by
  ext d
  constructor
  · rintro ⟨D, hEff, hDeg, hRank⟩
    exact ⟨equivalence.mapDiv D,
      (equivalence.effective_mapDiv_iff D).mpr hEff,
      by rw [equivalence.deg_mapDiv D]; exact hDeg,
      (equivalence.rank_mapDiv_ge_iff D 1).mpr hRank⟩
  · rintro ⟨D, hEff, hDeg, hRank⟩
    exact ⟨equivalence.symm.mapDiv D,
      (equivalence.symm.effective_mapDiv_iff D).mpr hEff,
      by rw [equivalence.symm.deg_mapDiv D]; exact hDeg,
      (equivalence.symm.rank_mapDiv_ge_iff D 1).mpr hRank⟩

/-- **Divisorial gonality is an invariant of the Laplacian.**  Every
presentation of the same graph computes the same number. -/
theorem divisorialGonality_of_laplacianEquiv {G H : CFGraph}
    (equivalence : LaplacianEquiv G H) :
    divisorialGonality G = divisorialGonality H := by
  unfold divisorialGonality
  rw [gonalitySet_eq_of_laplacianEquiv equivalence]

end Utilities.Gonality

namespace Utilities.Certificate.SubdivisionGraph.Spec

open Utilities.Gonality

variable {n p : ℕ}

/-! ## Regular subdivisions of a `Spec` -/

/-- `σ_k` of a subdivision specification: multiply every slot length by `k`. -/
def scale {n p : ℕ}
    (spec : Spec n p) (k : ℕ) (hk : 0 < k) : Spec n p where
  core := spec.core
  length := fun edge => k * spec.length edge
  core_nonempty := spec.core_nonempty
  core_loopless := spec.core_loopless
  length_pos := fun edge => Nat.mul_pos hk (spec.length_pos edge)

@[simp] theorem scale_length {n p : ℕ} (spec : Spec n p) (k : ℕ) (hk : 0 < k)
    (edge : Fin p) : (spec.scale k hk).length edge = k * spec.length edge := rfl

@[simp] theorem scale_core {n p : ℕ} (spec : Spec n p) (k : ℕ) (hk : 0 < k) :
    (spec.scale k hk).core = spec.core := rfl

/-- Scaling by one changes nothing (up to the relabeling that fixes everything
and only adjusts `1 * L` to `L`). -/
def scaleOneRelabeling {n p : ℕ} (spec : Spec n p) :
    (spec.scale 1 Nat.one_pos).Relabeling spec where
  coreEquiv := Equiv.refl _
  slotEquiv := Equiv.refl _
  reversed := fun _ => false
  length_eq := by intro edge; simp
  tail_eq := by intro edge; simp
  head_eq := by intro edge; simp

/-- **The regular-subdivision gonality of a subdivision-presented graph**:
`min_{k ≥ 1} dgon(σ_k)`, where `σ_k` multiplies every slot length by `k`.

See the module docstring for why this is neither `metricGonality` nor
`stableGonality`. -/
noncomputable def regularSubdivisionGonality {n p : ℕ} (spec : Spec n p) : ℕ :=
  sInf {d : ℕ | ∃ (k : ℕ) (hk : 0 < k), divisorialGonality (spec.scale k hk).graph = d}

theorem regularSubdivisionGonalitySet_nonempty {n p : ℕ} (spec : Spec n p) :
    {d : ℕ | ∃ (k : ℕ) (hk : 0 < k),
        divisorialGonality (spec.scale k hk).graph = d}.Nonempty :=
  ⟨_, 1, Nat.one_pos, rfl⟩

/-- The gonality of some `σ_k` bounds the invariant from above. -/
theorem regularSubdivisionGonality_le {n p : ℕ} (spec : Spec n p)
    {k : ℕ} (hk : 0 < k) {d : ℕ}
    (h : divisorialGonality (spec.scale k hk).graph = d) :
    spec.regularSubdivisionGonality ≤ d :=
  Nat.sInf_le ⟨k, hk, h⟩

/-- A uniform lower bound over all `k` bounds the invariant from below. -/
theorem le_regularSubdivisionGonality {n p : ℕ} (spec : Spec n p) {d : ℕ}
    (h : ∀ (k : ℕ) (hk : 0 < k), d ≤ divisorialGonality (spec.scale k hk).graph) :
    d ≤ spec.regularSubdivisionGonality := by
  obtain ⟨k, hk, heq⟩ :=
    Nat.sInf_mem (spec.regularSubdivisionGonalitySet_nonempty)
  rw [regularSubdivisionGonality, ← heq]
  exact h k hk

/-- The invariant never exceeds the divisorial gonality itself (`k = 1`). -/
theorem regularSubdivisionGonality_le_divisorialGonality {n p : ℕ}
    (spec : Spec n p) :
    spec.regularSubdivisionGonality ≤ divisorialGonality spec.graph := by
  refine spec.regularSubdivisionGonality_le Nat.one_pos ?_
  exact divisorialGonality_of_laplacianEquiv
    (Spec.laplacianEquiv _ _ spec.scaleOneRelabeling)


end Utilities.Certificate.SubdivisionGraph.Spec

namespace Utilities.Gonality

open Utilities.Certificate

/-! ## Regular subdivisions of an arbitrary `CFGraph` -/

/-- `σ_k(G)` for an arbitrary finite loopless multigraph, built on the
occurrence-safe unit subdivision presentation of `G`. -/
noncomputable def regularSubdivision (G : CFGraph) (k : ℕ) (hk : 0 < k) : CFGraph :=
  ((UnitSubdivisionPresentation.spec G).scale k hk).graph

/-- `min_{k ≥ 1} dgon(σ_k(G))` for an arbitrary finite loopless multigraph. -/
noncomputable def regularSubdivisionGonality (G : CFGraph) : ℕ :=
  (UnitSubdivisionPresentation.spec G).regularSubdivisionGonality

theorem regularSubdivisionGonality_le_divisorialGonality (G : CFGraph) :
    regularSubdivisionGonality G ≤ divisorialGonality G := by
  rw [regularSubdivisionGonality,
    divisorialGonality_of_laplacianEquiv (UnitSubdivisionPresentation.laplacianEquiv G)]
  exact Utilities.Certificate.SubdivisionGraph.Spec.regularSubdivisionGonality_le_divisorialGonality
    _

end Utilities.Gonality
